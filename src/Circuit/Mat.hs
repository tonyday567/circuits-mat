{-# LANGUAGE GADTs #-}

-- | Matrices over a semiring as an initial-encoding category.
--
-- Objects are index types; a morphism @i -> j@ is one scalar per input/output
-- pair. The 'Either' tensor gives block matrices. The encoding is initial:
-- 'Mat' is the fully-applied leaf, 'Id' / 'Fun' / 'Par' / 'Comp' are symbolic
-- constructors, and 'runMat' pays only boundary evidence to collect results.
--
-- Evaluation is by pushing a sparse formal sum through the term. 'Fun' needs no
-- finite evidence; 'Mat' and 'Par' carry their own dictionaries; 'Comp' is
-- structural recursion. This is total and terminating by construction — the
-- free-semimodule semantics of the category.
--
-- The design is intentionally parallel to 'Circuit.Trace': keep structure
-- symbolic, evaluate later. The one method that cannot be made evidence-free
-- is 'trace', because closing a matrix loop means enumerating the feedback
-- channel and taking star. Hence 'traceMat' stays explicit and 'Traced' is not
-- an instance this round.
module Circuit.Mat
  ( -- * Finite index types
    Finite (..),

    -- * Matrices
    Mat (..),
    runMat,

    -- * Closure
    starM,

    -- * Trace (explicit finite-channel form)
    traceMat,
  )
where

import Circuit.Monoidal.Category (Monoidal (..))
import Control.Category (Category (..))
import Data.List (foldl')
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding (id, sum, (*), (+), (.))

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> :set -XStandaloneDeriving
-- >>> import NumHask.Prelude
-- >>> import NumHask.Algebra.Tropical
-- >>> import Circuit.Mat
-- >>> data Node = A | B | C deriving (Eq, Ord, Enum, Bounded, Show)
-- >>> instance Finite Node where universe = [A, B, C]
-- >>> let sameMat m n = [runMat m i j | i <- universe, j <- universe] == [runMat n i j | i <- universe, j <- universe]

-- | A finite index type: enumerable and comparable.
class (Eq a) => Finite a where
  universe :: [a]

instance Finite () where
  universe = [()]

instance Finite Bool where
  universe = [False, True]

instance (Finite a, Finite b) => Finite (Either a b) where
  universe = map Left universe ++ map Right universe

-- | Matrix over a semiring @s@, indexed by @i@ (rows) and @j@ (columns).
--
-- * 'Mat' is the concrete, fully-applied leaf; it carries 'Finite' dictionaries
--   so that 'push' can enumerate indices when needed.
-- * 'Id', 'Fun', 'Par', and 'Comp' are symbolic; they are evaluated by 'push'.
data Mat s i j where
  Mat :: (Finite i, Finite j) => (i -> j -> s) -> Mat s i j
  Id :: Mat s a a
  Fun :: (i -> j) -> Mat s i j
  Par ::
    (Finite a, Finite b, Finite c, Finite d) =>
    Mat s a b ->
    Mat s c d ->
    Mat s (Either a c) (Either b d)
  Comp :: Mat s j k -> Mat s i j -> Mat s i k

-- | A sparse formal sum, i.e. a free semimodule element.
type Vec i s = [(i, s)]

-- | Push a formal sum through a matrix term.
--
-- Evidence flows perfectly: 'Fun' needs none; 'Mat'/'Par' carry their own
-- 'Finite' dictionaries; 'Comp' is structural recursion. The result is a formal
-- sum over the output indices; collecting equality is paid only at the boundary
-- by 'runMat'.
push ::
  (Additive s, Multiplicative s) =>
  Vec i s ->
  Mat s i j ->
  Vec j s
push v Id = v
push v (Fun f) = [(f i, x) | (i, x) <- v]
push v (Mat f) = [(j, x * f i j) | (i, x) <- v, j <- universe]
push v (Par m n) = lefts ++ rights
  where
    vLeft = [(a, x) | (Left a, x) <- v]
    vRight = [(c, x) | (Right c, x) <- v]
    lefts = [(Left b, x) | (b, x) <- push vLeft m]
    rights = [(Right d, x) | (d, x) <- push vRight n]
push v (Comp g f) = push (push v f) g

-- | Run a matrix at a single input/output pair.
--
-- Equality evidence is required only at the boundary (the output index).
runMat ::
  (Additive s, Multiplicative s, Eq j) =>
  Mat s i j ->
  i ->
  j ->
  s
runMat m i j = sum [x | (j', x) <- push [(i, one)] m, j' == j]

instance Category (Mat s) where
  id = Id
  (.) = Comp

-- | Associator for 'Either'.
assocEither :: Either (Either a b) c -> Either a (Either b c)
assocEither (Left (Left a)) = Left a
assocEither (Left (Right b)) = Right (Left b)
assocEither (Right c) = Right (Right c)

-- | Inverse associator for 'Either'.
assocEither' :: Either a (Either b c) -> Either (Either a b) c
assocEither' (Left a) = Left (Left a)
assocEither' (Right (Left b)) = Left (Right b)
assocEither' (Right (Right c)) = Right c

-- | Nested-slide braid for 'Either'.
--
-- This is the circuits braid, not a plain swap.
braidEither :: Either a (Either b c) -> Either b (Either a c)
braidEither (Left a) = Right (Left a)
braidEither (Right (Left b)) = Left b
braidEither (Right (Right c)) = Right (Right c)

instance Monoidal Either (Mat s) where
  assoc = Fun assocEither
  assoc' = Fun assocEither'
  braid = Fun braidEither

-- | Reflexive-transitive closure of a square matrix.
--
-- Implements Kleene's algorithm: for each intermediate index @k@, update all
-- entries @m(i,j) := m(i,j) + m(i,k) * star(m(k,k)) * m(k,j)@. The initial
-- matrix includes the identity: @m0(i,j) = if i == j then one + f i j else f i j@.
--
-- >>> let g = Mat (\i j -> case (i, j) of (A, B) -> True; (B, C) -> True; _ -> False) :: Mat Bool Node Node
-- >>> runMat (starM g) A C
-- True
--
-- >>> let w = Mat (\i j -> case (i, j) of (A, B) -> MinPlus 1; (B, C) -> MinPlus 2; (A, C) -> MinPlus 10; _ -> zero) :: Mat (MinPlus Double) Node Node
-- >>> getMinPlus (runMat (starM w) A C)
-- 3.0
starM :: (StarSemiring s, Additive s, Multiplicative s, Finite a) => Mat s a a -> Mat s a a
starM m = Mat (foldl' step start universe)
  where
    f = runMat m
    start i j = case i == j of True -> one + f i j; False -> f i j
    step stepm k i j = stepm i j + (stepm i k * star (stepm k k) * stepm k j)

-- | Explicit finite-channel composition for use inside 'traceMat'.
ecomp ::
  (Additive s, Multiplicative s, Finite i, Finite j, Finite k) =>
  Mat s j k ->
  Mat s i j ->
  Mat s i k
ecomp g f = Mat (\i k -> sum [runMat f i j * runMat g j k | j <- universe])

-- | Trace over an explicit finite feedback channel @a@.
--
-- For a block matrix @[[a,a->c],[b->a,b->c]]@, the trace is the Schur-complement:
-- @d + c * star(a) * b@.
--
-- Direct trace: feedback channel is @()@, data channel is 'Node', and the
-- off-diagonal blocks are coupled so 'star' actually fires.
--
-- >>> let fFun (Left ()) (Left ()) = False; fFun (Left ()) (Right B) = True; fFun (Right A) (Left ()) = True; fFun _ _ = False
-- >>> let f = Mat fFun :: Mat Bool (Either () Node) (Either () Node)
-- >>> runMat (traceMat f) A B
-- True
-- >>> runMat (traceMat f) A C
-- False
--
-- Naturality: post-composing the data output with @g@ before tracing equals
-- tracing then post-composing with @g@. The blocks are coupled so the loop is
-- live.
--
-- >>> let g = Mat (\i j -> case (i, j) of (B, C) -> True; _ -> False) :: Mat Bool Node Node
-- >>> sameMat (traceMat (Comp (Par Id g) f)) (Comp g (traceMat f))
-- True
--
-- Sliding: moving @g@ through the feedback wire. Feedback channel is 'Bool',
-- @g@ is the swap permutation, and the blocks are coupled so the loop is live.
--
-- >>> let gSwap = Mat (\i j -> i /= j) :: Mat Bool Bool Bool
-- >>> let fSlideFun (Left False) (Left True) = True; fSlideFun (Left True) (Right B) = True; fSlideFun (Right A) (Left False) = True; fSlideFun (Right B) (Right C) = True; fSlideFun _ _ = False
-- >>> let fSlide = Mat fSlideFun :: Mat Bool (Either Bool Node) (Either Bool Node)
-- >>> sameMat (traceMat (Comp (Par gSwap Id) fSlide)) (traceMat (Comp fSlide (Par gSwap Id)))
-- True
-- >>> runMat (traceMat (Comp (Par gSwap Id) fSlide)) A B
-- True
-- >>> runMat (traceMat (Comp (Par gSwap Id) fSlide)) B C
-- True
--
-- Vanishing: tracing over the unit channel @()@ collapses to the
-- Schur-complement formula @mbc + mac * star maa * mba@.
--
-- >>> let blockFun (Left ()) (Left ()) = False; blockFun (Left ()) (Right B) = True; blockFun (Right A) (Left ()) = True; blockFun _ _ = False
-- >>> let block = Mat blockFun :: Mat Bool (Either () Node) (Either () Node)
-- >>> let expected = Mat (\i j -> case (i, j) of (A, B) -> True; _ -> False) :: Mat Bool Node Node
-- >>> sameMat (traceMat block) expected
-- True
--
-- Regression: nested 'Comp' terminates. The old 'reduceComp' fallthrough looped
-- on @m . m . m@.
--
-- >>> let m = Mat (\i j -> case (i, j) of (A, A) -> True; (A, B) -> True; (B, B) -> True; _ -> False) :: Mat Bool Node Node
-- >>> runMat (Comp m (Comp m m)) A B
-- True
-- >>> runMat (Comp m (Comp m m)) B A
-- False
traceMat ::
  (StarSemiring s, Additive s, Multiplicative s, Finite a, Finite b, Finite c) =>
  Mat s (Either a b) (Either a c) ->
  Mat s b c
traceMat m = mbc `addMat` ecomp (ecomp mac (starM maa)) mba
  where
    maa = Mat (\i j -> runMat m (Left i) (Left j))
    mac = Mat (\i j -> runMat m (Left i) (Right j))
    mba = Mat (\i j -> runMat m (Right i) (Left j))
    mbc = Mat (\i j -> runMat m (Right i) (Right j))
    addMat x y = Mat (\i j -> runMat x i j + runMat y i j)
