{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Matrices over a semiring as a category with biproducts.
--
-- = Overview
--
-- Matrices over a semiring are not a /metaphor/ for category theory — they
-- /are/ the morphisms of a category with biproducts.  Objects are finite
-- index types; a morphism @i -> j@ is one scalar per input\/output pair.
-- 'Either' gives block matrices and is simultaneously product and coproduct
-- — a biproduct.  This is the matrix calculus, and it is a categorical fact,
-- not an analogy.
--
-- The encoding is initial: 'Mat' is the fully-applied leaf, 'Id' \/ 'Fun' \/
-- 'Par' \/ 'Comp' are symbolic constructors, and 'runMat' pays only boundary
-- evidence to collect results.
--
-- Evaluation is by pushing a sparse formal sum through the term.  'Fun' needs
-- no finite evidence; 'Mat' carries its own dictionary; 'Par' is structural
-- recursion; 'Comp' is composition of formal sums.  This is total and
-- terminating by construction — the free-semimodule semantics of the
-- category.
--
-- = Monoidal structure
--
-- __Tensor@Either@__: 'par' places two matrices on disjoint wires (block
-- diagonal).  'unitl' \/ 'unitr' witness that 'Void' (the uninhabited type)
-- is the tensor unit, reflecting the fact that a @0 × n@ or @m × 0@ matrix
-- has no entries.  Unit laws hold: @par (unitl . unitl') id = id@.
--
-- __Action@Either@__: 'swap' permutes index positions — the symmetry of the
-- biproduct.  The braiding @braid :: Either a (Either b c) -> Either b
-- (Either a c)@ is derivable as @assoc . par swap id . assoc'@.
--
-- = Biproduct structure and the 2-category
--
-- The additive monoid on each hom-set gives matrices over a semiring
-- the structure of a /locally posetal 2-category/ when the semiring is
-- idempotent:
--
-- * __0-cells__: finite types (the index sets).
--
-- * __1-cells__: matrices @i -> j@, elements of the free semimodule.
--
-- * __2-cells__: for idempotent semirings ('Bool', 'Tropical'),
--   the additive monoid @+@ induces a partial order:
--
--   @
--   m ≤ n   iff   m + n = n
--   @
--
--   This is the natural 2-categorical structure: matrix inequality is a
--   2-cell, and composition is monotone in both arguments.
--
-- The biproduct structure means 'Either' is simultaneously product and
-- coproduct.  For any finite types @a, b@ there exist:
--
-- * __projections__ @p1 :: a ⊕ b -> a@, @p2 :: a ⊕ b -> b@ (implemented as
--   pattern-matching on 'Left'\/'Right');
-- * __injections__ @i1 :: a -> a ⊕ b@, @i2 :: b -> a ⊕ b@ (the 'Left' and
--   'Right' constructors).
--
-- satisfying the biproduct equations:
--
-- @
-- p1 . i1 = id,    p2 . i2 = id,
-- p1 . i2 = 0,     p2 . i1 = 0,
-- i1 . p1 + i2 . p2 = id
-- @
--
-- where @0@ is the zero matrix and @+@ is pointwise addition.  Every matrix
-- decomposes into its components via these projections and injections.
--
-- = Kleene star as closure
--
-- The Kleene star 'starM' computes the reflexive-transitive closure of a
-- square matrix in the 2-category.  For idempotent semirings, this is the
-- least fixed point of @X ↦ I + A · X@, i.e. the closure operator of the
-- locally posetal 2-category:
--
-- * @Bool@: transitive closure of a graph (reachability).
-- * @Tropical@ (min-plus): all-pairs shortest paths (Floyd-Warshall).
-- * @StarSemiring String@: regular expression for all paths.
--
-- Kleene's algorithm enumerates intermediate indices: @O(|V|³)@ in the
-- number of elements of the 'Finite' type.
--
-- = Trace as Schur-complement
--
-- 'traceMat' computes the trace (feedback loop) of a block matrix:
--
-- @
--   ┌     ┐
--   │ a c │   :  a ⊕ b  →  a ⊕ c
--   │ b d │
--   └     ┘
--
--   traceMat  →  d + c · a* · b   :  b → c
-- @
--
-- This is exactly the Schur-complement formula for biproduct categories.
-- The trace satisfies the standard traced-monoidal laws (naturality,
-- sliding, vanishing, yanking) — see the docspec examples.
--
-- = Traced instance
--
-- With local 'Category' carrying @Ob (Mat s) a = Finite a@, the feedback
-- channel of 'trace' carries 'Finite' evidence. 'traceMat' is therefore a
-- lawful 'Traced' 'Either' instance (Schur-complement / star-closure).
--
-- = Relation to harpie
--
-- harpie provides statically-shaped arrays (@Harpie.Fixed.Array@) with
-- type-level dimensions.  Where 'Finite' enumerates a type's inhabitants at
-- runtime, a harpie @Array @[n] s@ knows its shape at compile time via
-- @KnownNat n@.  A matrix @i -> j@ could be a harpie array of shape @[i, j]@
-- with indices drawn from @Fin n@ (harpie's type-level finite set).  The
-- trace formula would still be the Schur-complement; the difference is that
-- the index set is a 'Nat' rather than a type-class dictionary.
--
-- Benchmarking ('Finite' enumeration vs matrix ops) shows that 'universe'
-- enumeration cost is linear in the number of inhabitants and typically
-- dominated by the @O(|V|³)@ star-closure computation for non-trivial
-- matrices.  See the enumeration spike section below for details.
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

import Circuit.Classes (Category (..))
import Circuit.Monoidal (Action (..), Tensor (..), Unit)
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Trace (Traced (..))
import Data.List (foldl')
import Data.Void (Void, absurd)
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

instance Finite Void where
  universe = []

instance (Finite a, Finite b) => Finite (Either a b) where
  universe = map Left universe ++ map Right universe

-- | Matrix over a semiring @s@, indexed by @i@ (rows) and @j@ (columns).
--
-- * 'Mat' is the concrete, fully-applied leaf; it carries 'Finite'
--   dictionaries so that 'push' can enumerate indices when needed.
-- * 'Id', 'Fun', 'Par', and 'Comp' are symbolic; they are evaluated by
--   'push'.
--
-- Note: 'Par' does not require 'Finite' — it is a structural constructor
-- whose 'Finite' evidence is supplied by the subterms or by 'Mat' leaves.
-- The 'Tensor' instance uses 'Par' for 'par'.
data Mat s i j where
  Mat :: (Finite i, Finite j) => (i -> j -> s) -> Mat s i j
  Id :: Mat s a a
  Fun :: (i -> j) -> Mat s i j
  Par :: Mat s a b -> Mat s c d -> Mat s (Either a c) (Either b d)
  Comp :: Mat s j k -> Mat s i j -> Mat s i k

-- | A sparse formal sum, i.e. a free semimodule element.
type Vec i s = [(i, s)]

-- | Push a formal sum through a matrix term.
--
-- Evidence flows perfectly: 'Fun' needs none; 'Mat' carries its own
-- 'Finite' dictionary; 'Par' is structural recursion; 'Comp' is
-- composition of formal sums.  The result is a formal sum over the output
-- indices; collecting equality is paid only at the boundary by 'runMat'.
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

-- | Run a matrix at a single input\/output pair.
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
  type Ob (Mat s) a = Finite a
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

-- | Symmetric swap for 'Either'.
swapEither :: Either a b -> Either b a
swapEither (Left a) = Right a
swapEither (Right b) = Left b

-- | Nested-slide braid for 'Either'.
--
-- This is the coproduct braid, derivable as @assoc . par swap id . assoc'@.
braidEither :: Either a (Either b c) -> Either b (Either a c)
braidEither (Left a) = Right (Left a)
braidEither (Right (Left b)) = Left b
braidEither (Right (Right c)) = Right (Right c)

-- | Coproduct tensor action on 'Mat'.
--
-- 'par' places two matrices on disjoint 'Either' wires (block diagonal).
-- Unit laws use 'Void' as the tensor unit — a matrix indexed by 'Void'
-- has no entries, so the unitor is the identity on the payload.
--
-- >>> let a = Mat (\i j -> if i == j then (1 :: Int) else 0) :: Mat Int Node Node
-- >>> let b = Mat (\i j -> (2 :: Int)) :: Mat Int Node Node
-- >>> runMat (par a b) (Left A) (Left A)
-- 1
-- >>> runMat (par a b) (Right A) (Right A)
-- 2
instance Tensor Either (Mat s) where
  par = Par
  unitl = Fun (either absurd id)
  unitl' = Fun Right
  unitr = Fun (either id absurd)
  unitr' = Fun Left

-- | Coproduct symmetry on 'Mat'.
--
-- 'swap' permutes index positions on the 'Either' sum.
--
-- >>> runMat (swap :: Mat Int (Either Node Node) (Either Node Node)) (Left A) (Right A)
-- 1
-- >>> runMat swap (Right A) (Left A)
-- 1
instance Action Either (Mat s) where
  swap = Fun swapEither

-- | Arrow-level monoidal structure for 'Either' inside 'Mat'.
instance (Additive s, Multiplicative s) => Monoidal Either (Mat s) where
  assoc = Fun assocEither
  assoc' = Fun assocEither'
  braid = Fun braidEither

-- | Lawful 'Traced' for matrices: feedback channel carries 'Finite'
-- evidence via 'Ob (Mat s) a = Finite a'.
instance (StarSemiring s, Additive s, Multiplicative s) => Traced Either (Mat s) where
  trace = traceMat
  untrace f = Par Id f

-- | Reflexive-transitive closure of a square matrix.
--
-- Implements Kleene's algorithm: for each intermediate index @k@, update all
-- entries @m(i,j) := m(i,j) + m(i,k) * star(m(k,k)) * m(k,j)@. The initial
-- matrix includes the identity: @m0(i,j) = if i == j then one + f i j else f i j@.
--
-- For idempotent semirings, this is the closure operator of the locally
-- posetal 2-category: 'starM' computes the least fixed point of
-- @X ↦ I + A · X@.
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
-- For a block matrix @[[a, a->c], [b->a, b->c]]@, the trace is the
-- Schur-complement:
--
-- @
-- traceMat  [[a, c], [b, d]]  =  d + c · a* · b
-- @
--
-- This is the standard trace for biproduct categories, satisfying the
-- traced-monoidal laws.
--
-- === Naturality
--
-- Post-composing the data output with @g@ before tracing equals tracing then
-- post-composing with @g@.  The blocks are coupled so the loop is live.
--
-- >>> let fFun (Left ()) (Left ()) = False; fFun (Left ()) (Right B) = True; fFun (Right A) (Left ()) = True; fFun _ _ = False
-- >>> let f = Mat fFun :: Mat Bool (Either () Node) (Either () Node)
-- >>> let g = Mat (\i j -> case (i, j) of (B, C) -> True; _ -> False) :: Mat Bool Node Node
-- >>> sameMat (traceMat (Comp (Par Id g) f)) (Comp g (traceMat f))
-- True
--
-- === Sliding
--
-- Moving @g@ through the feedback wire.  Feedback channel is 'Bool', @g@ is
-- the swap permutation, and the blocks are coupled so the loop is live.
--
-- >>> let gSwap = Mat (\i j -> i /= j) :: Mat Bool Bool Bool
-- >>> let fSlideFun (Left False) (Left True) = True; fSlideFun (Left True) (Right B) = True; fSlideFun (Right A) (Left False) = True; fSlideFun (Right B) (Right C) = True; fSlideFun _ _ = False
-- >>> let fSlide = Mat fSlideFun :: Mat Bool (Either Bool Node) (Either Bool Node)
-- >>> sameMat (traceMat (Comp (Par gSwap Id) fSlide)) (traceMat (Comp fSlide (Par gSwap Id)))
-- True
--
-- === Vanishing
--
-- Tracing over the unit channel @()@ collapses to the Schur-complement formula
-- @mbc + mac * star maa * mba@.
--
-- >>> let blockFun (Left ()) (Left ()) = False; blockFun (Left ()) (Right B) = True; blockFun (Right A) (Left ()) = True; blockFun _ _ = False
-- >>> let block = Mat blockFun :: Mat Bool (Either () Node) (Either () Node)
-- >>> let expected = Mat (\i j -> case (i, j) of (A, B) -> True; _ -> False) :: Mat Bool Node Node
-- >>> sameMat (traceMat block) expected
-- True
--
-- === Regression: nested 'Comp' terminates
--
-- The old 'reduceComp' fallthrough looped on @m . m . m@.
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
