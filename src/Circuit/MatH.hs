{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Harpie-backed matrices as a traced monoidal category.
--
-- Objects are type-level naturals @i@ and @j@; a morphism @i -> j@ is a
-- harpie @Array @[i, j] s@.  This is the concrete carrier that the symbolic
-- 'Circuit.Mat.Mat' approximates: every matrix is stored as a single
-- rectangular array, and composition is a fused triple loop instead of pushing
-- a sparse formal sum through a term tree.
--
-- The design is intentionally explicit.  A 'Control.Category' instance is
-- impossible because 'id' and @('.')@ cannot carry the 'KnownNat' evidence
-- needed to enumerate indices, and the tensor unit / coproduct shape cannot be
-- expressed with Haskell's 'Data.Either.Either' at kind 'GHC.TypeNats.Nat'.
-- So we expose named operators: 'idH', 'compH', 'parH', 'swapH', 'traceH',
-- 'starH'.
--
-- = Coproduct as initial segment
--
-- The biproduct tensor is realised by the standard disjoint-union isomorphism
-- already present in 'Circuit.Mat.Harpie':
--
-- @
-- Either (F i) (F j)  ≅  F (i + j)
-- @
--
-- 'parH' places two matrices block-diagonally inside a single array of shape
-- @[i + k, j + l]@, and 'swapH' is the corresponding index permutation on
-- @F (i + j)@.
--
-- = Fused composition
--
-- 'compH' tabulates over @[i, k]@ and folds the shared dimension @j@
-- directly:
--
-- @
-- (g `compH` f)[r, c] = Σₚ f[r, p] * g[p, c]
-- @
--
-- This avoids harpie's @dot sum (*)@, which first expands to a 4-D array and
-- then contracts, a known allocation hotspot.
--
-- = Trace and star via 'Circuit.Mat'
--
-- For this spike, 'traceH' and 'starH' convert to the function-based
-- 'Circuit.Mat.Mat', use 'Circuit.Mat.traceMat' / 'Circuit.Mat.starM', and
-- convert back.  Direct array-based versions are possible later, but the
-- Schur-complement formula is already correct and total here.
module Circuit.MatH
  ( -- * Matrix carrier
    MatH (..),

    -- * Conversion to and from functions
    tabulateH,
    runMatH,
    unsafeTabulateH,
    unsafeRunMatH,

    -- * Category structure
    idH,
    compH,

    -- * Monoidal / biproduct structure
    parH,
    swapH,
    unitlH,
    unitlH',
    unitrH,
    unitrH',

    -- * Closure and trace
    starH,
    traceH,
  )
where

import Circuit.Classes (Category (..))
import Circuit.Mat (Finite, Mat (..), runMat, starM, traceMat)
import Circuit.Mat.Harpie (F (..), eitherToF, fToEither, finF)
import Circuit.Monoidal (Action (..), Tensor (..), Unit)
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Trace (Traced (..))
import GHC.TypeNats (KnownNat, Nat, type (+))
import Harpie.Fixed (Array, unsafeIndex, unsafeTabulate)
import Harpie.Shape (Fin (..), valueOf)
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding (id, sum, (*), (+), (.))

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> :set -XDataKinds
-- >>> :set -XTypeApplications
-- >>> import NumHask.Prelude
-- >>> import Circuit.MatH
-- >>> import Circuit.Mat.Harpie (F (..), finF)
-- >>> import Harpie.Shape (Fin (..))

-- | A matrix @i -> j@ over a semiring @s@, stored as one harpie array.
newtype MatH s (i :: Nat) (j :: Nat) = MatH {unMatH :: Array '[i, j] s}

-- | Build a matrix from a function on 'F' indices.
tabulateH ::
  (KnownNat i, KnownNat j) =>
  (F i -> F j -> s) ->
  MatH s i j
tabulateH f = MatH $ unsafeTabulate $ \[r, c] -> f (F (UnsafeFin r)) (F (UnsafeFin c))

-- | Run a matrix at a single pair of 'F' indices.
runMatH ::
  (KnownNat i, KnownNat j) =>
  MatH s i j ->
  F i ->
  F j ->
  s
runMatH (MatH a) (F (UnsafeFin r)) (F (UnsafeFin c)) = unsafeIndex a [r, c]

-- | Build a matrix from a raw integer-indexed function.
unsafeTabulateH ::
  (KnownNat i, KnownNat j) =>
  (Int -> Int -> s) ->
  MatH s i j
unsafeTabulateH f = MatH $ unsafeTabulate $ \[r, c] -> f r c

-- | Run a matrix at raw integer positions.
unsafeRunMatH ::
  (KnownNat i, KnownNat j) =>
  MatH s i j ->
  Int ->
  Int ->
  s
unsafeRunMatH (MatH a) r c = unsafeIndex a [r, c]

-- | Identity matrix.
--
-- Note: a full @Tensor (+) (MatH s)@ instance needs an unsaturated type-level
-- tensor (data, not a type family) for @Unit@; keep named @parH@/@traceH@ for
-- now and use 'Category' with @Ob = KnownNat@.
idH ::
  (KnownNat n, Additive s, Multiplicative s) =>
  MatH s n n
idH = MatH $ unsafeTabulate $ \[r, c] -> case r == c of True -> one; False -> zero

-- | Fused matrix composition.
--
-- >>> let m = unsafeTabulateH @2 @2 (\i j -> if i == j then (1 :: Int) else 0)
-- >>> unsafeRunMatH (compH m m) 0 0
-- 1
-- >>> unsafeRunMatH (compH m m) 0 1
-- 0
compH ::
  forall s i j k.
  (KnownNat i, KnownNat j, KnownNat k, Additive s, Multiplicative s) =>
  MatH s j k ->
  MatH s i j ->
  MatH s i k
compH g f = tabulateH $ \r c ->
  sum
    [ runMatH f r (F (UnsafeFin p)) * runMatH g (F (UnsafeFin p)) c
      | p <- [0 .. valueOf @j - 1]
    ]

-- | Category of harpie matrices: objects are @Nat@s with 'KnownNat'.
instance (Additive s, Multiplicative s) => Category (MatH s) where
  type Ob (MatH s) a = KnownNat a
  id = idH
  (.) = compH

-- | Block-diagonal biproduct.
--
-- Left block occupies rows @[0, i)@ and columns @[0, j)@; right block
-- occupies the complementary rectangle.
--
-- >>> let a = unsafeTabulateH @2 @2 (\i j -> if i == j then (1 :: Int) else 0)
-- >>> let b = unsafeTabulateH @1 @1 (\_ _ -> (7 :: Int))
-- >>> unsafeRunMatH (parH a b) 1 1
-- 1
-- >>> unsafeRunMatH (parH a b) 2 2
-- 7
-- >>> unsafeRunMatH (parH a b) 0 2
-- 0
parH ::
  forall s i j k l.
  ( KnownNat i,
    KnownNat j,
    KnownNat k,
    KnownNat l,
    KnownNat (i + k),
    KnownNat (j + l),
    Additive s
  ) =>
  MatH s i j ->
  MatH s k l ->
  MatH s (i + k) (j + l)
parH (MatH m) (MatH n) = MatH $ unsafeTabulate $ \[r, c] ->
  case (r < valueOf @i, c < valueOf @j) of
    (True, True) -> unsafeIndex m [r, c]
    (False, False) -> unsafeIndex n [r - valueOf @i, c - valueOf @j]
    _ -> zero

-- | Symmetry of the biproduct, as an index permutation on @F (i + j)@.
--
-- >>> unsafeRunMatH (swapH @2 @3) 1 4
-- 1
-- >>> unsafeRunMatH (swapH @2 @3) 1 1
-- 0
swapH ::
  forall s i j.
  ( KnownNat i,
    KnownNat j,
    KnownNat (i + j),
    KnownNat (j + i),
    Additive s,
    Multiplicative s
  ) =>
  MatH s (i + j) (j + i)
swapH = tabulateH $ \(F (UnsafeFin r)) (F (UnsafeFin c)) ->
  let sigma x = case x < valueOf @i of True -> valueOf @j + x; False -> x - valueOf @i
   in case c == sigma r of True -> one; False -> zero

-- | Left unitor: @0 + j ≅ j@.
unitlH ::
  (KnownNat j, Additive s, Multiplicative s) =>
  MatH s (0 + j) j
unitlH = idH

-- | Inverse left unitor: @j ≅ 0 + j@.
unitlH' ::
  (KnownNat j, Additive s, Multiplicative s) =>
  MatH s j (0 + j)
unitlH' = idH

-- | Right unitor: @i + 0 ≅ i@.
unitrH ::
  (KnownNat i, Additive s, Multiplicative s) =>
  MatH s (i + 0) i
unitrH = idH

-- | Inverse right unitor: @i ≅ i + 0@.
unitrH' ::
  (KnownNat i, Additive s, Multiplicative s) =>
  MatH s i (i + 0)
unitrH' = idH

-- | Reflexive-transitive closure.
--
-- >>> let g = unsafeTabulateH @3 @3 (\i j -> case (i, j) of (0, 1) -> True; (1, 2) -> True; _ -> False) :: MatH Bool 3 3
-- >>> unsafeRunMatH (starH g) 0 2
-- True
starH ::
  (KnownNat n, StarSemiring s, Additive s, Multiplicative s) =>
  MatH s n n ->
  MatH s n n
starH = matHFromMat . starM . matHToMat

-- | Trace over a feedback channel of known size.
--
-- The block matrix has shape @[n + b, n + c]@; the result has shape
-- @[b, c]@ and is computed via the Schur-complement formula.
--
-- >>> let block = unsafeTabulateH @2 @2 (\i j -> case (i, j) of (0, 0) -> False; (0, 1) -> True; (1, 0) -> True; _ -> False) :: MatH Bool 2 2
-- >>> unsafeRunMatH (traceH @1 @1 @1 block) 0 0
-- True
traceH ::
  forall s n b c.
  ( KnownNat n,
    KnownNat b,
    KnownNat c,
    KnownNat (n + b),
    KnownNat (n + c),
    StarSemiring s,
    Additive s,
    Multiplicative s
  ) =>
  MatH s (n + b) (n + c) ->
  MatH s b c
traceH = matHFromMat . traceMat . matHToMatEither

-- | Convert a harpie matrix to the function-based 'Mat' over 'F' indices.
matHToMat ::
  (KnownNat i, KnownNat j) =>
  MatH s i j ->
  Mat s (F i) (F j)
matHToMat (MatH a) = Mat $ \(F (UnsafeFin r)) (F (UnsafeFin c)) -> unsafeIndex a [r, c]

-- | Convert a function-based 'Mat' over 'F' indices back to a harpie matrix.
matHFromMat ::
  (KnownNat i, KnownNat j, Additive s, Multiplicative s, Eq (F j)) =>
  Mat s (F i) (F j) ->
  MatH s i j
matHFromMat m = MatH $ unsafeTabulate $ \[r, c] -> runMat m (F (UnsafeFin r)) (F (UnsafeFin c))

-- | View a harpie matrix of shape @[n + b, n + c]@ as a block matrix whose
-- rows and columns are split by the coproduct isomorphism.
matHToMatEither ::
  forall s n b c.
  ( KnownNat n,
    KnownNat b,
    KnownNat c,
    KnownNat (n + b),
    KnownNat (n + c)
  ) =>
  MatH s (n + b) (n + c) ->
  Mat s (Either (F n) (F b)) (Either (F n) (F c))
matHToMatEither (MatH a) = Mat $ \r c ->
  let row = case r of
        Left (F (UnsafeFin x)) -> x
        Right (F (UnsafeFin x)) -> valueOf @n + x
      col = case c of
        Left (F (UnsafeFin x)) -> x
        Right (F (UnsafeFin x)) -> valueOf @n + x
   in unsafeIndex a [row, col]
