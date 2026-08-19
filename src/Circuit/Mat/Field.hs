{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Matrix field calculus for dense, statically-shaped matrices.
--
-- This module provides Cholesky decomposition, triangular-matrix inversion,
-- and square-matrix inversion for 'Harpie.Fixed.Array' matrices.  All
-- operations are expressed in NumHask algebraic classes rather than GHC's
-- 'Num'/'Floating' hierarchy, so they work for any scalar that satisfies the
-- required field structure.
--
-- The matrix-level 'Multiplicative' and 'Divisive' instances are also provided
-- here, in @circuits-mat@, rather than in @harpie@: @harpie@ stays a generic
-- array library with relaxed element-wise constraints, while matrix calculus
-- lives in the categorical/linear-algebra layer.
module Circuit.Mat.Field
  ( -- * Square matrix alias
    MatrixM,

    -- * Field calculus
    cholM,
    invtriM,
    inverseM,
    luM,
    luRank1M,
    householderStep,

    -- * Matrix-as-ring wrapper
    MatField (..),
  )
where

import Data.List (maximumBy)
import Data.Ord (comparing)
import GHC.TypeNats (KnownNat)
import Harpie.Fixed (Array, Matrix)
import Harpie.Fixed qualified as F
import Harpie.Shape (KnownNats)
import Harpie.Shape qualified as S
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Field (ExpField (..))
import NumHask.Algebra.Metric (Absolute, abs, signum)
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Prelude hiding (sum)

-- $setup
--
-- >>> :set -XDataKinds
-- >>> :set -XTypeApplications
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude
-- >>> import Harpie.Fixed qualified as F
-- >>> import Prettyprinter hiding (dot, fill)
-- >>> import Circuit.Mat.Field

-- | A square matrix of statically-known size.
type MatrixM n a = Matrix n n a

-- | Cholesky decomposition using the
-- <https://en.wikipedia.org/wiki/Cholesky_decomposition#The_Cholesky_algorithm Cholesky-Crout>
-- algorithm.
--
-- >>> e = F.array @[3,3] @Double [4,12,-16,12,37,-43,-16,-43,98]
-- >>> pretty (cholM e)
-- [[2.0,0.0,0.0],
--  [6.0,1.0,0.0],
--  [-8.0,5.0,3.0]]
-- >>> F.mult (cholM e) (F.transpose (cholM e)) == e
-- True
cholM ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a
  ) =>
  MatrixM n a ->
  MatrixM n a
cholM a = l
  where
    l = F.tabulate (\s -> norm_ 1 l s (F.index a s - cross_ l s))

norm_ ::
  forall n a.
  ( KnownNat n,
    Additive a,
    Multiplicative a,
    Divisive a,
    ExpField a
  ) =>
  Int ->
  MatrixM n a ->
  S.Fins '[n, n] ->
  a ->
  a
norm_ d l (S.UnsafeFins s) = bool (recip (diagL F.! [S.getDimL d s]) *) sqrt (S.isDiagL s)
  where
    diagL = F.diag l

-- | Cross term @sum_k l[i,k] * l[j,k]@ used by Cholesky-Crout.
cross_ ::
  forall n a.
  ( KnownNat n,
    Additive a,
    Multiplicative a
  ) =>
  MatrixM n a ->
  S.Fins '[n, n] ->
  a
cross_ l s = sum [l F.! [i, k] * l F.! [j, k] | k <- [0 .. j - 1]]
  where
    ij = S.fromFins s
    (i, j) = case ij of
      [x, y] -> (x, y)
      _ -> error "cross_: invalid Fins dimension (expected 2D index)"

-- | Inverse of a square matrix via Cholesky decomposition.
--
-- >>> e = F.array @[3,3] @Double [4,12,-16,12,37,-43,-16,-43,98]
-- >>> pretty (inverseM e)
-- [[49.36111111111111,-13.555555555555554,2.1111111111111107],
--  [-13.555555555555554,3.7777777777777772,-0.5555555555555555],
--  [2.1111111111111107,-0.5555555555555555,0.1111111111111111]]
inverseM ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a
  ) =>
  MatrixM n a ->
  MatrixM n a
inverseM a = F.mult (invtriM (F.transpose (cholM a))) (invtriM (cholM a))

-- | LU decomposition with partial pivoting.
--
-- Returns @(p, l, u)@ such that @a = p^T . l . u@, where @p@ is the
-- accumulated row-permutation matrix, @l@ is unit lower triangular, and @u@ is
-- upper triangular.  The algorithm is the standard iterative Schur-complement
-- update: at each pivot @k@, swap the pivot row into place, then eliminate the
-- rows below by a rank-1 update.
--
-- The Schur step @a' = a - c . r@ is an outer product followed by subtraction,
-- which is the matrix-level reading of the trace / feedback pattern used in
-- circuit constructions.
luM ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    Absolute a,
    Ord a,
    Show a
  ) =>
  MatrixM n a ->
  (MatrixM n a, MatrixM n a, MatrixM n a)
luM a = (p, l, u)
  where
    n = S.valueOf @n
    (p, m) = foldl step (F.ident @[n, n], a) [0 .. n - 2]
    step (p0, m0) k =
      let pivotRow = maximumBy (comparing (\i -> abs (m0 F.! [i, k]))) [k .. n - 1]
          p1 = swapRows k pivotRow p0
          m1 = swapRows k pivotRow m0
          m2 =
            F.tabulate $ \s -> case S.fromFins s of
              [i, j]
                | i > k && j > k ->
                    let mult = m1 F.! [i, k] / m1 F.! [k, k]
                     in m1 F.! [i, j] - mult * m1 F.! [k, j]
                | i > k && j == k -> m1 F.! [i, k] / m1 F.! [k, k]
                | otherwise -> m1 F.! [i, j]
              _ -> error "luM: expected rank-2 index"
       in (p1, m2)
    l =
      F.tabulate $ \s -> case S.fromFins s of
        [i, j]
          | i == j -> one
          | i > j -> m F.! [i, j]
          | otherwise -> zero
        _ -> error "luM: expected rank-2 index"
    u =
      F.tabulate $ \s -> case S.fromFins s of
        [i, j]
          | i <= j -> m F.! [i, j]
          | otherwise -> zero
        _ -> error "luM: expected rank-2 index"

-- | LU decomposition via iterated rank-1 updates.
--
-- This is the same factorisation as 'luM', but the Schur-complement step is
-- written explicitly as an outer-product contraction:
--
-- > A' = A - c ⊗ r
--
-- where @c@ is the column of multipliers below the pivot and @r@ is the pivot
-- row.  The outer product uses 'F.expand' and the subtraction is elementwise;
-- together they are the matrix-level reading of the trace / feedback pattern.
--
-- The result agrees with 'luM' on any invertible square matrix.
luRank1M ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    Absolute a,
    Ord a,
    Show a
  ) =>
  MatrixM n a ->
  (MatrixM n a, MatrixM n a, MatrixM n a)
luRank1M a = (p, l, u)
  where
    n = S.valueOf @n
    ((p, m), lAcc) = foldl step ((F.ident @[n, n], a), F.konst @[n, n] zero) [0 .. n - 2]
    step ((p0, m0), l0) k =
      let pivotRow = maximumBy (comparing (\i -> abs (m0 F.! [i, k]))) [k .. n - 1]
          p1 = swapRows k pivotRow p0
          m1 = swapRows k pivotRow m0
          l1 = swapRows k pivotRow l0
          pivot = m1 F.! [k, k]
          mult i = m1 F.! [i, k] / pivot
          c :: F.Array '[n] a
          c =
            F.tabulate $ \s -> case S.fromFins s of
              [i]
                | i > k -> mult i
                | otherwise -> zero
              _ -> error "luRank1M: expected rank-1 index"
          r :: F.Array '[n] a
          r =
            F.tabulate $ \s -> case S.fromFins s of
              [j]
                | j >= k -> m1 F.! [k, j]
                | otherwise -> zero
              _ -> error "luRank1M: expected rank-1 index"
          m2 = F.zipWith (-) m1 (F.expand (*) c r)
          l2 =
            F.tabulate $ \s -> case S.fromFins s of
              [i, j]
                | j == k && i > k -> mult i
                | otherwise -> l1 F.! [i, j]
              _ -> error "luRank1M: expected rank-2 index"
       in ((p1, m2), l2)
    l =
      F.tabulate $ \s -> case S.fromFins s of
        [i, j]
          | i == j -> one
          | i > j -> lAcc F.! [i, j]
          | otherwise -> zero
        _ -> error "luRank1M: expected rank-2 index"
    u =
      F.tabulate $ \s -> case S.fromFins s of
        [i, j]
          | i <= j -> m F.! [i, j]
          | otherwise -> zero
        _ -> error "luRank1M: expected rank-2 index"

-- | Apply a Householder reflection to zero the subdiagonal of column @k@.
--
-- For column @x = a[:,k]@, compute a reflector @H = I - 2 v v^T / (v^T v)@
-- such that @H x = α e_k@ with @α = -sign(x[k]) · ||x||@.  The action on the
-- whole matrix is the rank-1 update
--
-- > a' = a - (2 / (v^T v)) · v ⊗ (v^T a)
--
-- where @v^T a@ is a contraction over the row axis and @v ⊗ (...)@ is an
-- outer product.  This is the circuit-native QR step: a scheduled reflection
-- implemented as expand / contract / subtract.
householderStep ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a,
    Absolute a,
    Ord a,
    Show a
  ) =>
  Int ->
  MatrixM n a ->
  MatrixM n a
householderStep k a = F.zipWith (-) a (fmap (scale *) outer)
  where
    x :: F.Array '[n] a
    x = F.tabulate $ \s -> case S.fromFins s of
      [i] -> a F.! [i, k]
      _ -> error "householderStep: expected rank-1 index"
    xk = x F.! [k]
    norm = sqrt (sum [(x F.! [i]) * (x F.! [i]) | i <- [0 .. S.valueOf @n - 1]])
    alpha = bool (negate norm) norm (xk < zero)
    v :: F.Array '[n] a
    v = F.tabulate $ \s -> case S.fromFins s of
      [i]
        | i < k -> zero
        | i == k -> xk - alpha
        | otherwise -> x F.! [i]
      _ -> error "householderStep: expected rank-1 index"
    vtv = sum [(v F.! [i]) * (v F.! [i]) | i <- [0 .. S.valueOf @n - 1]]
    scale = (one + one) / vtv
    -- v^T a: contract v's only axis with a's row axis, leaving columns.
    vta :: F.Array '[n] a
    vta = F.prod (F.Dims @'[0]) (F.Dims @'[0]) sum (*) v a
    -- outer product v ⊗ (v^T a), shape [n, n].
    outer = F.expand (*) v vta

-- | Swap two rows of a matrix.
swapRows ::
  forall n a.
  (KnownNats '[n, n]) =>
  Int ->
  Int ->
  MatrixM n a ->
  MatrixM n a
swapRows k p = F.unsafeBackpermute $ \case
  [i, j]
    | i == k -> [p, j]
    | i == p -> [k, j]
    | otherwise -> [i, j]
  _ -> error "swapRows: expected rank-2 index"

-- | Inversion of a triangular matrix.
--
-- >>> t = F.array @[3,3] @Double [1,0,1,0,1,2,0,0,1]
-- >>> pretty (invtriM t)
-- [[1.0,0.0,-1.0],
--  [0.0,1.0,-2.0],
--  [0.0,0.0,1.0]]
-- >>> F.ident @[3,3] == F.mult t (invtriM t)
-- True
invtriM ::
  forall n a.
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a
  ) =>
  MatrixM n a ->
  MatrixM n a
invtriM a = i
  where
    ti = F.undiag (fmap recip (F.diag a))
    tl = F.zipWith (-) a (F.undiag (F.diag a))
    l = fmap negate (F.mult ti tl)
    pow xs x = foldr ($) (F.ident @[n, n]) (replicate x (F.mult xs))
    zero' = F.konst @[n, n] zero
    add = F.zipWith (+)
    sum' = foldl' add zero'
    i = F.mult (sum' (fmap (pow l) (F.range @'[n]))) ti

-- | Newtype wrapper that gives square matrices a multiplicative (and, over a
-- field, divisible) structure.
--
-- The unit is the identity matrix; multiplication is the usual matrix product.
-- Division uses Cholesky-based inversion.
newtype MatField n a = MatField {unMatField :: MatrixM n a}
  deriving stock (Eq, Show)

instance
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Multiplicative a
  ) =>
  Multiplicative (MatField n a)
  where
  one = MatField (F.ident @[n, n])
  MatField x * MatField y = MatField (F.mult x y)

instance
  ( KnownNat n,
    KnownNats '[n, n],
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a
  ) =>
  Divisive (MatField n a)
  where
  recip (MatField x) = MatField (inverseM x)
  MatField x / MatField y = MatField (F.mult x (inverseM y))
