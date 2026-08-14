{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
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

    -- * Matrix-as-ring wrapper
    MatField (..),
  )
where

import GHC.TypeNats (KnownNat)
import Harpie.Fixed qualified as F
import Harpie.Fixed (Array, Matrix)
import Harpie.Shape (KnownNats)
import Harpie.Shape qualified as S
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Field (ExpField (..))
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
  deriving stock (Show)

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
