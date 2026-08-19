{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Complex multiplication as a structure-constant contraction in
-- @Circuit.Mat@.
--
-- A complex number is a vector @(F 2 -> s)@: slot 0 is real, slot 1 is
-- imaginary.  The product is the contraction of the outer product against the
-- structure-constant tensor of @R[x]/(x² + 1)@.
module Circuit.Mat.Complex
  ( complexSMul,
    structureConst,
  )
where

import Circuit.Mat (Finite, Mat (..), runMat)
import Circuit.Mat.Harpie (F (..), fromF)
import Harpie.Shape (fromFin)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import Prelude hiding (id, negate, sum, (*), (+), (-))

-- | Structure-constant tensor for @ℂ = R[x]/(x² + 1)@.
--
-- @c k i j@ is the coefficient of @a[i] * b[j]@ in output component @k@.
structureConst ::
  (Additive s, Multiplicative s, Subtractive s) =>
  F 2 ->
  F 2 ->
  F 2 ->
  s
structureConst i j k =
  case (ix i, ix j, ix k) of
    (0, 0, 0) -> one
    (1, 1, 0) -> zero - one
    (0, 1, 1) -> one
    (1, 0, 1) -> one
    _ -> zero
  where
    ix = fromFin . fromF

-- | Complex multiplication as a @Mat@ contraction.
--
-- @complexSMul a b k@ returns component @k@ of the product of the two complex
-- numbers @a@ and @b@.
complexSMul ::
  (Additive s, Multiplicative s, Subtractive s, Eq (F 2), Eq (F 2, F 2), Finite (F 2, F 2)) =>
  (F 2 -> s) ->
  (F 2 -> s) ->
  F 2 ->
  s
complexSMul a b = runMat (cMat `Comp` outerProd) ()
  where
    outerProd = Mat $ \() (i, j) -> a i * b j
    cMat = Mat $ \(i, j) k -> structureConst i j k
