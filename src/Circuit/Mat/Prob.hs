{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | @Prob@ carrier for @Mat@.
--
-- A @Mat r i j@ is a linear map from input indices @i@ to output indices @j@
-- with weights in @r@.  That is exactly the linear fragment of the double-dual
-- probability arrow 'Circuit.Prob.Prob'.  This module gives the embedding that
-- lets a @Mat@ construction flow through the @Prob@ carrier with no rewrite.
module Circuit.Mat.Prob
  ( matToProb,
    runProbAt,
  )
where

import Circuit.Mat (Finite (..), Mat (..), runMat)
import Circuit.Prob (Prob (..))
import Data.Bool (bool)
import NumHask.Algebra.Additive (Additive (..), sum, zero)
import NumHask.Algebra.Multiplicative (Multiplicative (..), one)
import Prelude hiding (id, sum, (*), (+), (.))

-- | Embed a semiring matrix into the @Prob@ continuation carrier.
--
-- The resulting @Prob (->) r i j@ is the expectation transformer:
--
-- @
--   runProb (matToProb m) k (x, i) = Σⱼ m(i,j) · k(x,j)
-- @
matToProb ::
  forall r i j.
  (Additive r, Multiplicative r, Eq j, Finite i, Finite j) =>
  Mat r i j ->
  Prob (->) r i j
matToProb m = Prob $ \k (x, i) -> sum [runMat m i j * k (x, j) | j <- universe]

-- | Run a @Prob@ carrier at a single input/output pair.
--
-- This is the analogue of 'runMat' for the @Prob@ carrier: it selects one
-- output index by feeding a continuation that is @one@ at that index and
-- 'zero' elsewhere.
runProbAt ::
  forall r i j.
  (Additive r, Multiplicative r, Eq j) =>
  Prob (->) r i j ->
  i ->
  j ->
  r
runProbAt (Prob f) i j =
  f (\(_, j') -> bool zero one (j' == j)) ((), i)
