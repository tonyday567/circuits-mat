{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Exact deterministic oracles for the circuits-mat ⟜ harpie boundary.
--
-- Slice 1 of the harpie circuit-theory backport: the dot product as an
-- expansion/contraction cycle, checked three ways on the same data.
--
-- ⟜ harpie fused @dot@ is the ⅋ (shared-channel) reading
-- ⟜ harpie unfused @contract . expand@ is the ⊗ (materialized) reading
-- ⟜ circuits-mat @Comp@ is matrix multiplication of row with column
-- ⟜ circuits-mat @traceMat@ puts the common axis on the feedback channel
--
-- See coffee/loom/harpie-circuit-census.md.
module Main (main) where

import Circuit.Mat (Mat (..), runMat, traceMat)
import Circuit.Mat.Harpie (F (..), finF, matF)
import Harpie.Fixed qualified as F
import Harpie.Shape (Fin (..))
import NumHask.Algebra.Additive (Additive (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import System.Exit (exitFailure)
import Prelude hiding (sum, (*), (+))

main :: IO ()
main = do
  results <-
    traverse
      runCheck
      [ ("C1 harpie fused dot [4].[4]", checkC1),
        ("C2 harpie unfused contract . expand [4].[4]", checkC2),
        ("C3 circuits-mat Comp row.col [4].[4]", checkC3),
        ("C4 circuits-mat traceMat, common axis on the feedback channel", checkC4),
        ("C5 Comp == harpie dot [2,3].[3,2]", checkC5)
      ]
  if and results
    then putStrLn "circuits-mat-axioma: all green"
    else exitFailure

runCheck :: (String, Bool) -> IO Bool
runCheck (name, ok) = do
  putStrLn $ name ++ ": " ++ if ok then "ok" else "FAIL"
  pure ok

-- | Shared data: two vectors with a known inner product.
aval, bval :: [Int]
aval = [1, 2, 3, 4]
bval = [5, 6, 7, 8]

-- | Σᵢ aᵢ·bᵢ = 5+12+21+32
expected :: Int
expected = 70

va, vb :: F.Array '[4] Int
va = F.array aval
vb = F.array bval

-- | C1 ⟜ harpie's fused 'dot' (the ⅋ reading).
checkC1 :: Bool
checkC1 = F.fromScalar (F.dot (foldr (+) 0) (*) va vb) == expected

-- | C2 ⟜ harpie's unfused 'contract' after 'expand' (the ⊗ reading).
--
-- Regression: if 'prod's per-side 'insertDimsL' placement drifts, C1 ≠ C2.
checkC2 :: Bool
checkC2 = F.fromScalar (F.contract (F.Dims @'[0, 1]) (foldr (+) 0) (F.expand (*) va vb)) == expected

-- | C3 ⟜ matrix multiplication of a row with a column.
--
-- Regression: a row/column mixup in the Mat bridge shows here.
checkC3 :: Bool
checkC3 =
  let row = matF @1 @4 (\_ fj -> aval !! fromFin fj)
      col = matF @4 @1 (\fi _ -> bval !! fromFin fi)
   in runMat (Comp col row) (finF @1 0) (finF @1 0) == expected

-- | C4 ⟜ contraction as trace: the common axis on the feedback channel.
--
-- @mba@ carries a across, @mac@ carries b back, the loop block is zero and
-- stays zero ⟜ 'star' applied to a live value is an oracle failure, enforced
-- by construction.
checkC4 :: Bool
checkC4 =
  let m :: Mat DS (Either (F 4) (F 1)) (Either (F 4) (F 1))
      m =
        Mat $ \i j -> case (i, j) of
          (Right _, Left (F fj)) -> DS (aval !! fromFin fj)
          (Left (F fi), Right _) -> DS (bval !! fromFin fi)
          _ -> zero
   in runMat (traceMat m) (finF @1 0) (finF @1 0) == DS expected

-- | C5 ⟜ full matrix multiplication: 'Comp' agrees with harpie's 'dot'.
checkC5 :: Bool
checkC5 =
  let mA = matF @2 @3 (\(UnsafeFin i) (UnsafeFin j) -> i * 3 + j)
      mB = matF @3 @2 (\(UnsafeFin i) (UnsafeFin j) -> i * 2 + j)
      hd = F.dot (foldr (+) 0) (*) (F.range @'[2, 3]) (F.range @'[3, 2])
   in and
        [ runMat (Comp mB mA) (finF @2 i) (finF @2 k) == F.unsafeIndex hd [i, k]
        | i <- [0, 1],
          k <- [0, 1]
        ]

-- | Int with a star that only fires on zero.
--
-- A dead feedback loop reduces the Schur complement to
-- @mac . star 0 . mba = mac . mba@ ⟜ the contraction.  'star' on a live
-- value means the loop went live and the trace is no longer a dot product.
newtype DS = DS Int
  deriving (Eq, Show)

instance Additive DS where
  DS a + DS b = DS (a + b)
  zero = DS 0

instance Multiplicative DS where
  DS a * DS b = DS (a * b)
  one = DS 1

instance StarSemiring DS where
  star (DS 0) = DS 1
  star x = error ("trace-dot: feedback channel went live: " ++ show x)
