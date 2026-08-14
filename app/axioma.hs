{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}

-- | Exact deterministic oracles for the circuits-mat ⟜ harpie boundary.
--
-- Slice 1 of the harpie circuit-theory backport: the dot product as an
-- expansion/contraction cycle, checked three ways on the same data.
--
-- Slice 2 adds the scheduling/permutation story:
--
-- ⟜ @expand@ vs @coexpand@ are the two bias orders of the tensor (⊗) product
-- ⟜ @windows@ is a schedule morphism realised by @indexWindowsL@
-- ⟜ @prod@ with explicit dimensions is the alignment schedule inside ⅋
-- ⟜ @traceMat@ distinguishes a dead feedback loop from a live one
-- ⟜ @telecasts@ is aligned broadcasting as a batch schedule
--
-- See coffee/loom/harpie-circuit-census.md.
module Main (main) where

import Circuit.Mat (Finite (..), Mat (..), runMat, traceMat)
import Circuit.Mat.Array
import Circuit.Mat.Field (MatField (..), cholM, inverseM, invtriM)
import Circuit.Mat.Harpie (F (..), finF, matF)
import Harpie.Fixed qualified as F
import Harpie.Shape (Fins (..), Fin (..), KnownNats (..), SNats, pattern SNats, SNat, pattern SNat, indexWindowsL)
import NumHask.Algebra.Additive (Additive (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import System.Exit (exitFailure)
import Prelude hiding (recip, sum, (*), (+), (/))

main :: IO ()
main = do
  results <-
    traverse
      runCheck
      [ ("C1 harpie fused dot [4].[4]", checkC1),
        ("C2 harpie unfused contract . expand [4].[4]", checkC2),
        ("C3 circuits-mat Comp row.col [4].[4]", checkC3),
        ("C4 circuits-mat traceMat, common axis on the feedback channel", checkC4),
        ("C5 Comp == harpie dot [2,3].[3,2]", checkC5),
        ("C6 cholM recovery", checkC6),
        ("C7 inverseM recovery", checkC7),
        ("C8 invtriM recovery", checkC8),
        ("C9 MatField one is neutral", checkC9),
        ("C10 MatField division is inverse", checkC10),
        ("C11 coexpand is the bias-swapped twin of expand", checkC11),
        ("C12 windows is a schedule morphism via indexWindowsL", checkC12),
        ("C13 prod alignment schedule recovers dot after transpose", checkC13),
        ("C14 traceMat distinguishes dead and live feedback loops", checkC14),
        ("C15 telecasts is aligned broadcasting as a batch schedule", checkC15),
        ("C16 [C;I] reindexing identity (A1)", checkC16),
        ("C17 [C;I] reindexing composition / backpermute fusion (A2)", checkC17),
        ("C18 [C;I] batch identity (A3)", checkC18),
        ("C19 [C;I] batch composition (A4)", checkC19),
        ("C20 [C;I] Yoneda sliding for deterministic base maps (A5)", checkC20),
        ("C21 [C;I] join/separator iso for function arrays (A6)", checkC21),
        ("C22 [C;I] join/separator iso for Mat arrays (A7)", checkC22)
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

-- | Shared positive-definite test matrix for field calculus.
eM :: F.Array '[3,3] Double
eM = F.array @[3,3] [4,12,-16,12,37,-43,-16,-43,98]

-- | Shared upper-triangular test matrix.
tM :: F.Array '[3,3] Double
tM = F.array @[3,3] [1,0,1,0,1,2,0,0,1]

-- | Shared diagonal matrix with exact Cholesky and exact inverse.
--
-- Entries are powers of two so their square roots and reciprocals are exactly
-- representable in Double.
dM :: F.Array '[3,3] Double
dM = F.array @[3,3] [4,0,0,0,16,0,0,0,64]

-- | C6 ⟜ Cholesky factor recovers the original matrix.
checkC6 :: Bool
checkC6 = F.mult (cholM eM) (F.transpose (cholM eM)) == eM

-- | C7 ⟜ Inverse times original is identity.
checkC7 :: Bool
checkC7 = F.mult (inverseM dM) dM == F.ident @[3,3]

-- | C8 ⟜ Triangular inverse times original is identity.
checkC8 :: Bool
checkC8 = F.mult tM (invtriM tM) == F.ident @[3,3]

-- | C9 ⟜ MatField one is the identity matrix.
checkC9 :: Bool
checkC9 = one * MatField eM == MatField eM

-- | C10 ⟜ MatField division uses inverseM.
checkC10 :: Bool
checkC10 = MatField dM / MatField dM == (one :: MatField 3 Double)

-- | C11 ⟜ coexpand is the bias-swapped twin of expand.
--
-- For operands of the same shape, 'coexpand' is exactly the transpose of
-- 'expand'; this is the two possible scheduling orders of the tensor (⊗)
-- product.
checkC11 :: Bool
checkC11 =
  let v3a = F.range @'[3] :: F.Array '[3] Int
      v3b = F.array @'[3] [10, 11, 12] :: F.Array '[3] Int
   in F.coexpand (,) v3a v3b == F.transpose (F.expand (,) v3a v3b)

-- | C12 ⟜ windows is a schedule morphism via indexWindowsL.
--
-- The windowed array can be recovered by the explicit index schedule
-- @indexWindowsL@; this is the shared-medium fusion of the outer window
-- position and the inner window offset.
checkC12 :: Bool
checkC12 =
  let a = F.range @[4,3,2] :: F.Array '[4,3,2] Int
      w = F.windows (SNats @'[2,2]) a
      w' = F.unsafeTabulate @'[3,2,2,2,2] (\fi -> F.unsafeIndex a (indexWindowsL 2 fi)) :: F.Array '[3,2,2,2,2] Int
   in w == w'

-- | C13 ⟜ prod alignment schedule recovers dot after transpose.
--
-- 'dot' hard-codes the canonical schedule (last axis of left, first axis of
-- right).  Here we align the same contracting axes with the schedule
-- @(ds0 = [0], ds1 = [1])@ after transposing both operands.
checkC13 :: Bool
checkC13 =
  let m = F.range @[2,3] :: F.Array '[2,3] Int
      n = F.range @[3,2] :: F.Array '[3,2] Int
      d = F.dot (foldr (+) 0) (*) m n
      p = F.prod (F.Dims @'[0]) (F.Dims @'[1]) (foldr (+) 0) (*) (F.transpose m) (F.transpose n) :: F.Array '[2,2] Int
   in d == p

-- | C14 ⟜ traceMat distinguishes dead and live feedback loops.
--
-- A dead loop (zero feedback diagonal) reduces to the contraction @mac . mba@,
-- because @starM@ of the zero feedback matrix is the identity.  A live loop
-- includes the reflexive-transitive closure of the feedback diagonal, so the
-- trace differs.
checkC14 :: Bool
checkC14 =
  let dead :: Mat LS (Either (F 1) (F 1)) (Either (F 1) (F 1))
      dead =
        Mat $ \i j -> case (i, j) of
          (Right _, Left (F _)) -> LS 5
          (Left (F _), Right _) -> LS 3
          _ -> zero
      live :: Mat LS (Either (F 1) (F 1)) (Either (F 1) (F 1))
      live =
        Mat $ \i j -> case (i, j) of
          (Left (F fi), Left (F fj)) | fi == fj -> LS 2
          (Right _, Left (F _)) -> LS 5
          (Left (F _), Right _) -> LS 3
          _ -> zero
      -- dead:  mbc + mac * starM(0) * mba  = 0 + 3 * 1 * 5 = 15
      -- live:  mbc + mac * starM(2) * mba  = 0 + 3 * 15 * 5 = 225
      deadResult = runMat (traceMat dead) (finF @1 0) (finF @1 0)
      liveResult = runMat (traceMat live) (finF @1 0) (finF @1 0)
   in deadResult == LS 15 && liveResult == LS 225

-- | C15 ⟜ telecasts is aligned broadcasting as a batch schedule.
--
-- The outer dimensions are matched and the inner function is applied
-- pointwise across the shared batch axes.
checkC15 :: Bool
checkC15 =
  let a = F.array @[2,3] [0..5] :: F.Array '[2,3] Int
      b = F.array @'[3] [6..8] :: F.Array '[3] Int
      r = F.telecasts (SNats @'[1]) (SNats @'[0]) (F.concatenate (SNat @0)) a b :: F.Array '[3,3] Int
   in r == F.array @[3,3] [0,3,6,1,4,7,2,5,8]

-- | Helper: extensional equality of function arrays.
eqArrayFun :: forall s a. (KnownNats s, Eq a) => ArrayC (->) s a -> ArrayC (->) s a -> Bool
eqArrayFun (ArrayC f) (ArrayC g) = all (\i -> f i == g i) (allFins @s)

-- | Helper: extensional equality of Mat arrays.
eqArrayMat ::
  forall s a r.
  (KnownNats s, Finite a, Eq a, Additive r, Multiplicative r, Eq r) =>
  ArrayC (Mat r) s a ->
  ArrayC (Mat r) s a ->
  Bool
eqArrayMat (ArrayC m) (ArrayC n) =
  all (\(i, j) -> runMat m i j == runMat n i j)
    [(i, j) | i <- allFins @s, j <- universe]

-- | Helper: extensional equality of index functions.
eqIx :: forall s a. (KnownNats s, Eq a) => (Fins s -> a) -> (Fins s -> a) -> Bool
eqIx f g = all (\i -> f i == g i) (allFins @s)

-- | Swap the two axes of a [2,3] array to a [3,2] array.
swap23 :: IxMap '[3,2] '[2,3]
swap23 (UnsafeFins [i, j]) = UnsafeFins [j, i]
swap23 _ = error "swap23: unexpected index"

-- | Swap the two axes of a [3,2] array back to a [2,3] array.
swap32 :: IxMap '[2,3] '[3,2]
swap32 (UnsafeFins [j, i]) = UnsafeFins [i, j]
swap32 _ = error "swap32: unexpected index"

-- | A sample function array for the function-base oracles.
sampleFunArray :: ArrayC (->) '[2,3] Int
sampleFunArray = tabulateC $ \fi ->
  case fromFins fi of
    [i, j] -> i * 10 + j
    _ -> error "sampleFunArray: unexpected index"

-- | C16 ⟜ reindexing identity (A1).
--
-- Reindexing by the identity index map leaves the array unchanged.
checkC16 :: Bool
checkC16 = eqArrayFun (reindex id sampleFunArray) sampleFunArray

-- | C17 ⟜ reindexing composition / backpermute fusion (A2).
--
-- Reindexing is contravariant in the index map: @reindex f . reindex g = reindex (g . f)@.
-- Here swapping twice lands back on the original shape.
checkC17 :: Bool
checkC17 =
  eqArrayFun
    (reindex swap32 . reindex swap23 $ sampleFunArray)
    (reindex (swap23 . swap32) sampleFunArray)

-- | C18 ⟜ batch identity (A3).
--
-- The batch lift of the identity base morphism is the identity array morphism.
checkC18 :: Bool
checkC18 = eqArrayFun (batch id sampleFunArray) sampleFunArray

-- | C19 ⟜ batch composition (A4).
--
-- Batch lifting commutes with composition of base morphisms.
checkC19 :: Bool
checkC19 =
  eqArrayFun
    (batch ((+ 1) . (* 2)) sampleFunArray)
    (batch (+ 1) . batch (* 2) $ sampleFunArray)

-- | C20 ⟜ Yoneda sliding for deterministic base maps (A5).
--
-- For deterministic arrays, reindexing and batch lifting slide past each other.
checkC20 :: Bool
checkC20 =
  eqArrayFun
    (batch (+ 1) . reindex swap23 $ sampleFunArray)
    (reindex swap23 . batch (+ 1) $ sampleFunArray)

-- | C21 ⟜ join/separator iso for function arrays (A6).
--
-- @indexC . tabulateC = id@ and @tabulateC . indexC = id@ for the function
-- base category.
checkC21 :: Bool
checkC21 =
  let f :: Fins '[2,3] -> Int
      f fi = case fromFins fi of [i, j] -> i * 10 + j; _ -> error "checkC21: unexpected index"
      arr :: ArrayC (->) '[2,3] Int
      arr = tabulateC f
   in eqIx (indexC arr) f
        && eqArrayFun (tabulateC (indexC sampleFunArray) :: ArrayC (->) '[2,3] Int) sampleFunArray

-- | C22 ⟜ join/separator iso for Mat arrays (A7).
--
-- The same isomorphism holds when the base category is matrices: a functional
-- matrix can be recovered from its tabulated form.
checkC22 :: Bool
checkC22 =
  let fM :: Fins '[2,3] -> F 2
      fM fi = case fromFins fi of
        [i, j] -> F (UnsafeFin (mod (i + j) 2))
        _ -> error "checkC22: unexpected index"
      arrM :: ArrayC (Mat Int) '[2,3] (F 2)
      arrM = tabulateC fM
   in eqIx (indexC arrM) fM && eqArrayMat (tabulateC (indexC arrM)) arrM

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

-- | Int with a star that distinguishes dead and live loops.
--
-- @star 0 = 1@ keeps the contraction reading intact; @star n = n + 1@ for
-- non-zero @n@ makes a live feedback channel produce a different trace value.
newtype LS = LS Int
  deriving (Eq, Show)

instance Additive LS where
  LS a + LS b = LS (a + b)
  zero = LS 0

instance Multiplicative LS where
  LS a * LS b = LS (a * b)
  one = LS 1

instance StarSemiring LS where
  star (LS 0) = LS 1
  star (LS n) = LS (n + 1)
