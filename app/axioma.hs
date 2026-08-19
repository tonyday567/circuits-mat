{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import Circuit.Mat (Conjugate (..), Dual (..), Finite (..), Mat (..), conjugateMat, curryMat, dot, dualMat, evalMat, runMat, traceMat, transposeMat, uncurryMat)
import Circuit.Mat.Affine (affine, applyAffine, composeAffine, flattenAffine, identityAffine, swapAxesAffine, toHarpieBackpermute)
import Circuit.Mat.Array
import Circuit.Mat.Array.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import Circuit.Mat.Complex (complexSMul)
import Circuit.Mat.Dense (Matrix (..), forwardSubstStream, matTimes, qrM)
import Circuit.Mat.Field (MatField (..), cholM, householderStep, inverseM, invtriM, luM, luRank1M)
import NumHask.Algebra.Field (ExpField (..))
import NumHask.Algebra.Lattice (Lattice)
import NumHask.Algebra.Metric (Absolute, Epsilon, abs, aboutEqual)
import Circuit.Mat.Harpie (F (..), finF, matF)
import Circuit.Mat.Prob (matToProb, runProbAt)
import Circuit.Tensor (Bias (..), Fire (..), Schedule (..), Shared (..))
import Data.Bool (bool)
import Data.Maybe (fromJust)
import Data.These (These (..))
import Harpie.Array qualified as A
import Harpie.Fixed qualified as F
import Harpie.Shape (Fin (..), Fins (..), KnownNats (..), SNat, SNats, indexWindowsL, pattern SNat, pattern SNats)
import NumHask.Algebra.Additive (Additive (..), Subtractive, sum)
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import NumHask.Data.Complex (Complex, (+:))
import System.Exit (exitFailure)
import Prelude hiding (abs, curry, recip, sqrt, sum, uncurry, (*), (+), (/))

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
        ("C22 [C;I] join/separator iso for Mat arrays (A7)", checkC22),
        ("C23 Circuit.Stream: uncons nil == That nil", checkC23),
        ("C24 Circuit.Stream: uncons (cons x xs) == These x xs", checkC24),
        ("C25 Circuit.Stream: cons head tail recovers the array", checkC25),
        ("C26 Circuit.Stream: unsnoc (snoc xs x) == (xs, x)", checkC26),
        ("C27 Circuit.Stream: snoc init last recovers the array", checkC27),
        ("C28 Circuit.Stream: cons to empty stream builds a one-row array", checkC28),
        ("C29 Circuit.Stream: snoc to empty stream builds a one-row array", checkC29),
        ("C30 transpose on [2,3,4] is reorder by the reversed axis list", checkC30),
        ("C31 transpose is an involution", checkC31),
        ("C32 coexpand is expand followed by the block-swap permutation", checkC32),
        ("C33 Mat transpose is identity-on-objects and involutive", checkC33),
        ("C34 Mat dual is not identity-on-objects", checkC34),
        ("C35 Mat conjugation is a third involution over Complex", checkC35),
        ("C36 Lolli curry/uncurry reshape are inverse", checkC36),
        ("C37 Lolli eval contracts the repeated index", checkC37),
        ("C38 Affine identity/composition roundtrip", checkC38),
        ("C39 Affine swap-axes roundtrip", checkC39),
        ("C40 Mat -> Prob carrier agreement on a stochastic matrix", checkC40),
        ("C41 Dot-product construction agrees on harpie and Prob carriers", checkC41),
        ("C42 Affine flatten compiles to harpie reshape", checkC42),
        ("C43 Affine axis-swap compiles to harpie transpose", checkC43),
        ("C44 Dot product via Par/trace with no row/column naming", checkC44),
        ("C45 Complex multiplication as Shared-medium fusion", checkC45),
        ("C46 Mat structure-constant contraction matches expected complex product", checkC46),
        ("C47 Harpie prod structure-constant contraction matches expected", checkC47),
        ("C48 Mat and harpie complex multiplication agree", checkC48),
        ("D1 LU with partial pivoting recovers A = P^T L U", checkD1),
        ("D2 LU as iterated rank-1 update agrees with reference luM", checkD2),
        ("D3 Householder reflection zeroes the subdiagonal of a column", checkD3),
        ("D4 QR decomposition recovers A = Q R with orthogonal Q", checkD4),
        ("D5 Forward substitution as a Stream morphism recovers L y = b", checkD5)
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
eM :: F.Array '[3, 3] Double
eM = F.array @[3, 3] [4, 12, -16, 12, 37, -43, -16, -43, 98]

-- | Shared upper-triangular test matrix.
tM :: F.Array '[3, 3] Double
tM = F.array @[3, 3] [1, 0, 1, 0, 1, 2, 0, 0, 1]

-- | Shared diagonal matrix with exact Cholesky and exact inverse.
--
-- Entries are powers of two so their square roots and reciprocals are exactly
-- representable in Double.
dM :: F.Array '[3, 3] Double
dM = F.array @[3, 3] [4, 0, 0, 0, 16, 0, 0, 0, 64]

-- | C6 ⟜ Cholesky factor recovers the original matrix.
checkC6 :: Bool
checkC6 = F.mult (cholM eM) (F.transpose (cholM eM)) == eM

-- | C7 ⟜ Inverse times original is identity.
checkC7 :: Bool
checkC7 = F.mult (inverseM dM) dM == F.ident @[3, 3]

-- | C8 ⟜ Triangular inverse times original is identity.
checkC8 :: Bool
checkC8 = F.mult tM (invtriM tM) == F.ident @[3, 3]

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
  let a = F.range @[4, 3, 2] :: F.Array '[4, 3, 2] Int
      w = F.windows (SNats @'[2, 2]) a
      w' = F.unsafeTabulate @'[3, 2, 2, 2, 2] (\fi -> F.unsafeIndex a (indexWindowsL 2 fi)) :: F.Array '[3, 2, 2, 2, 2] Int
   in w == w'

-- | C13 ⟜ prod alignment schedule recovers dot after transpose.
--
-- 'dot' hard-codes the canonical schedule (last axis of left, first axis of
-- right).  Here we align the same contracting axes with the schedule
-- @(ds0 = [0], ds1 = [1])@ after transposing both operands.
checkC13 :: Bool
checkC13 =
  let m = F.range @[2, 3] :: F.Array '[2, 3] Int
      n = F.range @[3, 2] :: F.Array '[3, 2] Int
      d = F.dot (foldr (+) 0) (*) m n
      p = F.prod (F.Dims @'[0]) (F.Dims @'[1]) (foldr (+) 0) (*) (F.transpose m) (F.transpose n) :: F.Array '[2, 2] Int
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
  let a = F.array @[2, 3] [0 .. 5] :: F.Array '[2, 3] Int
      b = F.array @'[3] [6 .. 8] :: F.Array '[3] Int
      r = F.telecasts (SNats @'[1]) (SNats @'[0]) (F.concatenate (SNat @0)) a b :: F.Array '[3, 3] Int
   in r == F.array @[3, 3] [0, 3, 6, 1, 4, 7, 2, 5, 8]

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
  all
    (\(i, j) -> runMat m i j == runMat n i j)
    [(i, j) | i <- allFins @s, j <- universe]

-- | Helper: extensional equality of index functions.
eqIx :: forall s a. (KnownNats s, Eq a) => (Fins s -> a) -> (Fins s -> a) -> Bool
eqIx f g = all (\i -> f i == g i) (allFins @s)

-- | Swap the two axes of a [2,3] array to a [3,2] array.
swap23 :: IxMap '[3, 2] '[2, 3]
swap23 (UnsafeFins [i, j]) = UnsafeFins [j, i]
swap23 _ = error "swap23: unexpected index"

-- | Swap the two axes of a [3,2] array back to a [2,3] array.
swap32 :: IxMap '[2, 3] '[3, 2]
swap32 (UnsafeFins [j, i]) = UnsafeFins [i, j]
swap32 _ = error "swap32: unexpected index"

-- | A sample function array for the function-base oracles.
sampleFunArray :: ArrayC (->) '[2, 3] Int
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
  let f :: Fins '[2, 3] -> Int
      f fi = case fromFins fi of [i, j] -> i * 10 + j; _ -> error "checkC21: unexpected index"
      arr :: ArrayC (->) '[2, 3] Int
      arr = tabulateC f
   in eqIx (indexC arr) f
        && eqArrayFun (tabulateC (indexC sampleFunArray) :: ArrayC (->) '[2, 3] Int) sampleFunArray

-- | C22 ⟜ join/separator iso for Mat arrays (A7).
--
-- The same isomorphism holds when the base category is matrices: a functional
-- matrix can be recovered from its tabulated form.
checkC22 :: Bool
checkC22 =
  let fM :: Fins '[2, 3] -> F 2
      fM fi = case fromFins fi of
        [i, j] -> F (UnsafeFin (mod (i + j) 2))
        _ -> error "checkC22: unexpected index"
      arrM :: ArrayC (Mat Int) '[2, 3] (F 2)
      arrM = tabulateC fM
   in eqIx (indexC arrM) fM && eqArrayMat (tabulateC (indexC arrM)) arrM

-- | Short alias for the stream boundary type used in the oracles.
type ArrayThese a = These (A.Array a) (A.Array a)

-- | C23 ⟜ Circuit.Stream: uncons nil == That nil.
checkC23 :: Bool
checkC23 = (uncons (A.empty :: A.Array Int) :: ArrayThese Int) == That A.empty

-- | C24 ⟜ Circuit.Stream: uncons (cons x xs) == These x xs.
checkC24 :: Bool
checkC24 =
  let row :: A.Array Int
      row = A.array [3] [10, 11, 12]
      rows :: A.Array Int
      rows = A.array [2, 3] [1 .. 6]
   in (uncons (cons row rows) :: ArrayThese Int) == These row rows

-- | C25 ⟜ Circuit.Stream: cons head tail recovers the array.
checkC25 :: Bool
checkC25 =
  let rows :: A.Array Int
      rows = A.array [3, 3] [1 .. 9]
   in case (uncons rows :: ArrayThese Int) of
        These row rest -> cons row rest == rows
        _ -> False

-- | C26 ⟜ Circuit.Stream: unsnoc (snoc xs x) == (xs, x).
checkC26 :: Bool
checkC26 =
  let rows :: A.Array Int
      rows = A.array [2, 3] [1 .. 6]
      row :: A.Array Int
      row = A.array [3] [7, 8, 9]
   in A.unsnoc (snoc rows row :: A.Array Int) == (rows, row)

-- | C27 ⟜ Circuit.Stream: snoc init last recovers the array.
checkC27 :: Bool
checkC27 =
  let rows :: A.Array Int
      rows = A.array [3, 3] [1 .. 9]
   in case A.unsnoc rows of
        (init_, lastRow) -> (snoc init_ lastRow :: A.Array Int) == rows

-- | C28 ⟜ Circuit.Stream: cons to empty stream builds a one-row array.
checkC28 :: Bool
checkC28 =
  let row :: A.Array Int
      row = A.array [2, 3] [1 .. 6]
   in (uncons (cons row (A.empty :: A.Array Int)) :: ArrayThese Int) == This row

-- | C29 ⟜ Circuit.Stream: snoc to empty stream builds a one-row array.
--
-- The empty init returned by 'unsnoc' carries the row shape, so we only check
-- that it is null and that the last row is recovered.
checkC29 :: Bool
checkC29 =
  let row :: A.Array Int
      row = A.array [2, 3] [1 .. 6]
   in case A.unsnoc (snoc (A.empty :: A.Array Int) row :: A.Array Int) of
        (init_, lastRow) -> lastRow == row && A.isNull init_

-- | C30 ⟜ transpose on [2,3,4] is reorder by the reversed axis list.
--
-- 'transpose' is the symmetry of the shape-monoid: it reverses the axis order.
-- For a three-axis array this is exactly the permutation @[2,1,0]@.
checkC30 :: Bool
checkC30 =
  let a = F.range @'[2, 3, 4] :: F.Array '[2, 3, 4] Int
   in F.transpose a == F.reorder (F.Dims @'[2, 1, 0]) a

-- | C31 ⟜ transpose is an involution.
checkC31 :: Bool
checkC31 =
  let a = F.range @'[2, 3, 4] :: F.Array '[2, 3, 4] Int
   in F.transpose (F.transpose a) == a

-- | C32 ⟜ coexpand is expand followed by the block-swap permutation.
--
-- For operands of different shape, 'coexpand' is /not/ 'transpose' of 'expand';
-- it is the block-swap reorder that places the second operand's shape first.
-- Here @[2,3,0,1]@ swaps the @[2,3]@ block and the @[4,5]@ block of the
-- expanded shape @[2,3,4,5]@, yielding the @coexpand@ shape @[4,5,2,3]@.
checkC32 :: Bool
checkC32 =
  let a = F.range @'[2, 3] :: F.Array '[2, 3] Int
      b = F.range @'[4, 5] :: F.Array '[4, 5] Int
   in F.coexpand (,) a b == F.reorder (F.Dims @'[2, 3, 0, 1]) (F.expand (,) a b)

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

-- | C33 ⟜ Mat transpose is identity-on-objects and involutive.
--
-- Reversibility (dagger) flips the arrow but keeps the object labels.
-- For a concrete matrix, applying 'transposeMat' twice recovers the original.
checkC33 :: Bool
checkC33 =
  let m :: Mat Int Bool Bool
      m = Mat (\i j -> bool (0 :: Int) 1 (i == j))
   in runMat (transposeMat (transposeMat m)) False True
        == runMat m False True

-- | C34 ⟜ Mat dual is not identity-on-objects.
--
-- Duality tags both source and target with 'Dual'.  The involution property
-- holds only after stripping the double-dual; the object tag itself differs
-- from the original.
checkC34 :: Bool
checkC34 =
  let m :: Mat Int Bool Bool
      m = Mat (\i _ -> bool (0 :: Int) 1 i)
      dd :: Mat Int (Dual (Dual Bool)) (Dual (Dual Bool))
      dd = dualMat (dualMat m)
   in runMat dd (Dual (Dual False)) (Dual (Dual True))
        == runMat m False True

-- | C35 ⟜ Mat conjugation is a third involution over Complex.
--
-- Conjugation is the composite of duality and reversibility, expressed with
-- the standard self-duality of finite-dimensional spaces.  It is covariant,
-- identity-on-objects, and distinct from both transpose and dual: for a
-- non-real entry it changes the scalar while transpose moves it across the
-- diagonal.
checkC35 :: Bool
checkC35 =
  let i :: Complex Double
      i = 0 +: 1
      m :: Mat (Complex Double) Bool Bool
      m = Mat (\_ j -> bool zero i j)
      conjTwice = conjugateMat (conjugateMat m)
      transposed = transposeMat m
   in runMat conjTwice False True == runMat m False True
        && runMat (conjugateMat m) False True /= runMat m False True
        && runMat transposed True False == runMat m False True
        && runMat transposed False True /= runMat m False True

-- | C36 ⟜ curry/uncurry reshape an index pair and are inverse.
checkC36 :: Bool
checkC36 =
  let f :: Mat Int (Bool, Bool) Bool
      f = Mat $ \(x, y) z -> bool 0 1 ((x && y) == z)
      g = uncurryMat (curryMat f)
   in and [runMat f i j == runMat g i j | i <- universe, j <- universe]

-- | C37 ⟜ eval contracts the repeated index: (x, (x', y)) maps to y iff x == x'.
checkC37 :: Bool
checkC37 =
  let ev = evalMat @Int
   in runMat ev (True, (True, False)) False == 1
        && runMat ev (True, (False, False)) False == 0
        && runMat ev (True, (True, True)) True == 1

-- | C38 ⟜ Affine identity is the unit and composition respects it.
checkC38 :: Bool
checkC38 =
  let identP = identityAffine @'[2, 3]
      identQ = identityAffine @'[6]
      f = fromJust (affine @'[2, 3] @'[6] [[3, 1]] [0])
      x = [1, 2]
   in applyAffine identP x == x
        && applyAffine (composeAffine f identP) x == applyAffine f x
        && applyAffine (composeAffine identQ f) x == applyAffine f x

-- | C39 ⟜ Swapping axes twice is the identity.
checkC39 :: Bool
checkC39 =
  let swap12 = swapAxesAffine @2 @3
      swap21 = swapAxesAffine @3 @2
   in applyAffine (composeAffine swap21 swap12) [1, 2] == [1, 2]

-- | C40 ⟜ A Mat term produces the same entry when run directly and when run
-- through the Prob carrier.
checkC40 :: Bool
checkC40 =
  let m :: Mat Int (F 2) (F 2)
      m = Mat $ \(F (UnsafeFin ri)) (F (UnsafeFin cj)) -> [1, 2, 3, 4] !! (ri * 2 + cj)
      i0 = finF @2 0
      j1 = finF @2 1
   in runMat m i0 j1 == runProbAt (matToProb m) i0 j1

-- | C41 ⟜ The row/column dot-product construction flows through the Prob
-- carrier unchanged.
checkC41 :: Bool
checkC41 =
  let row = matF @1 @4 (\_ fj -> aval !! fromFin fj)
      col = matF @4 @1 (\fi _ -> bval !! fromFin fi)
      dotMat = Comp col row :: Mat Int (F 1) (F 1)
      i = finF @1 0
      j = finF @1 0
   in runMat dotMat i j == runProbAt (matToProb dotMat) i j
        && runMat dotMat i j == expected

-- | C42 ⟜ An affine flatten reindexing compiles to the harpie 'reshape' a
-- human would write.
checkC42 :: Bool
checkC42 =
  let arr23 = F.range @'[2, 3] :: F.Array '[2, 3] Int
   in toHarpieBackpermute (flattenAffine @'[2, 3]) arr23 == F.reshape @'[6] arr23

-- | C43 ⟜ An affine axis-swap compiles to the harpie 'transpose' a human
-- would write.
checkC43 :: Bool
checkC43 =
  let arr23 = F.range @'[2, 3] :: F.Array '[2, 3] Int
   in toHarpieBackpermute (swapAxesAffine @2 @3) arr23 == F.transpose arr23

-- | C44 ⟜ Dot product written with only 'Par', swap, and 'traceMat': no
-- row/column or dimension-index vocabulary.
checkC44 :: Bool
checkC44 =
  let f :: F 4 -> DS
      f (F (UnsafeFin k)) = DS (aval !! k)
      g :: F 4 -> DS
      g (F (UnsafeFin k)) = DS (bval !! k)
   in dot f g == DS expected

-- | C45 ⟜ Complex multiplication as shared-medium fusion (⅋).
--
-- The real and imaginary bodies share the two input complex numbers as state.
-- The schedule fires both poles, producing a total 'These' product: real part
-- from @ac - bd@, imaginary part from @ad + bc@.
checkC45 :: Bool
checkC45 =
  let s0 = ((1, 2), (3, 4)) :: ((Double, Double), (Double, Double))
      realBody (s, ()) = (s, a * c - b * d)
        where
          ((a, b), (c, d)) = s
      imagBody (s, ()) = (s, a * d + b * c)
        where
          ((a, b), (c, d)) = s
      sched = Schedule (\s -> (s, Both LeftFirst))
      (_, result) = sharedBy sched realBody imagBody (s0, ((), ()))
   in case result of
        These (-5.0) 10.0 -> True
        _ -> False

-- | C46 ⟜ The @Mat@ structure-constant contraction produces the expected
-- complex product.
checkC46 :: Bool
checkC46 =
  let a :: F 2 -> Double
      a (F (UnsafeFin 0)) = 1
      a (F (UnsafeFin 1)) = 2
      a _ = 0
      b :: F 2 -> Double
      b (F (UnsafeFin 0)) = 3
      b (F (UnsafeFin 1)) = 4
      b _ = 0
      re = complexSMul a b (finF @2 0)
      im = complexSMul a b (finF @2 1)
   in re == -5 && im == 10

-- | C47 ⟜ Harpie's @prod@ against the structure-constant tensor produces the
-- same complex product.
checkC47 :: Bool
checkC47 =
  let a = F.array @'[2] [1, 2] :: F.Array '[2] Double
      b = F.array @'[2] [3, 4] :: F.Array '[2] Double
      c = F.array @[2, 2, 2] [1, 0, 0, -1, 0, 1, 1, 0] :: F.Array '[2, 2, 2] Double
      outer = F.expand (*) a b
      r = F.prod (F.Dims @'[1, 2]) (F.Dims @'[0, 1]) (foldr (+) 0) (*) c outer
   in F.unsafeIndex r [0] == -5 && F.unsafeIndex r [1] == 10

-- | C48 ⟜ The @Mat@ and harpie structure-constant contractions agree.
checkC48 :: Bool
checkC48 =
  let a :: F 2 -> Double
      a (F (UnsafeFin 0)) = 1
      a (F (UnsafeFin 1)) = 2
      a _ = 0
      b :: F 2 -> Double
      b (F (UnsafeFin 0)) = 3
      b (F (UnsafeFin 1)) = 4
      b _ = 0
      matResult = [complexSMul a b (finF @2 0), complexSMul a b (finF @2 1)]
      harpieA = F.array @'[2] [1, 2] :: F.Array '[2] Double
      harpieB = F.array @'[2] [3, 4] :: F.Array '[2] Double
      c = F.array @[2, 2, 2] [1, 0, 0, -1, 0, 1, 1, 0] :: F.Array '[2, 2, 2] Double
      outer = F.expand (*) harpieA harpieB
      harpieResult = F.prod (F.Dims @'[1, 2]) (F.Dims @'[0, 1]) (foldr (+) 0) (*) c outer
   in matResult == [F.unsafeIndex harpieResult [0], F.unsafeIndex harpieResult [1]]

-- | D1 ⟜ LU decomposition with partial pivoting recovers the original matrix.
--
-- The factorisation is @a = p^T . l . u@, where @p@ is the permutation
-- accumulated during pivoting, @l@ is unit lower triangular, and @u@ is upper
-- triangular.  The recovery is checked with approximate equality because the
-- intermediate divisions can introduce rounding in floating-point.
checkD1 :: Bool
checkD1 =
  let a :: F.Array '[3, 3] Double
      a = F.array @[3, 3] [2, 1, 1, 4, 3, 1, 8, 7, 2]
      (p, l, u) = luM a
      recovered = F.mult (F.transpose p) (F.mult l u)
   in matAboutEqual a recovered

-- | D2 ⟜ LU expressed as iterated rank-1 updates agrees with the reference.
--
-- 'luRank1M' performs the same pivoting and arithmetic as 'luM', but the
-- Schur-complement step is written as the outer-product contraction
-- @A' = A - c ⊗ r@.  The two implementations must return the same @P@, @L@,
-- and @U@.
checkD2 :: Bool
checkD2 =
  let a :: F.Array '[3, 3] Double
      a = F.array @[3, 3] [2, 1, 1, 4, 3, 1, 8, 7, 2]
      (p1, l1, u1) = luM a
      (p2, l2, u2) = luRank1M a
   in p1 == p2 && l1 == l2 && u1 == u2

-- | D3 ⟜ Householder reflection zeroes the subdiagonal of a column.
--
-- Applying a Householder reflector to column 0 of a matrix should produce a
-- column whose only non-zero entry is at row 0, with magnitude equal to the
-- Euclidean norm of the original column.  The implementation uses the
-- rank-1 update @A' = A - (2 / v^T v) · v ⊗ (v^T A)@.
checkD3 :: Bool
checkD3 =
  let a :: F.Array '[3, 3] Double
      a = F.array @[3, 3] [2, 1, 1, 4, 3, 1, 8, 7, 2]
      a' = householderStep 0 a
      col0 :: F.Array '[3] Double
      col0 = F.tabulate $ \s -> case fromFins s of
        [i] -> a' F.! [i, 0]
        _ -> error "checkD3: expected rank-1 index"
      expectedNorm :: Double
      expectedNorm = sqrt (2 * 2 + 4 * 4 + 8 * 8)
   in aboutEqual (abs (col0 F.! [0]) :: Double) expectedNorm
        && aboutEqual (col0 F.! [1]) 0
        && aboutEqual (col0 F.! [2]) 0

-- | D4 ⟜ QR decomposition recovers the original matrix with an orthogonal Q.
--
-- Uses the value-sized 'Harpie.Array' API.  The oracle checks both @A = Q R@
-- and @Q^T Q = I@ with approximate equality.
checkD4 :: Bool
checkD4 =
  let a = A.array [4, 3] [2, 1, 1, 4, 3, 1, 8, 7, 2, 6, 5, 4] :: A.Array Double
      (Matrix q, Matrix r) = qrM (Matrix a)
      qtq = matTimes (Matrix (A.transpose q)) (Matrix q)
      ident = Matrix (A.ident [4, 4])
      qr = matTimes (Matrix q) (Matrix r)
   in matrixAboutEqual qr (Matrix a) && matrixAboutEqual qtq ident

-- | D5 ⟜ Forward substitution as a Stream morphism solves L y = b.
--
-- Streams rows of the unit lower-triangular @L@ and components of @b@,
-- accumulating @y@.  The oracle verifies @L y = b@ by direct multiplication.
checkD5 :: Bool
checkD5 =
  let l = A.array [3, 3] [1, 0, 0, 2, 1, 0, 3, 4, 1] :: A.Array Double
      b = A.array [3] [1, 2, 3] :: A.Array Double
      y = forwardSubstStream l b
      ly = A.tabulate [3] (\[i] -> sum [l A.! [i, j] * y A.! [j] | j <- [0 .. i]])
   in matrixAboutEqual (Matrix ly) (Matrix b)

-- | Elementwise approximate equality of two value-sized matrices.
matrixAboutEqual ::
  (Epsilon a, Lattice a, Subtractive a) =>
  Matrix a ->
  Matrix a ->
  Bool
matrixAboutEqual (Matrix x) (Matrix y) =
  A.shape x == A.shape y && and (A.zipWith aboutEqual x y)

-- | Elementwise approximate equality of two fixed-shape matrices.
matAboutEqual ::
  forall s a.
  (KnownNats s, Epsilon a, Lattice a, Subtractive a) =>
  F.Array s a ->
  F.Array s a ->
  Bool
matAboutEqual x y = all (\ix -> aboutEqual (F.index x ix) (F.index y ix)) (allFins @s)
