{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Harpie-backed finite indices for @Circuit.Mat@.
--
-- Harpie shapes are rectangular products of type-level naturals; there is no
-- native shape constructor for coproducts.  This module provides the minimal
-- bridge: a @KnownNat@-indexed wrapper @F n@ around @Harpie.Shape.Fin n@, with
-- a 'Circuit.Mat.Finite' instance, so that matrices can use harpie-style
-- type-level sizes while reusing the existing 'Mat' machinery.
--
-- The central isomorphism is the standard disjoint-union-as-initial-segment:
--
-- @
-- Either (F i) (F j)  ≅  F (i + j)
-- @
--
-- realised by 'eitherToF' and 'fToEither'.  This lets the biproduct 'parH'
-- embed block-diagonally into a single rectangular harpie dimension, and lets
-- 'traceF' reuse 'traceMat' on a feedback channel whose size is known at the
-- type level.
module Circuit.Mat.Harpie
  ( -- * KnownNat wrapper
    F (..),
    finF,
    safeFinF,
    fromF,
    toF,

    -- * Coproduct isomorphism
    eitherToF,
    fToEither,

    -- * Matrices indexed by F
    matF,
    runMatF,
    parH,
    traceF,
  )
where

import Circuit.Mat (Finite (..), Mat (..), runMat, traceMat)
import GHC.TypeNats (KnownNat, Nat, type (+))
import Harpie.Shape (Fin (..), fin, safeFin, valueOf)
import NumHask.Algebra.Additive (Additive (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding (id, sum, (*), (+))

-- $setup
--
-- >>> :set -XDataKinds
-- >>> :set -XTypeApplications
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude
-- >>> import Harpie.Shape (Fin (..))
-- >>> import Circuit.Mat
-- >>> import Circuit.Mat.Harpie

-- | A 'KnownNat'-backed finite index type.
--
-- @F n@ is exactly @Fin n@, but carries a 'Circuit.Mat.Finite' instance
-- derived from the type-level natural.  This is the smallest wrapper that lets
-- 'Mat' treat harpie-style indices as enumerable objects.
newtype F (n :: Nat) = F {unF :: Fin n}
  deriving stock (Eq, Ord)
  deriving newtype (Show)

-- | Construct an @F n@ from an 'Int'.  Errors if out of bounds.
--
-- >>> finF @3 2
-- 2
finF :: forall n. (KnownNat n) => Int -> F n
finF = F . fin @n

-- | Construct an @F n@ from an 'Int' safely.
--
-- >>> safeFinF @3 2
-- Just 2
-- >>> safeFinF @3 3
-- Nothing
safeFinF :: forall n. (KnownNat n) => Int -> Maybe (F n)
safeFinF = fmap F . safeFin @n

-- | Coerce to the underlying @Fin n@.
fromF :: F n -> Fin n
fromF = unF

-- | Coerce from a @Fin n@.
toF :: Fin n -> F n
toF = F

-- | Enumerate all @F n@ values.
--
-- >>> universe :: [F 3]
-- [0,1,2]
instance (KnownNat n) => Finite (F n) where
  universe = [F (fin @n i) | i <- [0 .. valueOf @n - 1]]

-- | Disjoint-union embedding into @F (i + j)@.
--
-- Left summand occupies indices @[0, i)@; right summand occupies @[i, i+j)@.
--
-- >>> eitherToF @2 @3 (Left (finF 1))
-- 1
-- >>> eitherToF @2 @3 (Right (finF 1))
-- 3
eitherToF :: forall i j. (KnownNat i, KnownNat j) => Either (F i) (F j) -> F (i + j)
eitherToF (Left (F (UnsafeFin a))) = F (UnsafeFin a)
eitherToF (Right (F (UnsafeFin b))) = F (UnsafeFin (valueOf @i + b))

-- | Split an @F (i + j)@ into the left or right summand.
--
-- >>> fToEither @2 @3 (finF @5 1)
-- Left 1
-- >>> fToEither @2 @3 (finF @5 3)
-- Right 1
fToEither :: forall i j. (KnownNat i, KnownNat j) => F (i + j) -> Either (F i) (F j)
fToEither (F (UnsafeFin x))
  | x < valueOf @i = Left (F (UnsafeFin x))
  | otherwise = Right (F (UnsafeFin (x - valueOf @i)))

-- | Build a matrix from a function on underlying @Fin@ indices.
matF ::
  (KnownNat i, KnownNat j) =>
  (Fin i -> Fin j -> s) ->
  Mat s (F i) (F j)
matF f = Mat $ \(F i) (F j) -> f i j

-- | Run a matrix at underlying @Fin@ indices.
runMatF ::
  (Additive s, Multiplicative s) =>
  Mat s (F i) (F j) ->
  Fin i ->
  Fin j ->
  s
runMatF m i j = runMat m (F i) (F j)

-- | Block-diagonal biproduct for harpie-backed indices.
--
-- The result lives on a single rectangular dimension @F (i + k) × F (j + l)@,
-- matching what a harpie @Array @[i + k, j + l] s@ expects.
--
-- >>> let m = matF @2 @2 (\i j -> if i == j then (1 :: Int) else 0)
-- >>> let n = matF @1 @1 (\_ _ -> (7 :: Int))
-- >>> runMat (parH m n) (eitherToF (Left (finF @2 1))) (eitherToF (Left (finF @2 1)))
-- 1
-- >>> runMat (parH m n) (eitherToF (Right (finF @1 0))) (eitherToF (Right (finF @1 0)))
-- 7
-- >>> runMat (parH m n) (eitherToF (Left (finF @2 0))) (eitherToF (Right (finF @1 0)))
-- 0
parH ::
  ( KnownNat i,
    KnownNat j,
    KnownNat k,
    KnownNat l,
    KnownNat (i + k),
    KnownNat (j + l),
    Additive s,
    Multiplicative s
  ) =>
  Mat s (F i) (F j) ->
  Mat s (F k) (F l) ->
  Mat s (F (i + k)) (F (j + l))
parH m n = Mat $ \r c ->
  case (fToEither r, fToEither c) of
    (Left r', Left c') -> runMat m r' c'
    (Right r', Right c') -> runMat n r' c'
    _ -> zero

-- | Trace over a feedback channel of known size.
--
-- This is just 'traceMat' with the 'Finite' dictionary supplied by the
-- @KnownNat n@ constraint on @F n@.
--
-- >>> let fFun (Left (F (UnsafeFin 0))) (Left (F (UnsafeFin 0))) = False; fFun (Left (F (UnsafeFin 0))) (Right (F (UnsafeFin 0))) = True; fFun (Right (F (UnsafeFin 0))) (Left (F (UnsafeFin 0))) = True; fFun _ _ = False
-- >>> let f = Mat fFun :: Mat Bool (Either (F 2) (F 1)) (Either (F 2) (F 1))
-- >>> runMat (traceF f) (finF @1 0) (finF @1 0)
-- True
traceF ::
  ( KnownNat n,
    StarSemiring s,
    Additive s,
    Multiplicative s,
    Finite b,
    Finite c
  ) =>
  Mat s (Either (F n) b) (Either (F n) c) ->
  Mat s b c
traceF = traceMat
