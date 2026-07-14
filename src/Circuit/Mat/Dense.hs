{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Dense rank-2 matrices as harpie 'A.Array' morphisms (carrier B).
--
-- = Design (see @loom/circuits-mat-dense.md@)
--
-- * __Carrier__ is 'Harpie.Array.Array' — shape and strides are values.
--   No new buffer ADT; no 'Harpie.Fixed'.
-- * __Objects__ are phantom tags with @Ob = ()@ — unconstrained. Indices
--   in kernels are 'Int'. Tags only help type composition of wires.
-- * __Size__ lives on the array shape @[rows, cols]@, not in 'Finite' or
--   'KnownNat'. No double bookkeeping with typed universes.
-- * __Composition__ is a fused triple loop. Never 'A.expand' / 'A.dot'.
--
-- = Category and identity
--
-- @Ob (Dense s) a = ()@ carries no size, so a polymorphic 'id' cannot
-- choose a dimension. Use 'eye' with an explicit size. The 'Category'
-- 'id' is 'eye' @0@ (the 0×0 identity); non-trivial identities are
-- always 'eye' @n@.
--
-- = Trace
--
-- Feedback width is a __value__ ('Int'), not recoverable from @Ob = ()@.
-- Use 'traceDense' / 'untraceDense'. A full 'Traced' instance would need
-- a size source for the feedback object — that is carrier A ('Finite')
-- or a future Ob refinement, not a silent guess.
module Circuit.Mat.Dense
  ( -- * Dense morphisms
    Dense (..),
    nrows,
    ncols,
    fromArray,
    toArray,
    tabulateDense,
    indexDense,

    -- * Category helpers
    eye,
    denseComp,

    -- * Monoidal / biproduct (value sizes)
    parDense,
    swapDense,
    unitlDense,
    unitlDense',
    unitrDense,
    unitrDense',

    -- * Trace / star (feedback width is a value)
    starDense,
    traceDense,
    untraceDense,

    -- * Boundary bridge to symbolic 'Mat' (Finite owns size on that side)
    fromMat,
    toMat,
  )
where

import Circuit.Classes (Category (..))
import Circuit.Mat (Finite (..), Mat (..), runMat)
import Circuit.Monoidal (Unit)
import Data.Kind (Type)
import Data.List qualified as List
import Data.Vector.Unboxed qualified as VU
import Data.Void (Void)
import Harpie.Array qualified as A
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding (id, sum, (*), (+), (.))

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude
-- >>> import Circuit.Mat.Dense
-- >>> import Circuit.Classes (Category (..))
-- >>> import qualified Harpie.Array as A

-- | Rank-2 dense matrix morphism @a → b@.
--
-- Phantom parameters @a@, @b@ are unconstrained object tags (@Ob = ()@).
-- Extents are 'nrows' / 'ncols' from the underlying array shape.
newtype Dense s (a :: Type) (b :: Type) = Dense {unDense :: A.Array s}
  deriving stock (Eq)

instance (Show s) => Show (Dense s a b) where
  showsPrec p (Dense a) =
    showParen (p > 10) $
      showString "Dense " . shows (VU.toList (A.shape a)) . showString " " . shows (A.arrayAs a :: [s])

-- | Row count (first shape component). @0@ if not rank-2.
nrows :: Dense s a b -> Int
nrows (Dense a) = case VU.toList (A.shape a) of
  (r : _) -> r
  [] -> 0

-- | Column count (second shape component). @0@ if not rank-2.
ncols :: Dense s a b -> Int
ncols (Dense a) = case VU.toList (A.shape a) of
  (_ : c : _) -> c
  _ -> 0

-- | Wrap a rank-2 array. Does not copy.
fromArray :: A.Array s -> Dense s a b
fromArray = Dense

-- | Underlying harpie array.
toArray :: Dense s a b -> A.Array s
toArray = unDense

-- | Build from a function on integer indices.
--
-- >>> let m = tabulateDense 2 2 (\i j -> if i == j then (1 :: Int) else 0)
-- >>> indexDense m 1 1
-- 1
tabulateDense :: Int -> Int -> (Int -> Int -> s) -> Dense s a b
tabulateDense r c f =
  Dense $
    A.tabulate [r, c] $ \case
      [i, j] -> f i j
      _ -> error "Circuit.Mat.Dense.tabulateDense: expected rank-2 index"

-- | Index at @(row, col)@.
indexDense :: Dense s a b -> Int -> Int -> s
indexDense (Dense a) i j = a A.! [i, j]

-- | Identity matrix of size @n@ (value size; phantoms free).
--
-- >>> indexDense (eye 3 :: Dense Int () ()) 1 1
-- 1
-- >>> indexDense (eye 3 :: Dense Int () ()) 1 2
-- 0
eye :: (Additive s, Multiplicative s) => Int -> Dense s a a
eye n =
  tabulateDense n n $ \i j -> case i == j of
    True -> one
    False -> zero

-- | Fused matrix multiply. Never uses 'A.expand' / 'A.dot'.
--
-- >>> let a = tabulateDense 2 3 (\i j -> i + j) :: Dense Int () ()
-- >>> let b = tabulateDense 3 2 (\i j -> i * j) :: Dense Int () ()
-- >>> indexDense (denseComp b a) 1 1
-- 8
denseComp ::
  (Additive s, Multiplicative s) =>
  Dense s b c ->
  Dense s a b ->
  Dense s a c
denseComp (Dense g) (Dense f) =
  let sf = VU.toList (A.shape f)
      sg = VU.toList (A.shape g)
   in case (sf, sg) of
        ([i, j], [j', k])
          | j == j' ->
              Dense $
                A.tabulate [i, k] $ \case
                  [r, c] ->
                    sum
                      [ (f A.! [r, p]) * (g A.! [p, c])
                        | p <- [0 .. j - 1]
                      ]
                  _ -> error "denseComp: bad index"
          | otherwise ->
              error $
                "Circuit.Mat.Dense.denseComp: inner dim mismatch "
                  <> show j
                  <> " vs "
                  <> show j'
        _ ->
          error $
            "Circuit.Mat.Dense.denseComp: expected rank-2 shapes, got "
              <> show sf
              <> " and "
              <> show sg

instance (Additive s, Multiplicative s) => Category (Dense s) where
  type Ob (Dense s) a = ()
  -- Size is not in Ob; polymorphic id is the 0×0 eye. Prefer 'eye n'.
  id = eye 0
  (.) = denseComp

-- ---------------------------------------------------------------------------
-- Biproduct layout (value sizes) — Either phantoms for wire tags only
-- ---------------------------------------------------------------------------

-- | Block-diagonal parallel: @parDense f g@ has shape
-- @[nrows f + nrows g, ncols f + ncols g]@.
--
-- >>> let f = eye 2 :: Dense Int () ()
-- >>> let g = eye 1 :: Dense Int () ()
-- >>> nrows (parDense f g)
-- 3
-- >>> indexDense (parDense f g) 2 2
-- 1
parDense ::
  (Additive s) =>
  Dense s a b ->
  Dense s c d ->
  Dense s (Either a c) (Either b d)
parDense f g =
  let rf = nrows f
      cf = ncols f
      rg = nrows g
      cg = ncols g
   in tabulateDense (rf + rg) (cf + cg) $ \r c ->
        case (r < rf, c < cf) of
          (True, True) -> indexDense f r c
          (False, False) -> indexDense g (r - rf) (c - cf)
          _ -> zero

-- | Swap block-permutation for equal block sizes on both wires.
--
-- @swapDense na nb@ is the symmetry @(na+nb) → (nb+na)@.
swapDense ::
  (Additive s, Multiplicative s) =>
  Int ->
  Int ->
  Dense s (Either a b) (Either b a)
swapDense na nb =
  tabulateDense (na + nb) (nb + na) $ \r c ->
    let r' = case r < na of
          True -> nb + r
          False -> r - na
     in case c == r' of
          True -> one
          False -> zero

-- Unitors are identity buffers; phantoms track Void-as-0-width wires.
unitlDense :: (Additive s, Multiplicative s) => Int -> Dense s (Either Void a) a
unitlDense n = case eye n of Dense a -> Dense a

unitlDense' :: (Additive s, Multiplicative s) => Int -> Dense s a (Either Void a)
unitlDense' n = case eye n of Dense a -> Dense a

unitrDense :: (Additive s, Multiplicative s) => Int -> Dense s (Either a Void) a
unitrDense n = case eye n of Dense a -> Dense a

unitrDense' :: (Additive s, Multiplicative s) => Int -> Dense s a (Either a Void)
unitrDense' n = case eye n of Dense a -> Dense a

-- Tensor class: unitors need a size for the non-Void wire; with Ob=() that
-- size is not available. We expose value-sized helpers above and instance
-- only 'par' via a thin wrapper would still leave unitl stuck.
-- So we do **not** force a incomplete Tensor Either instance — use parDense.

type instance Unit Either = Void

-- ---------------------------------------------------------------------------
-- Star / trace (feedback width is an Int value)
-- ---------------------------------------------------------------------------

-- | Kleene star on a square dense matrix (value size).
starDense ::
  (StarSemiring s, Additive s, Multiplicative s) =>
  Dense s a a ->
  Dense s a a
starDense m =
  let n = nrows m
   in case ncols m == n of
        False -> error "Circuit.Mat.Dense.starDense: not square"
        True ->
          let f = indexDense m
              start i j = case i == j of
                True -> one + f i j
                False -> f i j
              step stepm k i j =
                stepm i j
                  + (stepm i k * star (stepm k k) * stepm k j)
              go = List.foldl' step start [0 .. n - 1]
           in tabulateDense n n go

-- | Schur-complement trace with explicit feedback width @n@.
--
-- Body shape must be @[n+b, n+c]@; result is @b × c@.
--
-- >>> let body = tabulateDense 2 2 (\i j -> case (i, j) of (0,1) -> True; (1,0) -> True; _ -> False) :: Dense Bool (Either () ()) (Either () ())
-- >>> indexDense (traceDense 1 body) 0 0
-- True
traceDense ::
  (StarSemiring s, Additive s, Multiplicative s) =>
  Int ->
  Dense s (Either a b) (Either a c) ->
  Dense s b c
traceDense n body =
  let r = nrows body
      c = ncols body
      b = r - n
      d = c - n
   in case (b >= 0 && d >= 0) of
        False ->
          error $
            "Circuit.Mat.Dense.traceDense: feedback "
              <> show n
              <> " exceeds shape "
              <> show (r, c)
        True ->
          let at i j = indexDense body i j
              maa = tabulateDense n n $ \i j -> at i j
              mac = tabulateDense n d $ \i j -> at i (n + j)
              mba = tabulateDense b n $ \i j -> at (n + i) j
              mbc = tabulateDense b d $ \i j -> at (n + i) (n + j)
              mid = denseComp mac (denseComp (starDense maa) mba)
           in tabulateDense b d $ \i j ->
                indexDense mbc i j + indexDense mid i j

-- | Embed @f : b → c@ as the lower-right block with feedback size @n@
-- (upper-left identity on the feedback wire).
untraceDense ::
  (Additive s, Multiplicative s) =>
  Int ->
  Dense s b c ->
  Dense s (Either a b) (Either a c)
untraceDense n f = parDense (eye n) f

-- ---------------------------------------------------------------------------
-- Boundary bridge — Finite owns size on the Mat side only
-- ---------------------------------------------------------------------------

-- | Densify a symbolic matrix. Shape taken from 'universe' lengths.
fromMat ::
  forall s i j.
  (Finite i, Finite j, Additive s, Multiplicative s, Eq j) =>
  Mat s i j ->
  Dense s i j
fromMat m =
  let ui = universe @i
      uj = universe @j
      r = List.length ui
      c = List.length uj
   in tabulateDense r c $ \ri ci ->
        runMat m (ui List.!! ri) (uj List.!! ci)

-- | Reify a dense matrix as a function leaf (pays Finite at the boundary).
toMat ::
  forall s i j.
  (Finite i, Finite j) =>
  Dense s i j ->
  Mat s i j
toMat d =
  let ui = universe @i
      uj = universe @j
   in Mat $ \ix jx ->
        case (List.elemIndex ix ui, List.elemIndex jx uj) of
          (Just r, Just c) -> indexDense d r c
          _ -> error "Circuit.Mat.Dense.toMat: index not in universe"
