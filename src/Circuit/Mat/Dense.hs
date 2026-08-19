{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | Value-sized dense matrices backed by 'Harpie.Array'.
--
-- This module provides the canonical dense-matrix carrier for numhask-based
-- computation: Kleene star (reflexive-transitive closure), matrix
-- multiplication, and matrix-vector products.  It is intentionally rank-2 and
-- value-sized so it can serve categories whose object constraints live at
-- runtime (e.g. 'Circuit.Mat.Finite' enumeration or plain list channels) as
-- well as typed settings.
--
-- Moved from @harpie-numhask@ as part of the matrix-calculus extraction into
-- @circuits-mat@.
module Circuit.Mat.Dense
  ( Matrix (..),
    fromLists,
    toLists,
    matPlus,
    matTimes,
    matVec,
    starMatrix,
    qrM,
    forwardSubstStream,
  )
where

import Circuit.Mat.Array.Stream qualified as Stream
import Data.Bool (bool)
import Data.Foldable hiding (sum)
import Data.List (foldl')
import Data.Vector.Unboxed qualified as VU
import Harpie.Array as A
import NumHask.Algebra.Additive (Additive (..), Subtractive (..), sum)
import NumHask.Algebra.Field (ExpField (..))
import NumHask.Algebra.Metric (Absolute, abs)
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding (drop, foldl', length, negate, repeat, sqrt, sum, take, zipWith, (*), (+), (-), (/))
import Prelude qualified as P

-- | Square matrix stored as a rank-2 'Harpie.Array' in row-major order.
newtype Matrix a = Matrix {unMatrix :: A.Array a}
  deriving (Eq, Show)

-- | Row count.
rows :: Matrix a -> Int
rows (Matrix a) = case VU.toList (A.shape a) of (r : _) -> r; _ -> 0

-- | Column count.
cols :: Matrix a -> Int
cols (Matrix a) = case VU.toList (A.shape a) of (_ : c : _) -> c; _ -> 0

-- | Build a matrix from nested rows.
--
-- An empty list becomes a 0×0 matrix.
fromLists :: [[a]] -> Matrix a
fromLists [] = Matrix (A.array [0, 0] [])
fromLists xss@(r : _) = Matrix (A.array [P.length xss, P.length r] (P.concat xss))

-- | Convert a matrix to nested rows.
toLists :: Matrix a -> [[a]]
toLists (Matrix a) =
  let r = rows (Matrix a)
      c = cols (Matrix a)
   in [[a A.! [i, j] | j <- [0 .. c - 1]] | i <- [0 .. r - 1]]

-- | Elementwise addition.
matPlus :: (Additive a) => Matrix a -> Matrix a -> Matrix a
matPlus (Matrix a) (Matrix b) = Matrix (A.zipWith (+) a b)

-- | Matrix multiplication.
matTimes ::
  (Additive a, Multiplicative a) =>
  Matrix a ->
  Matrix a ->
  Matrix a
matTimes (Matrix a) (Matrix b) =
  case (VU.toList (A.shape a), VU.toList (A.shape b)) of
    ([ra, ca], [rb, cb]) ->
      case ca == rb of
        False -> error "Circuit.Mat.Dense.matTimes: inner dimension mismatch"
        True ->
          Matrix $
            A.tabulate
              [ra, cb]
              ( \ij -> case ij of
                  [i, j] -> sum [a A.! [i, k] * b A.! [k, j] | k <- [0 .. ca - 1]]
                  _ -> error "Circuit.Mat.Dense.matTimes: expected rank-2 index"
              )
    _ -> error "Circuit.Mat.Dense.matTimes: expected rank-2 matrices"

-- | Matrix–vector product.
matVec ::
  (Additive a, Multiplicative a) =>
  Matrix a ->
  [a] ->
  [a]
matVec (Matrix a) v =
  case VU.toList (A.shape a) of
    [r, c] ->
      let n = P.length v
       in case c == n of
            False -> error "Circuit.Mat.Dense.matVec: dimension mismatch"
            True ->
              [ sum [a A.! [i, k] * (v P.!! k) | k <- [0 .. c - 1]]
              | i <- [0 .. r - 1]
              ]
    _ -> error "Circuit.Mat.Dense.matVec: expected a rank-2 matrix"

-- | Kleene star of a square matrix by the standard state-elimination
-- (Warshall / Floyd-Kleene) algorithm.
--
-- For a matrix @A@, computes @A* = I + A + A² + ...@ as the least fixed
-- point of @X ↦ I + A·X@. Requires a 'StarSemiring' element type so that
-- @star x@ is available for the pivot updates.
--
-- When the element type is a 'NumHask.Algebra.Quantale.Quantale', this is the
-- join of the geometric series @I + A + A² + …@; the algorithm uses the
-- 'StarSemiring' fragment (iterative joins) to compute it finitely.
starMatrix ::
  (StarSemiring a) =>
  Matrix a ->
  Matrix a
starMatrix (Matrix a) =
  let sh = VU.toList (A.shape a)
   in case sh of
        [0, 0] -> Matrix a
        [n, m]
          | n == m ->
              let step arr k =
                    A.tabulate
                      [n, n]
                      ( \ij -> case ij of
                          [i, j] ->
                            let aik = A.index arr [i, k]
                                akk = A.index arr [k, k]
                                akj = A.index arr [k, j]
                                aij = A.index arr [i, j]
                             in aij + aik * star akk * akj
                          _ -> error "Circuit.Mat.Dense.starMatrix: expected rank-2 index"
                      )
                  closed = foldl' step a [0 .. n - 1]
               in -- Floyd-Kleene on A is A⁺. Seed I afterwards, matching 'starM':
                  -- A* = I + A⁺.
                  Matrix $
                    A.tabulate [n, n] $ \ij -> case ij of
                      [i, j] -> A.index closed [i, j] + bool zero one (i == j)
                      _ -> error "Circuit.Mat.Dense.starMatrix: expected rank-2 index"
        _ -> error "Circuit.Mat.Dense.starMatrix: expected a square matrix"

-- | QR decomposition via Householder reflections.
--
-- Returns @(q, r)@ with @q@ orthogonal and @r@ upper triangular such that
-- @a = q r@.  The algorithm is the standard column-by-column Householder
-- reduction on value-sized 'Harpie.Array' matrices.
qrM ::
  ( Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a,
    Absolute a,
    Ord a,
    Show a
  ) =>
  Matrix a ->
  (Matrix a, Matrix a)
qrM (Matrix a) =
  let sh = VU.toList (A.shape a)
   in case sh of
        [m, n] ->
          let q0 = Matrix (A.ident [m, m])
              r0 = Matrix a
              steps = [0 .. P.min m n - 1]
              (q, r) = foldl' (householderQRStep m n) (q0, r0) steps
           in (q, r)
        _ -> error "Circuit.Mat.Dense.qrM: expected a rank-2 matrix"

-- | One Householder QR step for column @k@.
householderQRStep ::
  ( Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    ExpField a,
    Absolute a,
    Ord a,
    Show a
  ) =>
  Int ->
  Int ->
  (Matrix a, Matrix a) ->
  Int ->
  (Matrix a, Matrix a)
householderQRStep m n (Matrix q, Matrix r) k =
  let mk = m - k
      nk = n - k
      -- subcolumn x = r[k..m-1, k]
      x = A.tabulate [mk] (\[i] -> r A.! [k + i, k])
      xk = x A.! [0]
      norm = sqrt (sum [(x A.! [i]) * (x A.! [i]) | i <- [0 .. mk - 1]])
      alpha = bool (negate norm) norm (xk < zero)
      v = A.tabulate [mk] (\[i] -> bool (x A.! [i]) (xk - alpha) (i == 0))
      vtv = sum [(v A.! [i]) * (v A.! [i]) | i <- [0 .. mk - 1]]
   in bool
        (Matrix q, Matrix r)
        ( let scale = (one + one) / vtv
              -- update r[k..m-1, k..n-1]
              subR = A.tabulate [mk, nk] (\[i, j] -> r A.! [k + i, k + j])
              vta = A.prod [0] [0] sum (*) v subR
              outerR = A.expand (*) v vta
              subR' = A.zipWith (-) subR (fmap (scale *) outerR)
              r' = updateSubmatrix r k k subR'
              -- update q[:, k..m-1] on the right by H_k
              subQ = A.tabulate [m, mk] (\[i, j] -> q A.! [i, k + j])
              qv = A.prod [1] [0] sum (*) subQ v
              outerQ = A.expand (*) qv v
              subQ' = A.zipWith (-) subQ (fmap (scale *) outerQ)
              q' = updateSubmatrix q 0 k subQ'
           in (Matrix q', Matrix r')
        )
        (vtv == zero)

-- | Overwrite a rectangular region of a matrix with a smaller array.
updateSubmatrix :: A.Array a -> Int -> Int -> A.Array a -> A.Array a
updateSubmatrix m rowOff colOff sub =
  let sh = VU.toList (A.shape m)
      subSh = VU.toList (A.shape sub)
      rowsSub = subSh !! 0
      colsSub = subSh !! 1
   in A.tabulate sh $ \ij -> case ij of
        [i, j]
          | i >= rowOff && i < rowOff + rowsSub && j >= colOff && j < colOff + colsSub ->
              sub A.! [i - rowOff, j - colOff]
          | otherwise -> m A.! [i, j]
        _ -> error "Circuit.Mat.Dense.updateSubmatrix: expected rank-2 index"

-- | Forward substitution as a stream morphism.
--
-- Solves @L y = b@ for unit lower-triangular @L@ by streaming rows of @L@ and
-- components of @b@, accumulating @y@ one component at a time.  Each step is a
-- dot product of the already-computed prefix of @y@ with the active row prefix
-- of @L@, followed by subtraction from the current @b@ component.
forwardSubstStream ::
  (Additive a, Subtractive a, Multiplicative a) =>
  A.Array a ->
  A.Array a ->
  A.Array a
forwardSubstStream l b = go (Stream.uncons l) (Stream.uncons b) A.empty
  where
    go (Stream.These rowL restL) (Stream.These bi restB) ys =
      let yi = solveRow rowL bi ys
       in go (Stream.uncons restL) (Stream.uncons restB) (Stream.snoc ys yi)
    go (Stream.This rowL) (Stream.This bi) ys = Stream.snoc ys (solveRow rowL bi ys)
    go _ _ ys = ys
    solveRow rowL bi ys =
      let k = A.length ys
          rowPrefix = A.take 0 k rowL
          rowDot = sum [rowPrefix A.! [j] * ys A.! [j] | j <- [0 .. k - 1]]
       in A.zipWith (-) bi (A.array [] [rowDot])
