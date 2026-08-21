{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Square matrices as a NumHask carrier.
--
-- This module adds the missing NumHask ring/field instances for square
-- @Harpie.Fixed.Array@s, turning @Array '[n,n] a@ into a lawful
-- 'Multiplicative' carrier.  No new wrapper type is introduced: 'Square' is
-- just a type synonym.
module Circuit.Mat.Square
  ( Square,
    inverse,
  )
where

import Data.Bool (bool)
import Data.List (maximumBy)
import Data.Ord (comparing)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal)
import Harpie.Fixed (Array)
import Harpie.Fixed qualified as F
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Metric (Absolute, abs)
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Data.Integral (FromInteger (..))
import NumHask.Data.Rational (FromRational (..))
import Prelude hiding (abs, fromInteger, fromRational, (*), (+), (-), (/))
import Prelude qualified as P

-- | A square matrix of known dimension.
type Square (n :: Nat) a = Array '[n, n] a

-- ---------------------------------------------------------------------------
-- NumHask instances
-- ---------------------------------------------------------------------------

instance
  ( KnownNat n,
    Additive a,
    Multiplicative a
  ) =>
  Multiplicative (Square n a)
  where
  (*) = F.mult
  one = F.ident

instance
  ( KnownNat n,
    Additive a,
    Subtractive a,
    Multiplicative a,
    Divisive a,
    Absolute a,
    Ord a
  ) =>
  Divisive (Square n a)
  where
  recip = inverse

instance
  ( KnownNat n,
    Additive a,
    Multiplicative a,
    FromInteger a
  ) =>
  FromInteger (Square n a)
  where
  fromInteger k = F.zipWith (*) (F.konst (fromInteger k)) F.ident

instance
  ( KnownNat n,
    Additive a,
    Multiplicative a,
    FromRational a
  ) =>
  FromRational (Square n a)
  where
  fromRational q = F.zipWith (*) (F.konst (fromRational q)) F.ident

-- ---------------------------------------------------------------------------
-- Matrix inverse (Gauss-Jordan with partial pivoting)
-- ---------------------------------------------------------------------------

-- | Inverse of a square matrix.
inverse ::
  forall n a.
  ( KnownNat n,
    Subtractive a,
    Divisive a,
    Absolute a,
    Ord a
  ) =>
  Square n a ->
  Square n a
inverse a =
  let n = P.fromIntegral (natVal (Proxy @n))
      row i = [a F.! [i, j] | j <- [0 .. n P.- 1]]
      eye i j = bool zero one (i P.== j)
      aug = [row i P.++ [eye i j | j <- [0 .. n P.- 1]] | i <- [0 .. n P.- 1]]
      reduced = gaussJordan aug
      invRows = P.map (P.drop n) reduced
   in F.array (P.concat invRows)

-- Gauss-Jordan elimination with partial pivoting.
gaussJordan ::
  ( Subtractive a,
    Divisive a,
    Absolute a,
    Ord a
  ) =>
  [[a]] ->
  [[a]]
gaussJordan [] = []
gaussJordan m0 = P.snd (P.foldl' step (m0, []) [0 .. n P.- 1])
  where
    n = P.length m0
    step (rows, doneRows) k =
      let pivotOffset =
            fst $
              maximumBy
                (comparing (abs . (!! k) . snd))
                (P.zip [0 ..] rows)
          rows' = swap k pivotOffset rows
          pivot = rows' !! k !! k
          rowK = P.map (/ pivot) (rows' !! k)
          eliminate i row
            | i P.== k = rowK
            | P.otherwise =
                let factor = row !! k
                 in P.zipWith (-) row (P.map (factor *) rowK)
          remaining = P.zipWith eliminate [0 ..] rows'
       in (remaining, doneRows P.++ [rowK])

-- Swap two positions in a list.
swap :: Int -> Int -> [a] -> [a]
swap i j xs =
  [ case k of
      _ | k P.== i -> xs P.!! j
      _ | k P.== j -> xs P.!! i
      _ -> x
  | (k, x) <- P.zip [0 ..] xs
  ]
