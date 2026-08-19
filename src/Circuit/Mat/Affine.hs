{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Affine indexing morphisms between harpie-style shapes.
--
-- An @Affine p q@ is an affine map @q = Λ·p + v@ where @Λ@ is a
-- @len q × len p@ matrix of natural numbers and @v@ is a @len q@ offset
-- vector.  In-bounds is checked at construction time.
--
-- These are the change-of-basis joints that let @Mat@ constructions flow
-- between carriers: flatten, shapen, axis swap, and arbitrary permutations
-- are all affine maps, and harpie consumes them as stride/index maps.
module Circuit.Mat.Affine
  ( -- * Type
    Affine (..),

    -- * Smart constructor
    affine,

    -- * Category structure
    identityAffine,
    composeAffine,
    applyAffine,

    -- * Canonical maps
    flattenAffine,
    swapAxesAffine,
    permuteAxes,

    -- * Harpie seam
    toIndexMap,
    toHarpieBackpermute,
  )
where

import Data.Bool (bool)
import Data.List (lookup, sort)
import GHC.TypeNats (KnownNat, Nat)
import qualified GHC.TypeNats as TN
import Harpie.Fixed qualified as F
import Harpie.Shape (Fins (..), KnownNats, valuesOf)
import Prelude

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XTypeApplications
-- >>> import Circuit.Mat.Affine

-- | Type-level product of a shape list.
type family SizeOf (p :: [Nat]) :: Nat where
  SizeOf '[] = 1
  SizeOf (n ': ns) = n TN.* SizeOf ns

-- | An affine map from shape @p@ to shape @q@.
--
-- The phantom types carry the shape; the fields carry the concrete matrix and
-- offset.  Use 'affine' to construct a validated value.
data Affine (p :: [Nat]) (q :: [Nat]) = Affine
  { lambda :: [[Int]],
    offset :: [Int]
  }
  deriving (Eq, Show)

-- | Smart constructor.  Returns 'Nothing' if the dimensions do not match the
-- shape, if entries are negative, or if offsets are out of bounds.
affine ::
  forall p q.
  (KnownNats p, KnownNats q) =>
  [[Int]] ->
  [Int] ->
  Maybe (Affine p q)
affine lam off
  | not shapeOK = Nothing
  | any (< 0) (concat lam) = Nothing
  | any (< 0) off = Nothing
  | not offsetsOK = Nothing
  | otherwise = Just (Affine lam off)
  where
    sp = valuesOf @p
    sq = valuesOf @q
    shapeOK =
      length lam == length sq
        && all (== length sp) (map length lam)
    offsetsOK = and (zipWith (<) off sq)

-- | Identity affine map.
identityAffine :: forall p. (KnownNats p) => Affine p p
identityAffine =
  let n = length (valuesOf @p)
   in Affine
        { lambda = [[bool 0 1 (i == j) | j <- [0 .. n - 1]] | i <- [0 .. n - 1]],
          offset = replicate n 0
        }

-- | Composition of affine maps.
--
-- >>> let Just f = affine @'[2,3] @'[6] [[3,1]] [0]
-- >>> let Just g = affine @'[6] @'[2,3] [[1],[2]] [0,0]
-- >>> applyAffine (composeAffine g f) [1,2]
-- [1,2]
composeAffine ::
  forall p q r.
  (KnownNats p, KnownNats q, KnownNats r) =>
  Affine q r ->
  Affine p q ->
  Affine p r
composeAffine (Affine lam2 off2) (Affine lam1 off1) =
  Affine
    { lambda = [[sum [lam2 !! i !! k * lam1 !! k !! j | k <- [0 .. q - 1]] | j <- [0 .. p - 1]] | i <- [0 .. r - 1]],
      offset = zipWith (+) off2 [sum [lam2 !! i !! k * off1 !! k | k <- [0 .. q - 1]] | i <- [0 .. r - 1]]
    }
  where
    p = length (valuesOf @p)
    q = length (valuesOf @q)
    r = length (valuesOf @r)

-- | Apply an affine map to an index vector.  Assumes the input is in bounds.
applyAffine :: Affine p q -> [Int] -> [Int]
applyAffine (Affine lam off) x = zipWith (+) off [sum (zipWith (*) row x) | row <- lam]

-- | Flatten a shape to its total size.
flattenAffine ::
  forall p.
  (KnownNats p) =>
  Affine p '[SizeOf p]
flattenAffine =
  let sp = valuesOf @p
      strides = drop 1 (scanr (*) 1 sp)
   in Affine
        { lambda = [strides],
          offset = [0]
        }

-- | Swap the two axes of a rank-2 shape.
swapAxesAffine ::
  (KnownNat m, KnownNat n) =>
  Affine '[m, n] '[n, m]
swapAxesAffine =
  Affine
    { lambda = [[0, 1], [1, 0]],
      offset = [0, 0]
    }

-- | Permute axes by a value-level permutation list.
--
-- The permutation must be a reordering of @[0 .. length p - 1]@.  No
-- type-level tracking of the output shape is attempted; the caller supplies
-- the desired shape phantom.
permuteAxes ::
  forall p q.
  (KnownNats p, KnownNats q) =>
  [Int] ->
  Maybe (Affine p q)
permuteAxes perm
  | not ok = Nothing
  | otherwise = affine lam (replicate (length sq) 0)
  where
    sp = valuesOf @p
    sq = valuesOf @q
    n = length sp
    m = length sq
    ok =
      m == n
        && sort perm == [0 .. n - 1]
        && sq == map (sp !!) perm
    lam = [[bool 0 1 (perm !! i == j) | j <- [0 .. n - 1]] | i <- [0 .. m - 1]]

-- | Apply the affine map to harpie 'Fins'.
toIndexMap :: Affine p q -> Fins p -> Fins q
toIndexMap a (UnsafeFins x) = UnsafeFins (applyAffine a x)

-- | Build a harpie 'F.backpermute' from an affine map.
--
-- This is the code generator: an affine reindexing becomes a harpie
-- backpermute with an index-map derived from the affine inverse.  The map is
-- precomputed, so the result fuses with surrounding harpie operations.
--
-- Precondition: the affine map must be a bijection between the index sets
-- (true for flatten, permutation, and axis-swap).  If it is not, the lookup
-- will fail at runtime.
toHarpieBackpermute ::
  forall p q s.
  (KnownNats p, KnownNats q) =>
  Affine p q ->
  F.Array p s ->
  F.Array q s
toHarpieBackpermute a arr = F.backpermute inverseFins arr
  where
    inverseFins (UnsafeFins q) =
      case lookup q inverseMap of
        Just p -> UnsafeFins p
        Nothing -> error "toHarpieBackpermute: affine map is not a bijection on indices"
    inverseMap =
      [ (applyAffine a ps, ps)
        | ps <- shapeIndices (valuesOf @p)
      ]

-- | All index vectors for a shape.
shapeIndices :: [Int] -> [[Int]]
shapeIndices = mapM (\d -> [0 .. d - 1])
