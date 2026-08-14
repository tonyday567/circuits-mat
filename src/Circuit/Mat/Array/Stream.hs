{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Harpie arrays as 'Circuit.Stream' instances.
--
-- A non-empty array of shape @[n, m₁, …, mₖ]@ is a stream of @n@ rows, each
-- a token of shape @[m₁, …, mₖ]@.  The stream classes give the abstract
-- boundary-aware interface; the underlying operations are harpie's
-- 'Harpie.Array.cons', 'uncons', 'snoc', and 'unsnoc'.
--
-- The empty stream is 'Harpie.Array.empty'.  Because the shape of rows is
-- value-level in harpie, 'cons' and 'snoc' construct a one-row array when
-- applied to the empty stream.
module Circuit.Mat.Array.Stream
  ( -- * Re-exported classes
    Stream.Uncons (..),
    Stream.Cons (..),
    Stream.Snoc (..),
    Stream.These (..),
  )
where

import Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import Circuit.Stream qualified as Stream
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Harpie.Array (Array (..))
import Harpie.Array qualified as D
import Prelude hiding (id, (.))

-- | An array is a stream of its rows.
--
-- * Empty array  → 'That' empty
-- * One-row array  → 'This' row
-- * Many-row array → 'These' head tail
instance Uncons (Array a) (Array a) where
  uncons a
    | D.isNull a = That a
    | D.length a == 1 = This (D.select 0 0 a)
    | otherwise =
        let (x, xs) = D.uncons a
         in These x xs
  nil = D.empty

-- | Prepend a row.  When the tail is the empty stream, construct a
-- one-row array from the row's shape.
instance Cons (Array a) (Array a) where
  cons x xs
    | D.isNull xs = D.array (1 : VU.toList (D.shape x)) (V.toList (D.asVector x))
    | otherwise = D.cons x xs
  consNil = D.empty

-- | Append a row.  When the initial stream is empty, construct a
-- one-row array from the row's shape.
instance Snoc (Array a) (Array a) where
  snoc xs x
    | D.isNull xs = D.array (1 : VU.toList (D.shape x)) (V.toList (D.asVector x))
    | otherwise = D.snoc xs x
  snocNil = D.empty
