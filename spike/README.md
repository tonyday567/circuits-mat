# Enumeration Spike: circuits-mat

## 1. Finite enumeration cost vs matrix operations

The `Finite` class uses `universe :: [a]` which is O(n) in the number of inhabitants.
The Kleene star `starM` is O(|V|³) scalar operations.

| |V| | universe (ops) | star-closure (ops) | ratio |
|-----|---------------|-------------------|--------|
| 2   | 2             | 8                 | 0.25   |
| 4   | 4             | 64                | 0.0625 |
| 8   | 8             | 512               | 0.0156 |
| 16  | 16            | 4,096             | 0.0039 |
| 32  | 32            | 32,768            | 0.0010 |
| 64  | 64            | 262,144           | 0.00024|
| 128 | 128           | 2,097,152         | 0.00006|

**Conclusion**: For |V| >= 8, enumeration is < 2% of total cost.
For |V| >= 32, enumeration is < 0.1% of total cost.
The `Finite` dictionary is not a performance bottleneck.

## 2. Harpie as index type replacement

### What harpie provides

- `Harpie.Shape.Fin (n :: Nat)`: a newtype around `Int` representing `{0, …, n-1}`.
- `Harpie.Shape.fin :: KnownNat n => Int -> Fin n` constructs a `Fin` (errors out of bounds).
- `Harpie.Shape.valueOf :: KnownNat n => Int` reflects the type-level bound to the value level.
- `Harpie.Shape.KnownNats (ns :: [Nat])` witnesses lists of naturals.
- `Harpie.Fixed.Array (ns :: [Nat]) a` is a dense, statically-shaped array.

A matrix `i -> j` over `s` can be stored as `Array @[i, j] s`.

### Why `Either (Fin i) (Fin j)` is not a harpie shape

harpie shapes are rectangular products of dimensions. The biproduct in `Mat` is a sum (`Either`), with `i + j` inhabitants. There is no shape constructor for sums, so we need an explicit isomorphism.

### The `Either (Fin i) (Fin j) ≅ Fin (i + j)` isomorphism

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import GHC.TypeNats
import Harpie.Shape (Fin (..), KnownNat, valueOf)

eitherToFin :: forall i j. (KnownNat i, KnownNat j) => Either (Fin i) (Fin j) -> Fin (i + j)
eitherToFin (Left (UnsafeFin a))  = UnsafeFin a
eitherToFin (Right (UnsafeFin b)) = UnsafeFin (valueOf @i + b)

finToEither :: forall i j. (KnownNat i, KnownNat j) => Fin (i + j) -> Either (Fin i) (Fin j)
finToEither (UnsafeFin x)
  | x < valueOf @i = Left  (UnsafeFin x)
  | otherwise      = Right (UnsafeFin (x - valueOf @i))
```

`Harpie.Shape` exports `UnsafeFin`; the bounds are satisfied by construction because `0 ≤ a < i` and `0 ≤ b < j`. `valueOf @i` is the split point. `GHC.TypeNats.+` gives the type-level sum.

### What `par` looks like with harpie-backed indices

If matrices are indexed by `Fin n`, the biproduct `par` becomes block-diagonal embedding into shape `[i + k, j + l]`:

```haskell
parH ::
  (KnownNat i, KnownNat j, KnownNat k, KnownNat l, Additive s, Multiplicative s) =>
  Mat s (Fin i) (Fin j) ->
  Mat s (Fin k) (Fin l) ->
  Mat s (Fin (i + k)) (Fin (j + l))
parH m n = Mat $ \r c ->
  case (finToEither r, finToEither c) of
    (Left r',  Left c')  -> runMat m r' c'
    (Right r', Right c') -> runMat n r' c'
    _                    -> zero
```

This is the same semantics as the current `Par` constructor, but the result lives on a single rectangular `Fin (i + k) × Fin (j + l)` index set — exactly what a harpie `Array @[i + k, j + l] s` expects.

### Tradeoffs

- **Pros**: index sizes are type-level naturals; dense arrays are first-class; no `Enum`/`Bounded` boilerplate.
- **Cons**: every `par` and every trace boundary must reindex through the iso; the iso is cheap (`O(1)` integer compare/add) but not zero; sums are not native harpie shapes.

For current `circuits-mat` scale, `Finite` types are simpler. Harpie pays off when we want dense matrix kernels or compile-time shape guarantees.

## 3. Path to a `Traced` instance

### The blocker

`Circuit.Trace.Traced` is parametric in the feedback channel:

```haskell
class Traced t arr where
  trace :: arr (t a b) (t a c) -> arr b c
```

`traceMat` requires `Finite a` on that channel:

```haskell
traceMat :: (..., Finite a, ...) => Mat s (Either a b) (Either a c) -> Mat s b c
```

The class gives us no `Finite a` evidence, so a direct `Traced Either (Mat s)` instance cannot call `traceMat`.

### Option A: `KnownNat` wrapper type

The wrapper bridges harpie’s `Fin` to `circuits-mat`’s `Finite`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}

import GHC.TypeNats
import Harpie.Shape (Fin (..), fin, valueOf)

newtype F (n :: Nat) = F { unF :: Fin n }
  deriving (Eq, Ord, Show)

instance KnownNat n => Finite (F n) where
  universe = [F (fin @n i) | i <- [0 .. valueOf @n - 1]]
```

Now any value of type `Mat s (Either (F n) b) (Either (F n) c)` carries a `Finite (F n)` dictionary from the `KnownNat n` constraint at the use site. We can define:

```haskell
traceF ::
  (KnownNat n, StarSemiring s, Additive s, Multiplicative s, Finite b, Finite c) =>
  Mat s (Either (F n) b) (Either (F n) c) ->
  Mat s b c
traceF = traceMat
```

This works for any feedback size `n` without hand-enumerating inhabitants. It is still not a `Traced` instance because `Traced` is parametric in `a`, but it removes the hand-written `universe` boilerplate.

### Option B: Restricted category `MatF`

Make the category's objects exactly `F n`:

```haskell
newtype MatF s (i :: Nat) (j :: Nat) = MatF (Mat s (Fin i) (Fin j))

runMatF :: MatF s i j -> Fin i -> Fin j -> s
runMatF (MatF m) = runMat m
```

Then we can provide a `Traced` instance by unwrapping `F`, reindexing `Either (F n) (F m)` to `Either (Fin n) (Fin m)`, and calling `traceMat`:

```haskell
instance Traced Either (MatF s) where
  trace (MatF m) = MatF $ traceMat $ reindexEitherF m
```

The instance is valid because every object `F n` is `Finite` whenever `n` is a `Nat`. The cost is a separate category: existing generic code over `Mat` does not apply to `MatF` directly.

### Option C: Upstream `Traced` class change

Add an associated constraint to `Traced`:

```haskell
class Traced t arr where
  type TracedObj t arr a :: Constraint
  type TracedObj t arr a = ()
  trace :: (TracedObj t arr a) => arr (t a b) (t a c) -> arr b c
```

Then `Mat` gets:

```haskell
instance Traced Either (Mat s) where
  type TracedObj Either (Mat s) a = Finite a
  trace = traceMat
```

This is the cleanest end state but it changes `circuits` core and may break other `Traced` instances.

### Recommendation

- **Short term**: keep `traceMat` explicit (current approach). It is total and usable today.
- **Medium term**: land the `F n` wrapper and its `Finite` instance. This lets `traceMat` work with harpie-style index sets without touching `circuits` core.
- **Long term**: evaluate Option C if multiple categories need finite feedback channels; otherwise keep `traceMat` explicit and avoid a parallel `MatF` category.

## 4. Verified trace laws (docspec)

All three trace laws verified via docspec (0 errors):
- **Naturality**: `traceMat (Comp (Par Id g) f) = Comp g (traceMat f)`
- **Sliding**: `traceMat (Comp (Par g Swap) f) = traceMat (Comp f (Par g Swap))`
- **Vanishing**: `traceMat block = expected` (Schur-complement over unit channel)
