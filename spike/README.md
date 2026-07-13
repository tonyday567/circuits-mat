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
- `Harpie.Shape.Fin n`: type-level finite index set `{0, ..., n-1}`
- `Harpie.Shape.KnownNats`: type-level dimension list
- `Harpie.Fixed.Array @[n] a`: fixed-shape array with `KnownNat n`
- `tabulate :: (Fin n -> a) -> Array @[n] a` — builds array from index function

### Matrix as harpie array
```
Mat i j s  ≅  Array @[i, j] s   (with KnownNat i, KnownNat j)
```

### Biproduct via Either
`Either (Fin i) (Fin j)` is not a harpie shape (shapes are rectangular/products, not sums).
Need the isomorphism:
```
eitherToFin :: Either (Fin i) (Fin j) -> Fin (i + j)
finToEither :: Fin (i + j) -> Either (Fin i) (Fin j)
```
This requires type-level arithmetic (`i + j`) via `GHC.TypeNats`.

The `par` operation would be block-diagonal embedding:
```
par :: Mat i j s -> Mat k l s -> Mat (i + k) (j + l) s
```
Clean with `KnownNat` — the index sets compose by addition.

### Feasibility
- **Yes**: harpie arrays can represent matrices. The `Either` biproduct maps to sum-of-sizes with an index isomorphism.
- **No**: harpie arrays are rectangular. The `Either` sum type needs explicit iso, adding runtime index arithmetic overhead inside the isomorphism.
- **Tradeoff**: `Finite` with `Enum`/`Bounded` types is simpler and sufficient for current scale. Harpie would add type-level size guarantees but with more complexity.

## 3. Traced instance with KnownNat + harpie

### Current state
The `Traced` class from `Circuit.Trace`:
```haskell
class Traced t arr where
  trace :: arr (t a b) (t a c) -> arr b c
```
`a` is fully parametric — no `Finite`/`KnownNat` constraint.

`traceMat` requires `Finite a` on the feedback channel:
```haskell
traceMat :: (..., Finite a, ...) => Mat s (Either a b) (Either a c) -> Mat s b c
```

### Why Traced can't be an instance
The parametric `a` in `Traced` prevents calling `starM` which needs `Finite a`.
This is a fundamental tension: categorical trace is parametric, but matrix trace needs enumeration.

### Possible resolutions

#### Option 1: Variant class (TracedK)
```haskell
class TracedK t arr where
  traceK :: KnownNat n => arr (t (F n) b) (t (F n) c) -> arr b c
```
Clean but incompatible with circuits' `Traced`. Creates a parallel universe.

#### Option 2: Wrapper type with KnownNat → Finite bridge
```haskell
newtype F (n :: Nat) = F (Fin n)

instance KnownNat n => Finite (F n) where
  universe = map F [0 .. fromIntegral (natVal (Proxy @n)) - 1]
```
Keeps `Traced` compatibility. `trace` would work for `F n` feedback channels.
Requires wrapping/unwrapping at use sites.

#### Option 3: Keep traceMat explicit (current approach)
`traceMat` is a standalone function with `Finite` constraints.
No `Traced` instance. Works today, zero friction.

### Recommendation
**Option 2 (wrapper type)** is most compatible. Add a `KnownNat`-backed `Finite`
instance for a wrapper around harpie's `Fin`. This lets `traceMat` work for
both `Enum`/`Bounded` types and `Fin n` without changing the `Traced` class.

For the `Traced` instance itself: wait until circuits upstream considers a
`TracedK` variant or until the parametric-vs-enumeration tension is resolved
differently (e.g., via type-level finite sets in GHC).

## 4. Verified trace laws (docspec)

All three trace laws verified via docspec (0 errors):
- **Naturality**: `traceMat (Comp (Par Id g) f) = Comp g (traceMat f)`
- **Sliding**: `traceMat (Comp (Par g Swap) f) = traceMat (Comp f (Par g Swap))`
- **Vanishing**: `traceMat block = expected` (Schur-complement over unit channel)
