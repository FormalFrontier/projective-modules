# Matrix rings and right-module K₀

## Additive equivalences

Let `R : Type u` be a ring and `ι : Type v` a finite nonempty type.
Import [`ProjectiveModules.KTheory.Matrix`](../ProjectiveModules/KTheory/Matrix.lean),
also exported by `ProjectiveModules`, to use the additive equivalences

```lean
KTheory.ProjectiveClass.matrixEquiv R ι :
  KTheory.ProjectiveClass R ≃+ KTheory.ProjectiveClass (Matrix ι ι R)
KTheory.K0.matrixEquiv R ι :
  KTheory.K0 R ≃+ KTheory.K0 (Matrix ι ι R)
```

Here classes are isomorphism classes of finitely generated projective **right**
modules, addition is direct sum, and K₀ is their additive group completion.
These are not ring equivalences. No commutativity, nontriviality, division-ring,
Noetherian, freeness, invariant-basis-number or cancellation hypothesis is used.
The concrete matrix operations use `[Fintype ι] [DecidableEq ι]`.
`[Nonempty ι]` supplies a coordinate for an inverse equivalence.

## Construction and orientation

For a coordinate `i : ι`, use Mathlib's ordinary category equivalence

```text
ModuleCat Rᵐᵒᵖ
  -- matrixEquivalence Rᵐᵒᵖ i --> ModuleCat (Matrix ι ι Rᵐᵒᵖ)
  -- restrictScalarsEquivalenceOfRingEquiv mopMatrix.symm -->
ModuleCat (Matrix ι ι R)ᵐᵒᵖ.
```

The transpose-and-opposite ring equivalence has direction

```lean
RingEquiv.mopMatrix :
  Matrix ι ι Rᵐᵒᵖ ≃+* (Matrix ι ι R)ᵐᵒᵖ
```

Restriction of scalars reverses the direction of a ring map. Consequently the
second category equivalence must use `mopMatrix.symm`, not `mopMatrix`.
These are categories of modules over **opposite rings**, not opposite categories.
No auxiliary commutative base algebra or linearity hypothesis is required.

The `equivOfModuleEquivalence` interfaces apply to this composite.
The definitions choose `Classical.arbitrary ι` at common carrier height
`H₀ = max u v`. For any universe `w`, put `H = max (max u v) w`.
In both namespaces, `matrixEquiv_eq_of_index` identifies the whole equivalence
with the same construction for **every** `i : ι` at height `H`. Thus canonical
includes coordinate independence and independence of the supported carrier
lift, with the `Fintype` and `DecidableEq` instances fixed. It does not assert
independence of arbitrary choices of those instances or definitional equality
of Mathlib's inverse functors. The forward matrix functor
`ModuleCat.toMatrixModCat Rᵐᵒᵖ ι` contains no chosen coordinate; only the inverse
chooses a corner.

## Direct rows in arbitrary carrier universes

For `M : Type w` with an additive commutative group and an `Rᵐᵒᵖ`-module
structure, `ModuleCat.toRightMatrixModCat R ι` composes Mathlib's
`toMatrixModCat` with restriction along `mopMatrix.symm.toRingHom`.
Its carrier is `ι → M`, in `Type (max v w)`, with action

```text
(op A • x) j = ∑ k, op (A k j) • x k.
```

In particular, for the ordinary right regular carrier `M = R`, this is
`(x * A) j = ∑ k, x k * A k j`; it is not left column multiplication.
The functor sends a linear map `f` to coordinatewise application:
`(F.map f x) j = f (x j)`. The functor structure supplies identity and
composition laws.

`ModuleCat.isFiniteProjective_toRightMatrixModCat_obj` preserves finite
projectivity for these direct rows with **no** carrier bound or `Small` premise.
It also allows an empty index.
For a finite projective right module `M`, the class and K₀ generator equations
are exactly

```text
matrixEquiv [M] = [F(M)],
```

where `F(M)` is this direct row. Both namespaces expose this equation as
`matrixEquiv_of_module`, with finite/projective evidence passed explicitly for
the row image.

The generic class construction first uses `ModuleCat.FiniteProjective.repr`
to take a ring-universe representative, then a supported `ULift`, then the
functor. An arbitrary `M : Type w` need not itself be a categorical object at
height `H`.
Comparing `F(ULift M)` with `F(M)` through the coordinatewise linear
equivalence, and using the representative equivalence, gives the direct-row
comparison. For empty `ι`,
the direct row is the zero module. The forward row functor itself therefore
does not need the nonempty hypothesis needed by the equivalences.

## Inverse generators and the regular matrix module

For a finite projective matrix module `N` at common supported height
`H = max (max u v) w`, `matrixEquiv_symm_of` in each namespace gives inverse
transport as the class, or K₀ generator, of the same composite's inverse image.
Its underlying corner is the range of the operator

```text
n ↦ op (Eᵢᵢ) • n.
```

The resulting `Rᵐᵒᵖ` action is the scalar-diagonal restriction already used by
Mathlib. This supported corner equation is the inverse generator interface;
it does not assume that arbitrary input carriers already have the supported
height. For an arbitrary carrier, first use its ring-universe representative
and a supported `ULift` before applying the inverse functor.

For the ordinary right regular matrix carrier, the operator is `A ↦ A * Eᵢᵢ`.
Its range consists of matrices supported in column `i`, and extracting that
column gives an `Rᵐᵒᵖ`-linear equivalence with `ι → R`. Its inverse sends `x`
to the matrix whose `(j,k)` entry is `if k = i then x j else 0`.
The target `ι → R` has the ordinary pointwise right-regular `Rᵐᵒᵖ` action.
Hence `matrixEquiv_symm_regular` in each namespace gives

```text
matrixEquiv.symm [Matrix ι ι R] = [ι → R]
```

in both the class monoid and K₀. This is a one-sided column module, not the
two-sided corner ring `eAe`; in general its class is **not** `[R]`.
No injectivity of the class-to-K₀ map, finite-projective cancellation or
invariant basis number is used in these equations.

## Completion and elementary boundaries

`KTheory.K0.matrixEquiv_comp_ofClass` is an equality of whole additive homomorphisms:

```text
K0.matrixEquiv.toAddMonoidHom.comp (K0.ofClass R)
  = (K0.ofClass (Matrix ι ι R)).comp
      ProjectiveClass.matrixEquiv.toAddMonoidHom.
```

The `AddEquiv` API supplies inverse, sum, zero and round-trip operations.

For `ι = Fin 2` and `R = ℚ`, the regular rational generator goes to the
right row. The inverse regular matrix generator is the two-coordinate
rational module, not the one-coordinate regular rational module. Extracting
the first column identifies the corner with that coordinate module.
For `Fin 1`, the inverse regular generator is the regular scalar generator.
For an empty index, the matrix ring is a zero ring; it is not Morita equivalent
to a nonzero scalar ring by this construction. Over a zero scalar ring the
class monoid and K₀ are trivial, while the nonempty-index construction still
makes sense. None of these boundaries promotes a matrix ring to a division ring.

## References

* Mathlib, `Mathlib/RingTheory/Morita/Matrix.lean`, by Yunzhou Xie and
  Jujian Zhang: the matrix module-category equivalence and corner inverse.
* Mathlib, `Mathlib/RingTheory/Morita/Basic.lean`,
  `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`,
  `Mathlib/LinearAlgebra/Matrix/Module.lean` and
  `Mathlib/Data/Matrix/Basic.lean`: the surrounding equivalence, restriction,
  matrix action and transpose/opposite interfaces.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II: finite-projective right modules, direct-sum classes and K₀.
* Projective Modules, `KTheory/ModuleEquivalence.lean`: independent-universe
  class transport and its group-completion extension.

Mathematical credit is separate from the licenses of the Lean expressions;
see the [library license and credit](../README.md#license-and-credit).
