# Countably generated submodules over Noetherian rings

Import `ProjectiveModules.Module.CountablyGenerated.Noetherian` for the focused
public theorem, or `ProjectiveModules` for the production aggregate:

```lean
Module.CountablyGenerated.submodule_of_isNoetherianRing
    (hM : Module.CountablyGenerated R M) (N : Submodule R M) :
    Module.CountablyGenerated R N
```

The hypotheses are `[Ring R]`, `[IsNoetherianRing R]`, `[AddCommGroup M]` and
`[Module R M]`. The ring may be noncommutative, and neither `M` nor `N` needs
an ambient Noetherian-module instance. The local
`ProjectiveModules.Module.CountablyGenerated` predicate says that a sequence
`x : ℕ → M` has range spanning `M`; it does not require a countable underlying
carrier. There is no finite-generation, PID, basis, freeness, projectivity or
splitting hypothesis.

For an infinite free module over the integers, add the two instance imports:

```lean
import ProjectiveModules.Module.CountablyGenerated.Noetherian
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

example (N : Submodule ℤ (ℕ →₀ ℤ)) :
    Module.CountablyGenerated ℤ N :=
  Module.CountablyGenerated.submodule_of_isNoetherianRing
    (Module.CountablyGenerated.finsupp (R := ℤ) ℕ) N
```

The ordinary aggregate-import client `tests/PublicAPIClient.lean` also checks
this arbitrary-submodule expression and its zero-submodule specialization as
private regression theorems.

## Proof and dependencies

Choose a sequence generating `M`. The first `n + 1` terms span an increasing
family of finitely generated submodules exhausting `M`. Mathlib's
`Submodule.FG.of_le` over the left-Noetherian ring makes each intersection
with `N` finitely generated. Lift the finite generating families into `N`.
Their dependent union is countable; adjoining zero makes it nonempty and
enumerable by a sequence. Each element of `N` belongs to some stage, hence
to the span of this sequence. The proof assumes no Noetherian instance for
the entire ambient module.

The producer directly imports the local countable-generation predicate and
`Mathlib.RingTheory.Noetherian.Basic`. This project pins Lean
`leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, alongside exact official
General Linear Groups and Stable Range dependencies in `lake-manifest.json`.
To check a fresh checkout, fetch the matching mathlib cache before building
the existing default production and ordinary-client targets:

```sh
lake exe cache get
lake --wfail -KwarningAsError=true build
```

**Transfer-author checkpoint (2026-09-29):** this is source-authored
documentation adapted for a candidate destination import graph, not native
generated API output. The original producer was registered and reviewed in
the shared project before transfer. This destination transfer has not yet
received its own changed-input build, transitive axiom audit, independent
review, owner acceptance, integration or official publication; no
source-specific coverage is inferred from this library theorem.
