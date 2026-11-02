module

import ProjectiveModules.Module.Koszul.HomogeneousContraction

noncomputable section

open CategoryTheory

universe u v

example (S : Type u) [CommRing S] (P : Type v) [AddCommGroup P] [Module S P]
    (n : ℕ) : ChainComplex (ModuleCat.{max u v} S) ℕ :=
  Module.Koszul.homogeneousComplex S P n

example (S : Type u) [CommRing S] (m i d : ℕ) :
    Module.Koszul.Term S (Fin m → S) i (d + 1) →ₗ[S]
      Module.Koszul.Term S (Fin m → S) (i + 1) d :=
  Module.Koszul.CanonicalFreeContraction.kappa S m i d

example (S : Type u) [CommRing S] (P : Type v) [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P] (n i : ℕ) :
    (Module.Koszul.homogeneousComplex S P n).X i ⟶
      (Module.Koszul.homogeneousComplex S P n).X (i + 1) :=
  Module.Koszul.homogeneousContraction S P n i
