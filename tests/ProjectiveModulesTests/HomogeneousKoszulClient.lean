module

import ProjectiveModules.Module.Koszul.Homogeneous

noncomputable section

universe u v

example (S : Type u) [CommRing S] (P : Type v) [AddCommGroup P] [Module S P]
    (n : ℕ) : ChainComplex (ModuleCat.{max u v} S) ℕ :=
  Module.Koszul.homogeneousComplex S P n

