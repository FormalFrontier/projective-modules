/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.RankLocallyConstantRing

/-! # Locally constant class rank on arbitrary-universe right modules -/

public section

universe uR uM

namespace KTheory.ProjectiveClass

example (R : Type uR) [CommRing R]
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    rankLocallyConstantRingHom R (of R M) =
      LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ M) := by
  simp

end KTheory.ProjectiveClass
