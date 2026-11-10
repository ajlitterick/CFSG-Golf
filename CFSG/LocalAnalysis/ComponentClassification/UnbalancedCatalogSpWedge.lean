module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix

namespace SpChain

variable {K : Type} [Field K]

variable (K) in
abbrev wedgeSpace : Type := ⋀[K]^2 (Fin 4 → K)

abbrev stdVec (i : Fin 4) : Fin 4 → K := Pi.single i 1


@[expose] def wedgeAct (g : Matrix (Fin 4) (Fin 4) K) : wedgeSpace K →ₗ[K] wedgeSpace K :=
  exteriorPower.map 2 (Matrix.toLin' g)


end SpChain

open SpChain


end CFSG.ComponentClassification.UnbalancedCatalog
