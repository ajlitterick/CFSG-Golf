
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final3Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathLift
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Fin76bNotZ2A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ y ∈ normalizer (E : Set G), y * β = β * y → y * z * y⁻¹ = z * t →
      y * t * y⁻¹ = t →
    ¬ Nonempty (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 6))

end CFSG.EvenSporadicStandard.Fin76b
