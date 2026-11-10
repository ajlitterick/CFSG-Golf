module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelShapeE
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_inner_conj_mem_diag_e6
    {F : Type} [Field F] [Finite F] [CharP F 2] (h3 : 3 ∣ Nat.card F - 1)
    {E : Subgroup (MulAut ↥(adjointGroup .E6 F))} (hE𝒟 : E ≤ LayerSixE.inndiagAut .E6 F)
    (hE : IsElemAbelian 3 E) (h5 : 3 ^ 5 ≤ Nat.card E) :
    ∃ g : ↥(adjointGroup .E6 F), ∀ x ∈ E,
      MulAut.conj g * x * (MulAut.conj g)⁻¹ ∈ (rootDiagAutHom .E6 F).range := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hEH : E ≤ (E6ThreeModel.eFrame F ζ hζ).H :=
    hE𝒟.trans (le_of_eq NoOffE6Three.hatAut_range_eq_sup.symm)
  obtain ⟨γ, hγ, hγE⟩ := E6ThreeModel.eFrame_shape hζo hζ E hEH hE h5
  obtain ⟨g, hg⟩ := OutdiagE6.exists_inner_conj_map_le le_rfl hγ (by
    rintro _ ⟨x, hx, rfl⟩
    exact OutdiagE6.vAd_le_diag ζ hζ (hγE x hx))
  exact ⟨g, fun x hx => hg ⟨x, hx, rfl⟩⟩

end CFSG.StandardType

end
