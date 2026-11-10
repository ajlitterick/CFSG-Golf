module

public import CFSG.GH74.QTGen4.U42.MSplitGenC
public import CFSG.GH74.QTGen4.U42.MSplitGenE

public section

namespace CFSG.GH74.QTGen4.U42

variable {G : Type} [Group G]

theorem exists_complement_of_conj {M L V A : Subgroup G}
    (hVL : V ≤ L) (hLM : L ≤ M)
    (hVn : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (hA : A ≤ L) (hAV : A ⊓ V = ⊥)
    (hconj : ∀ g ∈ M, ∃ w ∈ V, ∀ x : G, x ∈ A ↔ w⁻¹ * (g * x * g⁻¹) * w ∈ A)
    (hfix : ∀ v ∈ V, (∀ a ∈ A, v * a = a * v) → v = 1) :
    ∃ C : Subgroup G, C ≤ M ∧ C ⊓ V = ⊥ ∧ V ⊔ C = M := by
  have hVM : V ≤ M := hVL.trans hLM
  have hAM : A ≤ M := hA.trans hLM
  refine ⟨Subgroup.normalizer (A : Set G) ⊓ M, inf_le_right, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_bot]
    apply hfix x hxV
    intro a ha
    have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
    have h3 : x * a * x⁻¹ * a⁻¹ ∈ V := by
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact V.mul_mem hxV (hVn a (hAM ha) x⁻¹ (V.inv_mem hxV))
    have h4 : x * a * x⁻¹ * a⁻¹ = 1 := by
      have hbot : x * a * x⁻¹ * a⁻¹ ∈ A ⊓ V := Subgroup.mem_inf.mpr ⟨h2, h3⟩
      rw [hAV, Subgroup.mem_bot] at hbot
      exact hbot
    have h5 : x * a * x⁻¹ = a := mul_inv_eq_one.mp h4
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [h5]
  ·
    apply le_antisymm
    · exact sup_le hVM inf_le_right
    · intro g hg
      obtain ⟨w, hw, hwg⟩ := hconj g hg
      have hwM : w ∈ M := hVM hw
      have hnM : w⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hwM) hg
      have hnN : w⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have e : w⁻¹ * g * x * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * x * g⁻¹) * w := by group
        rw [e]
        exact hwg x
      have hn : w⁻¹ * g ∈ Subgroup.normalizer (A : Set G) ⊓ M :=
        Subgroup.mem_inf.mpr ⟨hnN, hnM⟩
      have hsplit : g = w * (w⁻¹ * g) := by group
      rw [hsplit]
      exact (V ⊔ (Subgroup.normalizer (A : Set G) ⊓ M)).mul_mem
        (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hn)


open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

namespace Setting


end Setting

end CFSG.GH74.QTGen4.U42

end
