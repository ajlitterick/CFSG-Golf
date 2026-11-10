module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open

theorem mem_conjSubg_iff {X : Type*} [Group X] (g : X) (A : Subgroup X) (x : X) :
    x ∈ conjSubg g A ↔ g⁻¹ * x * g ∈ A := by
  rw [conjSubg, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [← hax]
    change g⁻¹ * ((MulAut.conj g) a) * g ∈ A
    rw [MulAut.conj_apply]
    convert ha using 1
    group
  · intro h
    exact ⟨g⁻¹ * x * g, h, by
      change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group⟩


theorem pCoreOf_conjSubg (p : ℕ) {X : Type*} [Group X] (g : X) (H : Subgroup X) :
    pCoreOf p (conjSubg g H) = conjSubg g (pCoreOf p H) := by
  let φ : ↥H ≃* ↥(conjSubg g H) := MulEquiv.subgroupMap (MulAut.conj g) H
  calc pCoreOf p (conjSubg g H)
      = (pCore p ↥(conjSubg g H)).map (conjSubg g H).subtype := rfl
    _ = ((pCore p ↥H).map φ.toMonoidHom).map (conjSubg g H).subtype := by
          rw [← CFSG.pCore_map_iso p φ]
    _ = (pCore p ↥H).map ((conjSubg g H).subtype.comp φ.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (pCore p ↥H).map ((MulAut.conj g).toMonoidHom.comp H.subtype) := rfl
    _ = ((pCore p ↥H).map H.subtype).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = conjSubg g (pCoreOf p H) := rfl


theorem MY_smul_of_mem {α : Type*} [MulAction S24 α] {Γ : Subgroup S24} {τ : S24} (hτ : τ ∈ Γ)
    (Y : α) : MY Γ (τ • Y) = conjSubg τ (MY Γ Y) := by
  have hΓ : conjSubg τ Γ = Γ := by
    ext x
    rw [mem_conjSubg_iff]
    constructor
    · intro hx
      have h2 : τ * (τ⁻¹ * x * τ) * τ⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hτ hx) (Γ.inv_mem hτ)
      convert h2 using 1
      group
    · intro hx
      exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hτ) hx) hτ
  have hΓ' : Subgroup.map (MulAut.conj τ).toMonoidHom Γ = Γ := by
    simpa only [conjSubg] using hΓ
  unfold MY
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, conjSubg]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj τ).injective, hΓ']


end CFSG.ASVolI.H16
