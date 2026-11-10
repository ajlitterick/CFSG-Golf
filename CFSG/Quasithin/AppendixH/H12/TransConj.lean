module

public import CFSG.Quasithin.AppendixH.H12.TransModule

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH


namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

@[expose] def conj (c : ↥L') : Trans L' L ρ' ρ where
  φ := (MulAut.conj c).trans τ.φ
  β := (ρ' (c : Γ)).trans τ.β
  compat g v := by
    simp only [MulEquiv.trans_apply]
    rw [τ.compat ((MulAut.conj c) g) (ρ' (c : Γ) v)]
    congr 1
    simp [MulAut.conj_apply, map_mul]

@[simp] private theorem conj_φ_apply (c : ↥L') (g : ↥L') :
    (τ.conj c).φ g = τ.φ ((MulAut.conj c) g) := rfl

@[simp] private theorem conj_β_apply (c : ↥L') (v : V') :
    (τ.conj c).β v = τ.β (ρ' (c : Γ) v) := rfl

@[simp] private theorem conj_β_symm_apply (c : ↥L') (x : V) :
    ((τ.conj c).β).symm x = (ρ' (c : Γ))⁻¹ (τ.β.symm x) := by
  apply ((τ.conj c).β).injective
  rw [MulEquiv.apply_symm_apply, conj_β_apply]
  simp


end Trans

end CFSG.Quasithin.AppendixH.H12