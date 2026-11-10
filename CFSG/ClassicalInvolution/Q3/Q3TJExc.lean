module

public import CFSG.ClassicalInvolution.Q3.Q3TJExcCore
public import CFSG.ClassicalInvolution.Q3.Q3TJMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification

variable {X : Type} [Group X]

theorem nonempty_mulEquiv_of_central {K C : Type*} [Group K] [Group C] (f : K →* X)
    (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center K)
    (hZX : Subgroup.center X = ⊥) (π : K →* C) (hπ : Function.Surjective π)
    (hπk : π.ker ≤ Subgroup.center K) (hZC : Subgroup.center C = ⊥) : Nonempty (X ≃* C) := by
  have hk : f.ker = π.ker := le_antisymm
    (hfk.trans (ModelFacts.ChevAut.center_le_ker_of_surjective hπ hZC))
    (hπk.trans (ModelFacts.ChevAut.center_le_ker_of_surjective hf hZX))
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ))⟩

theorem natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem ker_id_le_center (G : Type*) [Group G] :
    (MonoidHom.id G).ker ≤ Subgroup.center G := fun x hx => by
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem exists_eq_conj_E6 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .E6 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .E6 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 3 1))
    (LieType.Steinberg.Isogeny.e6Isogeny_surjective _)
    (ModelFacts.ChevAut.e6Isogeny_ker_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_adjoint_E (Or.inl rfl) _ natCard_galoisField_three β hβ) α hodd

theorem exists_eq_conj_E7 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 3 1))
    (LieType.Steinberg.Isogeny.e7Isogeny_surjective _)
    (ModelFacts.ChevAut.e7Isogeny_ker_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_adjoint_E (Or.inr (Or.inl rfl)) _ natCard_galoisField_three β
      hβ) α hodd

theorem exists_eq_conj_E8 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .E8 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .E8 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (MonoidHom.id ↥(adjointGroup Tag.E8 (GaloisField 3 1))) Function.surjective_id
    (ker_id_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_adjoint_E (Or.inr (Or.inr rfl)) _ natCard_galoisField_three β
      hβ) α hodd

theorem exists_eq_conj_F4 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .F4 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .F4 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (MonoidHom.id ↥(adjointGroup Tag.F4 (GaloisField 3 1))) Function.surjective_id
    (ker_id_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β _ => mem_inner_adjoint_F4 _ natCard_galoisField_three β) α hodd


end CFSG.ClassicalInvolution.Q3.Q3T
