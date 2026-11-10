
module

public import CFSG.Monster.B.Fischer.Fi22CoverBase1

public import CFSG.Monster.B.Fischer.Fi22CoverCheck

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native


theorem fi22OuterT_involution_conj :
    ∀ g ∈ fi22OuterT, orderOf g = 2 →
    ∃ j < 54, ∃ t ∈ fi22OuterT, t * fi22OuterU j * t⁻¹ = g := by
  intro g hg ho
  obtain ⟨x, rfl⟩ := fi22TProd_surj hg
  obtain ⟨hj, ha, hb, hc, hok⟩ := fi22Cover_check.2.2.2.2.1 x ((isInv3_iff x).2 ho)
  set w := fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!
  refine ⟨w.1, hj, fi22TProd (⟨w.2.1, ha⟩, ⟨w.2.2.1, hb⟩, ⟨w.2.2.2, hc⟩), fi22TProd_mem _, ?_⟩
  exact conjOK3_spec (rep_fi22OuterU hj) hok

theorem fi22OuterU_spec
    {j : ℕ} (hj : j < 54) :
    fi22OuterU j ∈ fi22OuterT ∧ orderOf (fi22OuterU j) = 2 ∧ fi22OuterH j ∈ fi22P ∧
      ∃ i < 3, fi22OuterH j * fi22OuterU j * (fi22OuterH j)⁻¹ = fi22OuterXRep i := by
  obtain ⟨hs, h1, h2, hh, i, hi, hc⟩ := fi22Cover_check.2.2.2.2.2.1 j hj
  refine ⟨(siftA_iff_mem_originalSubgroup fi22OuterChainT_arrays (by norm_num)
      fi22Local_check.2.2.1 (rep_fi22OuterU hj)).1 hs,
    orderOf_eq_two_of_eqA (rep_fi22OuterU hj) h1 h2, mem_fi22P_of_siftA (rep_fi22OuterH hj) hh,
    i, hi, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_of_eqA (rep_compA (rep_fi22OuterH hj) (rep_fi22OuterU hj))
    (rep_compA (rep_fi22OuterXRep hi) (rep_fi22OuterH hj)) hc

theorem fi22OuterXRep_spec
    {i : ℕ} (hi : i < 3) :
    fi22OuterXRep i ∈ fi22P ∧ orderOf (fi22OuterXRep i) = 2 := by
  obtain ⟨hs, h1, h2⟩ := fi22Cover_check.2.2.2.2.2.2.1 i hi
  exact ⟨mem_fi22P_of_siftA (rep_fi22OuterXRep hi) hs,
    orderOf_eq_two_of_eqA (rep_fi22OuterXRep hi) h1 h2⟩

theorem fi22OuterXRep_two :
    fi22OuterXRep 2 = fi22OuterZ :=
  eq_of_eqA (rep_fi22OuterXRep (by norm_num)) rep_fi22OuterZ
    fi22Cover_check.2.2.2.2.2.2.2.2.2.2

theorem fi22P_involution_conj :
    ∀ g ∈ fi22P, orderOf g = 2 →
    ∃ k ∈ fi22P, k * g * k⁻¹ = fi22OuterXRep 0 ∨ k * g * k⁻¹ = fi22OuterXRep 1 ∨
      k * g * k⁻¹ = fi22OuterZ := by
  intro g hg ho
  set gP : fi22P := ⟨g, hg⟩
  have hoP : orderOf gP = 2 := by rw [Subgroup.orderOf_mk, ho]
  have hp : IsPGroup 2 (Subgroup.zpowers gP) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoP, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨S, hS⟩ := fi22OuterT_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq fi22P Q S
  have hmem : MulAut.conj h • gP ∈ ((h • Q : Sylow 2 fi22P) : Subgroup fi22P) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers gP))
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  have hconj : ((MulAut.conj h • gP : fi22P) : Equiv.Perm (Fin 3510)) =
      (h : Equiv.Perm (Fin 3510)) * g * (h : Equiv.Perm (Fin 3510))⁻¹ := rfl
  rw [hconj] at hmem
  have ho' : orderOf ((h : Equiv.Perm (Fin 3510)) * g * (h : Equiv.Perm (Fin 3510))⁻¹) = 2 := by
    rw [← ho]
    exact MulEquiv.orderOf_eq (MulAut.conj (h : Equiv.Perm (Fin 3510))) g
  obtain ⟨j, hj, t, ht, htg⟩ := fi22OuterT_involution_conj _ hmem ho'
  obtain ⟨-, -, hhj, i, hi, hx⟩ := fi22OuterU_spec hj
  refine ⟨fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510)), Subgroup.mul_mem _
    (Subgroup.mul_mem _ hhj (Subgroup.inv_mem _ (fi22OuterT_le ht))) h.2, ?_⟩
  have hg' : g = (h : Equiv.Perm (Fin 3510))⁻¹ * (t * fi22OuterU j * t⁻¹) *
      (h : Equiv.Perm (Fin 3510)) := by
    rw [htg]
    group
  have key : (fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510))) * g *
      (fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510)))⁻¹ = fi22OuterXRep i := by
    rw [hg', ← hx]
    group
  rw [key]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr fi22OuterXRep_two)


end CFSG.Monster.B.Fischer
