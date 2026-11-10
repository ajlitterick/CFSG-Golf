module

public import CFSG.Sporadic.Schreier.RuSylowB
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_ruRS :
    Nat.card ruRS = 2048 := by
  rw [card_subgroupOf_of_le ruR_leS, card_ruR]

theorem card_ruQ :
    Nat.card RuQ = 8 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ruRS
  rw [card_ruS, card_ruRS] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2048) (h.symm.trans (by norm_num)))

theorem ruQ_isMulCommutative :
    IsMulCommutative RuQ := ⟨⟨ruQ_comm⟩⟩

instance ruQ_elem :
    CFSG.IsElementaryAbelian 2 RuQ :=
  { toIsMulCommutative := ruQ_isMulCommutative
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ruQ_sq }

theorem isPGroup_ruS :
    IsPGroup 2 ruS := IsPGroup.of_card (n := 14) (by rw [card_ruS]; norm_num)


theorem ruZ_memS :
    ruZ ∈ ruS := ruJ_leS ruZ_memJ

theorem ruChainS_center
    {g : Equiv.Perm (Fin 1920)} (hg : g ∈ ruChainS.originalSubgroup)
    (hc : ∀ j < 4, g * ruResFPerm (ruSGens.getD j 1) = ruResFPerm (ruSGens.getD j 1) * g) :
    g = 1 ∨ g = ruResFPerm ruZ := by
  have h := ruChainS_check.1
  have hb : ruChainS.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => (∀ j < 4, g * ruResFPerm (ruSGens.getD j 1) =
      ruResFPerm (ruSGens.getD j 1) * g) → g = 1 ∨ g = ruResFPerm ruZ)
    (fun t g ht hp hcomm => by
      have hcs : ruCommutesS t = true := by
        rw [ruCommutesS, allLt_iff]
        intro j hj
        exact (eqA_iff (rep_compA ht (rep_ruSF hj)) (rep_compA (rep_ruSF hj) ht)).2 (hcomm j hj)
      simp only [hcs, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact Or.inl ((eqA_iff ht rep_idA).1 hp)
      · exact Or.inr ((eqA_iff ht (rep_ruResF rep_ruZ ruZ_memC)).1 hp))
    ruSylow_check.2.2.2.2.2 g hg
  exact key hc

theorem center_ruS :
    (Subgroup.center ruS).map ruS.subtype = Subgroup.zpowers ruZ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxC : (x : Equiv.Perm (Fin 4060)) ∈ ruC := ruS_leC x.2
    have hmem : ruResFPerm x ∈ ruChainS.originalSubgroup := by
      rw [ruChainS_sub]
      exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 x.2, (ruResFPerm_of_mem hxC).symm⟩
    have hcomm : ∀ j < 4, ruResFPerm x * ruResFPerm (ruSGens.getD j 1) =
        ruResFPerm (ruSGens.getD j 1) * ruResFPerm x := by
      intro j hj
      have hxj := Subgroup.mem_center_iff.1 hx (ruSGenS j)
      have e : (x : Equiv.Perm (Fin 4060)) * ruSGens.getD j 1 = ruSGens.getD j 1 * x :=
        congrArg Subtype.val hxj.symm
      rw [← ruResFPerm_mul hxC (ruSGens_memC' j), ← ruResFPerm_mul (ruSGens_memC' j) hxC, e]
    rcases ruChainS_center hmem hcomm with h | h
    · have : (x : Equiv.Perm (Fin 4060)) = 1 := by
        apply congrArg Subtype.val (ruResF_injective (a₁ := ⟨x, hxC⟩) (a₂ := 1) _)
        rw [← ruResFPerm_of_mem hxC, h, map_one]
      rw [Subgroup.coe_subtype, this]
      exact Subgroup.one_mem _
    · have : (x : Equiv.Perm (Fin 4060)) = ruZ := by
        apply congrArg Subtype.val (ruResF_injective (a₁ := ⟨x, hxC⟩) (a₂ := ⟨ruZ, ruZ_memC⟩) _)
        rw [← ruResFPerm_of_mem hxC, h, ruResFPerm_of_mem]
      rw [Subgroup.coe_subtype, this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨ruZ, ruZ_memS⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact ruZ_central g (ruS_leC g.2)

@[expose] def ruResYS :
    ruS →* Equiv.Perm (Fin 80) := ruResY.comp (Subgroup.inclusion ruS_leC)


theorem ruResYS_ker :
    ruResYS.ker = (Subgroup.zpowers ruZ).subgroupOf ruS := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ruResYS, MonoidHom.comp_apply,
    ← MonoidHom.mem_ker, ruResY_ker]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

instance ruZS_normal :
    ((Subgroup.zpowers ruZ).subgroupOf ruS).Normal := by
  rw [← ruResYS_ker]
  infer_instance


end CFSG.Sporadic.RuSchreier
