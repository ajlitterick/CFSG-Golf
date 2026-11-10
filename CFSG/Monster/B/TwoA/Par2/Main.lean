
module

public import CFSG.Monster.B.TwoA.Par2.MainBase

public import CFSG.Monster.B.TwoA.Unitary.LinThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Classical.ThreePlane CFSG.Monster.B.TwoA.Unitary.LinThree

attribute [local instance] restAction

attribute [local instance] nativeAction

theorem pCore_SigmaL3 :
    CFSG.pCore 2 SigmaL3 = ⊥ := by
  rw [← CFSG.pCore_map_iso 2 psi, pCore_P₂, Subgroup.map_bot]

@[expose] def bigPhi :
    H2 →* Equiv.Perm (Fin 3) × SigmaL3 :=
  ((MonoidHom.snd _ _).comp phiH).prod (psi.toMonoidHom.comp psiH)

theorem bigPhi_surjective :
    Function.Surjective bigPhi := by
  rintro ⟨σ, s⟩
  set p : P₂ := psi.symm s
  have hp : (⟨p, P₂_le_AutPerm p.2⟩ : AutPerm) ∈ Unitary.P2 := (mem_P₂_iff _).1 p.2
  set q : Ppair := ⟨⟨p, P₂_le_AutPerm p.2⟩, (Unitary.mem_P2.1 hp).1⟩
  obtain ⟨n, hn⟩ := mkK_surjective (twoCoreEquiv.symm (q, σ))
  have hnq : twoCoreEquiv (mkK n) = (q, σ) := by rw [hn, MulEquiv.apply_symm_apply]
  have hb : blockP n = q := congrArg Prod.fst hnq
  have hq2 : q • rest2 = rest2 := Subtype.ext (Unitary.mem_P2.1 hp).2
  have hx : (n : Dfull) * cQ * (n : Dfull)⁻¹ ∈ blk rest2 := by
    have := conj_blk_Ntwo n cQ_mem_blk
    rwa [hb, hq2] at this
  obtain ⟨r, hr, hrc⟩ := blk_R2_transitive rest2 hx cQ_mem_blk
  have hm : r * n ∈ H2 := by
    refine ⟨Ntwo.mul_mem (R2_le_Ntwo hr) n.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← mul_inv_eq_iff_eq_mul]
    calc r * (n : Dfull) * cQ * (r * n)⁻¹ = r * ((n : Dfull) * cQ * (n : Dfull)⁻¹) * r⁻¹ := by
          group
      _ = cQ := hrc
  have hmk : mkK (inclH ⟨_, hm⟩) = mkK n := by
    have e : inclH ⟨_, hm⟩ = ⟨r, R2_le_Ntwo hr⟩ * n := rfl
    rw [e, map_mul, show mkK ⟨r, R2_le_Ntwo hr⟩ = 1 from (QuotientGroup.eq_one_iff _).2 hr,
      one_mul]
  have hφ : phiH ⟨_, hm⟩ = (q, σ) := by
    rw [phiH_apply]
    change twoCoreEquiv (mkK (inclH ⟨_, hm⟩)) = _
    rw [hmk, hnq]
  refine ⟨⟨_, hm⟩, Prod.ext ?_ ?_⟩
  · change (phiH ⟨_, hm⟩).2 = σ
    rw [hφ]
  · change psi (psiH ⟨_, hm⟩) = s
    have e : psiH ⟨_, hm⟩ = p := by
      apply Subtype.ext
      rw [coe_psiH, hφ]
    rw [e, MulEquiv.apply_symm_apply]

theorem bigPhi_eq_one_iff
    (h : H2) : bigPhi h = 1 ↔ (h : Dfull) ∈ R2 := by
  constructor
  · intro h1
    have h2 : (phiH h).2 = 1 := congrArg Prod.fst h1
    have h3 : psi (psiH h) = 1 := congrArg Prod.snd h1
    have h4 : psiH h = 1 := by rwa [MulEquiv.map_eq_one_iff] at h3
    have h5 : (phiH h).1 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val h4
      rw [coe_psiH] at this
      exact this
    have h6 : phiH h = 1 := Prod.ext h5 h2
    rw [phiH_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h6
    exact h6
  · intro hr
    have h6 : phiH h = 1 := by
      rw [phiH_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact hr
    refine Prod.ext ?_ ?_
    · change (phiH h).2 = 1
      rw [h6]
      rfl
    · change psi (psiH h) = 1
      have e : psiH h = 1 := by
        apply Subtype.ext
        rw [coe_psiH, h6]
        rfl
      rw [e, map_one]

theorem ker_bigPhi :

    bigPhi.ker = (R2 ⊓ Subgroup.centralizer {cQ}).subgroupOf H2 := by
  ext h
  rw [MonoidHom.mem_ker, bigPhi_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hr => ⟨hr, (Subgroup.mem_inf.1 h.2).2⟩, fun hr => hr.1⟩

theorem natCard_ker_bigPhi :
    Nat.card bigPhi.ker = 2 ^ 30 := by
  rw [ker_bigPhi, Nat.card_congr (Subgroup.subgroupOfEquivOfLe R2_inf_le_H2).toEquiv,
    natCard_R2c]

theorem ker_bigPhi_eq_pCore :
    bigPhi.ker = CFSG.pCore 2 H2 :=
  ker_eq_pCore_of_surjective bigPhi_surjective (IsPGroup.of_card natCard_ker_bigPhi)
    (pCore_prod_eq_bot pCore_perm_three pCore_SigmaL3)

theorem map_pCore_H2 :

    (CFSG.pCore 2 H2).map H2.subtype = R2 ⊓ Subgroup.centralizer {cQ} := by
  rw [← ker_bigPhi_eq_pCore, ker_bigPhi, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 R2_inf_le_H2]


end CFSG.Monster.B.TwoA.Par2
