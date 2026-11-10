
module

public import CFSG.Monster.B.TwoA.Par2.Blocks

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

attribute [local instance] restAction

@[expose] def Xs : Set Dfull := {d | ∃ j : Rest, d ∈ blk j}

@[expose] def conjClass : Set Dfull := {d | ∃ n ∈ Ntwo, n * cQ * n⁻¹ = d}

theorem conjClass_eq :
    conjClass = Xs := by
  ext d
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨_, conj_blk_Ntwo ⟨n, hn⟩ cQ_mem_blk⟩
  · rintro ⟨j, hj⟩
    obtain ⟨n, hn⟩ := exists_Ntwo_blk j
    rw [← hn, ← image_conj_blk] at hj
    obtain ⟨d₀, hd₀, rfl⟩ := hj
    obtain ⟨r, hr, rfl⟩ := blk_two_orbit hd₀
    exact ⟨(n : Dfull) * r, Ntwo.mul_mem n.2 (R2_le_Ntwo hr), by group⟩


theorem cQ_ne_one :
    cQ ≠ 1 := by
  intro h
  have h1 : psiW ⟨cQ, cQ_mem_Ehat⟩ = psiW 1 := congrArg psiW (Subtype.ext h)
  rw [psiW_cQ, psiW_one] at h1
  exact pW_ne_zero rest2 0 h1

theorem orderOf_cQ :
    orderOf cQ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact dhat0_mul_self rest2) cQ_ne_one

theorem orderOf_of_mem_conjClass
    {d : Dfull} (hd : d ∈ conjClass) : orderOf d = 2 := by
  obtain ⟨n, -, rfl⟩ := hd
  rw [show n * cQ * n⁻¹ = MulAut.conj n cQ from rfl, MulEquiv.orderOf_eq, orderOf_cQ]

@[expose] def H2 : Subgroup Dfull := Ntwo ⊓ Subgroup.centralizer {cQ}

theorem H2_le_Ntwo : H2 ≤ Ntwo := inf_le_left

theorem conj_mem_Xs
    {n : Dfull} (hn : n ∈ Ntwo) {d : Dfull} (hd : d ∈ Xs) : n * d * n⁻¹ ∈ Xs := by
  obtain ⟨j, hj⟩ := hd
  exact ⟨_, conj_blk_Ntwo ⟨n, hn⟩ hj⟩

@[expose, instance_reducible] def xsAction :
    MulAction Ntwo Xs where
  smul n d := ⟨(n : Dfull) * d * (n : Dfull)⁻¹, conj_mem_Xs n.2 d.2⟩
  one_smul d := Subtype.ext (by
    change ((1 : Ntwo) : Dfull) * d * ((1 : Ntwo) : Dfull)⁻¹ = d
    simp)
  mul_smul g h d := Subtype.ext (by
    change ((g * h : Ntwo) : Dfull) * d * ((g * h : Ntwo) : Dfull)⁻¹ =
      (g : Dfull) * ((h : Dfull) * d * (h : Dfull)⁻¹) * (g : Dfull)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

attribute [local instance] xsAction


@[expose, instance_reducible] def seedAction :
    MulAction R2 (blk rest2) where
  smul r d := ⟨(r : Dfull) * d * (r : Dfull)⁻¹, conj_blk_R2 r.2 d.2⟩
  one_smul d := Subtype.ext (by
    change ((1 : R2) : Dfull) * d * ((1 : R2) : Dfull)⁻¹ = d
    simp)
  mul_smul g h d := Subtype.ext (by
    change ((g * h : R2) : Dfull) * d * ((g * h : R2) : Dfull)⁻¹ =
      (g : Dfull) * ((h : Dfull) * d * (h : Dfull)⁻¹) * (g : Dfull)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

attribute [local instance] seedAction

theorem seedAction_pretransitive :
    MulAction.IsPretransitive R2 (blk rest2) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨r, hr, hxy⟩ := blk_R2_transitive rest2 x.2 y.2
  exact ⟨⟨r, hr⟩, Subtype.ext hxy⟩

theorem stabilizer_seed :
    MulAction.stabilizer R2 (⟨cQ, cQ_mem_blk⟩ : blk rest2) =
      (R2 ⊓ Subgroup.centralizer {cQ}).subgroupOf R2 := by
  ext n
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, ← Subtype.coe_inj]
  change (n : Dfull) * cQ * (n : Dfull)⁻¹ = cQ ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩

theorem blk_eq_range (j : Rest) : blk j = Set.range fun v : Vhat => dhat 0 j * v := by
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.2, rfl⟩

theorem natCard_blk (j : Rest) : Nat.card (blk j) = 4 := by
  rw [blk_eq_range, Nat.card_range_of_injective (fun v v' h => Subtype.ext (mul_left_cancel h)),
    isKleinFour_Vhat.card_four]

theorem index_R2c :

    ((R2 ⊓ Subgroup.centralizer {cQ}).subgroupOf R2).index = 4 := by
  have := seedAction_pretransitive
  rw [← stabilizer_seed, MulAction.index_stabilizer_of_transitive, natCard_blk]

theorem natCard_R2c :
    Nat.card ↥(R2 ⊓ Subgroup.centralizer {cQ}) = 2 ^ 30 := by
  have h := ((R2 ⊓ Subgroup.centralizer {cQ}).subgroupOf R2).card_mul_index
  rw [index_R2c, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    natCard_R2] at h
  omega

end CFSG.Monster.B.TwoA.Par2
