module

public import CFSG.Walter.ReeOrder.WardLocal.Five

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))
  {Q : Subgroup G} {g : G} (hQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P)

namespace Block

include hQ in
omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem mem_normalizer_Q {n : G} : n ∈ Subgroup.normalizer (Q : Set G) ↔
    g⁻¹ * n * g ∈ Subgroup.normalizer (P : Set G) :=
  mem_normalizer_of_conj hQ

include hq hPc hQ in
omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem isPGroup_Q : IsPGroup 3 Q := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨_, (hQ x).mp hx⟩
  refine ⟨N, ?_⟩
  rw [Subgroup.orderOf_mk] at hN ⊢
  rw [← hN, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, ← MulAut.conj_apply,
    MulEquiv.orderOf_eq]

include hQ in
omit [Fintype K] [DecidableEq K] [CharP K 3] in
theorem card_normalizer_Q : Nat.card (Subgroup.normalizer (Q : Set G)) =
    Nat.card (Subgroup.normalizer (P : Set G)) := by
  rw [← card_filter_eq, ← card_filter_eq, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
    ← Nat.cast_inj (R := ℂ)]
  push_cast
  exact sum_conj (fun n => mem_normalizer_Q hQ) (fun _ => 1)

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem sum_normalizer_Q :
    ∑ n ∈ Finset.univ.filter (· ∈ Subgroup.normalizer (Q : Set G)), B.ξ₃ n =
      Nat.card (Subgroup.normalizer (Q : Set G)) := by
  rw [sum_conj (fun n => mem_normalizer_Q hQ), card_normalizer_Q hQ]
  simp_rw [B.xi3_class]
  exact B.sum_normalizer hq hK hG hP1P hPc hPn hN1c


include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_normalizer_Q_eq : Nat.card (Subgroup.normalizer (Q : Set G)) = q ^ 3 * (q - 1) := by
  rw [card_normalizer_Q hQ, card_normalizer hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c]

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem index_normalizer_Q : (Subgroup.normalizer (Q : Set G)).index = q ^ 3 + 1 := by
  have h := (Subgroup.normalizer (Q : Set G)).card_mul_index
  rw [B.card_normalizer_Q_eq hq hK hG hP1P hPc hPn hN1c hQ, hG] at h
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hpos : 0 < q ^ 3 * (q - 1) := by
    have : 0 < q - 1 := by omega
    positivity
  have : q ^ 3 * (q - 1) * (Subgroup.normalizer (Q : Set G)).index =
      q ^ 3 * (q - 1) * (q ^ 3 + 1) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem fixedPointCount_eq :
    fixedPointCount G (G ⧸ Subgroup.normalizer (Q : Set G)) = 1 + B.ξ₃ := by
  have hpair : BlocksInnerProduct (fixedPointCount G (G ⧸ Subgroup.normalizer (Q : Set G)))
      B.ξ₃ = 1 := by
    rw [blocksInnerProduct_fixedPointCount _ _ (fun g x => B.xi3_class g x) B.real_3,
      B.sum_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ]
    have : (Nat.card (Subgroup.normalizer (Q : Set G)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  have hdeg : deg B.ξ₃ + 1 = Nat.card (G ⧸ Subgroup.normalizer (Q : Set G)) := by
    rw [← Subgroup.index, B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ, B.deg_3]
    push_cast; ring
  exact fixedPointCount_eq_one_add B.irr_3 B.n13.symm hdeg hpair

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_fixedBy {x : G} {n : ℕ} (h : 1 + B.ξ₃ x = n) :
    Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) = n := by
  have h1 := congrFun (B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ) x
  rw [fixedPointCount, Pi.add_apply, Pi.one_apply, h] at h1
  exact_mod_cast h1

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_fixedBy_three {x : G} (hx : 3 ∣ orderOf x) :
    Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) = 1 :=
  B.card_fixedBy hq hK hG hP1P hPc hPn hN1c hQ (by rw [B.xi3_eq_zero hq hG hx]; simp)


omit [Fintype G] in
theorem conj_smul_eq_of_mem_normalizer {H : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (H : Set G)) : MulAut.conj c • H = H := by
  ext x
  rw [mem_conj_smul_iff]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) x)
  rw [inv_inv] at this
  exact this.symm

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem inf_conj (c : G) : Q ⊓ (MulAut.conj c • Q) = ⊥ ∨ Q ⊓ (MulAut.conj c • Q) = Q := by
  by_cases h : Q ⊓ (MulAut.conj c • Q) = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conj_smul_iff] at hxc
  have h3 : 3 ∣ orderOf x := three_dvd_of_mem (isPGroup_Q hq hPc hQ) hxQ hx1'
  have hcard := B.card_fixedBy_three hq hK hG hP1P hPc hPn hN1c hQ h3
  have hf1 : ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∈
      MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x := by
    rw [MulAction.mem_fixedBy, smul_mk_eq_iff]
    simpa using Subgroup.le_normalizer hxQ
  have hfc : (c : G ⧸ Subgroup.normalizer (Q : Set G)) ∈
      MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x := by
    rw [MulAction.mem_fixedBy, smul_mk_eq_iff]
    exact Subgroup.le_normalizer hxc
  have : Subsingleton (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have heq := congrArg Subtype.val (Subsingleton.elim (⟨_, hf1⟩ :
    MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) ⟨_, hfc⟩)
  simp only at heq
  have hcN : c ∈ Subgroup.normalizer (Q : Set G) := by
    have := QuotientGroup.eq.mp heq
    simpa using this
  rw [conj_smul_eq_of_mem_normalizer hcN, inf_idem]

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem isMultiplyPretransitive :
    MulAction.IsMultiplyPretransitive G (G ⧸ Subgroup.normalizer (Q : Set G)) 2 := by
  have h := (permutation_character_orbit_count G (G ⧸ Subgroup.normalizer (Q : Set G))).2.2.2
    inferInstance (by
      rw [← Subgroup.index, B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ]
      have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
      omega)
  refine h.mpr ?_
  rw [B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ, add_sub_cancel_left]
  exact B.irr_3


end Block

end CFSG.Walter.WardLocal
