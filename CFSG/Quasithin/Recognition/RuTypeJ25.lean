module

public import CFSG.Quasithin.Recognition.RuTypeJ26b
public import CFSG.RankThree.Asc83Table.GL23

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace Sigma

theorem card_centralizer_three : ∀ t : SigmaL2F4, (t ^ 3 = 1 ∧ t ≠ 1) →
    Fintype.card {g : SigmaL2F4 // g * t = t * g} = 6 := by
  decide +kernel

end Sigma

namespace RuDataM

variable (M : RuDataM G) [Finite G]

noncomputable abbrev CHB : Subgroup G := ruH M.T ⊓ Subgroup.centralizer (M.B : Set G)

theorem mem_CHB {x : G} : x ∈ M.CHB ↔ x ∈ ruH M.T ∧ (M.bel : G) * x = x * M.bel := by
  rw [Subgroup.mem_inf, M.mem_centralizer_B]

theorem card_CHB : Nat.card M.CHB = 48 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hCH : M.CHB ≤ ruH M.T := inf_le_left
  let f : M.CHB.subgroupOf (ruH M.T) →* SigmaL2F4 := M.φ.comp (M.CHB.subgroupOf (ruH M.T)).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hCH] at h
  have hker : Nat.card f.ker = 8 := by
    have hc : Nat.card ↥(ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)) = 8 := by
      rw [M.centralizer_Q_eq, M.card_centralizer_S_B]
      norm_num
    refine Eq.trans ?_ hc
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.1.2)).2⟩
        invFun := fun y => ⟨⟨⟨y.1, pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr ⟨pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1,
            (Subgroup.mem_inf.mp y.2).2⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.φ.ker := hx
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show M.φ ⟨y.1, _⟩ = 1
      have : (⟨y.1, pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).1
      exact this
  have hrange : Nat.card f.range = 6 := by
    refine Eq.trans ?_ ((Nat.card_eq_fintype_card).trans
      (Sigma.card_centralizer_three _ M.φ_bel))
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1, ?_⟩
        invFun := fun g => ⟨g.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun g => rfl }
    · obtain ⟨x, hx⟩ := y.2
      rw [← hx]
      have hb := (M.mem_CHB.mp (Subgroup.mem_subgroupOf.mp x.2)).2
      show M.φ x.1 * M.φ ⟨M.bel, M.bel_mem_H⟩ = M.φ ⟨M.bel, M.bel_mem_H⟩ * M.φ x.1
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hb.symm
    ·
      obtain ⟨h, hh⟩ := M.φ_surj g.1
      have hbQ : ∀ q ∈ ruQ M.T, (M.bel : G) * q * (M.bel : G)⁻¹ ∈ ruQ M.T := fun q hq =>
        M.conj_mem_Q M.bel_mem_H hq
      have hy : (h : G)⁻¹ * ((M.bel : G) * h * (M.bel : G)⁻¹) ∈ ruQ M.T := by
        have hmem : (h : G)⁻¹ * ((M.bel : G) * h * (M.bel : G)⁻¹) ∈ ruH M.T :=
          mul_mem (inv_mem h.2) (mul_mem (mul_mem M.bel_mem_H h.2) (inv_mem M.bel_mem_H))
        have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
          rw [MonoidHom.mem_ker]
          have e : (⟨_, hmem⟩ : ruH M.T) =
              h⁻¹ * (⟨M.bel, M.bel_mem_H⟩ * h * ⟨M.bel, M.bel_mem_H⟩⁻¹) := rfl
          rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hh, ← g.2]
          group
        rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hQ3 : ¬ 3 ∣ Nat.card (ruQ M.T) := by rw [M.toRuData.card_Q]; norm_num
      obtain ⟨q, hq, hfix⟩ := exists_fixed_mem_coset M.bel_pow_three hbQ hy hQ3
      have hhq : (h : G) * q ∈ ruH M.T := mul_mem h.2 (pCoreOf_le 2 _ hq)
      have hb : (M.bel : G) * (h * q) = (h * q) * M.bel := by
        calc (M.bel : G) * (h * q) = (M.bel : G) * (h * q) * (M.bel : G)⁻¹ * M.bel := by group
          _ = h * q * M.bel := by rw [hfix]
      refine ⟨⟨⟨_, hhq⟩, Subgroup.mem_subgroupOf.mpr (M.mem_CHB.mpr ⟨hhq, hb⟩)⟩, ?_⟩
      show M.φ ⟨(h : G) * q, hhq⟩ = g.1
      have hq1 : M.φ ⟨q, pCoreOf_le 2 _ hq⟩ = 1 := by
        have : (⟨q, pCoreOf_le 2 _ hq⟩ : ruH M.T) ∈ M.φ.ker := by
          rw [M.φ_ker, Subgroup.mem_subgroupOf]
          exact hq
        exact this
      have e : (⟨(h : G) * q, hhq⟩ : ruH M.T) = h * ⟨q, pCoreOf_le 2 _ hq⟩ := rfl
      rw [e, map_mul, hq1, mul_one, hh]
  rw [hker, hrange] at h
  omega

@[expose] noncomputable def jel : G := M.exists_inv_centralizer_B.choose

theorem jel_spec : M.jel ∈ ruH M.T ∧ M.jel ∉ M.K ∧ M.jel ^ 2 = 1 ∧
    (M.bel : G) * M.jel = M.jel * M.bel ∧ IsConj M.z M.jel :=
  M.exists_inv_centralizer_B.choose_spec

theorem jel_inv : M.jel⁻¹ = M.jel := inv_eq_self_of_sq M.jel_spec.2.2.1

theorem jel_conj_HB {x : G} (hx : x ∈ M.HB) : M.jel * x * M.jel⁻¹ ∈ M.HB := by
  obtain ⟨hjH, -, -, hjb, -⟩ := M.jel_spec
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  refine ⟨M.conj_mem_Q hjH (Subgroup.mem_inf.mp hx).1, (M.mem_centralizer_B).mpr ?_⟩
  have hjb' : (M.bel : G) * M.jel⁻¹ = M.jel⁻¹ * M.bel := (Commute.inv_right hjb).eq
  calc (M.bel : G) * (M.jel * x * M.jel⁻¹) = M.jel * ((M.bel : G) * x) * M.jel⁻¹ := by
        rw [← mul_assoc, ← mul_assoc, hjb]; group
    _ = M.jel * (x * M.bel) * M.jel⁻¹ := by rw [hxb]
    _ = M.jel * x * M.jel⁻¹ * M.bel := by rw [mul_assoc M.jel, mul_assoc x, hjb']; group

@[expose] noncomputable def TB : Subgroup G where
  carrier := {x | x ∈ M.HB ∨ x * M.jel⁻¹ ∈ M.HB}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · right
      have e : x * y * M.jel⁻¹ = (x * M.jel⁻¹) * (M.jel * y * M.jel⁻¹) := by group
      rw [e]
      exact mul_mem hx (M.jel_conj_HB hy)
    · left
      have e : x * y = (x * M.jel⁻¹) * (M.jel * (y * M.jel⁻¹) * M.jel⁻¹) := by
        rw [M.jel_inv]
        have h2 : M.jel * M.jel = 1 := by rw [← pow_two]; exact M.jel_spec.2.2.1
        calc x * y = x * (M.jel * M.jel) * y * (M.jel * M.jel) := by rw [h2, mul_one, mul_one]
          _ = x * M.jel * (M.jel * (y * M.jel) * M.jel) := by group
      rw [e]
      exact mul_mem hx (M.jel_conj_HB hy)
  one_mem' := Or.inl (one_mem _)
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · right
      have h2 : M.jel * M.jel = 1 := by rw [← pow_two]; exact M.jel_spec.2.2.1
      have e : x⁻¹ * M.jel⁻¹ = M.jel * (x * M.jel⁻¹)⁻¹ * M.jel⁻¹ := by
        rw [show (x * M.jel⁻¹)⁻¹ = M.jel * x⁻¹ by group]
        calc x⁻¹ * M.jel⁻¹ = (M.jel * M.jel) * x⁻¹ * M.jel⁻¹ := by rw [h2, one_mul]
          _ = M.jel * (M.jel * x⁻¹) * M.jel⁻¹ := by group
      rw [e]
      exact M.jel_conj_HB (inv_mem hx)

theorem TB_le_CHB : M.TB ≤ M.CHB := by
  obtain ⟨hjH, -, -, hjb, -⟩ := M.jel_spec
  rintro x (hx | hx)
  · obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
    exact M.mem_CHB.mpr ⟨pCoreOf_le 2 _ (Subgroup.mem_inf.mp hx).1, hxb⟩
  · obtain ⟨-, hxb⟩ := M.mem_HB.mp hx
    have hxH := pCoreOf_le 2 _ (Subgroup.mem_inf.mp hx).1
    have e : x = x * M.jel⁻¹ * M.jel := by group
    refine M.mem_CHB.mpr ⟨by rw [e]; exact mul_mem hxH hjH, ?_⟩
    rw [e, ← mul_assoc, hxb, mul_assoc, hjb, ← mul_assoc]

theorem sq_eq_z_of_HB {x : G} (hx : x ∈ M.HB) (hxZ : x ∉ ruZ M.T) : x ^ 2 = M.z := by
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  have hsq := M.sq_HC_mem_Z (M.HB_le_HC hx)
  rcases M.mem_Z_iff.mp hsq with h | h
  · exfalso
    apply hxZ
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · rw [M.eq_z_of_involution hxS hxb h hx1]; exact M.z_mem_Z
  · exact h

theorem jel_not_mem_HB : M.jel ∉ M.HB := fun h =>
  M.jel_spec.2.1 (M.Q_le_K (Subgroup.mem_inf.mp h).1)

theorem card_TB : Nat.card M.TB = 16 := by
  classical
  have hcHB : Nat.card M.HB = 8 := by
    show Nat.card ↥(ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)) = 8
    rw [M.centralizer_Q_eq, M.card_centralizer_S_B]
    norm_num
  have hprod : Nat.card (M.HB × Bool) = 16 := by
    rw [Nat.card_prod, hcHB, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  rw [← hprod]
  refine le_antisymm ?_ ?_
  · refine Nat.card_le_card_of_injective (fun x => if h : (x : G) ∈ M.HB then (⟨x, h⟩, false)
      else (⟨(x : G) * M.jel⁻¹, (x.2).resolve_left h⟩, true)) ?_
    intro x y hxy
    by_cases hx : (x : G) ∈ M.HB <;> by_cases hy : (y : G) ∈ M.HB <;>
      simp only [hx, hy, ↓reduceDIte, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
        and_false, and_true] at hxy
    · exact Subtype.ext (congrArg (fun w : M.HB => (w : G)) hxy)
    · have h := congrArg (fun w : M.HB => (w : G)) hxy
      exact Subtype.ext (mul_right_cancel h)
  · refine Nat.card_le_card_of_injective (fun p => if p.2 then
      ⟨(p.1 : G) * M.jel, Or.inr (by rw [mul_inv_cancel_right]; exact p.1.2)⟩
      else ⟨p.1, Or.inl p.1.2⟩) ?_
    rintro ⟨x, ex⟩ ⟨y, ey⟩ hxy
    cases ex <;> cases ey <;> simp only [Bool.false_eq_true, ↓reduceIte] at hxy
    · exact Prod.ext (Subtype.ext (congrArg (fun w : M.TB => (w : G)) hxy)) rfl
    · exfalso
      apply M.jel_not_mem_HB
      have h : (x : G) = y * M.jel := congrArg Subtype.val hxy
      have : M.jel = (y : G)⁻¹ * x := by rw [h]; group
      rw [this]
      exact mul_mem (inv_mem y.2) x.2
    · exfalso
      apply M.jel_not_mem_HB
      have h : (x : G) * M.jel = y := congrArg Subtype.val hxy
      have : M.jel = (x : G)⁻¹ * y := by rw [← h]; group
      rw [this]
      exact mul_mem (inv_mem x.2) y.2
    · have h : (x : G) * M.jel = y * M.jel := congrArg Subtype.val hxy
      exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl


theorem B_le_CHB : M.B ≤ M.CHB := by
  rw [Subgroup.zpowers_le]
  exact M.mem_CHB.mpr ⟨M.bel_mem_H, rfl⟩

instance B_normal_CHB : (M.B.subgroupOf M.CHB).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc : ((g : M.CHB) : G) ∈ Subgroup.centralizer (M.B : Set G) :=
      (Subgroup.mem_inf.mp g.2).2
    have e : ((g * x * g⁻¹ : M.CHB) : G) = x := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [← (Subgroup.mem_centralizer_iff.mp hc) x hx]
      group
    rw [e]
    exact hx⟩


end RuDataM

end CFSG.Quasithin.RuType
