module

public import CFSG.ClassicalInvolution.Q3.Q3CPQuat
public import CFSG.ClassicalInvolution.Q3.Q3YSMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}


structure BDNbhd (zb : X) : Prop where
  ne_one : zb ≠ 1
  mul_self : zb * zb = 1
  central : ∀ x : X, x * zb = zb * x
  mem : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → zb ∈ F


@[expose] def ShapeDoubleOr (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧ D.kind i = CompData.sl23 ∧ D.kind j = CompData.sl23 ∧
    ∃ ζi ζj : X, ζi ∈ (D.hom i).range ∧ ζj ∈ (D.hom j).range ∧ ζi ≠ ζj ∧ ζi * ζi = 1 ∧
      ζj * ζj = 1 ∧ ζi ≠ 1 ∧ ζj ≠ 1 ∧ (∀ g : X, g * ζi = ζi * g) ∧ (∀ g : X, g * ζj = ζj * g) ∧
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζi) ∧
      (∀ u ∈ (D.hom j).range, u * u = 1 → u = 1 ∨ u = ζj) ∧ (zb = ζi ∨ zb = ζj ∨ zb = ζi * ζj)

@[expose] def ShapeDouble (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧ D.kind i = CompData.sl23 ∧ D.kind j = CompData.sl23 ∧
    ∃ ζi ζj : X, ζi ∈ (D.hom i).range ∧ ζj ∈ (D.hom j).range ∧ ζi ≠ ζj ∧ ζi * ζi = 1 ∧
      ζj * ζj = 1 ∧ ζi ≠ 1 ∧ ζj ≠ 1 ∧ (∀ g : X, g * ζi = ζi * g) ∧ (∀ g : X, g * ζj = ζj * g) ∧
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζi) ∧
      (∀ u ∈ (D.hom j).range, u * u = 1 → u = 1 ∨ u = ζj) ∧ zb = ζi * ζj

theorem ShapeDoubleOr.exact {D : LieSystemData3 ι X Φ} {zb : X} (h : ShapeDoubleOr D zb)
    (hne : ∀ (i : ι) (ζ : X), D.kind i = CompData.sl23 → ζ ∈ (D.hom i).range →
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζ) → zb ≠ ζ) : ShapeDouble D zb := by
  obtain ⟨i, j, hij, hk, hi, hj, ζi, ζj, hζi, hζj, hne', h2i, h2j, h1i, h1j, hci, hcj, hui, huj,
    hz⟩ := h
  refine ⟨i, j, hij, hk, hi, hj, ζi, ζj, hζi, hζj, hne', h2i, h2j, h1i, h1j, hci, hcj, hui, huj, ?_⟩
  rcases hz with e | e | e
  · exact absurd e (hne i ζi hi hζi hui)
  · exact absurd e (hne j ζj hj hζj huj)
  · exact e

@[expose] def ShapeSp4 (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i₁ : ι, (∀ i, i = i₁) ∧ D.kind i₁ = CompData.model .PSp 2 ∧
    ∃ f ∈ Subgroup.center (D.kind i₁).G, D.hom i₁ f = zb


variable [Finite X]


theorem range_eq_top_of_forall_eq (D : LieSystemData3 ι X Φ) {i₁ : ι} (hall : ∀ i, i = i₁) :
    (D.hom i₁).range = ⊤ := by
  have h1 : (⨆ i, (D.hom i).range) = (D.hom i₁).range :=
    le_antisymm (iSup_le fun i => by rw [hall i]) (le_iSup (fun i => (D.hom i).range) i₁)
  rw [← h1]
  exact D.generate


section Quat

variable {x y x' y' ζ ζ' : X}


theorem zeta_ne_of_bd {zb : X} (h : BDNbhd zb) (hQ : QuatPair x y ζ) (hQ' : QuatPair x' y' ζ')
    (hxx' : x * x' = x' * x) (hxy' : x * y' = y' * x) (hyx' : y * x' = x' * y)
    (hyy' : y * y' = y' * y) : ζ ≠ ζ' := by
  intro hζ
  subst hζ
  have ha2 := quatPair_prod_sq_a hQ hQ' hxx'
  have hb2 := quatPair_prod_sq_b hQ hQ' hyy'
  have hab := quatPair_prod_comm hQ hQ' hxy' hyx'
  have hane := quatPair_prod_a_ne hQ hyx'
  have hbne := quatPair_prod_b_ne hQ hxy'
  have habne := quatPair_prod_ab_ne hQ hxx' hxy'
  have ha1 : x * x' ≠ 1 := fun h1 => hane (by rw [h1]; simp)
  have hb1 : y * y' ≠ 1 := fun h1 => hbne (by rw [h1]; simp)
  have hax : (x * x') * x = x * (x * x') := by
    calc (x * x') * x = x * (x' * x) := by group
      _ = x * (x * x') := by rw [← hxx']
  have hne : x * x' ≠ y * y' := fun h1 => hbne (by rw [← h1]; exact hax)
  rcases Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem ha2 hb2 ha1 hb1 hne hab with h1 | h1 | h1
  · exact hane (by rw [← h1]; exact (h.central y).symm)
  · exact hbne (by rw [← h1]; exact (h.central x).symm)
  · exact habne (by rw [← h1]; exact (h.central x).symm)

theorem bd_of_zeta_ne {zb : X} (h : BDNbhd zb) (hQ : QuatPair x y ζ) (hQ' : QuatPair x' y' ζ')
    (hne : ζ ≠ ζ') : zb = ζ ∨ zb = ζ' ∨ zb = ζ * ζ' :=
  Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem hQ.zz hQ'.zz hQ.ne hQ'.ne hne (hQ.cen ζ').symm


end Quat


theorem zb_eq_of_triple {zb : X} (h : BDNbhd zb) {s xk yk ζk : X} (hQ : QuatPair xk yk ζk)
    (hs2 : s * s = 1) (hrel : s * yk = ζk * (yk * s)) : zb = ζk := by
  have hnc : s * yk ≠ yk * s := by
    intro hc
    apply hQ.ne
    have h2 : ζk * (yk * s) = 1 * (yk * s) := by rw [← hrel, hc, one_mul]
    exact mul_right_cancel h2
  have hs1 : s ≠ 1 := fun h1 => hnc (by rw [h1]; simp)
  have hsζ : s ≠ ζk := fun h1 => hnc (by rw [h1]; exact (hQ.cen yk).symm)
  rcases Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem hs2 hQ.zz hs1 hQ.ne hsζ (hQ.cen s)
    with h1 | h1 | h1
  · exact absurd (by rw [← h1]; exact (h.central yk).symm) hnc
  · exact h1
  · exfalso
    have hz := h.central yk
    rw [h1] at hz
    apply hnc
    have e : (yk * s) * ζk = (s * yk) * ζk := by
      calc (yk * s) * ζk = yk * (s * ζk) := by group
        _ = (s * ζk) * yk := hz
        _ = s * (ζk * yk) := by group
        _ = s * (yk * ζk) := by rw [← hQ.cen yk]
        _ = (s * yk) * ζk := by group
    exact (mul_right_cancel e).symm

theorem false_of_three {zb : X} (h : BDNbhd zb) {x₁ y₁ x₂ y₂ x₃ y₃ ζ₁ ζ₂ ζ₃ : X}
    (h₁ : QuatPair x₁ y₁ ζ₁) (h₂ : QuatPair x₂ y₂ ζ₂) (h₃ : QuatPair x₃ y₃ ζ₃)
    (c12 : x₁ * x₂ = x₂ * x₁ ∧ x₁ * y₂ = y₂ * x₁ ∧ y₁ * x₂ = x₂ * y₁ ∧ y₁ * y₂ = y₂ * y₁)
    (c13 : x₁ * x₃ = x₃ * x₁ ∧ x₁ * y₃ = y₃ * x₁ ∧ y₁ * x₃ = x₃ * y₁ ∧ y₁ * y₃ = y₃ * y₁)
    (c23 : x₂ * x₃ = x₃ * x₂ ∧ x₂ * y₃ = y₃ * x₂ ∧ y₂ * x₃ = x₃ * y₂ ∧ y₂ * y₃ = y₃ * y₂) :
    False := by
  have n12 := zeta_ne_of_bd h h₁ h₂ c12.1 c12.2.1 c12.2.2.1 c12.2.2.2
  have n13 := zeta_ne_of_bd h h₁ h₃ c13.1 c13.2.1 c13.2.2.1 c13.2.2.2
  have n23 := zeta_ne_of_bd h h₂ h₃ c23.1 c23.2.1 c23.2.2.1 c23.2.2.2
  have A12 := bd_of_zeta_ne h h₁ h₂ n12
  have A13 := bd_of_zeta_ne h h₁ h₃ n13
  have A23 := bd_of_zeta_ne h h₂ h₃ n23
  have hprod : ζ₁ * ζ₂ * ζ₃ = 1 := by
    have key23 : ζ₁ = ζ₂ * ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e]
      calc ζ₂ * ζ₃ * ζ₂ * ζ₃ = ζ₂ * (ζ₃ * ζ₂) * ζ₃ := by group
        _ = ζ₂ * (ζ₂ * ζ₃) * ζ₃ := by rw [h₂.cen ζ₃]
        _ = (ζ₂ * ζ₂) * (ζ₃ * ζ₃) := by group
        _ = 1 := by rw [h₂.zz, h₃.zz, one_mul]
    have key13 : ζ₂ = ζ₁ * ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e]
      calc ζ₁ * (ζ₁ * ζ₃) * ζ₃ = (ζ₁ * ζ₁) * (ζ₃ * ζ₃) := by group
        _ = 1 := by rw [h₁.zz, h₃.zz, one_mul]
    have key12 : ζ₁ * ζ₂ = ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e, h₃.zz]
    rcases A12 with e | e | e
    · rcases A23 with f | f | f
      · exact absurd (e.symm.trans f) n12
      · exact absurd (e.symm.trans f) n13
      · exact key23 (e.symm.trans f)
    · rcases A13 with f | f | f
      · exact absurd (e.symm.trans f) n12.symm
      · exact absurd (e.symm.trans f) n23
      · exact key13 (e.symm.trans f)
    · rcases A13 with f | f | f
      · exfalso
        have : ζ₁ * ζ₂ = ζ₁ * 1 := by rw [mul_one]; exact e.symm.trans f
        exact h₂.ne (mul_left_cancel this)
      · exact key12 (e.symm.trans f)
      · exfalso
        have : ζ₁ * ζ₂ = ζ₁ * ζ₃ := e.symm.trans f
        exact n23 (mul_left_cancel this)
  have hs2 : (x₁ * x₂ * x₃) * (x₁ * x₂ * x₃) = 1 := by
    have hc12 : Commute x₁ x₂ := c12.1
    have hc13 : Commute x₁ x₃ := c13.1
    have hc23 : Commute x₂ x₃ := c23.1
    have hc : Commute (x₁ * x₂) x₃ := hc13.mul_left hc23
    have e : (x₁ * x₂ * x₃) ^ 2 = x₁ ^ 2 * x₂ ^ 2 * x₃ ^ 2 := by
      rw [Commute.mul_pow hc, Commute.mul_pow hc12]
    rw [← pow_two, e, pow_two x₁, pow_two x₂, pow_two x₃, h₁.xx, h₂.xx, h₃.xx, hprod]
  have hrel1 : (x₁ * x₂ * x₃) * y₁ = ζ₁ * (y₁ * (x₁ * x₂ * x₃)) := by
    calc (x₁ * x₂ * x₃) * y₁ = x₁ * x₂ * (x₃ * y₁) := by group
      _ = x₁ * x₂ * (y₁ * x₃) := by rw [← c13.2.2.1]
      _ = x₁ * (x₂ * y₁) * x₃ := by group
      _ = x₁ * (y₁ * x₂) * x₃ := by rw [← c12.2.2.1]
      _ = (x₁ * y₁) * x₂ * x₃ := by group
      _ = (ζ₁ * (y₁ * x₁)) * x₂ * x₃ := by rw [h₁.xy]
      _ = ζ₁ * (y₁ * (x₁ * x₂ * x₃)) := by group
  have hrel2 : (x₁ * x₂ * x₃) * y₂ = ζ₂ * (y₂ * (x₁ * x₂ * x₃)) := by
    calc (x₁ * x₂ * x₃) * y₂ = x₁ * x₂ * (x₃ * y₂) := by group
      _ = x₁ * x₂ * (y₂ * x₃) := by rw [← c23.2.2.1]
      _ = x₁ * (x₂ * y₂) * x₃ := by group
      _ = x₁ * (ζ₂ * (y₂ * x₂)) * x₃ := by rw [h₂.xy]
      _ = (x₁ * ζ₂) * (y₂ * x₂) * x₃ := by group
      _ = (ζ₂ * x₁) * (y₂ * x₂) * x₃ := by rw [← h₂.cen x₁]
      _ = ζ₂ * (x₁ * y₂) * x₂ * x₃ := by group
      _ = ζ₂ * (y₂ * x₁) * x₂ * x₃ := by rw [c12.2.1]
      _ = ζ₂ * (y₂ * (x₁ * x₂ * x₃)) := by group
  exact n12 ((zb_eq_of_triple h h₁ hs2 hrel1).symm.trans (zb_eq_of_triple h h₂ hs2 hrel2))


end CFSG.ClassicalInvolution.Q3.Q3CP
