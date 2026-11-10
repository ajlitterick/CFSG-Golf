module

public import CFSG.Quasithin.Background.C116Three.L3Transfer
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.C116Three.L3LocalB

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

theorem Ustd_iff {γ : L3.Γ} : L3F.Ustd γ ↔ L3F.Ppt γ ∧ L3F.Pline γ := Iff.rfl

theorem Ppt_one' : L3F.Ppt (1 : L3.Γ) := by
  unfold L3F.Ppt; exact L3.act_one _

theorem Ppt_mul' {a b : L3.Γ} (ha : L3F.Ppt a) (hb : L3F.Ppt b) : L3F.Ppt (a * b) := by
  unfold L3F.Ppt at *; rw [L3.act_mul, hb, ha]

theorem Ppt_inv' {a : L3.Γ} (ha : L3F.Ppt a) : L3F.Ppt a⁻¹ := by
  unfold L3F.Ppt at *
  calc L3.act a⁻¹ L3F.e1 = L3.act a⁻¹ (L3.act a L3F.e1) := by rw [ha]
    _ = L3F.e1 := L3.act_inv_act a L3F.e1

theorem Pline_one' : L3F.Pline (1 : L3.Γ) := by
  unfold L3F.Pline; intro x hx; rw [L3.act_one]; exact hx

theorem Pline_mul' {a b : L3.Γ} (ha : L3F.Pline a) (hb : L3F.Pline b) : L3F.Pline (a * b) := by
  unfold L3F.Pline at *; intro x hx; rw [L3.act_mul]; exact ha _ (hb x hx)

theorem Pline_pow' {a : L3.Γ} (ha : L3F.Pline a) (n : ℕ) : L3F.Pline (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Pline_one'
  | succ k ih => rw [pow_succ]; exact Pline_mul' ih ha

theorem Pline_inv' {a : L3.Γ} (ha : L3F.Pline a) : L3F.Pline a⁻¹ := by
  have hpos : 0 < orderOf a := orderOf_pos a
  have hmul : a * a ^ (orderOf a - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_right hmul]
  exact Pline_pow' ha _

@[expose] def USub : Subgroup L3.Γ where
  carrier := {γ | L3F.Ustd γ}
  mul_mem' := fun {a b} ha hb => Ustd_iff.2 ⟨Ppt_mul' (Ustd_iff.1 ha).1 (Ustd_iff.1 hb).1,
    Pline_mul' (Ustd_iff.1 ha).2 (Ustd_iff.1 hb).2⟩
  one_mem' := Ustd_iff.2 ⟨Ppt_one', Pline_one'⟩
  inv_mem' := fun {a} ha => Ustd_iff.2 ⟨Ppt_inv' (Ustd_iff.1 ha).1, Pline_inv' (Ustd_iff.1 ha).2⟩


@[expose] def sylowQ (D : L3Data G M C) : Subgroup ↥G := USub.map D.π


section Syl


end Syl

end CFSG.Quasithin.C116Three
