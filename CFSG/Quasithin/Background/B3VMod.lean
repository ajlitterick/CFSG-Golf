module

public import CFSG.Quasithin.Background.B3One

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

noncomputable def toV (n : ℕ) (k : Mod) (m : ℕ) : Mod.V n k :=
  if h : inWk n k m = true then
    (QuotientGroup.mk ⟨vecOfNat n m, (vecOfNat_mem_W k m).2 h⟩ : Mod.V n k)
  else 1

theorem toV_of_inW {k : Mod} {m : ℕ} (h : inWk n k m = true) :
    toV n k m = (QuotientGroup.mk ⟨vecOfNat n m, (vecOfNat_mem_W k m).2 h⟩ : Mod.V n k) := by
  unfold toV
  simp only [h, ↓reduceDIte]

theorem inWk_xor {k : Mod} {a b : ℕ} (ha : inWk n k a = true) (hb : inWk n k b = true) :
    inWk n k (a ^^^ b) = true := by
  rw [← vecOfNat_mem_W, vecOfNat_xor]
  exact (k.W n).mul_mem ((vecOfNat_mem_W k a).2 ha) ((vecOfNat_mem_W k b).2 hb)

theorem inWk_actM {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    inWk n k (actM n (tab σ) m) = true := by
  rw [← vecOfNat_mem_W, vecOfNat_actM]
  exact k.isInv_W n σ _ ((vecOfNat_mem_W k m).2 hm)

theorem toV_xor {k : Mod} {a b : ℕ} (ha : inWk n k a = true) (hb : inWk n k b = true) :
    toV n k (a ^^^ b) = toV n k a * toV n k b := by
  rw [toV_of_inW (inWk_xor ha hb), toV_of_inW ha, toV_of_inW hb, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact vecOfNat_xor a b

theorem act_toV {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    Mod.act n k σ (toV n k m) = toV n k (actM n (tab σ) m) := by
  rw [toV_of_inW hm, toV_of_inW (inWk_actM σ hm), act_mk]
  congr 1
  apply Subtype.ext
  exact (vecOfNat_actM σ m).symm

theorem toV_eq_one_iff {k : Mod} {m : ℕ} (hm : inWk n k m = true) :
    toV n k m = 1 ↔ inNk n k m = true := by
  rw [toV_of_inW hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← vecOfNat_mem_N]

theorem toV_ratio {k : Mod} (σ : Gp n) {m : ℕ} (hm : inWk n k m = true) :
    Mod.act n k σ (toV n k m) * (toV n k m)⁻¹ = toV n k (actM n (tab σ) m ^^^ m) := by
  rw [act_toV σ hm, toV_xor (inWk_actM σ hm) hm]
  have h2 : (toV n k m)⁻¹ = toV n k m := by
    have := V_sq (n := n) k (toV n k m)
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  rw [h2]

theorem toV_surj (k : Mod) (v : Mod.V n k) :
    ∃ m, m < 2 ^ n ∧ inWk n k m = true ∧ toV n k m = v := by
  induction v using QuotientGroup.induction_on with
  | H w =>
    obtain ⟨m, hm⟩ := (vecEquiv n).surjective (w : U n)
    have hmW : inWk n k m.val = true := by
      rw [← vecOfNat_mem_W]
      have h1 : vecOfNat n m.val = (w : U n) := hm
      rw [h1]
      exact w.2
    refine ⟨m.val, m.isLt, hmW, ?_⟩
    rw [toV_of_inW hmW]
    congr 1
    apply Subtype.ext
    exact hm


end CFSG.Quasithin.B3
