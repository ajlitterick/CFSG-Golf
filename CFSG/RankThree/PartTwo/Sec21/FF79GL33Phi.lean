module

public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Dict
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Lat
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts13

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def GL33At (X : Subgroup (GL (Fin 3) (ZMod 3))) (v w₁ w₂ : Fin 3 → ZMod 3) : Prop :=
  (∃ τ ∈ X, act33 τ v = v ∧ act33 τ w₁ = -w₁ ∧ act33 τ w₂ = -w₂) →
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g v = v} = 8 →
    (∃ g ∈ X, ∃ h ∈ X, act33 g v = v ∧ act33 h v = v ∧ g * h ≠ h * g) →
    (∀ g ∈ X, (act33 g v = v ∨ act33 g v = -v) →
      (∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∃ d ∈ X, act33 d v = v ∧
        ((∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = act33 d w) ∨
          ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = -act33 d w)) →
    (∃ g ∈ X, act33 g v ≠ v ∧ act33 g v ≠ -v) →
    ((∀ g ∈ X, ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
        act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∀ u : Fin 3 → ZMod 3, u ∉ Submodule.span (ZMod 3) {w₁, w₂} →
        ∃ g ∈ X, act33 g v = u ∨ act33 g v = -u) ∨
    (∃ u₁ ∈ Submodule.span (ZMod 3) {w₁, w₂}, ∃ u₂ ∈ Submodule.span (ZMod 3) {w₁, w₂},
      LinearIndependent (ZMod 3) ![v, u₁, u₂] ∧
      (∀ g ∈ X, ∀ x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
        act33 g x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3))) ∧
      (∃ g ∈ X, act33 g v = -v ∧ act33 g u₁ = u₁ ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = v ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = u₂ ∧ act33 g u₂ = v))


structure TabSpec (T : Array ℕ) : Prop where
  lt : TabLt T
  act_spec : ∀ r c, r < 27 → c < N → decV (act T c r) = Matrix.vecMul (decV r) (dec c)
  mul_spec : ∀ a b, b < N → dec (mulc T a b) = dec a * dec b


section Spec

variable {T : Array ℕ} (hT : TabSpec T) {X : Subgroup (GL (Fin 3) (ZMod 3))} {S : Array ℕ}

include hT in
theorem actG {g : GL (Fin 3) (ZMod 3)} {c r : ℕ} (hc : c < N) (hg : dec c = (g : Mat))
    (hr : r < 27) : act33 g (decV r) = decV (act T c r) := by
  rw [hT.act_spec r c hr hc, hg]


include hT in
theorem act_e1 {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e1 = decV (act T c 3) := by
  have := actG hT hc hg (r := 3) (by norm_num)
  rwa [decV_three] at this

include hT in
theorem act_e2 {g : GL (Fin 3) (ZMod 3)} {c : ℕ} (hc : c < N) (hg : dec c = (g : Mat)) :
    act33 g e2 = decV (act T c 9) := by
  have := actG hT hc hg (r := 9) (by norm_num)
  rwa [decV_nine] at this


theorem vecMul_e1 (M : Mat) (j : Fin 3) : Matrix.vecMul e1 M j = M 1 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e1]

theorem vecMul_e2 (M : Mat) (j : Fin 3) : Matrix.vecMul e2 M j = M 2 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e2]


theorem li_of_raw {r₁ r₂ : ℕ} (h₁ : r₁ % 3 = 0) (h₂ : r₂ % 3 = 0)
    (h : ((r₁ / 3) % 3 * ((r₂ / 9) % 3) + 2 * ((r₁ / 9) % 3 * ((r₂ / 3) % 3))) % 3 ≠ 0) :
    LinearIndependent (ZMod 3) ![e0, decV r₁, decV r₂] := by
  have hdet : (Matrix.of ![e0, decV r₁, decV r₂]).det =
      (((r₁ / 3) % 3 * ((r₂ / 9) % 3) + 2 * ((r₁ / 9) % 3 * ((r₂ / 3) % 3)) : ℕ) : ZMod 3) := by
    rw [Matrix.det_fin_three]
    simp [decV, e0, h₁, h₂]
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2]
    generalize ((r₁ / 3 : ℕ) : ZMod 3) = a
    generalize ((r₂ / 9 : ℕ) : ZMod 3) = b
    generalize ((r₁ / 9 : ℕ) : ZMod 3) = c
    generalize ((r₂ / 3 : ℕ) : ZMod 3) = d
    revert a b c d
    decide
  have hne : (Matrix.of ![e0, decV r₁, decV r₂]).det ≠ 0 := by
    rw [hdet]
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_natCast, ZMod.val_zero] at this
    exact h this
  exact Matrix.linearIndependent_rows_of_det_ne_zero hne


end Spec

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
