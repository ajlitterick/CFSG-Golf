module

public import CFSG.Quasithin.Background.D36GluedOther
import CFSG.Quasithin.Background.D36GluedL3Mod
public import CFSG.Quasithin.Background.D36GluedL3Rec
import CFSG.Quasithin.Background.D36GluedBig
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z4bPrime
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B

public section

namespace CFSG.Quasithin

open scoped commutatorElement

section Perfect


variable {Y : Type} [CommGroup Y] {L₀ : Subgroup (MulAut Y)}


theorem fixed_of_perfect (hperf : commutator ↥L₀ = ⊤) {Z : Subgroup Y} (hZ : Z ≤ fixV L₀) {x : Y}
    (hx : ∀ l ∈ L₀, l x * x⁻¹ ∈ Z) : ∀ l ∈ L₀, l x = x := by
  have hab : ∀ a b : ↥L₀,
      (a : MulAut Y) ((b : MulAut Y) x) = (b : MulAut Y) ((a : MulAut Y) x) := by
    intro a b
    have hzb : (b : MulAut Y) x * x⁻¹ ∈ Z := hx b b.2
    have hza : (a : MulAut Y) x * x⁻¹ ∈ Z := hx a a.2
    have e1 : (a : MulAut Y) ((b : MulAut Y) x) =
        ((b : MulAut Y) x * x⁻¹) * (a : MulAut Y) x := by
      have h1 : (b : MulAut Y) x = ((b : MulAut Y) x * x⁻¹) * x := by
        rw [inv_mul_cancel_right]
      conv_lhs => rw [h1]
      rw [map_mul, hZ hzb a a.2]
    have e2 : (b : MulAut Y) ((a : MulAut Y) x) =
        ((a : MulAut Y) x * x⁻¹) * (b : MulAut Y) x := by
      have h1 : (a : MulAut Y) x = ((a : MulAut Y) x * x⁻¹) * x := by
        rw [inv_mul_cancel_right]
      conv_lhs => rw [h1]
      rw [map_mul, hZ hza b b.2]
    rw [e1, e2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let K : Subgroup ↥L₀ := MulAction.stabilizer ↥L₀ x
  have hmemK : ∀ l : ↥L₀, l ∈ K ↔ (l : MulAut Y) x = x := fun l => MulAction.mem_stabilizer_iff
  have hcomm : ∀ a b : ↥L₀, ⁅a, b⁆ ∈ K := by
    intro a b
    have key : ∀ a b : ↥L₀, a⁻¹ * b⁻¹ * a * b ∈ K := by
      intro a b
      rw [hmemK]
      have e : a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
      rw [e]
      change (((b : MulAut Y) * (a : MulAut Y))⁻¹) ((a : MulAut Y) ((b : MulAut Y) x)) = x
      rw [hab a b]
      change (((b : MulAut Y) * (a : MulAut Y))⁻¹) (((b : MulAut Y) * (a : MulAut Y)) x) = x
      exact MulAut.inv_apply_self (M := Y) _ _
    have := key a⁻¹ b⁻¹
    rw [inv_inv, inv_inv] at this
    rw [commutatorElement_def]
    exact this
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Subgroup.commutator_le.mpr (fun a _ b _ => hcomm a b)
  intro l hl
  have : (⟨l, hl⟩ : ↥L₀) ∈ K := by rw [hKtop]; trivial
  exact (hmemK _).mp this

end Perfect

section Sec


end Sec

section Bridge


end Bridge

section Glued


namespace GluedSwap


end GluedSwap

end Glued


end CFSG.Quasithin
