module

public import CFSG.Sporadic.Ly.ActSpec

public section

namespace CFSG.Sporadic.Ly

open Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true parAll_eq_true)
open CFSG.Sporadic.Th.Native (ap)

@[expose] def Canon (key : ByteArray) : Prop :=
  ValidKey key ∧ keyDigit key 826 = 0 ∧ keyDigit key 827 = 0 ∧ (∃ p, IsRREF (keyU key) p) ∧
    ∃ Si, keyC key * Si = 1


theorem canon_actKey (M : Array (Array ℕ)) {key key' : ByteArray} (hk : Canon key)
    (h : actKey (frTable M) key = some key') : Canon key' := by
  obtain ⟨hv, -, -, -, Si, hSi⟩ := hk
  obtain ⟨hv', hR, -⟩ := actKey_spec M hv h
  refine ⟨hv', ?_, ?_, hR, keyC_inv_actKey M hv h hSi⟩
  all_goals
    unfold actKey at h
    simp only at h
    split at h
    · obtain rfl := (Option.some.inj h).symm
      rw [keyDigit_encodeDigits _ (by omega)]
      unfold keyFun
      simp
    · exact absurd h (by simp)

theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have h' : (a.data == b.data) = true := h
  exact ByteArray.ext (beq_iff_eq.1 h')

theorem option_byteArray_eq_of_beq {x : Option ByteArray} {y : ByteArray}
    (h : (x == some y) = true) : x = some y := by
  cases x with
  | none => cases h
  | some a => exact congrArg some (byteArray_eq_of_beq h)

structure KFacts (MA MB : Array (Array ℕ)) (k₀ : ByteArray) (O : KOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 30
  root : O.keys[0]! = k₀
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, O.keys[i]! = O.keys[j]! → i = j
  alpha : ∀ i < O.keys.size, ap O.alpha i < O.keys.size ∧
    actKey (frTable MA) O.keys[i]! = some O.keys[ap O.alpha i]!
  beta : ∀ i < O.keys.size, ap O.beta i < O.keys.size ∧
    actKey (frTable MB) O.keys[i]! = some O.keys[ap O.beta i]!
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))


theorem KFacts.canon {MA MB : Array (Array ℕ)} {k₀ : ByteArray} {O : KOrbit}
    (hF : KFacts MA MB k₀ O) (h0 : Canon k₀) : ∀ i < O.keys.size, Canon O.keys[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hF.root]; exact h0
    · obtain ⟨hp, hlab⟩ := hF.tree i hi hpos
      have hcp := ih _ hp (lt_trans hp hi)
      rcases hlab with ⟨-, he⟩ | ⟨-, he⟩
      · have := (hF.alpha _ (lt_trans hp hi)).2
        rw [he] at this
        exact canon_actKey MA hcp this
      · have := (hF.beta _ (lt_trans hp hi)).2
        rw [he] at this
        exact canon_actKey MB hcp this

end CFSG.Sporadic.Ly
