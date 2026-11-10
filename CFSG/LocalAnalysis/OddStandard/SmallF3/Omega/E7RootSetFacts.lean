module

public import Certificates.Data.OmegaSevenMax.Checker

public section

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax

theorem encV_lt (v : V) : encV v < 2187 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  unfold encV
  omega

theorem digit_encV (v : V) (i : Fin 7) : encV v / 3 ^ (i : ℕ) % 3 = (v i).val := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  unfold encV
  match i with
  | ⟨0, _⟩ => show _ / 1 % 3 = (v 0).val; omega
  | ⟨1, _⟩ => show _ / 3 % 3 = (v 1).val; omega
  | ⟨2, _⟩ => show _ / 9 % 3 = (v 2).val; omega
  | ⟨3, _⟩ => show _ / 27 % 3 = (v 3).val; omega
  | ⟨4, _⟩ => show _ / 81 % 3 = (v 4).val; omega
  | ⟨5, _⟩ => show _ / 243 % 3 = (v 5).val; omega
  | ⟨6, _⟩ => show _ / 729 % 3 = (v 6).val; omega
  | ⟨n + 7, h⟩ => exact absurd h (by omega)

theorem decV_encV (v : V) : decV (encV v) = v := by
  funext i
  simp only [decV, digit_encV, ZMod.natCast_zmod_val]

theorem encV_decV {c : ℕ} (hc : c < 2187) : encV (decV c) = c := by
  have e0 : ((0 : Fin 7) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 7) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 7) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 7) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 7) : ℕ) = 4 := rfl
  have e5 : ((5 : Fin 7) : ℕ) = 5 := rfl
  have e6 : ((6 : Fin 7) : ℕ) = 6 := rfl
  simp only [encV, decV, ZMod.val_natCast, e0, e1, e2, e3, e4, e5, e6, Nat.reducePow, pow_zero,
    Nat.div_one]
  omega


theorem testBit_foldl (L : List ℕ) (acc c : ℕ) :
    (L.foldl (fun a d => a ||| (1 <<< d)) acc).testBit c = (acc.testBit c || decide (c ∈ L)) := by
  induction L generalizing acc with
  | nil => simp
  | cons d t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases h1 : d = c
    · subst h1
      simp
    · have h2 : ¬ c = d := fun h => h1 h.symm
      simp [h1, h2]

theorem testBit_bitsOf (L : List ℕ) (c : ℕ) : (bitsOf L).testBit c = decide (c ∈ L) := by
  unfold bitsOf
  rw [testBit_foldl]
  simp

theorem bitsOf_eq_iff {L L' : List ℕ} : bitsOf L = bitsOf L' ↔ ∀ c, c ∈ L ↔ c ∈ L' := by
  constructor
  · intro h c
    have h' := congrArg (fun n => n.testBit c) h
    simp only [testBit_bitsOf, decide_eq_decide] at h'
    exact h'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro c
    rw [testBit_bitsOf, testBit_bitsOf]
    exact decide_eq_decide.2 (h c)


@[expose] def decSet (L : List ℕ) : Finset V := (L.map decV).toFinset

theorem mem_decSet {L : List ℕ} {x : V} : x ∈ decSet L ↔ ∃ c ∈ L, decV c = x := by
  simp [decSet]

theorem decSet_eq_of_bitsOf {L L' : List ℕ} (h : bitsOf L = bitsOf L') : decSet L = decSet L' := by
  have h' := bitsOf_eq_iff.1 h
  ext x
  rw [mem_decSet, mem_decSet]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (h' c).1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (h' c).2 hc, rfl⟩


@[expose] def rootSetOf (T : Tables) : Finset V := decSet T.roots


end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
