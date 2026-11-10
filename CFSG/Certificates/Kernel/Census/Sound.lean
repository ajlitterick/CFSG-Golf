module

public import CFSG.Certificates.Kernel.Census.ToMain
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2.Native

theorem allRange_zero (f : Nat → Bool) : ∀ i < 0, f i = true := fun _ h => absurd h (by omega)

theorem allRange_extend {f : Nat → Bool} {a len : Nat} (h : ∀ i < a, f i = true)
    (hb : (List.range' a len).all f = true) : ∀ i < a + len, f i = true := by
  intro i hi
  rcases Nat.lt_or_ge i a with h1 | h1
  · exact h i h1
  · exact List.all_eq_true.1 hb i (List.mem_range'_1.2 ⟨h1, hi⟩)


private theorem pg_big {n w p k : Nat} (hp : canon1 n w p = true) (hk : n ≤ k) :
    pg w (CFSG.KS.mask w) p k = 0 := by
  have h0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
  have hlt : p < 2 ^ (n * w) := by
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · exact h0
  apply Nat.eq_of_testBit_eq
  intro j
  rw [CFSG.KS.PackFld.testBit_pgM, Nat.zero_testBit]
  have hle : n * w ≤ w * k + j := by
    have := Nat.mul_le_mul_right w hk
    rw [Nat.mul_comm k w] at this
    omega
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hle)),
    Bool.and_false]

private theorem unpackP_get! {n w p i : Nat} (hi : i < n) :
    (unpackP n w p)[i]! = pg w (CFSG.KS.mask w) p i := by
  rw [getElem!_pos _ _ (by simp [unpackP]; exact hi)]
  unfold unpackP
  rw [Array.getElem_ofFn]

theorem unpackP_pc {n w p q : Nat} (hn : n < 2 ^ 32) (_hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true) :
    unpackP n w (pc n w p q) = compA n (unpackP n w p) (unpackP n w q) := by
  apply Array.ext
  · simp [unpackP, compA]
  · intro i h1 _
    have hi : i < n := by simpa [unpackP] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [unpackP_get! hi]
    have hL : (unpackP n w (pc n w p q))[i] =
        pg w (CFSG.KS.mask w) p (pg w (CFSG.KS.mask w) q i) := by
      simp only [unpackP, pc, Array.getElem_ofFn]
      exact CFSG.KS.PackFld.pg_pcomp hn hi
    rw [hL]
    by_cases hk : pg w (CFSG.KS.mask w) q i < n
    · rw [unpackP_get! hk]
    · rw [getElem!_neg _ _ (by simp only [unpackP, Array.size_ofFn]; exact hk),
        pg_big hp (by omega)]
      rfl

private theorem lt_of_canon {n w p : Nat} (hp : canon1 n w p = true) : p < 2 ^ (n * w) := by
  have h0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · exact h0

private theorem eq_of_pg {n w p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true)
    (h : ∀ i < n, pg w (CFSG.KS.mask w) p i = pg w (CFSG.KS.mask w) q i) : p = q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < n * w
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, Nat.mul_zero] at hb
        omega
      · exact h0
    have hi : b / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw]
      exact hb
    have hd := Nat.div_add_mod b w
    have hm : b % w < w := Nat.mod_lt _ hw
    have e := congrArg (fun x => x.testBit (b % w)) (h _ hi)
    rw [CFSG.KS.PackFld.testBit_pgM, CFSG.KS.PackFld.testBit_pgM, hd] at e
    simpa [hm] using e
  · have hle : n * w ≤ b := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hp) (Nat.pow_le_pow_right
      (by omega) hle)), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hq)
      (Nat.pow_le_pow_right (by omega) hle))]

private theorem eqA_unpackP' {n w p q : Nat} (hp : canon1 n w p = true)
    (hq : canon1 n w q = true) : eqA n (unpackP n w p) (unpackP n w q) = Nat.beq p q := by
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq]
  unfold eqA allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h
    refine eq_of_pg hp hq (fun i hi => ?_)
    have := h ⟨i, hi⟩ (List.mem_finRange _)
    rw [beq_iff_eq, unpackP_get! hi, unpackP_get! hi] at this
    exact this
  · intro h i _
    rw [h]
    exact beq_self_eq_true _

theorem pinXL_eq {n w P : Nat} {xs : Array Nat} (hP : canon1 n w P = true)
    (hxs : xs.toList.all (canon1 n w) = true) :
    pinXL xs P = inXL n (xs.map (unpackP n w)) (unpackP n w P) := by
  unfold pinXL CFSG.ComponentClassification.RankTwoSporadic.Cert.inXL
  rw [Array.toList_map, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  have hc : ∀ x ∈ xs.toList, canon1 n w x = true := List.all_eq_true.mp hxs
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [Function.comp_apply, eqA_unpackP' hP (hc x hx)]; exact h⟩
  · rintro ⟨x, hx, h⟩
    rw [Function.comp_apply, eqA_unpackP' hP (hc x hx)] at h
    exact ⟨x, hx, h⟩

end CFSG.KC.Census
