
module

public import Certificates.Data.Kernel.SporSch.HNF5Rank
public import CFSG.Certificates.Kernel.SporSch.HNF5ModSound
public import CFSG.Sporadic.HNSchreier.RankCheckInputs
public import Mathlib.Data.List.GetD
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

theorem subId5_sound {T X : Nat → Nat} (hT : Canon5 T) (h : ∀ i < 133, X i = subRow5 T i) :
    subId (rows5 T) = rows5 X := by
  unfold subId
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [rows5_get _ i.isLt j.isLt, h i i.isLt]
  unfold subRow5
  rw [F5Lane.lane5_red5 _ j.isLt]
  have e : Nat.add (T i.val) (Nat.shiftLeft (nat_lit 4) (Nat.mul (nat_lit 16) i.val)) =
      ∑ k ∈ Finset.range 133, (lane5 (T i.val) k + if i.val = k then 4 else 0) * 2 ^ (16 * k) := by
    change T i.val + 4 <<< (16 * i.val) = _
    rw [Nat.shiftLeft_eq]
    simp only [Nat.add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [← F5Lane.row_expand (F5Lane.canon5_lt (hT i i.isLt)), Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.2 i.isLt)]
  have hb : ∀ k < 133, lane5 (T i.val) k + (if i.val = k then 4 else 0) < 2 ^ 16 := fun k hk => by
    have := F5Lane.canon5_lane (hT i i.isLt) hk
    split_ifs <;> omega
  rw [e, F5Lane.lane_sum5 hb j.isLt]

theorem diag5_sound {X : Nat → Nat} {r : Nat} (h : ∀ i < 133, X i = diagRow5 r i) :
    rows5 X = diagR r := by
  unfold rows5 diagR
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [h i i.isLt]
  unfold diagRow5
  rw [LyM.nIf_eqL]
  by_cases hr : i.val < r
  · rw [ite_eq_left (Eq.mpr Nat.blt_eq hr), F5Lane.lane5_idRow5]
    by_cases hij : i.val = j.val
    · rw [ite_eq_left hij.symm, ite_eq_left ⟨hij, hr⟩]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right fun hc => hij hc.1]
  · have hb : ¬ Nat.blt i.val r = true := fun hc => hr (Eq.mp Nat.blt_eq hc)
    rw [ite_eq_right hb, F5Lane.lane5_zero, ite_eq_right fun hc => hr hc.2]

@[expose] def chainOK (OP L R : Nat → Nat) (lt : Int → Nat) (n : Nat) (w : List Int) (o : Nat) :
    Bool :=
  decide (1 ≤ w.length) && decide (o + w.length ≤ n) &&
    w.all (fun l => decide (lt l < n)) &&
    OP o == 1 && L o == lt (w.getD (w.length - 1) 0) &&
    (List.range (w.length - 1)).all fun u => OP (o + u + 1) == 0 &&
      L (o + u + 1) == lt (w.getD (w.length - 2 - u) 0) && R (o + u + 1) == o + u

theorem mword_one (S Si : Array (Array (Array Nat))) (l : Int) :
    mword S Si [l] = mulM 5 133 (mletter S Si l) (idM 133) := rfl


end CFSG.KS.SporSch

end
