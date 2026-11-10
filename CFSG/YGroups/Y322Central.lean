module

public import CFSG.YGroups.Exact.Y321
public import CFSG.YGroups.Exact.Y322
public import CFSG.YGroups.Y322Central.Transitive
public import Certificates.Certificate10103
public meta import CFSG.YGroups.Defs
public meta import CFSG.YGroups.Exact.Y322
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import Certificates.Data.CFSGNative.YGroups.Y322CentralData

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)


@[expose] noncomputable def y322F1 : YGroup 3 2 2 := evalWord (yGen 3 2 2) y322WordF1

@[expose] noncomputable def y322F2 : YGroup 3 2 2 := evalWord (yGen 3 2 2) y322WordF2

theorem evalWord_const_ofAdd (w : List ℕ) :
    evalWord (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) w =
      Multiplicative.ofAdd ((w.length : ℕ) : ZMod 2) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, ih, List.length_cons, Nat.cast_succ, ← ofAdd_add, add_comm]

theorem y322_parity_relators :
    ∀ w ∈ yRels 3 2 2, evalWord (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) w = 1 := by
  have key : ∀ w ∈ yRels 3 2 2, w.length % 2 = 0 := by decide +kernel
  intro w hw
  rw [evalWord_const_ofAdd]
  have h0 : ((w.length : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (key w hw)
  rw [h0]
  rfl

noncomputable def y322Parity : YGroup 3 2 2 →* Multiplicative (ZMod 2) :=
  yModelHom (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) y322_parity_relators

theorem y322Parity_yGen {c : ℕ} (hc : c < 8) :
    y322Parity (yGen 3 2 2 c) = Multiplicative.ofAdd 1 :=
  yModelHom_yGen hc

theorem y322Parity_evalWord (w : List ℕ) (hw : ∀ c ∈ w, c < 8) :
    y322Parity (evalWord (yGen 3 2 2) w) = Multiplicative.ofAdd ((w.length : ℕ) : ZMod 2) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, map_mul, y322Parity_yGen (hw c (by simp)),
      ih (fun d hd => hw d (by simp [hd])), List.length_cons, Nat.cast_succ, ← ofAdd_add,
      add_comm]

theorem y322Parity_F1 : y322Parity y322F1 = Multiplicative.ofAdd 1 := by
  rw [y322F1, y322Parity_evalWord _ (by decide)]
  have : y322WordF1.length = 63 := by decide
  rw [this]
  rfl

theorem y322F1_ne_one : y322F1 ≠ 1 := by
  intro h
  have := y322Parity_F1
  rw [h, map_one] at this
  exact absurd (Multiplicative.ofAdd.injective this) (by decide)

theorem y322Central_check :
    eqA 728 (ModelNative.evalW 728 y322Arrays y322WordF1)
      (ModelNative.evalW 728 y322Arrays y322WordF2) = true ∧
    (∀ c < 8, eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [c]))
      (ModelNative.evalW 728 y322Arrays (c :: y322WordF1)) = true) ∧
    eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ y322WordF1))
      (ModelNative.evalW 728 y322Arrays []) = true :=
  Certificates.certificate10103.1

theorem y322F1_eq_F2 :
    y322F1 = y322F2 :=
  (evalWord_yGen_322_eq_iff _ _).2 y322Central_check.1

theorem y322F1_mul_self :
    y322F1 * y322F1 = 1 := by
  have h := (evalWord_yGen_322_eq_iff (y322WordF1 ++ y322WordF1) []).2 y322Central_check.2.2
  rwa [evalWord_append, evalWord_nil] at h

theorem y322F1_comm_yGen
    {c : ℕ} (hc : c < 8) : yGen 3 2 2 c * y322F1 = y322F1 * yGen 3 2 2 c := by
  have h := (evalWord_yGen_322_eq_iff (y322WordF1 ++ [c]) (c :: y322WordF1)).2
    (y322Central_check.2.1 c hc)
  rw [evalWord_append, evalWord_cons, evalWord_cons, evalWord_nil, mul_one] at h
  exact h.symm


end CFSG.YGroups
