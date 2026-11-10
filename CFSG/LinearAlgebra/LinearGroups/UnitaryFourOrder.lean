module

public import CFSG.Fischer.F4
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

section StdForm

variable {p f : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def stdHermForm (h : UnitaryFieldData p f K) (n : ℕ) :
    (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun x y => ∑ i, h.bar (x i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_left_comm])

theorem stdHermForm_apply (h : UnitaryFieldData p f K) (n : ℕ) (x y : Fin n → K) :
    stdHermForm h n x y = ∑ i, h.bar (x i) * y i :=
  rfl

theorem stdHermForm_isSymm (h : UnitaryFieldData p f K) (n : ℕ) : (stdHermForm h n).IsSymm :=
  ⟨fun x y => by
    simp only [stdHermForm_apply, map_sum, map_mul, h.bar_bar]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

theorem stdHermForm_single (h : UnitaryFieldData p f K) (n : ℕ) (i : Fin n) (y : Fin n → K) :
    stdHermForm h n (Pi.single i 1) y = y i := by
  rw [stdHermForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem stdHermForm_separatingLeft (h : UnitaryFieldData p f K) (n : ℕ) :
    (stdHermForm h n).SeparatingLeft := by
  intro x hx
  funext j
  have := hx (Pi.single j 1)
  rw [stdHermForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at this
  simpa [h.bar_eq_zero_iff] using this

end StdForm

open CFSG.Fischer

theorem unitaryFieldData_F4 : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num⟩


end CFSG.LinearGroups
