module

public import CFSG.ClassicalInvolution.Balance.WeakFrame.Frame

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section SquareRoot

variable {H : Type*} [Group H]


end SquareRoot

variable {F : Type*} [Field F] {G : Type*} [Group G] {E K : Subgroup G}

namespace WeakInSigma

theorem mul_mem_axis (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) (hx' : x ∉ axisSub E K) (hy' : y ∉ axisSub E K) : x * y ∈ axisSub E K := by
  obtain ⟨a, haE, haN, hsplit⟩ := hK.exists_split
  have hxa : x * a ∈ axisSub E K := (hsplit x hx).resolve_left hx'
  have hya : y * a ∈ axisSub E K := (hsplit y hy).resolve_left hy'
  have h4 := (axisSub E K).mul_mem hxa hya
  have e1 : x * a * (y * a) = x * y := by
    calc x * a * (y * a) = x * (a * y) * a := by group
      _ = x * (y * a) * a := by rw [comm_of_sq_eq_one hE haE hy]
      _ = x * y * (a * a) := by group
      _ = x * y := by rw [hE a haE, mul_one]
  rwa [e1] at h4

variable [Finite G]

theorem conj_eq_mul_of_not_mem_axis (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1)
    (hodd : Odd (Nat.card F)) {z : G} (hz : IsCentralInvolution K z) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) {x : G} (hx : x ∈ E)
    (hx' : x ∉ axisSub E K) : w * x * w⁻¹ = x * z := by
  obtain ⟨φ, hφ, -, -⟩ := hK.chart
  have hwK : w ∈ K := (mem_normPart_iff.mp hw).1
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  have hyE : w * x * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hwN x).mp hx
  have hcE : w * x * w⁻¹ * x⁻¹ ∈ E := E.mul_mem hyE (E.inv_mem hx)
  have hcK : w * x * w⁻¹ * x⁻¹ ∈ K := by
    have := K.mul_mem hwK (hK.normalizes x hx w⁻¹ (K.inv_mem hwK))
    have e : w * (x * w⁻¹ * x⁻¹) = w * x * w⁻¹ * x⁻¹ := by group
    rwa [e] at this
  have hcsq : w * x * w⁻¹ * x⁻¹ * (w * x * w⁻¹ * x⁻¹) = 1 := hE _ hcE
  rcases hφ.eq_one_or_eq_of_sq hodd hz hcK hcsq with h | h
  · exfalso
    have hxc : w * x = x * w := by
      have : w * x * w⁻¹ = x := by
        calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
          _ = x := by rw [h, one_mul]
      calc w * x = (w * x * w⁻¹) * w := by group
        _ = x * w := by rw [this]
    apply hw'
    rw [mem_centPart_iff]
    refine ⟨hwK, fun e he => ?_⟩
    by_cases hea : e ∈ axisSub E K
    · exact ((mem_axisSub_iff.mp hea).2 w hwK).symm
    · have hexa : e * x ∈ axisSub E K := hK.mul_mem_axis hE he hx hea hx'
      have h1 : w * (e * x) = (e * x) * w := ((mem_axisSub_iff.mp hexa).2 w hwK)
      have hxx : x * x = 1 := hE x hx
      have : w * e = e * w := by
        calc w * e = w * (e * x) * x := by
              calc w * e = w * e * (x * x) := by rw [hxx, mul_one]
                _ = w * (e * x) * x := by group
          _ = (e * x) * w * x := by rw [h1]
          _ = (e * x) * (w * x) := by group
          _ = (e * x) * (x * w) := by rw [hxc]
          _ = e * (x * x) * w := by group
          _ = e * w := by rw [hxx, mul_one]
      exact this.symm
  · have hzE : z ∈ E := by rw [← h]; exact hcE
    calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
      _ = z * x := by rw [h]
      _ = x * z := comm_of_sq_eq_one hE hzE hx

theorem conj_inv_eq (hK : WeakInSigma F E K) (hE : ∀ x ∈ E, x * x = 1)
    (hodd : Odd (Nat.card F)) {z : G} (hz : IsCentralInvolution K z) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) {x : G} (hx : x ∈ E) :
    w⁻¹ * x * w = w * x * w⁻¹ := by
  have hwK : w ∈ K := (mem_normPart_iff.mp hw).1
  have hwz : w * z * w⁻¹ = z := by
    have := hz.central w hwK
    calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [this]
      _ = z := by group
  have key : w * (w * x * w⁻¹) * w⁻¹ = x := by
    by_cases hxa : x ∈ axisSub E K
    · have : w * x * w⁻¹ = x := InSigma.conj_eq_of_mem_axis hwK hxa
      rw [this, this]
    · have h1 := hK.conj_eq_mul_of_not_mem_axis hE hodd hz hw hw' hx hxa
      rw [h1]
      calc w * (x * z) * w⁻¹ = (w * x * w⁻¹) * (w * z * w⁻¹) := by group
        _ = x * z * z := by rw [h1, hwz]
        _ = x := by
          have hzz : z * z = 1 := hz.sq
          rw [mul_assoc, hzz, mul_one]
  calc w⁻¹ * x * w = w⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * w := by rw [key]
    _ = w * x * w⁻¹ := by group


end WeakInSigma

end CFSG.ClassicalInvolution.Balance
