module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}


@[expose] def pairVec (a b : Fin n → ZMod 2) : PairN n :=
  (Multiplicative.ofAdd a, Multiplicative.ofAdd b)

theorem pairVec_mul (a b a' b' : Fin n → ZMod 2) :
    pairVec a b * pairVec a' b' = pairVec (a + a') (b + b') := by
  rfl


theorem pairVec_surj (x : PairN n) : ∃ a b : Fin n → ZMod 2, x = pairVec a b :=
  ⟨x.1.toAdd, x.2.toAdd, by ext <;> simp [pairVec]⟩

theorem pairVec_inj {a b a' b' : Fin n → ZMod 2} :
    pairVec a b = pairVec a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    rw [pairVec, pairVec, Prod.ext_iff] at h
    exact ⟨Multiplicative.ofAdd.injective h.1, Multiplicative.ofAdd.injective h.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl


theorem dualGLn_dualGLn (A : GL (Fin n) (ZMod 2)) : dualGLn n (dualGLn n A) = A := by
  apply Units.ext
  change ((((dualGLn n A)⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ = ((A : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))
  rw [show (((dualGLn n A)⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ from rfl,
    Matrix.transpose_transpose]

theorem pairActN_pairVec (A : GL (Fin n) (ZMod 2)) (a b : Fin n → ZMod 2) :
    pairActN n A (pairVec a b) =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
        (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) := by
  rfl

theorem swapN_pairVec (a b : Fin n → ZMod 2) : swapN n (pairVec a b) = pairVec b a := by
  rfl


theorem swapN_mul_self : swapN n * swapN n = 1 := by
  apply MulEquiv.ext
  intro x
  rfl

theorem swapN_inv : (swapN n)⁻¹ = swapN n :=
  inv_eq_of_mul_eq_one_right (swapN_mul_self (n := n))

theorem swapN_mul_pairActN (A : GL (Fin n) (ZMod 2)) :
    swapN n * pairActN n A = pairActN n (dualGLn n A) * swapN n := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  simp only [MulAut.mul_apply, pairActN_pairVec, swapN_pairVec, dualGLn_dualGLn]

private theorem swap_mul_pairAct_mul_swap (A : GL (Fin n) (ZMod 2)) :
    swapN n * pairActN n A * swapN n = pairActN n (dualGLn n A) := by
  rw [swapN_mul_pairActN, mul_assoc, swapN_mul_self, mul_one]

theorem pairActN_injective : Function.Injective (pairActN n) := by
  intro A B h
  have h1 : ∀ a : Fin n → ZMod 2,
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a =
        (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a := by
    intro a
    have h2 := congrArg (fun e : MulAut (PairN n) => e (pairVec a 0)) h
    simp only [pairActN_pairVec, Matrix.mulVec_zero] at h2
    exact (pairVec_inj.mp h2).1
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun j => h1 (Pi.single j 1)

theorem mem_Lg_iff {g : MulAut (PairN n)} : g ∈ Lg n ↔ ∃ A : GL (Fin n) (ZMod 2), pairActN n A = g := by
  rw [Lg, MonoidHom.mem_range]

theorem pairActN_mem_Lg (A : GL (Fin n) (ZMod 2)) : pairActN n A ∈ Lg n := by
  rw [mem_Lg_iff]
  exact ⟨A, rfl⟩


private theorem mem_zpowers_swapN {z : MulAut (PairN n)}
    (hz : z ∈ Subgroup.zpowers (swapN n)) : z = 1 ∨ z = swapN n := by
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [← hk]
  have h2 : (swapN n) ^ (2 : ℕ) = 1 := by
    rw [pow_two, swapN_mul_self]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem mem_Mg_iff {g : MulAut (PairN n)} :
    g ∈ Mg n ↔ g ∈ Lg n ∨ ∃ A : GL (Fin n) (ZMod 2), g = pairActN n A * swapN n := by
  have hnorm : Subgroup.zpowers (swapN n) ≤
      Subgroup.normalizer ((Lg n : Set (MulAut (PairN n)))) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh l hl
    rcases mem_zpowers_swapN hh with rfl | rfl
    · simpa using hl
    · rw [mem_Lg_iff] at hl
      obtain ⟨B, rfl⟩ := hl
      rw [swapN_inv, swap_mul_pairAct_mul_swap]
      exact pairActN_mem_Lg _
  have hset : g ∈ (Lg n ⊔ Subgroup.zpowers (swapN n) : Subgroup (MulAut (PairN n))) ↔
      ∃ l ∈ (Lg n : Set (MulAut (PairN n))),
        ∃ z ∈ (Subgroup.zpowers (swapN n) : Set (MulAut (PairN n))), l * z = g := by
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left (Lg n) (Subgroup.zpowers (swapN n)) hnorm,
      Set.mem_mul]
  rw [Mg, hset]
  constructor
  · rintro ⟨l, hl, z, hz, hgz⟩
    rcases mem_zpowers_swapN hz with rfl | rfl
    · left
      rw [← hgz, mul_one]
      exact hl
    · right
      change l ∈ Lg n at hl
      rw [mem_Lg_iff] at hl
      obtain ⟨A, rfl⟩ := hl
      exact ⟨A, hgz.symm⟩
  · rintro (hg | ⟨A, rfl⟩)
    · exact ⟨g, hg, 1, Subgroup.one_mem _, mul_one g⟩
    · exact ⟨pairActN n A, pairActN_mem_Lg A, swapN n, Subgroup.mem_zpowers _, rfl⟩


end CFSG.ASVolI.ChH
