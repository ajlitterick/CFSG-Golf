module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup


variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem le_of_isPGroup_of_not_dvd_relIndex {A C Q : Subgroup X} (hA : IsPGroup p A)
    (hAC : A ≤ C) (hidx : ¬ p ∣ A.relIndex C) (hQ : IsPGroup p Q) (hQC : Q ≤ C)
    (hQA : Q ≤ normalizer (A : Set X)) : Q ≤ A := by
  have hR : IsPGroup p ↥(Q ⊔ A) := hQ.to_sup_of_normal_right' hA hQA
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : A.relIndex (Q ⊔ A) ∣ p ^ k := hk ▸ (A.subgroupOf (Q ⊔ A)).index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have hmul := relIndex_mul_relIndex A (Q ⊔ A) C le_sup_right (sup_le hQC hAC)
  have hj0 : j = 0 := by
    by_contra hj0
    refine hidx ((dvd_pow_self p hj0).trans ?_)
    rw [← hj, ← hmul]
    exact dvd_mul_right _ _
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact le_sup_left.trans hj

omit [Finite X] in
theorem le_normalizer_centralizer {A K : Subgroup X} (hK : K ≤ normalizer (A : Set X)) :
    K ≤ normalizer (centralizer (A : Set X) : Set X) := by
  intro g hg
  have hgA := mem_normalizer_iff.1 (hK hg)
  rw [mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hc a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      refine (hgA (g⁻¹ * a * g)).2 ?_
      simpa [mul_assoc] using ha
    have h := hc _ ha'
    calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * a := by group
  · intro hc a ha
    have h := hc _ ((hgA a).1 ha)
    calc a * c = g⁻¹ * ((g * a * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = c * a := by group


end CFSG.GroupTheory.FT63ChII
