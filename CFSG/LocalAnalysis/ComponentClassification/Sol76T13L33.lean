module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props33C
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma316

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

omit [Finite G] in
theorem conjugate_conjugate_mul (H : Subgroup G) (a b : G) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    show a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ by group]


omit [Finite G] in
theorem conjugate_one' (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem exists_orderOf_eq_two_of_isTwoComponentIn {X C : Subgroup G} (hX : IsTwoComponentIn X C) :
    ∃ b ∈ X, orderOf b = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) := isQuasisimple_quotient_of_isPComponent hX.1 hX.2
  by_contra hno
  push Not at hno
  have hodd : Odd (Nat.card ↥X) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have := Fintype.ofFinite ↥X
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥X) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    exact hno x x.2 (by rw [orderOf_coe]; exact hx)
  have htop : pPrimeCore 2 ↥X = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨inferInstance, by rw [card_top]; exact Nat.coprime_two_left.mpr hodd⟩)
  have hnt : Nontrivial (↥X ⧸ pPrimeCore 2 ↥X) := LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨y, z, hyz⟩ := hnt.exists_pair_ne
  induction y using QuotientGroup.induction_on with
  | H y =>
  induction z using QuotientGroup.induction_on with
  | H z =>
  apply hyz
  rw [QuotientGroup.eq, htop]
  exact mem_top _

theorem eq_or_eq_of_le_sup {C X P P' : Subgroup G} (hX : IsTwoComponentIn X C)
    (hP : IsTwoComponentIn P C) (hP' : IsTwoComponentIn P' C) (hle : X ≤ P ⊔ P') :
    X = P ∨ X = P' := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hPX : P ≤ coreActionKernel X := GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hP.1 hX.2 hP.2 h1
  have hP'X : P' ≤ coreActionKernel X :=
    GSThmB.B5a.le_coreActionKernel_of_ne hX.1 hP'.1 hX.2 hP'.2 h2
  have hperf : ⁅X, X⁆ = X := UnbalancedCorr.commutator_eq_of_isPComponent hX.1 hX.2
  exact not_le_coreActionKernel_of_le le_rfl hperf (exists_orderOf_eq_two_of_isTwoComponentIn hX)
    (hle.trans (sup_le hPX hP'X))


end CFSG.ComponentClassification.Sol76T13
