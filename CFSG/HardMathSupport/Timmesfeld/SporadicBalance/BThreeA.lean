module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodes
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster CFSG.Monster.B
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem mem_pow_mul_of_card_le [Finite G] {C Q : Subgroup G} {s : G} (hsC : s ∈ C)
    (hQC : Q ≤ C) (hs3 : s * s * s = 1) (hsQ : s ∉ Q) (hcard : Nat.card C ≤ 3 * Nat.card Q) :
    ∀ g ∈ C, ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q := by
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  have hsq : ∀ k : Fin 3, s ^ (k : ℕ) * 1 ∈ C := fun k => C.mul_mem (C.pow_mem hsC _) C.one_mem
  let f : Fin 3 × Q → C := fun p => ⟨s ^ (p.1 : ℕ) * p.2, C.mul_mem (C.pow_mem hsC _) (hQC p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨k, q⟩ ⟨k', q'⟩ h
    have h1 : s ^ (k : ℕ) * (q : G) = s ^ (k' : ℕ) * q' := congrArg Subtype.val h
    have h2 : (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) = q' * (q : G)⁻¹ := by
      calc (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) = (s ^ (k' : ℕ))⁻¹ * (s ^ (k : ℕ) * q) * (q : G)⁻¹ := by
            group
        _ = (s ^ (k' : ℕ))⁻¹ * (s ^ (k' : ℕ) * q') * (q : G)⁻¹ := by rw [h1]
        _ = q' * (q : G)⁻¹ := by group
    have hmem : (s ^ (k' : ℕ))⁻¹ * s ^ (k : ℕ) ∈ Q := by
      rw [h2]; exact Q.mul_mem q'.2 (Q.inv_mem q.2)
    have hpow : ∀ m : ℕ, s ^ m ∈ Q → m % 3 = 0 := by
      intro m hm
      have e : s ^ m = s ^ (m % 3) := by
        conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hs3', one_pow, one_mul]
      rw [e] at hm
      have h012 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases h012 with h | h | h
      · exact h
      · rw [h, pow_one] at hm
        exact absurd hm hsQ
      · exfalso
        apply hsQ
        rw [h] at hm
        have h4 : s = s ^ 2 * s ^ 2 := by
          rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hs3', one_mul, pow_one]
        rw [h4]
        exact Q.mul_mem hm hm
    have hinv : (s ^ (k' : ℕ))⁻¹ = s ^ (2 * (k' : ℕ)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (k' : ℕ) + 2 * k' = 3 * k' by ring, pow_mul, hs3', one_pow]
    rw [hinv, ← pow_add] at hmem
    have h3 := hpow _ hmem
    have hk := k.2
    have hk' := k'.2
    have hkk : k = k' := Fin.ext (by omega)
    subst hkk
    have hq : (q : G) = q' := by
      have := h1
      simpa using this
    exact Prod.ext rfl (Subtype.ext hq)
  have hcardf : Nat.card (Fin 3 × Q) = 3 * Nat.card Q := by
    rw [Nat.card_prod, Nat.card_fin]
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hcardf]; exact hcard)
  intro g hg
  obtain ⟨⟨k, q⟩, hkq⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨k, q, q.2, (congrArg Subtype.val hkq).symm⟩


end Generic

section Labels


@[expose] def BThreeABound : Prop :=
  ∀ v w : CVert, w ∈ sphereThree v →
    Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat)

theorem commute_of_mem_vStab {v : CVert} {q : Shat} (hq : q ∈ vStab v) :
    q * clabelS v = clabelS v * q := by
  have h := clabelS_cvMul v q
  rw [mem_vStab.1 hq] at h
  calc q * clabelS v = q * (q⁻¹ * clabelS v * q) := by rw [← h]
    _ = clabelS v * q := by group

end Labels

section ThreeA


@[expose] def BThreeCensus : Prop :=
  ∀ s : Shat, orderOf s = 3 →
    (∃ v w : CVert, w ∈ sphereThree v ∧ IsConj s (clabelS v * clabelS w)) ∨
      3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set Shat))


end ThreeA

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
