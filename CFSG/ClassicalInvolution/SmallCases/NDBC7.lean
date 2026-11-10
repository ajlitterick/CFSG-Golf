module

public import CFSG.ClassicalInvolution.SmallCases.NDBC6
import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

section Counting

theorem card_eq_two_of {n : ℕ} {a b : Fin n} (hab : a ≠ b) (h : ∀ i : Fin n, i = a ∨ i = b) :
    n = 2 := by
  have ha := a.2
  have hb := b.2
  have hne : a.val ≠ b.val := fun e => hab (Fin.ext e)
  by_contra hn
  have h3 : 3 ≤ n := by omega
  obtain ⟨k, hk, hka, hkb⟩ : ∃ k, k < 3 ∧ k ≠ a.val ∧ k ≠ b.val := by
    by_cases h0 : a.val = 0 ∨ b.val = 0
    · by_cases h1 : a.val = 1 ∨ b.val = 1
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega⟩
  rcases h ⟨k, by omega⟩ with e | e
  · exact hka (congrArg Fin.val e)
  · exact hkb (congrArg Fin.val e)

theorem card_eq_three_of {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ i : Fin n, i = a ∨ i = b ∨ i = c) : n = 3 := by
  have ha := a.2
  have hb := b.2
  have hc := c.2
  have h1 : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have h2 : a.val ≠ c.val := fun e => hac (Fin.ext e)
  have h3 : b.val ≠ c.val := fun e => hbc (Fin.ext e)
  by_contra hn
  have h4 : 4 ≤ n := by omega
  obtain ⟨k, hk, hka, hkb, hkc⟩ : ∃ k, k < 4 ∧ k ≠ a.val ∧ k ≠ b.val ∧ k ≠ c.val := by
    by_cases e0 : a.val = 0 ∨ b.val = 0 ∨ c.val = 0
    · by_cases e1 : a.val = 1 ∨ b.val = 1 ∨ c.val = 1
      · by_cases e2 : a.val = 2 ∨ b.val = 2 ∨ c.val = 2
        · exact ⟨3, by omega, by omega, by omega, by omega⟩
        · exact ⟨2, by omega, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega, by omega⟩
  rcases h ⟨k, by omega⟩ with e | e | e
  · exact hka (congrArg Fin.val e)
  · exact hkb (congrArg Fin.val e)
  · exact hkc (congrArg Fin.val e)

theorem two_le_of_psl {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .PSL) : 2 ≤ n := by
  subst ht
  exact hadm.2.2.1

theorem three_le_of_psu {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .PSU) : 3 ≤ n := by
  subst ht
  exact hadm.2.2.1

end Counting

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem A1_member_twin (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin C.D.card}
    (hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2)) {i₀ : Fin C.D.card}
    (hi₀ : C.D.tag i₀ = .PSL ∧ C.D.rank i₀ = 2)
    (hK₀ : modOdd z (exactCore z C.K) = (C.psi i₀).range) {i : Fin C.D.card}
    (hi : C.D.tag i = .PSL ∧ C.D.rank i = 2) (hii₀ : i ≠ i₀) :
    ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z ∧ modOdd z T = (C.psi i).range := by
  obtain ⟨R, hR, N, hN, hNR⟩ := exists_member_of_meets C i
  rw [C.fund_eq_top i hi hR, Subgroup.map_top] at hNR
  obtain ⟨n, hn⟩ := C.hΩ.classical N hN.1
  have hnz : n = z := eq_z_of_le_A1 C hnoF hQ hN hn hi (le_of_eq hNR)
  rw [hnz] at hn
  have hNe : exactCore z N = N := exactCore_eq_self hn.perfect (isSubnormal_le hn.subnormal)
  refine ⟨N, hN.1, fun h => ?_, hn, by rw [← hNe, hNR]⟩
  have hz₀ : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₀).range := by
    rw [← hK₀, C.exactCore_K]
    exact oddQuotMk_mem_modOdd C.K_cl.mem _
  apply ne_range_of_A1 C (Ne.symm hii₀) hi₀ hz₀
  rw [← hK₀, ← hNR, h]

theorem exists_triangle_plus {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (ht : t = .POmegaPlus) (hn : n = 4) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K} (hR : R ∈ RouteD.ModelFund p t n e) :
    ∃ R₂ ∈ RouteD.ModelFund p t n e, ∃ R₃ ∈ RouteD.ModelFund p t n e, R ≠ R₂ ∧ R ≠ R₃ ∧
      R₂ ≠ R₃ ∧ Commutes R R₂ ∧ Commutes R R₃ ∧ Commutes R₂ R₃ := by
  subst ht hn
  obtain ⟨R₂, h₂, R₃, h₃, -, -, n12, n13, -, n23, -, -, c12, c13, -, c23, -⟩ :=
    Asc77.MuTab.clique_plus hp2 hq hadm hR
  exact ⟨R₂, h₂, R₃, h₃, n12, n13, n23, c12, c13, c23⟩


end Shape

end Cover

end CFSG.ClassicalInvolution.NDB
