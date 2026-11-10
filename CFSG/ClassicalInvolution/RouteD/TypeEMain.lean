module

public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeERecognition
public import CFSG.ClassicalInvolution.RouteD.TypeEFive

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers LieSystemData)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerAt (p f : ℕ) [Fact p.Prime] {r : ℕ} (Ω : Set (Subgroup G))
    (j : Fin r → Subgroup G) (k : Fin r) : Prop :=
  ∃ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j k)) ∧
    ∀ a, a ≠ k → Commutes β (j a)

section Residual

variable (p f) (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G)


end Residual

section ChainE6

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}


end ChainE6

section ChainE7

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem chainE7_of_partner {j : Fin 6 → Subgroup G}
    (hj : NodeSystem p f (edgeD 6) Ω K z j) (hβ : PartnerAt p f Ω j 4) :
    ∃ U : Fin 7 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 7, edgeE 7 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  obtain ⟨β, hβΩ, ⟨W₀, hW₀⟩, hβc⟩ := hβ
  have hD : ∀ a b : Fin 6, a ≠ b → ¬ edgeD 6 a b → ¬ edgeD 6 b a → Commutes (j a) (j b) :=
    hj.comm
  have hP : ∀ a b : Fin 6, edgeD 6 a b →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (j b) (j a) :=
    fun a b h => by
      obtain ⟨W, hW⟩ := hj.pair a b h
      exact ⟨W, hW.symm⟩
  refine ⟨![β, j 5, j 4, j 3, j 2, j 1, j 0], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hβΩ
    all_goals exact (hj.mem _).1
  · intro i k hik h1 h2
    have b0 := hβc 0 (by decide)
    have b1 := hβc 1 (by decide)
    have b2 := hβc 2 (by decide)
    have b3 := hβc 3 (by decide)
    have b5 := hβc 5 (by decide)
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1 h2 ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact b1 | exact b1.symm | exact b2 | exact b2.symm
      | exact b3 | exact b3.symm | exact b5 | exact b5.symm
      | exact hD _ _ (by decide) (by decide) (by decide)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact ⟨W₀, hW₀⟩
      | exact hP _ _ (by decide)

end ChainE7

section ChainE8

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem chainE8_of_partner {j : Fin 7 → Subgroup G}
    (hj : NodeSystem p f (edgeE 7) Ω K z j) (hβ : PartnerAt p f Ω j 6) :
    ∃ U : Fin 8 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 8, edgeE 8 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  obtain ⟨β, hβΩ, ⟨W₀, hW₀⟩, hβc⟩ := hβ
  have hD : ∀ a b : Fin 7, a ≠ b → ¬ edgeE 7 a b → ¬ edgeE 7 b a → Commutes (j a) (j b) :=
    hj.comm
  refine ⟨![j 0, j 1, j 2, j 3, j 4, j 5, j 6, β], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    all_goals first | exact hβΩ | exact (hj.mem _).1
  · intro i k hik h1 h2
    have b0 := hβc 0 (by decide)
    have b1 := hβc 1 (by decide)
    have b2 := hβc 2 (by decide)
    have b3 := hβc 3 (by decide)
    have b4 := hβc 4 (by decide)
    have b5 := hβc 5 (by decide)
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1 h2 ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact b1 | exact b1.symm | exact b2 | exact b2.symm
      | exact b3 | exact b3.symm | exact b4 | exact b4.symm | exact b5 | exact b5.symm
      | exact hD _ _ (by decide) (by decide) (by decide)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact hj.pair _ _ (by decide)
      | exact ⟨W₀, hW₀.symm⟩

end ChainE8


section Relabel

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem NodeSystem.comp_equiv {r : ℕ} {adj : Fin r → Fin r → Prop} {j : Fin r → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j) (σ : Equiv.Perm (Fin r))
    (hσ : ∀ a b, adj (σ a) (σ b) ↔ adj a b) :
    NodeSystem p f adj Ω K z (j ∘ σ) where
  mem a := hj.mem (σ a)
  ne_K a := hj.ne_K (σ a)
  commK a := hj.commK (σ a)
  comm a b hab h1 h2 := hj.comm (σ a) (σ b) (fun e => hab (σ.injective e))
    (fun h => h1 ((hσ a b).mp h)) (fun h => h2 ((hσ b a).mp h))
  pair a b h := hj.pair (σ a) (σ b) ((hσ a b).mpr h)

theorem PartnerAt.comp_equiv {r : ℕ} {j : Fin r → Subgroup G} {k : Fin r}
    (σ : Equiv.Perm (Fin r)) (h : PartnerAt p f Ω j (σ k)) : PartnerAt p f Ω (j ∘ σ) k := by
  obtain ⟨β, hβ, hW, hc⟩ := h
  exact ⟨β, hβ, hW, fun a ha => hc (σ a) (fun e => ha (σ.injective e))⟩

theorem edgeD6_swap : ∀ a b : Fin 6, edgeD 6 (Equiv.swap (4 : Fin 6) 5 a) (Equiv.swap 4 5 b) ↔
    edgeD 6 a b := by
  decide

end Relabel

section Main


end Main

end CFSG.ClassicalInvolution.RouteD
