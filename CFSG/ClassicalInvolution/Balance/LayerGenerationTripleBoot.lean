module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.BootstrapFinal
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_indepTripleOn (hp2 : p ≠ 2) (hf : 0 < f) (h : CoreAssembly.IndepTriple p f Ω) :
    ∃ A : Subgroup G, IndepTripleOn p f Ω A ∧ MemberFamily p f Ω A (frameFamily p f Ω A) := by
  obtain ⟨K, z, hK, hcomm, hel, hcard⟩ := h
  have hKA := triple_centralizes (p := p) (f := f) hK hcomm
  have hmem : ∀ i, K i ∈ frameFamily p f Ω (Subgroup.closure (Set.range z)) := fun i =>
    ⟨(hK i).1, hKA i, z i, Subgroup.subset_closure ⟨i, rfl⟩, (hK i).2⟩
  refine ⟨Subgroup.closure (Set.range z), ⟨K, z, hK, hcomm, rfl, hel, hcard⟩, ?_⟩
  exact
    { elem := hel
      card := hcard
      subset := fun L hL => hL.1
      nonempty := ⟨K 0, hmem 0⟩
      involution := fun L hL => by
        obtain ⟨-, hLA, z', hz'A, hz'⟩ := hL
        exact ⟨z', hz'A, hz', hLA⟩
      generate := by
        apply le_antisymm
        · refine Subgroup.closure_mono ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨K i, hmem i, (hK i).2⟩
        · rw [Subgroup.closure_le]
          rintro w ⟨L, ⟨-, -, z', hz'A, hz'⟩, hw⟩
          have : w = z' := hz'.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution
          rw [this]
          exact hz'A }

end Family

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}
  {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem centralizerGenerationModOTwo_of_triple_of_noF3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationTriple)
    (hM : MemberFamily p f Ω A 𝒦) (hT : IndepTripleOn p f Ω A) (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hF3 : NoComponentOverF3 p f Ω a) :
    CentralizerGenerationModOTwo Ω A a := by
  classical
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (A : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAY : A ≤ centLayer Ω a := by
    rw [hM.generate, Subgroup.closure_le]
    rintro z ⟨K, hK, hz⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact le_centLayer ⟨hM.subset hK, hcen hKA⟩ hz.mem
  obtain ⟨Dsys⟩ := hIH {a} hnc
  obtain ⟨D, hcompD, hbigD⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ Dsys
  have hD := hbigD (hF3 Dsys)
  refine centralizerGenerationModOTwo_of_components hΩ.conjInvariant hM.elem hM.card ha ha1 hAY D
    fun i F' hF' hfaith => ?_
  rcases hD i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | _
  · exfalso
    have hr1 : RankOneAt Ω a (D.Q i) := by
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    have hF'A : F' ≤ A := hF'.1
    have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact hM.elem.2 x hx
    have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
    have hcard : 1 < Nat.card (modOdd a F') := by
      rw [card_modOdd_of_exponent_two (hF'A.trans hAC) fun x hx => hA2 x (hF'A hx), hF'.2]
      norm_num
    have : Nontrivial (modOdd a F') := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨x, hx1⟩ := exists_ne (1 : modOdd a F')
    obtain ⟨k, hk, hkx⟩ := mem_modOdd_iff.mp x.2
    refine hfaith x x.2 (fun h => hx1 (Subtype.ext h)) fun y hy => ?_
    rw [← hkx]
    exact oddQuotMk_centralizes_of_memberFamily hM ha (Or.inr hr1) (hF'A hk) _ y hy
  · obtain ⟨j, hj⟩ := hcompD i
    have h5 : 5 ≤ p ^ Dsys.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) (hF3 Dsys j)
    exact generation_of_triple hmodel hp2 hΩ hT ha hAY Dsys j h5 D i hj.symm hF' hfaith

end Generation

section BootTriple


end BootTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
