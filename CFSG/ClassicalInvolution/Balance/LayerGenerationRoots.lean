module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationToral

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section RootDatum

variable {K : Type*} [Group K] {X : Type*} [Group X]

@[expose] def rankOneRoot (D : UniversalRootDatum K) (g : K) (γ : Fin D.rank → ℤ) : Subgroup K :=
  (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom

@[expose] def rankOneImage (D : UniversalRootDatum K) (ψ : K →* X) (g : K)
    (γ : Fin D.rank → ℤ) : Subgroup X :=
  (rankOneRoot D g γ).map ψ

theorem iSup_rankOneRoot_eq_top (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e)
    (g : (modelUniv t n p e hp).K) :
    ⨆ γ ∈ (modelUniv t n p e hp).D.roots, rankOneRoot (modelUniv t n p e hp).D g γ = ⊤ := by
  obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e hp hfund hadm
  have h : ⨆ γ ∈ (modelUniv t n p e hp).D.roots, (modelUniv t n p e hp).D.rootGroup γ = ⊤ :=
    hct.iSup_eq_top
  refine eq_top_iff.mpr ?_
  have hmap : (⨆ γ ∈ (modelUniv t n p e hp).D.roots,
      (modelUniv t n p e hp).D.rootGroup γ).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [← hmap, Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  exact le_iSup₂_of_le γ hγ (Subgroup.map_mono le_sup_left)

theorem iSup_rankOneImage_eq_range (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (ψ : (modelUniv t n p e hp).K →* X)
    (g : (modelUniv t n p e hp).K) :
    ⨆ γ ∈ (modelUniv t n p e hp).D.roots, rankOneImage (modelUniv t n p e hp).D ψ g γ =
      ψ.range := by
  rw [MonoidHom.range_eq_map, ← iSup_rankOneRoot_eq_top t n p e hp hfund hadm g,
    Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  rw [Subgroup.map_iSup]
  rfl

theorem divisible_eq_empty (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible t n p e)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    (modelUniv t n p e hp).D.divisible = ∅ := by
  have : Fact p.Prime := ⟨hp⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    show (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp).D.divisible = ∅
    rw [CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn]
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)

theorem isLongestRoot_of_mem_roots_simplyLaced (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    {γ : Fin (modelUniv t n p e hp).D.rank → ℤ} (hγ : γ ∈ (modelUniv t n p e hp).D.roots) :
    IsLongestRoot (modelUniv t n p e hp).D γ := by
  have hdiv := divisible_eq_empty t n p e hp hadm ht
  have hlong : ∀ k : Fin (modelUniv t n p e hp).D.rank,
      CFSG.ClassicalInvolution.ModelFacts.IsLongNode t n k.val := by
    intro k
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · have h : CFSG.ClassicalInvolution.ModelFacts.IsLongest
        (modelUniv t n p e hp).D.isFiniteType (modelUniv t n p e hp).D.divisible
        (Pi.single i 1) :=
      CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single t n p e hp hfund hadm i (hlong i)
    exact h.map_weylAction w
  · exfalso
    rw [hdiv] at hi
    exact Set.notMem_empty i hi

end RootDatum

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def componentHom (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card) : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K →* OddQuot a :=
  (layerQuotientHom hΩ.conjInvariant a).comp (D.hom j)


end Members

section Provider


end Provider

end CFSG.ClassicalInvolution.Balance
