module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationRoots
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.CurtisTits

section RootDatum

variable {K : Type*} [Group K] {X : Type*} [Group X]

theorem iSup_rankOne_eq_top (D : UniversalRootDatum K) {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H) :
    ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤ := by
  have h := iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem D.isFiniteType D.divisible) hct
  rw [eq_top_iff, ← h]
  refine iSup_le fun J => ?_
  exact iSup₂_le fun j _ => le_iSup (fun i => rankOne D.rootGroup i) j

theorem single_mem_roots (D : UniversalRootDatum K) (i : Fin D.rank) :
    (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (CFSG.LieType.RootSystem.isCTRootSystem D.isFiniteType D.divisible).single_mem i

theorem iSup_rankOneRoot_simple_eq_top (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (g : (modelUniv t n p e hp).K) :
    ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOneRoot (modelUniv t n p e hp).D g (Pi.single i 1) = ⊤ := by
  obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e hp hfund hadm
  have h : ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOne (modelUniv t n p e hp).D.rootGroup i = ⊤ := iSup_rankOne_eq_top _ hct
  refine eq_top_iff.mpr ?_
  have hmap : (⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOne (modelUniv t n p e hp).D.rootGroup i).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [← hmap, Subgroup.map_iSup]
  exact le_rfl

theorem iSup_rankOneImage_simple_eq_range (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (ψ : (modelUniv t n p e hp).K →* X)
    (g : (modelUniv t n p e hp).K) :
    ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOneImage (modelUniv t n p e hp).D ψ g (Pi.single i 1) = ψ.range := by
  rw [MonoidHom.range_eq_map, ← iSup_rankOneRoot_simple_eq_top t n p e hp hfund hadm g,
    Subgroup.map_iSup]
  rfl

end RootDatum

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

section Criterion

variable {X : Type} [Group X] [Finite X]


end Criterion


noncomputable abbrev compModel {a : G} (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) :
    LieUniversal :=
  modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out


end Provider

end CFSG.ClassicalInvolution.Balance
