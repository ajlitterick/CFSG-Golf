module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOne
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.RankThree.PartTwo.Sec21 Matrix

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveAllAJoin (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ e : (CoxeterMatrix.A m).Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      ∀ i, GGIsReflection p ((e ((CoxeterMatrix.A m).simple i) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)

@[expose] def GGTypeASplitConfig (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) : Prop :=
  StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f ∧ p ∣ 2 ^ f - 1 ∧ 3 ≤ n ∧
    ¬ p ∣ n + 3 ∧ GGScalarsPmOne Bs ∧
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 f ∧
      (∃ e : (CoxeterMatrix.A (n + 1)).Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
        ∀ i, GGIsReflection p ((e ((CoxeterMatrix.A (n + 1)).simple i) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) ∧
      GGSecFiveAllAJoin p B Bs x L D J

end Config

@[expose] def GGTypeAEndNodeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
    GGNoTransvection p Bs → GGTypeASplitConfig p B Bs x L D J n f →
    ∀ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      ∃ T : G, T ∈ ggG0 p B x L D J ∧ GGTypeAEndNode φ₁ T ∧
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom

theorem ggSecFiveTypeA_of_endNodeInput (hin : GGTypeAEndNodeInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hA : GGTypeASplitConfig p B Bs x L D J n f) :
    ∃ m k f : ℕ, 4 ≤ k ∧ k ≤ m ∧ 1 ≤ f ∧ GGSecFiveTypeA p B x L D J m k f := by
  obtain ⟨hmod, hpq, hn, -⟩ := id hA
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hf1 : 1 ≤ f := hmod.1.2.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
  obtain ⟨φ₁, hφL, hker⟩ := exists_slLift_of_classicalModel (by omega) hf (by omega) hperf hmod
  obtain ⟨T, hTG, hT, hnbr⟩ := hin G p B Bs x L D J n f hcfg hOp hInn hNoTr hA φ₁ hφL hker
  exact ⟨n + 1, n + 1, f, by omega, le_rfl, hf1,
    ggSecFiveTypeA_of_endNode hn hf1 φ₁ hφL hker hT hTG hnbr⟩

section Input

@[expose] def GGSecFiveDataInputRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      (¬ ∃ n f : ℕ, GGTypeASplitConfig p B Bs x L D J n f) →
      (∃ m k f : ℕ, 4 ≤ k ∧ k ≤ m ∧ 1 ≤ f ∧ GGSecFiveTypeA p B x L D J m k f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFiveLocal p B x L D J t n f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFivePres p B x L D J t n f)

theorem ggSecFiveDataInput_of_typeA (hin : GGTypeAEndNodeInput) (hrest : GGSecFiveDataInputRest) :
    GGSecFiveDataInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW
  by_cases hA : ∃ n f : ℕ, GGTypeASplitConfig p B Bs x L D J n f
  · obtain ⟨n, f, hA⟩ := hA
    exact Or.inl (ggSecFiveTypeA_of_endNodeInput hin hcfg hOp hInn hNoTr hA)
  · exact hrest G p B Bs x L D J hcfg hOp hInn hNoTr hW hA

end Input

section Assembly


end Assembly

end CFSG.StandardType
