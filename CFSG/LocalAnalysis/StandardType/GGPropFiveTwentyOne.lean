module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Input

@[expose] def GGSecFiveDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      (∃ m k f : ℕ, 4 ≤ k ∧ k ≤ m ∧ 1 ≤ f ∧ GGSecFiveTypeA p B x L D J m k f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFiveLocal p B x L D J t n f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFivePres p B x L D J t n f)

end Input

section Wiring

theorem ggPropFiveTwentyOneV2Input_of_data (h : GGSecFiveDataInput) :
    GGPropFiveTwentyOneV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW
  rcases h G p B Bs x L D J hcfg hOp hInn hNoTr hW with ⟨m, k, f, hk, hkm, hf, hA⟩ |
    ⟨t, n, f, hloc⟩ | ⟨t, n, f, hpres⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_typeA hk hkm hf hA
    exact ⟨.PSL, m + 1, f, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_secFivePres (ggSecFivePres_of_local hloc)
    exact ⟨t, n, f, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_secFivePres hpres
    exact ⟨t, n, f, ψ, hψ⟩

end Wiring

section Assembly


end Assembly

end CFSG.StandardType
