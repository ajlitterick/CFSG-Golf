module

public import CFSG.Quasithin.Background.C1PackS15368
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.C1PackS15349
public import CFSG.Quasithin.EmptyFaithful.T1531In47
public import CFSG.Quasithin.EmptyFaithful.T1531In62
public import CFSG.Quasithin.EmptyFaithful.T1531In63
public import CFSG.Quasithin.EmptyFaithful.T1531In66b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F6

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ : Subgroup G}

theorem IsGoldschmidtTripleIn.f6_18Cat (hF : TheoremF618Cat) (h : IsGoldschmidtTripleIn I G₁ G₂)
    (hsq : SQTKTauCeti.StronglyQuasithin ↥I) (hK : CFSG.SectionRank.IsKGroupCat ↥I) :
    ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
          (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
        (G₁.subgroupOf I ⊓ G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
      IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      IsAmalgamIso ((G₁.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      F618ConclusionCat ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) ∨
    (pCoreOf 2 (G₁.subgroupOf I) = Open.pCore 2 ↥I ∧
      pCoreOf 2 (G₂.subgroupOf I) = Open.pCore 2 ↥I ∧
      Nonempty (↥I ⧸ CFSG.pPrimeCore 3 ↥I ≃* Equiv.Perm (Fin 3)) ∧
      G₁.subgroupOf I ⊔ CFSG.pPrimeCore 3 ↥I = ⊤ ∧
      ¬ IsCyclic ↥((CFSG.pPrimeCore 3 ↥I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))) := by
  rcases h.goldschmidt_mod_pPrimeCore with ⟨h₁, h₂, h₃⟩ | h'
  · exact Or.inl ⟨h₁, h₂, h₃, hF _ _ _ h₂.toIsGoldschmidtTriple
      ⟨↥I, inferInstance, inferInstance,
        ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hsq, hK⟩, ⟨MulEquiv.refl _⟩⟩⟩
  · exact Or.inr h'

end F6


section Cases


end Cases


section Geometry


end Geometry


end CFSG.Quasithin
