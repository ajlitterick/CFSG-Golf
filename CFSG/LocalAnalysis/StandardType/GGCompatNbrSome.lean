module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Case

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveLeviCase (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  (∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K) ∨
    (∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K) ∨
    (∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeCNbr p B Bs x L D J n f y K)

theorem GGTypeASplitConfig.exists_typeANbr {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} (h : GGTypeASplitConfig p B Bs x L D J n f) :
    ∃ (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K := by
  obtain ⟨hmod, hpq, hn, -, hsc, y, K, hnbr, hmodK, hW⟩ := h
  exact ⟨y, K, hmod, hpq, hn, hsc, hnbr, hmodK, hW⟩

theorem GGTypeASplitConfig.leviCase {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (h : GGTypeASplitConfig p B Bs x L D J n f) : GGSecFiveLeviCase p B Bs x L D J := by
  obtain ⟨y, K, hN⟩ := h.exists_typeANbr
  exact Or.inl ⟨n, f, y, K, hN⟩

end Case

section Inputs

@[expose] def GGSecFiveCompatRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ¬ GGSecFiveLeviCase p B Bs x L D J → GGSecFiveCompat p B x L D J


end Inputs

section Main


end Main

end CFSG.StandardType
