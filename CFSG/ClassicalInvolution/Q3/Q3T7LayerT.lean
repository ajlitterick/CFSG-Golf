module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ
public import CFSG.ClassicalInvolution.Q3.Q3T7SectB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Disc3

section Gen

theorem omegaGen_oddQuotientFamily3 {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}
    (hgen : omegaGen Λ = ⊤) : omegaGen (oddQuotientFamily Λ) = ⊤ :=
  CFSG.ClassicalInvolution.Asc77.omegaGen_oddQuotientFamily hgen

end Gen

section Convert


variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}


end Convert

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {c : G}

theorem omegaGen_layerFam3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) : omegaGen (layerFam3 Ω c) = ⊤ :=
  omegaGen_oddQuotientFamily3 (Λ := exactPair3 Ω c)
    (inClass3_exactPair3 (inClass3_of_stand3 hs) hc2 hne).generated


end Layer

end CFSG.ClassicalInvolution.Q3.Q3T7
