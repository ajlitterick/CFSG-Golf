module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Outdiag


theorem largeEvenLabelAll_outdiag_simple {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) := by
  by_cases ht : GGOutdiagTwistedLabel lab
  · rcases ht with ht | ht | ht
    · exact largeEvenLabelAll_outdiag_twE6 ggTwistedE6DiagInput_holds hlab ht
    · exact (largeEvenLabelAll_outdiag_triD4 hlab ht).mono fun _ _ _ _ hO _ _ => hO
    · exact (largeEvenLabelAll_outdiag_twF4' hlab ht).mono fun _ _ _ _ hO _ _ => hO
  · exact (largeEvenLabelAll_outdiag_of_not_twisted hlab ht).mono fun _ _ _ _ hO _ _ => hO

end Outdiag

@[expose] def GGInndiagNormalInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)

section Marking

variable {G : Type} [Group G]

theorem largeEvenMarking_outdiag_inndiag {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    (hO : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (hN : GGInndiagNormalInput) (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ =>
      P lab R I F θ ∧ GGOutdiagCyclic R I ∧ GGInndiagNormal R I := by
  have h1 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (fun lab hl _ => hO lab hl) (fun _ _ _ _ _ _ _ => trivial) h
  have h2 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (fun lab hl _ => hN lab hl) (fun _ _ _ _ _ _ _ => trivial) h1
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.1.2, hP.2⟩) h2

theorem le_sup_centralizer_of_innerDiagOn
    (hO : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (hN : GGInndiagNormalInput) {K S D X : Subgroup G} (hS : GGInnerDiagOn S K) (hDS : D ≤ S)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) (hXD : ⁅X, D⁆ = X) :
    X ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  obtain ⟨hK, lab, -, hraw⟩ := largeEvenMarking_outdiag_inndiag hO hN hS
  obtain ⟨R, _, I, F, -, -, θ, ⟨hSN, hSI⟩, hOc, hNn⟩ := largeEvenRawDatum_exists hraw
  exact le_sup_centralizer_of_inndiag hK hOc hNn
    (hDS.trans (le_ggInndiagPre_of_induces hSN hSI)) hX hXD

theorem normalizer_le_normalizer_sup_of_innerDiagOn
    (hO : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (hN : GGInndiagNormalInput) {K S : Subgroup G} (hS : GGInnerDiagOn S K) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((S ⊔ K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hK, lab, -, hraw⟩ := largeEvenMarking_outdiag_inndiag hO hN hS
  obtain ⟨R, _, I, F, -, -, θ, ⟨hSN, hSI⟩, hOc, hNn⟩ := largeEvenRawDatum_exists hraw
  exact normalizer_le_normalizer_sup_of_inndiag hK hOc hNn (le_ggInndiagPre_of_induces hSN hSI)

end Marking

section Inputs


end Inputs

section Main


end Main

end CFSG.StandardType
