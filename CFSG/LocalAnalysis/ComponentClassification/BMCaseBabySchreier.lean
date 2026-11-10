module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar
public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster.B CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.SporadicSchreierDispatch

theorem nonempty_pinnedB_equiv_Cbar : Nonempty (Blueprint.NativeSporadic.B ≃* Cbar) :=
  pinned_B_explicit_native_isomorphism_simplicity_and_order.2.1.elim fun e _ =>
    ⟨e.trans (MulEquiv.inv' Cbar).symm⟩

theorem inner_of_mulEquiv_pinnedB : ∀ (S : Type) [Group S],
    Nonempty (S ≃* Blueprint.NativeSporadic.B) →
      ∀ α : MulAut S, α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  intro S _ hS α
  obtain ⟨g, hg⟩ := inner_of_equiv (hS.some.trans nonempty_pinnedB_equiv_Cbar.some) cbar_inner α
  exact ⟨g, hg.symm⟩

theorem B_model_Schreier : Group.IsSolvable (Outer Blueprint.NativeSporadic.B) ∧
    ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* Blueprint.NativeSporadic.B) → Group.IsSolvable (Outer T) := by
  have hB : Group.IsSolvable (Outer Blueprint.NativeSporadic.B) :=
    (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism Blueprint.NativeSporadic.B Cbar
      Units.instGroup _ nonempty_pinnedB_equiv_Cbar.some).2.2
      native_B_generated_quotient_Schreier
  refine ⟨hB, fun T _ _ _ _ hT => ?_⟩
  exact (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism T Blueprint.NativeSporadic.B _
    Units.instGroup hT.some).2.2 hB

theorem sporadicSchreierCase_B : SporadicSchreierCase .B :=
  sporadicSchreierCase_of_outer B_model_Schreier.1

end CFSG.ComponentClassification.BMCase
