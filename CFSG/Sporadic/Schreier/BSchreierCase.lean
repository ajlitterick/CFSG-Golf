module

public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

namespace CFSG.Sporadic.BSchreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SporadicSchreierDispatch

noncomputable def nativeBEquivCbar :
    NativeSporadic.B ≃* CFSG.Monster.B.Cbar :=
  (CFSG.Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order.2.1.choose).trans
    (MulEquiv.inv' CFSG.Monster.B.Cbar).symm

theorem AT_B_model_Schreier :
    Group.IsSolvable (Outer NativeSporadic.B) ∧
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
        Nonempty (T ≃* NativeSporadic.B) → Group.IsSolvable (Outer T) := by
  have hB : Group.IsSolvable (Outer NativeSporadic.B) :=
    (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism NativeSporadic.B CFSG.Monster.B.Cbar
      Units.instGroup (QuotientGroup.Quotient.group _) nativeBEquivCbar).2.2
      CFSG.ComponentClassification.BMCase.native_B_generated_quotient_Schreier
  exact ⟨hB, fun T instT _ _ _ ⟨e⟩ =>
    (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism T NativeSporadic.B instT
      Units.instGroup e).2.2 hB⟩

theorem sporadicSchreierCase_B :
    SporadicSchreierCase .B :=
  sporadicSchreierCase_of_outer AT_B_model_Schreier.1

end CFSG.Sporadic.BSchreier
