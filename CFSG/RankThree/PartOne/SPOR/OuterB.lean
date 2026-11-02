module

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Monster.B.Final.PinnedBOrder
import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.Monster.AxisCount.BabyCount
public import CFSG.Monster.AxisCount.BabyCover
public import CFSG.Monster.AxisCount.BabyCoverCheck
public import CFSG.Monster.AxisCount.BabyCoverSpec
public import CFSG.Monster.AxisCount.BabyIdentCheck
public import CFSG.Monster.AxisCount.BabyInvCheck
public import CFSG.Monster.Visible.SignCompat
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Sporadic.Schreier.RuLocal
import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.RankThree.PartOne.SPOR

theorem allInner_B :
    ∀ α : MulAut (NativeSporadic.Carrier .B), ∃ g : NativeSporadic.Carrier .B,
      α = MulAut.conj g := by
  obtain ⟨-, ⟨e, -⟩, -⟩ :=
    CFSG.Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order
  exact CFSG.ComponentClassification.BMCase.inner_of_equiv
    (e.trans (MulEquiv.inv' CFSG.Monster.B.Cbar).symm)
    CFSG.ComponentClassification.BMCase.cbar_inner

theorem card_outer_B :
    Nat.card (Outer (NativeSporadic.Carrier .B)) = 1 := by
  have h := CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner (allInner_B)
  exact Nat.card_eq_one_iff_unique.2 ⟨h, inferInstance⟩

end CFSG.RankThree.PartOne.SPOR
