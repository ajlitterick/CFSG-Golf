module

public import CFSG.ClassicalInvolution.Q3.Q3TY4
public import CFSG.ClassicalInvolution.Q3.Q3TY5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel
  minusLongBlock shortBlock)


theorem twistedB2BlockPair_of_locImg3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {x : G} {b c : GaloisField 3 1} (hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0)
    (hg6 : SpinMinus6Generated hirr) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {A B : Subgroup G} (hA : A ≤ locLayer Ω x)
    (hB : B ≤ locLayer Ω x) (hA12 : ∀ a ∈ A, a ^ 12 = 1) (hBp : B ≤ ⁅B, B⁆)
    {W : Subgroup (locQuot Ω x)}
    (h : TwistedB2BlockPair hirr W (locImg Ω x A) (locImg Ω x B)) :
    ∃ W' : Subgroup G, TwistedB2BlockPair hirr W' A B := by
  have hexp : ∀ a ∈ A.subgroupOf (locLayer Ω x), a ^ 12 = 1 := fun a ha =>
    Subtype.ext (by simpa using hA12 (a : G) (Subgroup.mem_subgroupOf.mp ha))
  obtain ⟨W', hW'⟩ := twistedB2BlockPair_lift3 hirr hg6
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) hO3 hexp (perfect_subgroupOf hB hBp) h
  have := twistedB2BlockPair_map hirr hW' (locLayer Ω x).subtype (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA,
    inf_eq_left.mpr hB] at this
  exact ⟨_, this⟩

end CFSG.ClassicalInvolution.Q3.Q3TY

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W


end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3
