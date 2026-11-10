module

public import CFSG.GH74.FinalAssemblyDeep
public import CFSG.GH74.GLS.Stage12.Master
public import CFSG.GH74.GLS.SP.Local.Setup
public import CFSG.GH74.Uniqueness.SU.KI4Main
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.GLS.Stage4.HexCoordD4
public import CFSG.GH74.E2.BoxFinal13T5
public import CFSG.GH74.Uniqueness.SU.SU12T9
public import CFSG.GH74.Uniqueness.SU.KI6Janko
public import CFSG.GH74.Uniqueness.SU.KI1r4Complete
public import CFSG.GH74.GLS.C3.Layer2.L5C20
public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.LU.Local.Torus8
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a
public import CFSG.GH74.GLS.SP.Local.Gen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore

public section

namespace CFSG.GH74

open GLS Subgroup Blueprint Assembly.LowTwoRank

theorem walterNativeModels
    : CFSG.Walter.WalterNativeModels :=
  fun G _ _ _ hn P hP => CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models G hn P hP

end CFSG.GH74
