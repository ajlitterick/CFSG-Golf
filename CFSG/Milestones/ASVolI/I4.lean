module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Quasithin.Recognition.HSType17m
public import CFSG.LargeExtraspecial.A2ModSLModel
public import CFSG.Walter.J1Props.Janko
public import CFSG.Walter.Models
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

scoped instance generalizedFitting_normal_inst (X : Type) [Group X] [Finite X] :
    (CFSG.generalizedFitting X).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic).2


end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups


section BurnsideId


end BurnsideId

section


end


end CFSG.ASVolI
