module

public import CFSG.Monster.GMS.S4CohAGen
public import CFSG.Monster.GMS.S4CohATrans
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionTools
public import CFSG.Monster.GMS.S4FamilyGroup
public import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.Monster.GMS.S4CohA

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

end CFSG.Monster.GMS.S4CohA
