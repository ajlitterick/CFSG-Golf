module

public import CFSG.GH74.QTGen4.Recog.Ku.GenC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Inputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13


theorem stmtKuM22_of_leaves
    (hCard : LeafCardKuA) (hComm : LeafIsMulCommutativeKuA) (hHC : LeafHInfCentralizerKuA)
    (hEq : LeafEqKuAOfElemAbelian) (hTC : LeafTInfCentralizerKuWLeKuA) (hV2W : LeafKuV2LeKuW)
    (hPar : LeafExistsIsParabolicL1) (hL2 : LeafOTwoUpperInfL2) (hL2c : LeafCardOTwoUpperInfL2)
    (hDC : LeafKuNEqL2DoubleCoset) (hA6 : LeafExistsA6Model) (hClose : LeafKuCloseHolds) :
    StmtKuM22 := by
  haveI : KuLeaf LeafCardKuA := ⟨hCard⟩
  haveI : KuLeaf LeafIsMulCommutativeKuA := ⟨hComm⟩
  haveI : KuLeaf LeafHInfCentralizerKuA := ⟨hHC⟩
  haveI : KuLeaf LeafEqKuAOfElemAbelian := ⟨hEq⟩
  haveI : KuLeaf LeafTInfCentralizerKuWLeKuA := ⟨hTC⟩
  haveI : KuLeaf LeafKuV2LeKuW := ⟨hV2W⟩
  haveI : KuLeaf LeafExistsIsParabolicL1 := ⟨hPar⟩
  haveI : KuLeaf LeafOTwoUpperInfL2 := ⟨hL2⟩
  haveI : KuLeaf LeafCardOTwoUpperInfL2 := ⟨hL2c⟩
  haveI : KuLeaf LeafKuNEqL2DoubleCoset := ⟨hDC⟩
  rw [stmtKuM22_iff_of_hyp]
  intro G _ _ T M H P z hK
  obtain ⟨Ψ⟩ := hA6 hK
  exact hK.nonempty_mulEquiv_m22_of_close Ψ (hClose hK Ψ)


end CFSG.GH74.QTGen4.Ku
