module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem LargeEvenLabelAll.mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.1, hPP' R I F hq.2⟩) (h Q hQ)


end CFSG.StandardType
