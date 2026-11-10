module

public import CFSG.ClassicalInvolution.SmallCases.NDB5Main
public import CFSG.ClassicalInvolution.SmallCases.NDBGlue
public import CFSG.ClassicalInvolution.SmallCases.NDB6Main

public section

namespace CFSG.ClassicalInvolution.NDB

variable (p f : ℕ) [Fact p.Prime]

theorem pspCaseP1_of_sAlpha (hα : SAlpha p f) : PSpCaseP1 p f :=
  pspCaseP1_of_pieces (axisExists p f) (axisHyp51Classical p f) (axisFrameSide p f)
    (axisHyp51S_of_sAlpha p f hα) (axisP1 p f)

theorem pspCaseP1Core_of_sAlphaCore (hα : SAlphaCore p f) : PSpCaseP1Core p f :=
  pspCaseP1Core_of_pieces (axisExistsCore p f) (axisHyp51ClassicalCore p f)
    (axisFrameSideCore p f) (axisHyp51S_of_sAlphaCore p f hα) (axisP1Core p f)

end CFSG.ClassicalInvolution.NDB
