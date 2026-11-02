module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
import CFSG.LocalAnalysis.StandardType.KGLangS1EExc
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcE6
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcTwE6
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcE6Even
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcTwE6Odd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangAxisS1ExcInput_holds :
    KGLangAxisS1ExcInput := by
  intro p lab hp hp2 hlab hE
  obtain ⟨htag, hp3, h3⟩ := hE
  subst hp3
  rcases htag with h | h | h
  · rcases Nat.even_or_odd lab.n with he | ho
    · exact kgLangS1E_cont_E6_even hlab h h3 he
    · exact kgLangS1E_cont_E6_odd hlab h h3 ho
  · rcases Nat.even_or_odd lab.n with he | ho
    · exact kgLangS1E_cont_twE6_even hlab h h3 he
    · exact kgLangS1E_cont_twE6_odd hlab h h3 ho
  · exact kgLangS1E_cont_E7 hlab h h3

end CFSG.StandardType
