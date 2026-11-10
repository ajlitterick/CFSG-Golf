module

public import CFSG.ClassicalInvolution.Asc77.AscT7U8
public import CFSG.ClassicalInvolution.Asc77.AscT7QMain
public import CFSG.ClassicalInvolution.Asc77.AscT7TOdd
public import CFSG.ClassicalInvolution.Asc77.AscT7W13

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

namespace T7U

variable {p f : ℕ} [Fact p.Prime]


theorem c25_16_of_inv_even (h11 : C25_11 p f) (hres : Even f → C25_16inv p f) : C25_16 p f :=
  (Nat.even_or_odd f).elim (fun he => c25_16_of_inv h11 (hres he)) T7T.c25_16_of_odd

end T7U


end CFSG.ClassicalInvolution.Asc77
