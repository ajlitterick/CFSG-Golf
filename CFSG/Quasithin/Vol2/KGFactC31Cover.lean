module

public import CFSG.Sporadic.Schreier.PairClasses

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative


end CFSG.Quasithin.KGC31.Native

namespace CFSG.Quasithin.KGC31

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
  CFSG.Quasithin.KGC31.Native

variable {n : ℕ}

section Facts

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF


end Facts

theorem contains_iff_mem {l : List ℕ} {a : ℕ} : l.contains a = true ↔ a ∈ l := by
  simp


end CFSG.Quasithin.KGC31

end
