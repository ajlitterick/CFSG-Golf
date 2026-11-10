module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Quasithin.Vol2.KGFactC31BadScan

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31.Native


@[expose] def refPrime (τ : ℕ) : ℕ := if τ < 3 then 7 else 5


@[expose] def cosetWords : List (List ℤ) := hWordsZ ++ hWordsA


end CFSG.Quasithin.KGC31.Ru

end
