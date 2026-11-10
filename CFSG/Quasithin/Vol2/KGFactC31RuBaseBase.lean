
module

public import CFSG.Quasithin.Vol2.KGFactC31RuReps
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverCheck

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native


section Reps


end Reps

theorem ruJoin_base : (ruChainJoin.base.toList.map Fin.val) = ruJoinBase := by
  decide

theorem ruJoin_baseFaithful :
    BaseFaithful ruP ruJoinBase := by
  have h := baseFaithful_of_valid ruChainJoin_valid
  rw [ruChainJoin_sub, ← ruP_eq_sup, ruJoin_base] at h
  exact h


section Cover

end Cover

end CFSG.Quasithin.KGC31.Ru

end
