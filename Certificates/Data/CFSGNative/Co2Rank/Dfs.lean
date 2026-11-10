module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Rank

open CFSG.Sporadic.SmallF2.Native


@[expose] def kids (pr : Nat → Nat → Nat) (S cand : List Nat) (lo : Nat) : List Nat :=
  cand.filter fun c => decide (lo ≤ c) && S.all fun s => decide (c < pr c s)

@[expose] def childS (pr : Nat → Nat → Nat) (S : List Nat) (c : Nat) : List Nat :=
  c :: (S ++ S.map (pr c))

@[expose] def childCand (adj : Nat → Nat → Bool) (pr : Nat → Nat → Nat) (S cand : List Nat)
    (c : Nat) : List Nat :=
  cand.filter fun d => adj c d && S.all fun s => adj (pr c s) d

@[expose] def dfs (adj : Nat → Nat → Bool) (pr : Nat → Nat → Nat) :
    Nat → List Nat → List Nat → Nat → Bool
  | 0, S, cand, lo => (kids pr S cand lo).isEmpty
  | d + 1, S, cand, lo => (kids pr S cand lo).all fun c =>
      dfs adj pr d (childS pr S c) (childCand adj pr S cand c) (c + 1)

end CFSG.Sporadic.Co2Rank
