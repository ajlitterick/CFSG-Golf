module

public import Certificates.Data.TwoDepSmall

public section

namespace Certificates.TwoDepSmallN

open Certificates.DepASmall Certificates.TwoDepSmall

set_option compiler.extract_closed false

@[expose] def ggTWDGen (p N : Nat) (news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g + 1 < N then (ggDepANH p N g, ggDepANA p N g) else news.getD (g + 1 - N) ([], [])

@[expose] def ggTWDWord (p N : Nat) (news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj p acc (ggTWDGen p N news g)) q

@[expose] def ggTWDWitTest (p N : Nat) (news : List GGDepANPair) (w : GGDepANWit) : Bool :=
  ggDepANTestPair p (ggTWDWord p N news (ggTWDGen p N news w.g1) w.w1)
    (ggTWDWord p N news (ggTWDGen p N news w.g2) w.w2)

@[expose] def ggTWDWitValid (G : Nat) (w : GGDepANWit) : Bool :=
  decide (w.g1 < G) && decide (w.g2 < G) && w.w1.all (fun g => decide (g < G)) &&
    w.w2.all fun g => decide (g < G)


end Certificates.TwoDepSmallN
