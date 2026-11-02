module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumI
public import CFSG.Quasithin.EmptyFaithful.Insp7NumK

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def SmallSimple' (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨ StatedClassicalModel L .PSU 3 2 2 ∨
    StatedClassicalModel L .PSp 2 2 2 ∨ StatedClassicalModel L .PSL 4 2 1 ∨
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel L .PSU 3 3 1

theorem numFactAt_smallSimple
    (h : NumFactAt SmallSimple') : NumFactAt SmallSimple :=
  numFactAt_of_cover (G := SmallSimple') (H := fun L _ => SuzukiModel L 2 3)
    (fun L _ hL => by
      unfold SmallSimple at hL
      unfold SmallSimple'
      tauto) h numFactAt_sz8

theorem lemma14320Inspect_final
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallSimple') (hT : NumFactAt LargeReeTits) (hO : NumFactAt L33Fam)
    (hP : NumFactAt SporSimple) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_simple_groups hbig hsimple (numFactAt_smallSimple hS) hT hO hP

end Insp7

end CFSG.Quasithin
