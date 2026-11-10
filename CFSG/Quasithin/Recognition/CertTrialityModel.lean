module

public import CFSG.Open.QuasithinDefs
public import CFSG.Quasithin.Recognition.CertF8

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def trialityElt (a : GF8) (s : Bool) : Matrix (Fin 8) (Fin 8) GF8 :=
  quasithinRootElt (quasithinD4Root 0 s) a * quasithinRootElt (quasithinD4Root 2 s) (a ^ 2) *
    quasithinRootElt (quasithinD4Root 3 s) (a ^ 4)

@[expose] def trialityMid (s : Bool) : Matrix (Fin 8) (Fin 8) GF8 :=
  quasithinRootElt (quasithinD4Root 1 s) 1

@[expose] def trialityGens8 : Set (Matrix (Fin 8) (Fin 8) GF8) :=
  {M | ∃ (a : GF8) (s : Bool), M = trialityElt a s} ∪ {M | ∃ s : Bool, M = trialityMid s}

@[expose] def trialityGroup8 : Subgroup (GL (Fin 8) GF8) :=
  Subgroup.closure {A | (A : Matrix (Fin 8) (Fin 8) GF8) ∈ trialityGens8}

noncomputable def gf8EquivGaloisField : GF8 ≃+* GaloisField 2 3 :=
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num),
      Nat.card_eq_fintype_card]
    decide)


end CFSG.Quasithin
