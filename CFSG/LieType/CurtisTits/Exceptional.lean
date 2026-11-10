module

public import CFSG.LieType.CurtisTits.Minuscule
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny

universe w

variable (p f : ℕ) [Fact p.Prime]

theorem curtisTitsConclusion_e6 (hadm : StatedLieAdmissible .E6 0 p f) :
    CurtisTitsConclusion.{w} (e6Datum (GaloisField p f)) .E6 0 p f :=
  curtisTitsConclusion_e6_of_surjective p f hadm (e6Isogeny _) (e6Isogeny_surjective _)

theorem curtisTitsConclusion_e7 (hadm : StatedLieAdmissible .E7 0 p f) :
    CurtisTitsConclusion.{w} (e7Datum (GaloisField p f)) .E7 0 p f :=
  curtisTitsConclusion_e7_of_surjective p f hadm (e7Isogeny _) (e7Isogeny_surjective _)

theorem curtisTitsConclusion_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p f) :
    CurtisTitsConclusion.{w} (twistedE6Datum p f) .twistedE6 0 p f :=
  curtisTitsConclusion_twistedE6_of_surjective p f hadm (twistedE6Isogeny p f hadm.2.1)
    (twistedE6Isogeny_surjective p f hadm.2.1) (twistedE6Isogeny_ne_one p f hadm.2.1)

end CFSG.LieType.CurtisTits
