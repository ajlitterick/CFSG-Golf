module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHMain2
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTwinAll
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHG2
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHNT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank


variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_of_not_fund {t : StatedLieTag} (ht : ¬ IsFundTag t) {k e : ℕ} (P : Prop → Prop) :
    T5BaseAt p f t k e P := fun _ _ hfund => absurd hfund ht


end CFSG.ClassicalInvolution.Asc77
