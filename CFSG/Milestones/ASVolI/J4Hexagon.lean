module

public import CFSG.Milestones.ASVolI.J4
public import CFSG.Quasithin.Recognition.RuTypeJ47Sig
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Co1.Module.TwoBCert

public section

namespace CFSG.ASVolI

open CFSG.Open

section BurnsideJ410Basic

variable {G : Type} [Group G]


end BurnsideJ410Basic


section BurnsideJ410B

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]


section Loc

variable {z u : G}


end Loc


section Loc2

variable {z u : G} [Finite G]


end Loc2

section Equiv

variable {z u : G} [Finite G]


end Equiv

end BurnsideJ410B

section BurnsideJ410C

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]


section Path

variable {z u : G} [Finite G]


end Path

end BurnsideJ410C

section BurnsideJ410D

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]


variable [Finite G]


end BurnsideJ410D

section BurnsideJ410E

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]


section Walk

variable [Finite G] {z u : G}


end Walk

section Walk2

variable [Finite G] {z u : G}


end Walk2

end BurnsideJ410E

section BurnsideJ410F

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 : Subgroup G}


section Theta

variable {θ : ℤ → Subgroup G}


end Theta

end BurnsideJ410F

section BurnsideJ410G

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 I0 : Subgroup G}


end BurnsideJ410G

section BurnsideJ410H

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 I0 : Subgroup G}


end BurnsideJ410H

section BurnsideJ410S5

open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma47


end BurnsideJ410S5

section BurnsideJ410I

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G]


section Conf

variable {M : RuDataM G} (C : RuDataM.Conf47 M)


end Conf

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.RuDataM
  CFSG.Quasithin.RuType.RuDataM.Conf47 CFSG.Quasithin.RuType.Sigma47 CFSG.LieType.BorelTits
  CFSG.QuasithinUnique in
attribute [local instance] CFSG.Quasithin.RuType.RuDataM.Conf47.fact_prime_five in


end BurnsideJ410I

section BurnsideJ410Setup


end BurnsideJ410Setup

section


end

end CFSG.ASVolI
