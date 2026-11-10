module

public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.CosetTable

section Ev

variable {G H : Type*} [Group G] [Group H] {m : ℕ}

@[simp] theorem burnsideF48s_ev_nil (h : Fin m → G) : burnsideF48s_ev h [] = 1 := rfl


end Ev

section Pres


end Pres


end CFSG.ASVolI
