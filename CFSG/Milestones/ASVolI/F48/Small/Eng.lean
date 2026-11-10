module

public import CFSG.Milestones.ASVolI.F48.Small.Core

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable

section Sem

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))}


variable {G : Fin n → ↥X} {LS LSi : List (List ℕ)}


theorem burnsideF48s_e_getD_mem {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _


end Sem

section Model


end Model

section Core


end Core

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end QE

section Sylow

open CFSG.Open CFSG.ASVolI.ChF


end Sylow

end CFSG.ASVolI
