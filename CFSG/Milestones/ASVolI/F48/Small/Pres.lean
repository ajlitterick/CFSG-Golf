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

theorem burnsideF48s_ev_cons (h : Fin m → G) (l : Fin m × Bool) (w : List (Fin m × Bool)) :
    burnsideF48s_ev h (l :: w) = cond l.2 (h l.1) (h l.1)⁻¹ * burnsideF48s_ev h w := rfl

theorem burnsideF48s_ev_append (h : Fin m → G) (u v : List (Fin m × Bool)) :
    burnsideF48s_ev h (u ++ v) = burnsideF48s_ev h u * burnsideF48s_ev h v := by
  simp [burnsideF48s_ev, List.map_append, List.prod_append]

theorem burnsideF48s_ev_map (f : G →* H) (h : Fin m → G) (w : List (Fin m × Bool)) :
    burnsideF48s_ev (fun i => f (h i)) w = f (burnsideF48s_ev h w) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [burnsideF48s_ev_cons, burnsideF48s_ev_cons, ih, map_mul]
    congr 1
    cases l.2 <;> simp

theorem burnsideF48s_ev_replicate (h : Fin m → G) (u : List (Fin m × Bool)) (k : ℕ) :
    burnsideF48s_ev h (List.replicate k u).flatten = burnsideF48s_ev h u ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero]; rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, burnsideF48s_ev_append, ih, pow_succ']

theorem burnsideF48s_ev_mem {K : Subgroup G} (h : Fin m → G) (w : List (Fin m × Bool))
    (hw : ∀ l ∈ w, h l.1 ∈ K) : burnsideF48s_ev h w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [burnsideF48s_ev_cons]
    refine K.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have := hw l List.mem_cons_self
    cases l.2
    · exact K.inv_mem this
    · exact this


end Ev

section Pres


end Pres


end CFSG.ASVolI
