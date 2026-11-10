module

public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.Sporadic.HNOddCore.SixB
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native

section Words

variable {N n : ℕ}

@[expose] def burnsideF48t_RecL (N : ℕ) (L Li : Array (Array ℕ)) (σ : Fin n → Equiv.Perm (Fin N)) :
    Prop :=
  ∀ i : Fin n, PRep N L[(i : ℕ)]! (σ i) ∧ PRep N Li[(i : ℕ)]! (σ i)⁻¹

theorem burnsideF48t_prep_evA {L Li : Array (Array ℕ)} {σ : Fin n → Equiv.Perm (Fin N)}
    (h : burnsideF48t_RecL N L Li σ) (w : List (Fin n × Bool)) :
    PRep N (burnsideF48t_evA N L Li w) (burnsideF48s_ev σ w) := by
  induction w with
  | nil => exact prep_pid
  | cons l w ih =>
    rw [burnsideF48t_evA, burnsideF48s_ev_cons]
    refine prep_pcomp ?_ ih
    obtain ⟨i, b⟩ := l
    cases b
    · exact (h i).2
    · exact (h i).1


end Words

section Closed

variable {N : ℕ}


end Closed

section Checks

open CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {N : ℕ}


theorem burnsideF48t_preserves {m : ℕ} {gens : Array (Array ℕ)} {σ : ℕ → Equiv.Perm (Fin m)}
    (hrep : ∀ s < gens.size, CFSG.ONSchreier.PRep m gens[s]! (σ s)) {S : Set (Fin m)}
    (hS : ∀ s < gens.size, ∀ x ∈ S, σ s x ∈ S) :
    ∀ g ∈ Subgroup.closure (Set.range fun s : Fin gens.size => σ s), ∀ x ∈ S, g x ∈ S := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, rfl⟩ := hg
    exact hS s s.2
  | one => intro x hx; exact hx
  | mul a b _ _ ha hb => intro x hx; exact ha _ (hb x hx)
  | inv a _ ha => exact perm_preimage_of_image ha

end Checks

end CFSG.ASVolI
