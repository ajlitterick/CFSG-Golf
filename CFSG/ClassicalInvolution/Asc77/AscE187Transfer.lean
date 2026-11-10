module

public import CFSG.ClassicalInvolution.Asc77.AscE187Conj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.conj_of_mem (c : MinCex p f Ω K S R W H) {x : G} (hx : x ∈ H) :
    MinCex p f Ω (conjSub x K) (conjSylow x S) (conjSub x R) (conjSub x W) H := by
  have := c.conj x
  rwa [conjSub_eq_self_of_mem hx] at this


end CFSG.ClassicalInvolution.Asc77
