module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Open CFSG.ASVolI.ChF

@[expose] noncomputable def burnsideF48d_perm (T : Table) : Equiv.Perm (Fin 26572) :=
  Classical.epsilon fun g => Rep 26572 T g

@[expose] noncomputable def burnsideF48d_γ (k : ℕ) : Equiv.Perm (Fin 26572) :=
  burnsideF48d_perm (burnsideF48d_toT (burnsideF48d_gen k))

@[expose] noncomputable def burnsideF48d_frob : Equiv.Perm (Fin 26572) :=
  burnsideF48d_perm (burnsideF48d_toT (burnsideF48d_phi ()))

@[expose] noncomputable def burnsideF48d_X : Subgroup (Equiv.Perm (Fin 26572)) :=
  Subgroup.closure (Set.range fun k : Fin 8 => burnsideF48d_γ k)

theorem burnsideF48d_γ_mem (k : Fin 8) : burnsideF48d_γ k ∈ burnsideF48d_X :=
  Subgroup.subset_closure ⟨k, rfl⟩

@[expose] noncomputable def burnsideF48d_σ (j : ℕ) : Equiv.Perm (Fin 26572) :=
  burnsideF48s_ev (fun k : Fin 8 => burnsideF48d_γ k) (burnsideF48d_LW.getD j [])

theorem burnsideF48d_σ_mem (j : ℕ) : burnsideF48d_σ j ∈ burnsideF48d_X :=
  burnsideF48s_ev_mem _ _ fun l _ => burnsideF48d_γ_mem l.1

@[expose] noncomputable def burnsideF48d_L (j : Fin 17) : ↥burnsideF48d_X :=
  ⟨burnsideF48d_σ j, burnsideF48d_σ_mem j⟩

abbrev burnsideF48d_S1 : Set (Fin 17) := {j | j ≠ 1}

abbrev burnsideF48d_S2 : Set (Fin 17) := {j | j ≠ 0}

@[expose] noncomputable def burnsideF48d_P1 : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' burnsideF48d_S1)

@[expose] noncomputable def burnsideF48d_P2 : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' burnsideF48d_S2)


@[expose] noncomputable def burnsideF48d_U : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' {j | 5 ≤ j.val})

abbrev burnsideF48d_line : Finset (Fin 26572) := {0, 1, 2, 6}

abbrev burnsideF48d_aptF : Finset (Fin 26572) := {0, 6, 479, 26571, 15916, 186}

abbrev burnsideF48d_baseF : Finset (Fin 26572) := {0, 26571, 6, 479, 15916, 186, 1, 3}


end CFSG.ASVolI
