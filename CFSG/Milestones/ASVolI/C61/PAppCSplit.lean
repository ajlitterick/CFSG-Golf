module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem pCoreOf_comm_blockU (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    {q u : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ blockU L) : q * u = u * q := by
  have hqH : q ∈ H ⊓ Subgroup.centralizer (blockU L : Set G) := by
    rw [C56.inf_centralizer_eq hcs hj]; exact hq
  exact (Subgroup.mem_centralizer_iff.1 hqH.2 u hu).symm


end CFSG.QuasithinUnique.burnsideC56_P.AppC
