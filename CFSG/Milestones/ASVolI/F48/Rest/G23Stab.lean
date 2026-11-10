module

public import Certificates.Certificate7763
public import Certificates.Certificate7764
public import CFSG.Milestones.ASVolI.F48.Rest.G23FactsBase
public import CFSG.Milestones.ASVolI.F48.Rest.Perm

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

section Generic

variable {N : ℕ}

theorem burnsideF48t_permOfArr_mem_arrGen {O : Array (Array ℕ)} {t : Array ℕ} (ht : t ∈ O) :
    CFSG.Monster.B.Co2.permOfArr N t ∈ arrGen N O := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ht
  exact Subgroup.subset_closure ⟨k, hk, by rw [getElem!_pos O k hk]⟩


end Generic


section Model


end Model

section Norm


end Norm

section Tau


end Tau

section K


end K

end CFSG.ASVolI
