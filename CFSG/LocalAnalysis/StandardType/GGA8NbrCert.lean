module

public import Certificates.Certificate476001
public import Mathlib.Algebra.Group.Submonoid.BigOperators

public section

namespace CFSG.StandardType

open Certificates.A8Nbr476

section Cert


theorem ggA8Nbr_claim : A8Claim := a8Claim_of_check Certificates.certificate476001

theorem ggA8Nbr_exists_transv_of_case {c : Case} (hc : c ∈ allCases) (hx : c ∉ excCases)
    (S : Submonoid M4) (hgen : ∀ k : Fin 6, gens c k ∈ S) : ∃ g ∈ S, IsTransv g := by
  obtain ⟨-, -, hcov, hW, -⟩ := ggA8Nbr_claim
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hcov c hc hx)
  refine ⟨(e.2.map (gens e.1)).prod, S.list_prod_mem fun g hg => ?_, hW e he⟩
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
  exact hgen k


end Cert

theorem ggA8Nbr_excCases_fst : ∀ c ∈ excCases, c.1 = true := by
  intro c hc
  simp only [excCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end CFSG.StandardType
