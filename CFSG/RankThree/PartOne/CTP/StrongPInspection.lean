module

public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeHyp)
open CFSG.RankThree.GroupTheory
  (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four)

section Omega

variable {H : Type*} [Group H] {p : ℕ}

theorem omegaOne_le (P : Subgroup H) : omegaOne p P ≤ P :=
  (Subgroup.closure_le P).mpr fun _ hx => hx.1

theorem omegaOne_eq_of_pow_eq_one {P : Subgroup H} (h : ∀ x ∈ P, x ^ p = 1) :
    omegaOne p P = P :=
  le_antisymm (omegaOne_le P) fun _ hx => Subgroup.subset_closure ⟨hx, h _ hx⟩

theorem isElementaryAbelian_of_subgroup {A : Type*} [Group A] [IsElementaryAbelian p A]
    (K : Subgroup A) : IsElementaryAbelian p ↥K := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
  have hx : (x : A) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A) x
  simpa using hx

theorem exists_elementaryAbelian_sq_le [Fact p.Prime] [Finite H] {A : Subgroup H}
    [IsElementaryAbelian p ↥A] (hdvd : p ^ 2 ∣ Nat.card A) :
    ∃ E : Subgroup H, E ≤ A ∧ IsElementaryAbelian p ↥E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have : IsElementaryAbelian p ↥K := isElementaryAbelian_of_subgroup K
  refine ⟨K.map A.subtype, ?_, CFSG.IsElementaryAbelian.map A.subtype, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK]

end Omega


end CFSG.RankThree.PartOne.CTP
