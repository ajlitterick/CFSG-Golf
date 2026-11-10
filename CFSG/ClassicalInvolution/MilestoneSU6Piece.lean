module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired5
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptPartner
public import CFSG.ClassicalInvolution.Balance.Theorem5FuzzyExact

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem pieceSU6_of_p1x (hMFZ : Gaps.FundNoncentral p) (hP1x : SU6P1x p f) : PieceSU6 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .twistedE6 0 p f := ⟨Fact.out, hf, rfl⟩
  rcases NonClassical.routeD_typeU_five_of_partner S.odd hadm S.five S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1 hMFZ S.ih
    (fun c nd {_} hβ hn => hP1x G hnab K z S hS c nd hβ hn) with ⟨D, -, -⟩ | ⟨D, -, -⟩
  · exact ⟨D⟩
  · exact ⟨D⟩

end CFSG.ClassicalInvolution.MilestoneAssembly
