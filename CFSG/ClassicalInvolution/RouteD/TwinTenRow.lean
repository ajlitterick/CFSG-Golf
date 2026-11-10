module

public import CFSG.ClassicalInvolution.RouteD.TwinTenChain
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]


@[expose] def TwinSL4Pattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternD p f 3 (conjClass K) K β t


theorem pieceTwinSL4_of_pattern (h : TwinSL4Pattern p f) : PieceTwinSL4 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  obtain ⟨D, -, -⟩ := routeD_typeD5_of_pattern S.odd S.five (Gaps.fundNoncentral p) S.inClass
    S.exact (mem_conjClass_self K) (single_class K) S.conn S.cls hS S.p1
    (fun β hβ t₁ ht₁ hKβ hfix => h G hnab K z S hS β hβ t₁ ht₁ hKβ hfix)
  exact ⟨D⟩


end CFSG.ClassicalInvolution.Generic.CoreAssembly
