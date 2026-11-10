module

public import CFSG.ClassicalInvolution.SmallCases.SmallConnSetup
public import CFSG.ClassicalInvolution.Generic.CoreAssembly

public section

namespace CFSG.ClassicalInvolution.SmallConn

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem lieSystem_of_noDataBootD (hN : NoDataBootD p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (h4 : ¬ TwoSubgroupsFourGenerated G) (hD : DConnected (𝒞 K))
    (hB : ¬ BootData p f (𝒞 K)) : LieSystem p f G (𝒞 K) := by
  obtain ⟨hex, hp1⟩ := hN G hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hconn : RouteD.DeltaConnected (𝒞 K) :=
    routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hp1
  have S : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hp1
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hsh⟩ | hm
  · exact hshape a t n G hnab K z S hsh
  · exact hmulti G hnab K z S hm

theorem coreStep_small_of_noDataBootD (hs4 : CITSectionalFour) (hd : SmallDisconnected p f)
    (hN : NoDataBootD p f) (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) (hup : SmallUpgrade p f) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (hgen : ¬ (RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K))) :
    LieSystem p f G (𝒞 K) := by
  by_cases h4 : TwoSubgroupsFourGenerated G
  · exact hup G hnab hp2 hq K z hz
      (hs4 G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) ⟨h3, h4⟩)
  · by_cases hΔ : CFSG.ClassicalInvolution.DeltaConnected K
    · have hB : ¬ BootData p f (𝒞 K) := fun hB => hgen ⟨(deltaConnected_iff K).mp hΔ, hB⟩
      exact lieSystem_of_noDataBootD hN hshape hmulti hnab hp2 hq hz hBelow h3 h4
        (dConnected_of_deltaConnected hΔ) hB
    · exact hup G hnab hp2 hq K z hz (hd G hnab hp2 hq hBelow K z hz h3 h4 hΔ)

theorem dBridge_of_noDataBootD (hmodel : Balance.Bootstrap.LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hexotic : ExoticLeviBlock p f)
    (hBN : BootNoTripleD p f) (hN : NoDataBootD p f) : DBridge p f :=
  deltaConnected_of_dConnected hmodel hMFC hexotic hBN (noDataD_of_noDataBootD hN)

end CFSG.ClassicalInvolution.SmallConn
