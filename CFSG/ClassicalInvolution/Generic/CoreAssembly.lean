module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyRows

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem shapePiece_of_rows (h7 : PieceSL7 p f) (h6 : PieceSL6 p f)
    (hs : RowPiece p f ShapeSLs) (hu7 : PieceSU7 p f) (hu6 : PieceSU6 p f) (hus : PieceSUs p f)
    (hc4 : RowPiece p f ShapeSp4) (hc3 : PieceSp3 p f) (he7 : PieceE7 p f) (he8 : PieceE8 p f)
    (hd : RowPiece p f ShapeTwinD) (hd5 : PieceTwinSL4 p f) (hb : PieceTwinB p f)
    (hb4 : PieceTwinSp2 p f) (htd : PieceTwinTD p f) (htd5 : PieceTwinSU4 p f)
    (hx : ShapeExcluded p f) : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n := by
  intro a t n
  by_cases h : ShapeTable a t n
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact h7 a t n h
    · exact h6 a t n h
    · exact hs a t n h
    · exact hu7 a t n h
    · exact hu6 a t n h
    · exact hus a t n h
    · exact hc4 a t n h
    · exact hc3 a t n h
    · exact he7 a t n h
    · exact he8 a t n h
    · exact hd a t n h
    · exact hd5 a t n h
    · exact hb a t n h
    · exact hb4 a t n h
    · exact htd a t n h
    · exact htd5 a t n h
  · exact hx a t n h

theorem coreStep_generic (hb3 : BootTriple p f) (hb : BootNoTriple p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n) (hmulti : MultiPiece p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hconn : RouteD.DeltaConnected (conjClass K))
    (hdata : BootData p f (conjClass K)) : LieSystem p f G (conjClass K) := by
  obtain ⟨hex, hp1⟩ : ExactMembers (conjClass K) ∧ LocalOddCentral (conjClass K) {z} := by
    by_cases hT : IndepTriple p f (conjClass K)
    · exact hb3 G hnab hp2 hq K z hz hBelow hconn hT
    · exact hb G hnab hp2 hq K z hz hBelow hconn hdata hT
  have S : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hp1
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hs⟩ | hm
  · exact hshape a t n G hnab K z S hs
  · exact hmulti G hnab K z S hm

theorem coreStep_small (hs4 : CITSectionalFour) (hd : SmallDisconnected p f)
    (ha : SmallConnectedA2 p f) (hc : SmallTypeC p f) (hup : SmallUpgrade p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (hgen : ¬ (RouteD.DeltaConnected (conjClass K) ∧ BootData p f (conjClass K))) :
    LieSystem p f G (conjClass K) := by
  refine hup G hnab hp2 hq K z hz ?_
  by_cases h4 : TwoSubgroupsFourGenerated G
  · exact hs4 G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
      (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) ⟨h3, h4⟩
  · by_cases hΔ : CFSG.ClassicalInvolution.DeltaConnected K
    · have hB : ¬ BootData p f (conjClass K) := fun hB => hgen ⟨(deltaConnected_iff K).mp hΔ, hB⟩
      by_cases hA2 : A2Configuration z K
      · exact ha G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
      · exact hc G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
    · exact hd G hnab hp2 hq hBelow K z hz h3 h4 hΔ


end CFSG.ClassicalInvolution.Generic.CoreAssembly
