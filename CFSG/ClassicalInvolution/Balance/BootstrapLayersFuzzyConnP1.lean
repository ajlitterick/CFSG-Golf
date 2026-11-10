module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj
public import CFSG.ClassicalInvolution.Balance.Theorem5FuzzyExact

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers fuzzyFrames fuzzyVertices ShareFourIn TriangleConnected
    TriangleConnectedAll TriangleLayers conjInvariant_conjMembers fuzzyMemberConn_conjMembers
    fuzzyVertexConn_of_adj)

section Connected

variable {p f : ℕ} [Fact p.Prime]

@[expose] def FuzzyFramesConnected (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ A ∈ fuzzyFrames p f (CoreAssembly.conjClass K),
          ∀ A' ∈ fuzzyFrames p f (CoreAssembly.conjClass K),
            Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f (CoreAssembly.conjClass K))) A A'


end Connected

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem indepTriple_of_indepTripleOn {Ω : Set (Subgroup G)} {A : Subgroup G}
    (h : IndepTripleOn p f Ω A) : CoreAssembly.IndepTriple p f Ω := by
  obtain ⟨K', z', hK', hcomm, hAdef, hel, hcard⟩ := h
  subst hAdef
  exact ⟨K', z', hK', hcomm, hel, hcard⟩

theorem triangleConnected_of_fuzzyFramesConnected [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hcon : ∀ A ∈ fuzzyFrames p f Ω, ∀ A' ∈ fuzzyFrames p f Ω,
      Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f Ω)) A A') :
    TriangleConnected p f Ω := by
  intro A hA A' hA'
  have key : ∀ B : Subgroup G, Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f Ω)) A B →
      Relation.ReflTransGen (fun X Y => X ∈ Theorem5.triangleFrames p f Ω ∧
        Y ∈ Theorem5.triangleFrames p f Ω ∧ ShareFour X Y) A B := by
    intro B h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨hX, hY, hXY⟩ := hbc
      exact ih.tail ⟨Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hX,
        Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hY, hXY⟩
  exact key A' (hcon A (Theorem5.fuzzyFrameOn_of_indepTripleOn hA) A'
    (Theorem5.fuzzyFrameOn_of_indepTripleOn hA'))

theorem fuzzyFramesBalanced_of_exact [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a) :
    ∀ A ∈ fuzzyFrames p f Ω, RankThreeBalance A := fun A hA => by
  have hT := Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hA
  exact Theorem5.rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hT (hlay A hT)

theorem triangleConnectedAll_of_bootTriple (hBT : CoreAssembly.BootTriple p f)
    (hcon : FuzzyFramesConnected p f) : TriangleConnectedAll p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA A' hA'
  have hind : CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) :=
    indepTriple_of_indepTripleOn hA
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hex := (hBT G hnab hp2 hq K z hz hBelow hconn hind).1
  exact triangleConnected_of_fuzzyFramesConnected hnab hp2 hq hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) hex (hcon G hnab hp2 hq K z hz hBelow hconn hind)
    A hA A' hA'


end Triangle

section P1


end P1

end CFSG.ClassicalInvolution.Balance.Bootstrap
