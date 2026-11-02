module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Defs
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.LocalTwin
import CFSG.ClassicalInvolution.SmallCases.NDBD4Shape
import CFSG.ClassicalInvolution.SmallCases.NDBC3
import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
import CFSG.ClassicalInvolution.Asc77.WP3L52Main

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def D4FivePred : Asc77.ShapePred := fun G _ _ K z =>
  (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∧
    ∃ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∃ i : Fin D.card,
      (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∧ D.card = 5

@[expose] def ExoticD4FourFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      RouteD.LocalShapeT p f 4 .POmegaPlus 4 (𝒞 K) z → False

variable {p f}

theorem d4FiveCore_of_frame (hfr : Asc77.FrameExistsOnE p f (D4FivePred p f))
    (hF : ExoticD4FourFalse p f) : D4FiveCore p f := by
  intro G _ _ _ K z hnab hp2 hq hz hBelow hD hnoF D i hi h5
  obtain ⟨L₀, z₀, A, S, a, hfrm, hA⟩ :=
    hfr G hnab hp2 hq K z hz hBelow hD ⟨hnoF, D, i, hi, h5⟩
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := Asc77.exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hD hfrm
    (Asc77.lemma52 G A hA)
  have hP1z := hP1 K (mem_conjClass_self K) z hz
  have hconn := Disconnected.routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD
    hex hP1z
  have hS : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hP1z
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    have h1 : D.tag i = .PSL := h.1
    rw [hi.1] at h1
    exact absurd h1 (by decide)
  have hrest : ∀ j, j ≠ i → D.tag j = .PSL ∧ D.rank j = 2 := fun j hj => by
    by_contra h
    exact Cover.false_of_two_nonA1 C hnoF hj h hQ
  exact hF G hnab K z hS
    (D4.localShapeT_of_exact hex hΩ.classical D (by omega) hi.1 hi.2 hrest)

end CFSG.ClassicalInvolution.NDB
