module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameChainMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLift2
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1Shape

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainLift.frameSideTwoStar {C : ChainCtx p f Ω z} (L : ChainLift C)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hGen : CentralizerGenerationStar Ω (Subgroup.closure ({z, L.t, L.z'} : Set G)) L.t) :
    FrameSideTwoStar p f Ω (Subgroup.closure ({z, L.t, L.z'} : Set G))
      ({C.K, L.J} : Set (Subgroup G)) := by
  have hKz : IsUniqueInvolution C.K z := C.hKz
  have hKJ : ∀ a : G, IsClassicalMember p f C.K a → a = z := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq hKz
  have hJt : ∀ a : G, IsClassicalMember p f L.J a → a = L.t := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  exact
    { elem := L.frameData.isElemAbelian C.hp C.hΩ
      card := (L.frameData.natCard_eight C.hp C.hq C.hΩ).ge
      subset := by
        rintro M (rfl | rfl)
        · exact C.hK
        · exact L.hJ.1
      nonempty := ⟨C.K, Set.mem_insert _ _⟩
      involution := by
        rintro M (rfl | rfl)
        · exact ⟨z, L.z_mem_B, hKcl⟩
        · exact ⟨L.t, L.t_mem_B, L.hJt⟩
      generation := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.generation_z
        · rw [hJt a hMa]
          exact hGen
      link := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.link_z_star
        · rw [hJt a hMa]
          exact L.link_t_star htrans }

variable [IsSimpleGroup G]

theorem centralizes_of_frame (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G}
    {S : Set (Subgroup G)} (hframe : FrameSideTwoStar p f Ω A S)
    (hcls : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A) (htq : A ≤ trivialOnQuot L₀)
    (hbal : RankThreeBalance A) :
    L₀ ≤ Subgroup.centralizer (A : Set G) := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hgen : rankTwoSpan A = ⊤ := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩ hframe hconn
  have hc := hcls.isCentralInvolution
  have hz2 : z₀ * z₀ = 1 := hbal.mul_self hz₀A
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  by_cases hgz : g = z₀
  · rw [hgz]
    exact hc.central x hx
  have hg2 : g * g = 1 := hbal.mul_self hg
  have hcomm : z₀ * g = g * z₀ := hbal.comm hz₀A hg
  have hFA : Subgroup.closure ({z₀, g} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hz₀A
    · rw [Set.mem_singleton_iff.mp hy]
      exact hg
  have hcard : Nat.card (Subgroup.closure ({z₀, g} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hg2 hc.ne_one hg1 (fun e => hgz e.symm) hcomm
  have hF : Subgroup.closure ({z₀, g} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have hα : alphaCore (Subgroup.closure ({z₀, g} : Set G)) = ⊥ :=
    TypeCSetup.alphaCore_eq_bot_of_rankTwoSpan_eq_top hO hbal hgen hF
  exact Theorem5.mem_centralizer_of_alphaCore_eq_bot hcls (htq hg) hg2 hc.ne_one hα x hx

end Frame

section Inputs


end Inputs

section P1


end P1

end CFSG.ClassicalInvolution.Asc77
