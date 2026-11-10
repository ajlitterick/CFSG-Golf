module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPair
public import CFSG.ClassicalInvolution.RouteD.TypeE8TorGlueNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExcl

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TypeE8

variable {p f : ℕ} [Fact p.Prime]

theorem commutes_of_conjSub_commutes {G : Type} [Group G] {A B : Subgroup G} (g : G)
    (h : Commutes (conjSub g A) (conjSub g B)) : Commutes A B := by
  have := h.conjSub g⁻¹
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem e7Perp2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : E7Perp2 p f := by
  intro R₁ hR₁ R₂ hR₂ hadj hlin
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  obtain ⟨g, hg₁, hg₂⟩ := e7PairFrame hp2 hq R₁ hR₁ R₂ hR₂ hadj hlin 2 3 (by decide)
  have hfund : ∀ a : Fin 7, conjSub g (rankOne (D7 p f).rootGroup a) ∈ F7 p f := fun a =>
    conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamental _ (hl a trivial)) g
  have hnc : ∀ a b : Fin 7, edgeE 7 a b →
      ¬ Commutes (conjSub g (rankOne (D7 p f).rootGroup a))
        (conjSub g (rankOne (D7 p f).rootGroup b)) := fun a b hab h => by
    obtain ⟨W, hW⟩ := stdPair_edge_E7 (F := GaloisField p f) hab
    exact not_commutes_of_linearBlockStandardPair hW (commutes_of_conjSub_commutes g h)
  refine ⟨_, hfund 1, _, hfund 4, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h14 : rankOne (D7 p f).rootGroup (1 : Fin 7) = rankOne (D7 p f).rootGroup (4 : Fin 7) := by
      have := congrArg (conjSub g⁻¹) h
      rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
      exact this
    have h15 := ETCtx.commutes_rankOne_E7 (p := p) (f := f) hadm 1 5 (by decide) (by decide)
      (by decide)
    rw [h14] at h15
    obtain ⟨W, hW⟩ := stdPair_edge_E7 (F := GaloisField p f) (i := 4) (j := 5) (by decide)
    exact not_commutes_of_linearBlockStandardPair hW h15
  · rw [hg₁]
    exact (ETCtx.commutes_rankOne_E7 (p := p) (f := f) hadm 2 1 (by decide) (by decide)
      (by decide)).conjSub g
  · rw [hg₁]
    exact (ETCtx.commutes_rankOne_E7 (p := p) (f := f) hadm 2 4 (by decide) (by decide)
      (by decide)).conjSub g
  · rw [hg₂]
    intro h
    exact hnc 1 3 (by decide) h.symm
  · rw [hg₂]
    intro h
    exact hnc 3 4 (by decide) h

end CFSG.ClassicalInvolution.ModelFacts.E7Model
