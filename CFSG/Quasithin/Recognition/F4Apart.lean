module

public import CFSG.Quasithin.Recognition.F4Thirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V}


variable {M : ℕ} (hM : 0 < M) {S : Set V} (φ : SimpleGraph.cycleGraph M ≃g Γ.induce S) (i₀ : ℕ)


end GPath

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V}


variable {c : V → Bool}


end GPath

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}
  (F : Facts46 c m)

include F


end RankTwoAmalgam.Completion

namespace RankTwoAmalgam

@[expose] noncomputable def qv (α : RankTwoAmalgam.{u}) (b : Bool) : ℕ :=
  if b then α.qTwo else α.qOne

end RankTwoAmalgam

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y}

omit [Finite Y] in
theorem card_nbrs_smul (g : c.G0) (v : c.Γ) :
    Nat.card (CosetGeom.nbrs (g • v)) = Nat.card (CosetGeom.nbrs v) := by
  have h : CosetGeom.nbrs (g • v) = (fun w => g • w) '' CosetGeom.nbrs v := by
    ext w
    constructor
    · intro hw
      refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
      show c.graph.Adj v (g⁻¹ • w)
      have := (CosetGeom.smul_adj g⁻¹).mpr hw
      rwa [inv_smul_smul] at this
    · rintro ⟨w', hw', rfl⟩
      exact (CosetGeom.smul_adj g).mpr hw'
  rw [h]
  exact Nat.card_image_of_injective (MulAction.injective g) _

theorem card_nbrs (hc : c.IsFaithful) (u : c.Γ) :
    Nat.card (CosetGeom.nbrs u) = α.qv (CosetGeom.vtype u) + 1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have hcard : Nat.card (CosetGeom.nbrs u) =
      Nat.card (CosetGeom.nbrs (c.baseVert (CosetGeom.vtype u))) :=
    calc Nat.card (CosetGeom.nbrs u)
        = Nat.card (CosetGeom.nbrs (g • c.baseVert (CosetGeom.vtype u))) := by rw [hg]
      _ = _ := card_nbrs_smul g _
  have hf1 : Finite α.G1 := Finite.of_injective c.φ1 hc.1
  have hf2 : Finite α.G2 := Finite.of_injective c.φ2 hc.2.2
  have i1 : α.α1.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have i2 : α.α2.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  generalize CosetGeom.vtype u = b at hcard ⊢
  cases b
  · have : Nat.card (CosetGeom.nbrs c.xv) = α.α1.range.index := nbrs_xv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qOne
    simp only [Bool.false_eq_true, ↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.xv) = _
    rw [this]
    omega
  · have : Nat.card (CosetGeom.nbrs c.lv) = α.α2.range.index := nbrs_lv_card hc
    rw [hcard]
    unfold RankTwoAmalgam.qv RankTwoAmalgam.qTwo
    simp only [↓reduceIte]
    show Nat.card (CosetGeom.nbrs c.lv) = _
    rw [this]
    omega

end RankTwoAmalgam.Completion

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}

@[expose] def IsSimplex (c : α.Completion Y) (s : Set c.Γ) : Prop :=
  (∃ a, s = {a}) ∨ ∃ a b, c.graph.Adj a b ∧ s = {a, b}

omit [Finite Y] in
theorem IsSimplex.finite {s : Set c.Γ} (h : IsSimplex c s) : s.Finite := by
  rcases h with ⟨a, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact Set.finite_singleton a
  · exact Set.toFinite _

omit [Finite Y] in
theorem IsSimplex.nonempty {s : Set c.Γ} (h : IsSimplex c s) : s.Nonempty := by
  rcases h with ⟨a, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact Set.singleton_nonempty a
  · exact Set.insert_nonempty _ _


end RankTwoAmalgam.Completion

end CFSG.Quasithin
