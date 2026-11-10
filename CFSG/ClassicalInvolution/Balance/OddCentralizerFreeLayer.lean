module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceModel
public import CFSG.ClassicalInvolution.Balance.PassTwoWeak
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

section Definitions

variable {G : Type} [Group G]

@[expose] def LayerGenerationAt (E : Subgroup G) (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
    ∀ F₀ : Subgroup G, F₀ ≤ E → Nat.card F₀ = 4 →
      modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) →
      (∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
        OddCentralizerFree (modOdd a F₀) L

end Definitions

@[expose] def IsOddLieBig (L : Type) [Group L] : Prop :=
  ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ 5 ≤ p ^ f ∧
    (t = .PSL → 3 ≤ n) ∧ (t ∈ CFSG.Blueprint.classicalTags ∨
      t ∈ CFSG.Blueprint.chevalleyExceptionalTags) ∧
    CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n p f

@[expose] def IsOddLieComponentBig {X : Type} [Group X] (L : Subgroup X) : Prop :=
  IsOddLieBig ↥L

theorem IsOddLieComponentBig.isOddLieComponent {X : Type} [Group X] {L : Subgroup X}
    (h : IsOddLieComponentBig L) : IsOddLieComponent L := by
  obtain ⟨t, n, p, f, hp, -, hn, ht, hm⟩ := h
  exact ⟨t, n, p, f, hp, hn, ht, hm⟩

@[expose] def LayerGenerationModel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), CFSG.IsComponent L →
    IsOddLieComponentBig L → ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
      F ≤ Subgroup.normalizer (L : Set X) → (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
        L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f

section Reductions

variable {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem LayerGenerationAt.of_model (hE2 : ∀ x ∈ E, x * x = 1) (hmodel : LayerGenerationModel)
    {a : G} (ha : a ∈ E)
    (hbig : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      IsOddLieComponentBig L) : LayerGenerationAt E a := by
  intro L hL hlie F₀ hF₀E h4 hFn hfaith
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  exact OddCentralizerFree.of_le_layers
    (hmodel (OddQuot a) L hL (hbig L hL hlie) (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar hFn hfaith)


end Reductions

section Classical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Generic.IsClassicalMember.isInvolutionMember
    {K : Subgroup G} {z : G} (h : IsClassicalMember p f K z) (hq : 5 ≤ p ^ f) :
    IsInvolutionMember K := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact IsInvolutionMember.of_weakMember
    (⟨h.orderOf_eq_two, h.mem, h.perfect, h.subnormal, h.nonempty_equiv⟩ :
      WeakMember (GaloisField p f) K z) (by rw [hcard]; omega)

omit [Finite G] in
theorem InClass.isInvolutionMember {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hq : 5 ≤ p ^ f) : ∀ K ∈ Ω, IsInvolutionMember K := fun K hK => by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.isInvolutionMember hq

end Classical

section Frame


end Frame

end CFSG.ClassicalInvolution.Balance
