module

public import CFSG.ClassicalInvolution.Asc77.AscT7TInv
import CFSG.ClassicalInvolution.Asc77.AscT7U11Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7U

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}


private theorem hyp25F_asc (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    Hyp25F K S R R' z where
  hz2 := hyp.std.setting.hz.sq
  hz1 := hyp.std.setting.hz.ne_one
  hzS := hyp.hzS
  hRS := hyp.hR.2.2
  zA := T7T.z_mem_centralizer_of_hyp hyp
  swap_nf := T7G2.exists_swap_nonfused hyp
  hRne := T7ER.ne_of_hyp25 hyp
  cA := fun hs => T7T.conjSub_centralizer_of_hyp hyp hs
  twin_sq := fun hx =>
      T7T.twin_sq (show Hyp23Setting p f Ω K K' z from hyp.std.setting) hx
  not_norm := fun hg hzt hnf => T7G2.not_normalizes_of_nonfused hyp hg hzt hnf
  c25_5 := fun A hzA hAS hAn hall =>
      T7T.c25_5_proved (p := p) (f := f) G Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAn hall


theorem exists_normal_four_bad (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    (hne : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≠
      Subgroup.zpowers z) :
    ∃ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) ∧
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.exists_normal_four_badE (hyp25F_asc hyp) hne

theorem comm_swap_of_normal_four (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {a : G} (haS : a ∈ (S : Subgroup G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) :
    t' * a = a * t' := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.comm_swap_of_normal_fourE (hyp25F_asc hyp) ht'S ht'2 hg
    hnf haS hconj

section Residual

variable (p f)

@[expose] def C25_11E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
            z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))

end Residual

theorem c25_11_of_E4 (h : C25_11E4 p f) : C25_11 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_contra hne
  obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := exists_normal_four_bad hyp hne
  exact hbad (h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj)


end T7U

end CFSG.ClassicalInvolution.Asc77
