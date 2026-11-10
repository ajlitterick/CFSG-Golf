module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsSep
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {f : ℕ} {K : Type} [Field K] [Finite K]

variable (σ : K ≃+* K)


@[expose] def trialityHasKind (τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    AutKind → Prop
  | .inner => IsInnerAut τ
  | .diagonal => False
  | .field => ∃ δ : K ≃+* K, δ ≠ 1 ∧ Nat.Coprime (orderOf δ) 3 ∧
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        τ = MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹
  | .graph => False
  | .graphField => ∃ δ : K ≃+* K, 3 ∣ orderOf δ ∧ IsInnerAut (τ * (fieldActor σ δ)⁻¹)

variable {σ}

section NormalForm

variable (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
include hf hK hσ

theorem exists_conj_mul_fieldActor (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      α = MulAut.conj g * fieldActor σ δ := by
  obtain ⟨-, hex, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hex α
  exact ⟨g, δ, hgδ⟩

theorem isInnerAut_fieldActor_iff {δ : K ≃+* K} :
    IsInnerAut (fieldActor (t := TwistTag.D4) σ δ) ↔ δ = 1 := by
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  constructor
  · intro hin
    have h1 : Θ (fieldActor σ δ) = δ := hΘ _ 1 δ (by rw [map_one, one_mul])
    have h2 : fieldActor (t := TwistTag.D4) σ δ ∈ Θ.ker := by rw [hker]; exact hin
    rw [MonoidHom.mem_ker, h1] at h2
    exact h2
  · rintro rfl
    rw [fieldActor_one]
    exact ⟨1, map_one _⟩

omit hf hK hσ in
theorem fieldActor_mul_comm (δ ε : K ≃+* K) :
    fieldActor (t := TwistTag.D4) σ δ * fieldActor σ ε =
      fieldActor σ ε * fieldActor (t := TwistTag.D4) σ δ := by
  rw [← fieldActor_mul, ← fieldActor_mul,
    CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ ε]

theorem exists_conj_eq_conj_fieldActor
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ δ : K ≃+* K,
      α * fieldActor σ δ * α⁻¹ = MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹ := by
  obtain ⟨g, ε, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ α
  refine ⟨g, fun δ => ?_⟩
  have h1 := fieldActor_mul_comm (σ := σ) ε δ
  calc MulAut.conj g * fieldActor σ ε * fieldActor σ δ * (MulAut.conj g * fieldActor σ ε)⁻¹ =
      MulAut.conj g * (fieldActor σ ε * fieldActor σ δ) * (fieldActor σ ε)⁻¹ *
        (MulAut.conj g)⁻¹ := by group
    _ = _ := by rw [h1]; group


theorem not_isInnerAut_of_trialityHasKind {τ : MulAut (graphFixedRootGroup TwistTag.D4 K
    σ.toRingHom)} {k : AutKind} (hτ : trialityHasKind σ τ k) (hk : k ≠ .inner) :
    ¬ IsInnerAut τ := by
  intro hin
  cases k with
  | inner => exact hk rfl
  | diagonal => exact hτ
  | graph => exact hτ
  | field =>
    obtain ⟨δ, hδ1, -, g, rfl⟩ := hτ
    refine hδ1 ((isInnerAut_fieldActor_iff hf hK hσ).mp ?_)
    have h1 := (isInnerAut_conj_iff (MulAut.conj g)⁻¹ _).mpr hin
    rwa [show (MulAut.conj g)⁻¹ * (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹) *
      (MulAut.conj g)⁻¹⁻¹ = fieldActor σ δ by group] at h1
  | graphField =>
    obtain ⟨δ, h3, hc⟩ := hτ
    have hδ : IsInnerAut (fieldActor (t := TwistTag.D4) σ δ) := by
      rw [show fieldActor (t := TwistTag.D4) σ δ =
        (τ * (fieldActor σ δ)⁻¹)⁻¹ * τ by group]
      exact mul_mem (inv_mem hc) hin
    rw [(isInnerAut_fieldActor_iff hf hK hσ).mp hδ, orderOf_one] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)


end NormalForm

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (σ) in
@[expose] def InducesKindTriality (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    ∃ hx : x ∈ Subgroup.normalizer (L : Set G), trialityHasKind σ (inducedAutHom L e ⟨x, hx⟩) k

variable (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
include hf hK hσ


theorem InducesKindTriality.inducesOuterTheta {x : G} {k : AutKind}
    (h : InducesKindTriality σ L x k) (hk : k ≠ .inner) : InducesOuterTheta x L := by
  obtain ⟨e, hx, h⟩ := h
  exact (not_isInnerAut_inducedAutHom_iff L e hx).mp
    (not_isInnerAut_of_trialityHasKind hf hK hσ h hk)

end Induced

end CFSG.RankThree.PartTwo.KFacts
