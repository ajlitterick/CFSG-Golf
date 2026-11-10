module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ABGLocalTools

@[expose] def OutTwo (Y : Type) [Group Y] : Prop :=
  ∀ α β : MulAut Y, (∃ l : Y, α = MulAut.conj l) ∨ (∃ l : Y, β = MulAut.conj l) ∨
    ∃ l : Y, α⁻¹ * β = MulAut.conj l

@[expose] def autTransport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') :
    MulAut Y' ≃* MulAut Y :=
  MulAut.congr e.symm

theorem autTransport_apply {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (a : MulAut Y')
    (y : Y) : autTransport e a y = e.symm (a (e y)) := rfl

theorem autTransport_conj {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (l : Y) :
    autTransport e (MulAut.conj (e l)) = MulAut.conj l := by
  ext y
  simp [autTransport_apply, MulAut.conj_apply]

theorem OutTwo.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : OutTwo Y) :
    OutTwo Y' := by
  intro α β
  have key : ∀ γ : MulAut Y', (∃ l : Y, autTransport e γ = MulAut.conj l) →
      ∃ l : Y', γ = MulAut.conj l := by
    rintro γ ⟨l, hl⟩
    refine ⟨e l, (autTransport e).injective ?_⟩
    rw [hl, autTransport_conj]
  rcases h (autTransport e α) (autTransport e β) with h1 | h1 | h1
  · exact Or.inl (key α h1)
  · exact Or.inr (Or.inl (key β h1))
  · refine Or.inr (Or.inr (key (α⁻¹ * β) ?_))
    rwa [map_mul, map_inv]

@[expose] def TwoCentralAut {Y : Type} [Group Y] (σ : MulAut Y) : Prop :=
  2 ^ (Nat.card Y).factorization 2 ∣ Nat.card (fixSubgroup σ)

theorem card_fixSubgroup_autTransport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (σ : MulAut Y') : Nat.card (fixSubgroup (autTransport e σ)) = Nat.card (fixSubgroup σ) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)
  show autTransport e σ y = y ↔ σ (e y) = e y
  rw [autTransport_apply]
  exact MulEquiv.symm_apply_eq e

theorem twoCentralAut_autTransport_iff {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (σ : MulAut Y') : TwoCentralAut (autTransport e σ) ↔ TwoCentralAut σ := by
  unfold TwoCentralAut
  rw [card_fixSubgroup_autTransport, Nat.card_congr e.toEquiv]

@[expose] def AutCenterCond2 (Y : Type) [Group Y] : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν → (∀ y : Y, ν y = y → σ y = y) →
    σ = 1 ∨ σ = ν ∨ ¬ TwoCentralAut σ

theorem AutCenterCond2.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : AutCenterCond2 Y) : AutCenterCond2 Y' := by
  intro ν σ hν hσ hνσ hfix
  have h1 := h (autTransport e ν) (autTransport e σ) (by rw [← map_mul, hν, map_one])
    (by rw [← map_mul, hσ, map_one]) (by rw [← map_mul, ← map_mul, hνσ]) (by
      intro y hy
      rw [autTransport_apply] at hy ⊢
      have h2 : ν (e y) = e y := by
        have := congrArg e hy
        rwa [MulEquiv.apply_symm_apply] at this
      rw [hfix _ h2, MulEquiv.symm_apply_apply])
  rcases h1 with h1 | h1 | h1
  · exact Or.inl ((autTransport e).injective (h1.trans (map_one _).symm))
  · exact Or.inr (Or.inl ((autTransport e).injective h1))
  · exact Or.inr (Or.inr fun h' => h1 ((twoCentralAut_autTransport_iff e σ).2 h'))


end CFSG.EvenSporadicStandard.Solomon78
