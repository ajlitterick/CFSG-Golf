module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

@[expose] def AutCenterCond (Y : Type) [Group Y] : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν →
    (∀ y : Y, ν y = y → σ y = y) → σ = 1 ∨ σ = ν

@[expose] def AutCenterCondExc (Y : Type) [Group Y] (Exc : MulAut Y → Prop) : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν →
    (∀ y : Y, ν y = y → σ y = y) → σ = 1 ∨ σ = ν ∨ Exc ν

theorem AutCenterCond.toExc {Y : Type} [Group Y] (h : AutCenterCond Y) :
    AutCenterCondExc Y (fun _ => False) := fun ν σ hν hσ hνσ hfix =>
  (h ν σ hν hσ hνσ hfix).imp id Or.inl

theorem AutCenterCondExc.toCond {Y : Type} [Group Y] (h : AutCenterCondExc Y (fun _ => False)) :
    AutCenterCond Y := fun ν σ hν hσ hνσ hfix =>
  (h ν σ hν hσ hνσ hfix).elim Or.inl fun h' => h'.elim Or.inr False.elim

theorem AutCenterCond.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : AutCenterCond Y) : AutCenterCond Y' := by
  intro ν σ hν hσ hνσ hfix
  let φ : MulAut Y' → MulAut Y := fun a => (e.trans a).trans e.symm
  have hφ : ∀ (a : MulAut Y') (y : Y), φ a y = e.symm (a (e y)) := fun a y => rfl
  have hmul : ∀ a b : MulAut Y', φ (a * b) = φ a * φ b := fun a b => MulEquiv.ext fun y => by
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, MulEquiv.apply_symm_apply]
  have hone : φ 1 = 1 := MulEquiv.ext fun y => by
    rw [hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  have h1 := h (φ ν) (φ σ) (by rw [← hmul, hν, hone]) (by rw [← hmul, hσ, hone])
    (by rw [← hmul, ← hmul, hνσ]) (by
      intro y hy
      rw [hφ] at hy ⊢
      have h2 : ν (e y) = e y := by
        have := congrArg e hy
        rwa [MulEquiv.apply_symm_apply] at this
      rw [hfix _ h2, MulEquiv.symm_apply_apply])
  have h3 : ∀ a b : MulAut Y', φ a = φ b → a = b := fun a b hab => MulEquiv.ext fun y' => by
    have := congrArg (fun f : MulAut Y => e (f (e.symm y'))) hab
    simpa [hφ] using this
  rcases h1 with h1 | h1
  · exact Or.inl (h3 _ _ (h1.trans hone.symm))
  · exact Or.inr (h3 _ _ h1)


@[expose] def fixSubgroup {Y : Type} [Group Y] (ν : MulAut Y) : Subgroup Y where
  carrier := {y | ν y = y}
  mul_mem' := fun {a b} (ha : ν a = a) (hb : ν b = b) => by
    show ν (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one ν
  inv_mem' := fun {a} (ha : ν a = a) => by
    show ν a⁻¹ = a⁻¹
    rw [map_inv, ha]


variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem normalizerMonoidHom_coe {g : G} (hg : g ∈ normalizer (L : Set G)) (x : L) :
    ((L.normalizerMonoidHom ⟨g, hg⟩ x : L) : G) = g * x * g⁻¹ := rfl


end CFSG.EvenSporadicStandard.Solomon78
