module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.ASVolI

variable {K : Type} [Field K]

theorem burnsideF411a_ringEquiv_pow [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (ρ : K ≃+* K) : ∃ j : ℕ, ∀ x : K, ρ x = x ^ (p ^ j) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let ρ' : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := ρ) (fun x => by
    have : (ρ.toRingHom).comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
      RingHom.ext_zmod _ _
    exact congrArg (fun f : ZMod p →+* K => f x) this)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p K ρ'
  refine ⟨i, fun x => ?_⟩
  have h1 : ρ x = x ^ (Nat.card (ZMod p) ^ i) := hi x
  rwa [Nat.card_zmod] at h1


end CFSG.ASVolI
