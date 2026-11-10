module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.Cotangent.Localization
import TauCeti.RingTheory.FiniteType.PointSeparation

public section

namespace CFSG

open IsLocalRing Ideal

universe u v


ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
        hmin (by rwa [ringJacobson_eq_maximalIdeal R])
      rw [h, Nat.cast_succ, ENat.WithBot.add_one_cancel] at this
      exact this
    have hane : span {a} ≠ ⊤ := fun htop => (maximalIdeal.isMaximal A).ne_top
      (top_le_iff.mp (htop ▸ (span_singleton_le_iff_mem _).mpr ha))
    have : Nontrivial (A ⧸ span {a}) := Ideal.Quotient.nontrivial_iff.mpr hane
    have : IsLocalRing (A ⧸ span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (span {a})) Ideal.Quotient.mk_surjective
    have hle : span {a} ≤ (span {x}).comap f := by
      rw [span_singleton_le_iff_mem, mem_comap]
      exact mem_span_singleton_self x
    let f' : A ⧸ span {a} →+* R ⧸ span {x} := Ideal.quotientMap (span {x}) f hle
    have hmA : maximalIdeal (A ⧸ span {a}) = (maximalIdeal A).map (Ideal.Quotient.mk _) :=
      (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    have hmR : maximalIdeal (R ⧸ span {x}) = (maximalIdeal R).map (Ideal.Quotient.mk _) :=
      (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    have : IsLocalHom f' := by
      refine ⟨fun y hy => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      by_contra hny
      have hy' : y ∈ maximalIdeal A := (mem_maximalIdeal _).mpr fun hu => hny (hu.map _)
      have hmem : f' (Ideal.Quotient.mk _ y) ∈ maximalIdeal (R ⧸ span {x}) := by
        rw [Ideal.quotientMap_mk, hmR]
        exact mem_map_of_mem _ (map_nonunit f y hy')
      exact (mem_maximalIdeal _).mp hmem hy
    have hres' : ∀ r : R ⧸ span {x}, ∃ c : A ⧸ span {a},
        r - f' c ∈ maximalIdeal (R ⧸ span {x}) := by
      intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨c, hc⟩ := hres r
      refine ⟨Ideal.Quotient.mk _ c, ?_⟩
      rw [Ideal.quotientMap_mk, ← map_sub, hmR]
      exact mem_map_of_mem _ hc
    have hf' : ∀ u ∈ maximalIdeal (A ⧸ span {a}), f' u ∈ maximalIdeal (R ⧸ span {x}) ^ 2 →
        u ∈ maximalIdeal (A ⧸ span {a}) ^ 2 := by
      intro u hu hu2
      rw [hmA, mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hu
      obtain ⟨u, hu, rfl⟩ := hu
      rw [Ideal.quotientMap_mk, hmR, ← Ideal.map_pow,
        mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hu2
      obtain ⟨r, hr, hr'⟩ := hu2
      rw [Ideal.Quotient.eq, mem_span_singleton'] at hr'
      obtain ⟨s, hs⟩ := hr'
      obtain ⟨c, hc⟩ := hres s
      have hmem : f (u + c * a) ∈ maximalIdeal R ^ 2 := by
        have heq : f (u + c * a) = r - (s - f c) * x := by
          rw [map_add, map_mul, hx]
          linear_combination hs
        rw [heq]
        refine sub_mem hr ?_
        rw [pow_two]
        exact mul_mem_mul hc hxm
      have h2 := hf (u + c * a) (add_mem hu (mul_mem_left _ c ha)) hmem
      have heq : Ideal.Quotient.mk (span {a}) u = Ideal.Quotient.mk (span {a}) (u + c * a) := by
        rw [Ideal.Quotient.eq, sub_add_cancel_left, neg_mem_iff]
        exact mul_mem_left _ c (mem_span_singleton_self a)
      rw [heq, hmA, ← Ideal.map_pow]
      exact mem_map_of_mem _ h2
    have hinj' : Function.Injective f' := ih (A ⧸ span {a}) (R ⧸ span {x}) f' hres' hf' hdim
    have hker : ∀ p, f p = 0 → p ∈ span {a} := by
      intro p hp
      have h0 : f' (Ideal.Quotient.mk _ p) = f' 0 := by
        rw [Ideal.quotientMap_mk, hp, map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj' h0)
    have hK : RingHom.ker f = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (span {a}) (RingHom.ker f)
        (RingHom.ker f).fg_of_isNoetherianRing (fun p hp => ?_) ?_
      · obtain ⟨q, rfl⟩ := mem_span_singleton'.mp (hker p (RingHom.mem_ker.mp hp))
        have hq : f q = 0 := by
          have h0 : f q * x = 0 := by rw [hx, ← map_mul]; exact RingHom.mem_ker.mp hp
          exact (mul_eq_zero.mp h0).resolve_right hx0
        rw [mul_comm, ← smul_eq_mul]
        exact Submodule.smul_mem_smul (mem_span_singleton_self a) (RingHom.mem_ker.mpr hq)
      · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top, span_singleton_le_iff_mem]
        exact ha
    exact (RingHom.injective_iff_ker_eq_bot f).mpr hK


end CFSG
