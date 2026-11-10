module

public import CFSG.Monster.B.Dyadic.Reduce
public import Certificates.Certificate3103
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native

@[expose] def Bmat : Matrix (Fin 4371) (Fin 4371) ℤ := fun i j => Bz i j

abbrev denD : ℕ := 128

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

@[expose] noncomputable def ell (R : Module.Basis (Fin 4371) ℚ V) (i : Fin 4371) : V :=
  (1 / (denD : ℚ)) • ∑ j, (Bmat i j : ℚ) • R j

@[expose] def Lam (R : Module.Basis (Fin 4371) ℚ V) : Submodule ℤ V :=
  Submodule.span ℤ (Set.range (ell R))

theorem Bmat_apply (i j : Fin 4371) : Bmat i j = Bz i j := rfl


theorem Pmap_apply (y : Fin 4371 → ZMod 2) (j : Fin 4370) :
    Pmap y j = y (pIdx.succAbove j) + y pIdx * fvec (pIdx.succAbove j) := rfl

theorem Qmat_apply (g : Fin 26) (k t : Fin 4370) :
    Qmat g k t = Pmap (fun j => Cmat g (pIdx.succAbove k) j) t := rfl

theorem fixed_facts : fixedVector.testBit 1197 = true ∧
    ∀ i < 1197, (!fixedVector.testBit i) = true := by
  obtain ⟨-, h1, h2⟩ := Certificates.certificate3103
  exact ⟨h1, fun i hi => by rw [h2 i hi]; rfl⟩

theorem fvec_p : fvec pIdx = 1 := by
  unfold fvec
  exact ite_eq_left fixed_facts.1


theorem Pmap_eq_zero_iff (y : Fin 4371 → ZMod 2) :
    Pmap y = 0 ↔ y = 0 ∨ y = fvec := by
  constructor
  · intro h
    have hy : y = y pIdx • fvec := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove pIdx i with hi | ⟨j, rfl⟩
      · subst hi
        simp [fvec_p]
      · have := congrFun h j
        rw [Pmap_apply, Pi.zero_apply] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← ZMod.neg_eq_self_mod_two (y pIdx * _)]
        exact eq_neg_of_add_eq_zero_left this
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y pIdx) with hp | hp
    · left
      rw [hy, hp, zero_smul]
    · right
      rw [hy, hp, one_smul]
  · rintro (rfl | rfl)
    · exact map_zero Pmap
    · funext j
      rw [Pmap_apply, fvec_p, one_mul, Pi.zero_apply]
      exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

theorem Pmap_single (j : Fin 4370) : Pmap (Pi.single (pIdx.succAbove j) 1) = Pi.single j 1 := by
  funext t
  rw [Pmap_apply, Pi.single_apply, Pi.single_apply, Pi.single_apply,
    ite_eq_right (Fin.succAbove_ne pIdx j).symm, zero_mul, add_zero]
  by_cases h : t = j
  · subst h
    simp
  · rw [ite_eq_right (fun e => h (Fin.succAbove_right_injective e)), ite_eq_right h]

theorem Pmap_surjective : Function.Surjective Pmap := by
  intro z
  refine ⟨Fin.insertNth pIdx 0 z, ?_⟩
  funext j
  rw [Pmap_apply, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, zero_mul, add_zero]

end CFSG.Monster.B.Dyadic

end
