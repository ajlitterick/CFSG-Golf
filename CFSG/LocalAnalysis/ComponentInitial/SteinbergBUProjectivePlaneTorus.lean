module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] {p : ℕ}

@[expose] def torusHom (P : GL (Fin p) K) : (Fin p → Kˣ) →* ProjGenLinGroup (Fin p) K :=
  mk.comp ((MulAut.conj P).toMonoidHom.comp TauCeti.diagGL)

theorem torusHom_apply (P : GL (Fin p) K) (x : Fin p → Kˣ) :
    torusHom P x = mk (P * TauCeti.diagGL x * P⁻¹) :=
  rfl

theorem diagGL_eq_scalar_iff (x : Fin p → Kˣ) (u : Kˣ) :
    TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) u ↔ ∀ i, x i = u := by
  constructor
  · intro h i
    have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K) i i) h
    simp only [TauCeti.diagGL_coe, diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
      scalar_apply] at h1
    exact Units.ext h1
  · intro h
    rw [show x = fun _ => u from funext h, TauCeti.diagGL_const]

theorem torusHom_eq_one_iff [NeZero p] (P : GL (Fin p) K) (x : Fin p → Kˣ) :
    torusHom P x = 1 ↔ ∀ i j, x i = x j := by
  rw [torusHom_apply, mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, hu⟩ i j
    have h : TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) u := by
      have hc := (Subgroup.mem_center_iff.1 (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩ :
          GeneralLinearGroup.scalar (Fin p) u ∈ Subgroup.center (GL (Fin p) K)) P).symm
      calc TauCeti.diagGL x = P⁻¹ * (P * TauCeti.diagGL x * P⁻¹) * P := by group
        _ = GeneralLinearGroup.scalar (Fin p) u := by rw [← hu, mul_assoc, hc, inv_mul_cancel_left]
    have hx := (diagGL_eq_scalar_iff x u).1 h
    rw [hx i, hx j]
  · intro h
    refine ⟨x 0, ?_⟩
    rw [show TauCeti.diagGL x = GeneralLinearGroup.scalar (Fin p) (x 0) from
      (diagGL_eq_scalar_iff x (x 0)).2 fun i => h i 0]
    have hc := (Subgroup.mem_center_iff.1 (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨x 0, rfl⟩ :
        GeneralLinearGroup.scalar (Fin p) (x 0) ∈ Subgroup.center (GL (Fin p) K)) P)
    rw [hc]
    group


theorem torusHom_comm (P : GL (Fin p) K) (x y : Fin p → Kˣ) :
    torusHom P x * torusHom P y = torusHom P y * torusHom P x := by
  rw [← map_mul, ← map_mul, mul_comm]


@[expose] def rootTorusHom (P : GL (Fin p) K) :
    (Fin p → rootsOfUnity p K) →* ProjGenLinGroup (Fin p) K :=
  (torusHom P).comp (MonoidHom.compLeft (rootsOfUnity p K).subtype (Fin p))

theorem rootTorusHom_apply (P : GL (Fin p) K) (f : Fin p → rootsOfUnity p K) :
    rootTorusHom P f = torusHom P fun i => (f i : Kˣ) :=
  rfl


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
