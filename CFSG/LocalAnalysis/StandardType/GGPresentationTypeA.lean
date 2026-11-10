module

public import CFSG.LocalAnalysis.StandardType.GGPresentationReduce
public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear

variable (m : ℕ) (F : Type) [Field F]

theorem exists_weyl_toStd (π : Equiv.Perm (Fin (m + 1))) :
    ∃ w : (coxeterMatrix (isFiniteType_A m)).Group,
      ∀ γ, toStd m (weylAction (isFiniteType_A m) w γ) = fun a => toStd m γ (π.symm a) := by
  have hmem : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top π
  induction hmem using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨(coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k, fun γ => ?_⟩
    rw [weylAction_simple, toStd_reflection]
    funext a
    simp
  | one => exact ⟨1, fun γ => by rw [map_one, Module.End.one_apply]; rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨w₁, h₁⟩ := ihx
    obtain ⟨w₂, h₂⟩ := ihy
    refine ⟨w₁ * w₂, fun γ => ?_⟩
    rw [weylAction_mul_apply, h₁, h₂]
    funext a
    simp [Equiv.Perm.mul_def]


@[expose] def TypeARealizes (w : (coxeterMatrix (isFiniteType_A m)).Group)
    (π : Equiv.Perm (Fin (m + 1))) : Prop :=
  ∀ γ, toStd m (weylAction (isFiniteType_A m) w γ) = fun a => toStd m γ (π.symm a)

theorem typeARealizes_one : TypeARealizes m 1 1 := fun γ => by
  rw [map_one, Module.End.one_apply]
  rfl

theorem typeARealizes_mul {w₁ w₂ : (coxeterMatrix (isFiniteType_A m)).Group}
    {π₁ π₂ : Equiv.Perm (Fin (m + 1))} (h₁ : TypeARealizes m w₁ π₁)
    (h₂ : TypeARealizes m w₂ π₂) : TypeARealizes m (w₁ * w₂) (π₁ * π₂) := fun γ => by
  rw [weylAction_mul_apply, h₁, h₂]
  funext a
  simp [Equiv.Perm.mul_def]

theorem typeARealizes_simple (k : Fin m) :
    TypeARealizes m ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k)
      (Equiv.swap k.castSucc k.succ) := fun γ => by
  rw [weylAction_simple, toStd_reflection]
  funext a
  simp

theorem exists_typeARealizes (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    ∃ π, TypeARealizes m w π := by
  induction w using (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple_induction_left with
  | one => exact ⟨1, typeARealizes_one m⟩
  | mul_simple_left w k ih =>
    obtain ⟨π, hπ⟩ := ih
    exact ⟨_, typeARealizes_mul m (typeARealizes_simple m k) hπ⟩

theorem typeARealizes_inj {w w' : (coxeterMatrix (isFiniteType_A m)).Group}
    {π : Equiv.Perm (Fin (m + 1))} (h : TypeARealizes m w π) (h' : TypeARealizes m w' π) :
    w = w' :=
  weylAction_injective (isFiniteType_A m)
    (LinearMap.ext fun γ => toStd_injective m ((h γ).trans (h' γ).symm))


end CFSG.StandardType
