module

public import CFSG.Quasithin.Background.F2Equiv
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

universe u v w w'

namespace Amalgam

open Completion

section Setting

variable (D : Type u) [Preorder D] (Y : Type w) [Group Y]

structure XYSetting where
  Xd : D → Subgroup Y
  Yd : D → Subgroup Y
  mono_X : Monotone Xd
  mono_Y : Monotone Yd
  le : ∀ d, Xd d ≤ Yd d
  normal : ∀ d, ((Xd d).subgroupOf (Yd d)).Normal
  gen_Y : ⨆ d, Yd d = ⊤
  least : D
  least_le : ∀ d, least ≤ d

end Setting

namespace XYSetting

variable {D : Type u} [Preorder D] {Y : Type w} [Group Y] (S : XYSetting D Y)

abbrev alpha : Amalgam.{u, w} D := ofSubgroups S.Xd S.mono_X


theorem conj_mem {d : D} {y : Y} (hy : y ∈ S.Yd d) {x : Y} (hx : x ∈ S.Xd d) :
    y * x * y⁻¹ ∈ S.Xd d := by
  have h := (S.normal d).conj_mem ⟨x, S.le d hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem conj_inv_mem {d : D} {y : Y} (hy : y ∈ S.Yd d) {x : Y} (hx : x ∈ S.Xd d) :
    y⁻¹ * x * y ∈ S.Xd d := by
  have := S.conj_mem ((S.Yd d).inv_mem hy) hx
  simpa using this

@[expose] def conjX (d : D) (y : S.Yd d) : MulAut (S.Xd d) where
  toFun x := ⟨y * x * y⁻¹, S.conj_mem y.2 x.2⟩
  invFun x := ⟨y⁻¹ * x * y, S.conj_inv_mem y.2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x x' := Subtype.ext (by simp [mul_assoc])

@[expose] def cAut (y : S.Yd S.least) : Aut S.alpha :=
  ⟨fun d => S.conjX d ⟨y, S.mono_Y (S.least_le d) y.2⟩, fun {_ _} _ _ => Subtype.ext rfl⟩


@[expose] def c : S.Yd S.least →* Aut S.alpha where
  toFun := S.cAut
  map_one' := by
    apply Subtype.ext
    funext d
    ext x
    show (1 : Y) * x * (1 : Y)⁻¹ = x
    simp
  map_mul' y y' := by
    apply Subtype.ext
    funext d
    ext x
    show ((y * y' : S.Yd S.least) : Y) * x * ((y * y' : S.Yd S.least) : Y)⁻¹ =
      (y : Y) * ((y' : Y) * x * (y' : Y)⁻¹) * (y : Y)⁻¹
    simp [mul_assoc]


section Completions

variable {G : Type w'} [Group G]


end Completions

section Lemma211

variable {G : Type w'} [Group G]

structure Hyp211 (μ : Completion S.alpha G) : Prop where
  faithful : μ.IsFaithful
  stab : ∀ y : S.Yd S.least, S.c y ∈ stabilizer μ
  inter_trivial :
    (⨅ d, (Subgroup.centralizer (S.Xd d : Set Y)).subgroupOf (S.Yd S.least)) = ⊥
  factor : ∀ d, ∀ g ∈ S.Yd d, ∃ y ∈ S.Yd S.least, ∃ x ∈ S.Xd d, g = y * x
  inter : ∀ d, S.Yd S.least ⊓ S.Xd d = S.Xd S.least


variable {S}

namespace Hyp211

variable {μ : Completion S.alpha G} (h : S.Hyp211 μ)


end Hyp211

end Lemma211

end XYSetting

namespace Completion

variable {D : Type u} [Preorder D] {α : Amalgam.{u, v} D} {G : Type w'} [Group G]


theorem conj_eq_one_iff {g : G} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut G => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group


end Completion

namespace XYSetting


namespace Hyp211


end Hyp211

end XYSetting

end Amalgam

end CFSG.Quasithin
