module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.CentralCover

variable {X : Type*} [Group X]

@[expose] def IsCocycle₂ (d : X × X → ZMod 2) : Prop :=
  ∀ g h k, d (g * h, k) + d (g, h) = d (h, k) + d (g, h * k)


structure Cocycle₂ (X : Type*) [Group X] where
  f : X × X → ZMod 2
  cond : IsCocycle₂ f

@[ext] structure CExt (c : Cocycle₂ X) where
  fst : ZMod 2
  snd : X

namespace CExt

variable (c : Cocycle₂ X)

theorem f_one_left (g : X) : c.f (1, g) = c.f (1, 1) := by
  have h := c.cond 1 1 g
  rw [one_mul, one_mul] at h
  exact (add_left_cancel h).symm


instance : Mul (CExt c) := ⟨fun x y => ⟨x.fst + y.fst + c.f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One (CExt c) := ⟨⟨-c.f (1, 1), 1⟩⟩

instance : Inv (CExt c) := ⟨fun x => ⟨-c.f (1, 1) - x.fst - c.f (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩


instance : Group (CExt c) :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine CExt.ext ?_ (mul_assoc x.snd y.snd z.snd)
      change x.fst + y.fst + c.f (x.snd, y.snd) + z.fst + c.f (x.snd * y.snd, z.snd) =
        x.fst + (y.fst + z.fst + c.f (y.snd, z.snd)) + c.f (x.snd, y.snd * z.snd)
      linear_combination c.cond x.snd y.snd z.snd)
    (fun x => by
      refine CExt.ext ?_ (one_mul x.snd)
      change -c.f (1, 1) + x.fst + c.f (1, x.snd) = x.fst
      rw [f_one_left c x.snd]
      ring)
    (fun x => by
      refine CExt.ext ?_ (inv_mul_cancel x.snd)
      change -c.f (1, 1) - x.fst - c.f (x.snd⁻¹, x.snd) + x.fst + c.f (x.snd⁻¹, x.snd) =
        -c.f (1, 1)
      ring)


@[expose] def ι (a : ZMod 2) : CExt c := ⟨a - c.f (1, 1), 1⟩


instance [Finite X] : Finite (CExt c) :=
  Finite.of_injective (fun x : CExt c => (x.fst, x.snd)) fun _ _ h =>
    CExt.ext (congrArg Prod.fst h) (congrArg Prod.snd h)


end CExt

open CExt

section Words


end Words


section Hom


end Hom

section Main


end Main

end CFSG.LocalAnalysis.CentralCover
