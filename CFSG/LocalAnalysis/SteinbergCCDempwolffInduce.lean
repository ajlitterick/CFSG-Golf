module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffPermH1

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix


structure VCocycle where
  f : G × G → V
  cond : ∀ g h j, f (g * h, j) + f (g, h) = ρV g (f (h, j)) + f (g, h * j)

namespace VCocycle

variable (c : VCocycle)

theorem f_one_left (g : G) : c.f (1, g) = c.f (1, 1) := by
  have h := c.cond 1 1 g
  rw [one_mul, one_mul, map_one] at h
  change c.f (1, g) + c.f (1, 1) = c.f (1, g) + c.f (1, g) at h
  exact (add_left_cancel h).symm

@[ext] structure Ext (_c : VCocycle) where
  fst : V
  snd : G

noncomputable instance : Mul c.Ext :=
  ⟨fun x y => ⟨x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One c.Ext := ⟨⟨-c.f (1, 1), 1⟩⟩

noncomputable instance : Inv c.Ext :=
  ⟨fun x => ⟨-c.f (1, 1) - ρV x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩


noncomputable instance : Group c.Ext :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine Ext.ext ?_ (mul_assoc x.snd y.snd z.snd)
      change x.fst + ρV x.snd y.fst + c.f (x.snd, y.snd) + ρV (x.snd * y.snd) z.fst +
          c.f (x.snd * y.snd, z.snd) =
        x.fst + ρV x.snd (y.fst + ρV y.snd z.fst + c.f (y.snd, z.snd)) +
          c.f (x.snd, y.snd * z.snd)
      rw [map_mul, LinearEquiv.mul_apply, map_add, map_add]
      have := c.cond x.snd y.snd z.snd
      calc _ = x.fst + ρV x.snd y.fst + ρV x.snd (ρV y.snd z.fst) +
            (c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd)) := by abel
        _ = _ := by rw [this]; abel)
    (fun x => by
      refine Ext.ext ?_ (one_mul x.snd)
      change -c.f (1, 1) + ρV 1 x.fst + c.f (1, x.snd) = x.fst
      rw [map_one, c.f_one_left x.snd]
      change -c.f (1, 1) + x.fst + c.f (1, 1) = x.fst
      abel)
    (fun x => by
      refine Ext.ext ?_ (inv_mul_cancel x.snd)
      change -c.f (1, 1) - ρV x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd) + ρV x.snd⁻¹ x.fst +
        c.f (x.snd⁻¹, x.snd) = -c.f (1, 1)
      abel)

@[expose] def ι (a : V) : c.Ext := ⟨a - c.f (1, 1), 1⟩


end VCocycle

section Induce


end Induce

end CFSG.LocalAnalysis.DempwolffFive
