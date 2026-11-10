module

public import CFSG.Quasithin.Background.G9GolayRelabel
public import CFSG.Quasithin.Background.B4ModelsSporadic

public section

namespace CFSG.Quasithin.G11

@[expose] def GolayCorr (T : Equiv.Perm (Fin 24)) (S : Submodule (ZMod 2) GolayAmbient)
    (G : Subgroup (G6.PermMod 24)) : Prop :=
  ∀ w : GolayAmbient, w ∈ S ↔ Multiplicative.ofAdd (permAct T w) ∈ G

theorem GolayCorr.inf {T : Equiv.Perm (Fin 24)} {S₁ S₂ : Submodule (ZMod 2) GolayAmbient}
    {G₁ G₂ : Subgroup (G6.PermMod 24)} (h₁ : GolayCorr T S₁ G₁) (h₂ : GolayCorr T S₂ G₂) :
    GolayCorr T (S₁ ⊓ S₂) (G₁ ⊓ G₂) := by
  intro w
  rw [Submodule.mem_inf, Subgroup.mem_inf, h₁ w, h₂ w]

theorem GolayCorr.sup {T : Equiv.Perm (Fin 24)} {S₁ S₂ : Submodule (ZMod 2) GolayAmbient}
    {G₁ G₂ : Subgroup (G6.PermMod 24)} (h₁ : GolayCorr T S₁ G₁) (h₂ : GolayCorr T S₂ G₂) :
    GolayCorr T (S₁ ⊔ S₂) (G₁ ⊔ G₂) := by
  intro w
  constructor
  · intro hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hw
    rw [← hyz, golay_permAct_add, ofAdd_add]
    exact Subgroup.mul_mem_sup ((h₁ y).mp hy) ((h₂ z).mp hz)
  · intro hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hw
    set a : GolayAmbient := permAct T⁻¹ (Multiplicative.toAdd y) with ha
    set b : GolayAmbient := permAct T⁻¹ (Multiplicative.toAdd z) with hb
    have ha' : a ∈ S₁ := by
      apply (h₁ a).mpr
      rw [ha, golay_permAct_inv_cancel, ofAdd_toAdd]
      exact hy
    have hb' : b ∈ S₂ := by
      apply (h₂ b).mpr
      rw [hb, golay_permAct_inv_cancel, ofAdd_toAdd]
      exact hz
    have hab : a + b = w := by
      apply golay_permAct_injective T
      rw [golay_permAct_add, ha, hb, golay_permAct_inv_cancel, golay_permAct_inv_cancel]
      have h := congrArg Multiplicative.toAdd hyz
      rw [toAdd_mul, toAdd_ofAdd] at h
      exact h
    rw [← hab]
    exact Submodule.add_mem_sup ha' hb'


end CFSG.Quasithin.G11
