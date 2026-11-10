module

public import CFSG.ClassicalInvolution.Q3.Q3UWiel
public import CFSG.ClassicalInvolution.Q3.Q3MApp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Orbit

variable {Y : Type} [Group Y] {L T : Subgroup Y}

@[expose] def layerOrbit (L T : Subgroup Y) : Subgroup Y := ⨆ l ∈ L, conjSub l T

theorem conjSub_le_layerOrbit {l : Y} (hl : l ∈ L) : conjSub l T ≤ layerOrbit L T :=
  le_iSup₂_of_le l hl le_rfl

theorem le_layerOrbit : T ≤ layerOrbit L T := by
  have := conjSub_le_layerOrbit (T := T) (L.one_mem)
  rwa [conjSub_one] at this

theorem conjSub_layerOrbit_le {l : Y} (hl : l ∈ L) :
    conjSub l (layerOrbit L T) ≤ layerOrbit L T := by
  unfold layerOrbit
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun l' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hl' => ?_
  have h : (conjSub l' T).map (MulAut.conj l).toMonoidHom = conjSub (l * l') T := by
    rw [conjSub_mul]
    rfl
  rw [h]
  exact conjSub_le_layerOrbit (L.mul_mem hl hl')

theorem conjSub_layerOrbit {l : Y} (hl : l ∈ L) : conjSub l (layerOrbit L T) = layerOrbit L T := by
  refine le_antisymm (conjSub_layerOrbit_le hl) ?_
  have h := conjSub_mono (n := l) (conjSub_layerOrbit_le (T := T) (L.inv_mem hl))
  rwa [conjSub_conjSub_inv] at h

theorem layerOrbit_normal (hTL : T ⊔ L = ⊤) : (layerOrbit L T).Normal := by
  have h : T ⊔ L ≤ Subgroup.normalizer (layerOrbit L T : Set Y) := by
    refine sup_le (fun t ht => ?_) (fun l hl => ?_)
    · exact Subgroup.le_normalizer (le_layerOrbit ht)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := conjSub_layerOrbit (T := T) hl
      constructor
      · intro hy
        have := conj_mem_conjSub (n := l) hy
        rwa [h] at this
      · intro hy
        rw [← h, mem_conjSub_iff] at hy
        have e : l⁻¹ * (l * y * l⁻¹) * l = y := by group
        rwa [e] at hy
  rw [hTL, top_le_iff, Subgroup.normalizer_eq_top_iff] at h
  exact h

end Orbit

section Centralizer


end Centralizer

end CFSG.ClassicalInvolution.Q3
