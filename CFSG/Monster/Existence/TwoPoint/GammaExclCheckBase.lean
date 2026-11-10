
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclDefBase

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

theorem gx_fix_of_commute {y g : SpaceB ≃ₗ[ℚ] SpaceB} (hy : y ∈ Gmat) (hg : g ∈ Gmat)
    (h : g * (y * tStar * y⁻¹) = (y * tStar * y⁻¹) * g) : g (y aStar) = y aStar := by
  have hmem : y⁻¹ * g * y ∈ Gmat := Gmat.mul_mem (Gmat.mul_mem (Gmat.inv_mem hy) hg) hy
  have hc : y⁻¹ * g * y * tStar = tStar * (y⁻¹ * g * y) := by
    calc y⁻¹ * g * y * tStar = y⁻¹ * (g * (y * tStar * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * tStar * y⁻¹) * g) * y := by rw [h]
      _ = tStar * (y⁻¹ * g * y) := by group
  have h2 : y⁻¹ (g (y aStar)) = aStar := (mul_tStar_comm_iff hmem).1 hc
  calc g (y aStar) = y (y⁻¹ (g (y aStar))) := (y.apply_symm_apply _).symm
    _ = y aStar := by rw [h2]

@[expose] noncomputable def GmatM : Subgroup MGriess := Gmat.comap AutO.subtype

theorem fiMkW_mem_GmatM (w : List Native.Gen) : fiMkW w ∈ GmatM := wordLin_mem_Gmat w

theorem gxElem_mem_GmatM (k : ℕ) : gxElem k ∈ GmatM := by
  rw [← fiMkW_gxElemWord]
  exact fiMkW_mem_GmatM _

@[expose] noncomputable def gxD : MGriess := fiMkW fiCAlpha

@[expose] noncomputable def gxAxis (j : ℕ) : SpaceB := (xHat j * gxD).1 aStar


theorem fiMkW_wordBetaPrime : fiMkW (fiWAlpha ++ fiWBeta ++ fiWAlpha) = betaPrime := by
  rw [fiMkW_append, fiMkW_append]
  show fiAlpha * (fiBeta * fiAlpha) = fiAlpha * fiBeta * fiAlpha
  rw [mul_assoc]

@[expose] def gxYWord (j : ℕ) : List Native.Gen := fiCAlpha ++ gxProdWord (gxXList j)

@[expose] def gxBPWord : List Native.Gen := fiWAlpha ++ fiWBeta ++ fiWAlpha

@[expose] def gxNodeNe (j : ℕ) : Prop :=
  (j ≠ 9 → wordLin (gxYWord j ++ fiWAlpha) aStar ≠ wordLin (gxYWord j) aStar) ∧
    wordLin (gxYWord j ++ gxBPWord) aStar ≠ wordLin (gxYWord j) aStar

theorem gxNodeNe_of {j : ℕ}
    (h : wordLin (gxYWord j ++ fiWAlpha) aStar ≠ wordLin (gxYWord j) aStar ∧
      wordLin (gxYWord j ++ gxBPWord) aStar ≠ wordLin (gxYWord j) aStar) : gxNodeNe j :=
  ⟨fun _ => h.1, h.2⟩

end CFSG.Monster.Existence
