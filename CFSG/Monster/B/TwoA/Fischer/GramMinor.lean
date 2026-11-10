module

public import CFSG.Monster.B.TwoA.Fischer.CanonicalIdent
public import CFSG.Monster.B.TwoA.Fischer.CertGram
public import CFSG.Monster.B.TwoA.Fischer.GramData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open scoped IsMulCommutative Matrix

theorem jWord_mem_J :
    ∀ w : List ℕ, (∀ k ∈ w, k < 13) → Cert.jWord w ∈ J
  | [], _ => J.one_mem
  | k :: w, hw => by
    have hk : jGen k ∈ J := by
      rw [J_eq_closure_jGen]
      exact Subgroup.subset_closure ⟨⟨k, hw k List.mem_cons_self⟩, rfl⟩
    exact J.mul_mem hk (jWord_mem_J w fun k' hk' => hw k' (List.mem_cons_of_mem k hk'))

theorem jWord_labelWord_mem_J
    {i : ℕ} (hi : i < 78) : Cert.jWord (Cert.labelWord i) ∈ J :=
  jWord_mem_J _ (Cert.fischer_gram_minor_certificate.2.1 i hi)

theorem rowsMatrix_gramRowArr (i k : Fin 78) :
    rowsMatrix 78 Cert.gramRowArr i k = if (Cert.gramRow i).testBit k then 1 else 0 := by
  rw [rowsMatrix_apply, toVecD_apply, Cert.gramRow, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?]
  rfl

theorem gramMinor_det_ne_zero :
    (rowsMatrix 78 Cert.gramRowArr).det ≠ 0 :=
  Cert.fischer_gram_minor_certificate.2.2.2.2.2

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (Y) in
@[expose] def gramPt
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (i : ℕ) : Y :=
  Φ.symm (Cert.jWord (Cert.labelWord i) o)

theorem ι_gramPt
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) {i : ℕ} (hi : i < 78) :
    (ι (Φ (gramPt Y Φ i)) : ℕ) = Cert.basisPt i := by
  rw [gramPt, Equiv.apply_symm_apply]
  exact Cert.ι_jWord_o hi


namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y) {Φ : Y ≃ CFSG.Monster.B.Fischer.Y}
  {ψ : sliceGroup lab Y ≃* J}
  (hψ : ∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
    (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w)
  {x : V} (hx : x ∈ Y) (hxo : Φ ⟨x, hx⟩ = o)
  (hxT : (ψ ⟨lab x, lab_mem_sliceGroup hx⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm)
include hS hψ hxo hxT

theorem psi_lab_gramPt
    {i : ℕ} (hi : i < 78) :
    (ψ ⟨lab (gramPt Y Φ i), lab_mem_sliceGroup (gramPt Y Φ i).2⟩ :
      Equiv.Perm CFSG.Monster.B.Fischer.Y) = Cert.jLabel (Cert.labelWord i) := by
  set g : J := ⟨Cert.jWord (Cert.labelWord i), jWord_labelWord_mem_J hi⟩ with hg
  set h : sliceGroup lab Y := ψ.symm g with hh
  have hψh : ψ h = g := ψ.apply_symm_apply g
  have hmem : act (h : S) x ∈ Y := hS.mapsTo _ h.2 x hx
  have h1 := hψ h ⟨x, hx⟩ ⟨act (h : S) x, hmem⟩ rfl
  rw [hxo, hψh] at h1
  have h1' : Cert.jWord (Cert.labelWord i) o = Φ ⟨act (h : S) x, hmem⟩ := h1
  have h2 : (⟨act (h : S) x, hmem⟩ : Y) = gramPt Y Φ i := by
    rw [gramPt, h1', Equiv.symm_apply_apply]
  have h3 : (⟨lab (gramPt Y Φ i), lab_mem_sliceGroup (gramPt Y Φ i).2⟩ : sliceGroup lab Y) =
      h * ⟨lab x, lab_mem_sliceGroup hx⟩ * h⁻¹ := by
    rw [← h2]
    exact Subtype.ext (hS.lab_act (h : S) x)
  rw [h3, map_mul, map_mul, map_inv, hψh, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hxT]
  rfl

theorem ncommInd_gramPt
    {i : ℕ} (hi : i < 78) (z : Y) :
    ncommInd lab (gramPt Y Φ i) z = if (Cert.ncRow i).testBit (ι (Φ z)) then 1 else 0 := by
  have hfix : Commute (lab (gramPt Y Φ i)) (lab z) ↔
      ¬(Cert.ncRow i).testBit (ι (Φ z)) = true := by
    rw [← hS.act_lab_eq_iff (gramPt Y Φ i).2 z.2, ← Cert.jLabel_ne_iff hi, not_not,
      ← hS.psi_lab_gramPt hψ hx hxo hxT hi,
      hψ _ z ⟨act (lab (gramPt Y Φ i)) z, hS.mapsTo _ (lab_mem_sliceGroup (gramPt Y Φ i).2) z z.2⟩
        rfl, Φ.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  by_cases hb : (Cert.ncRow i).testBit (ι (Φ z)) = true
  · rw [ncommInd_of_not_commute lab (fun h => hfix.1 h hb), ite_eq_left hb]
  · rw [ncommInd_of_commute lab (hfix.2 hb), ite_eq_right hb]

theorem ncommQuotForm_gramPt
    (i k : Fin 78) :
    ncommQuotForm lab Y (ncommVec lab Y (gramPt Y Φ i)) (ncommVec lab Y (gramPt Y Φ k)) =
      rowsMatrix 78 Cert.gramRowArr i k := by
  rw [ncommQuotForm_ncommVec, hS.ncommInd_gramPt hψ hx hxo hxT i.2, ι_gramPt Φ k.2,
    rowsMatrix_gramRowArr, Cert.testBit_gramRow i.2 k.2]

theorem linearIndependent_gramPt :
    LinearIndependent (ZMod 2) fun i : Fin 78 => ncommVec lab Y (gramPt Y Φ i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hvec : g ᵥ* rowsMatrix 78 Cert.gramRowArr = 0 := by
    funext k
    have h1 := congrArg (fun a => ncommQuotForm lab Y a (ncommVec lab Y (gramPt Y Φ k))) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at h1
    show ∑ i, g i * rowsMatrix 78 Cert.gramRowArr i k = 0
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    rw [hS.ncommQuotForm_gramPt hψ hx hxo hxT i k]
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero gramMinor_det_ne_zero hvec)


end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
