module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (blockSL B12 B23 LinearBlockStandardPair pair_normalize
  pair_block_inj coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

section Transport

variable {K K' : Type} [Field K] [Field K']

theorem slMap_injective (e : K ≃+* K') (m : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map e.toRingHom : SL(m, K) →* SL(m, K')) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
  exact Matrix.map_injective e.injective h'

theorem slMap_surjective (e : K ≃+* K') (m : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map e.toRingHom : SL(m, K) →* SL(m, K')) := by
  intro b
  refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom b, ?_⟩
  apply Subtype.ext
  ext i j
  simp


theorem range_comp_of_surjective {A B C : Type*} [Group A] [Group B] [Group C] (g : B →* C)
    {f : A →* B} (hf : Function.Surjective f) : (g.comp f).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, Subgroup.map_top]

end Transport

section Pairs

variable {G : Type} [Group G] {F : Type} [Field F]


theorem exists_pairB_zmod (e : ZMod 3 ≃+* F) {W U V : Subgroup G}
    (h : SymplecticBlockStandardPair F W U V) :
    ∃ θ : StatedSp 2 (ZMod 3) →* G,
      Function.Injective (θ.comp (longBlock (ZMod 3) 2 1)) ∧
      Function.Injective
        (θ.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))) ∧
      (longBlock (ZMod 3) 2 1).range.map θ = U ∧
      (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map θ = V := by
  obtain ⟨θ, c, -, -, hinjL, hinjS, hU, hV⟩ := h
  let θ0 : StatedSp 2 F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  let Φ2 : SL(2, ZMod 3) →* SL(2, F) := Matrix.SpecialLinearGroup.map e.toRingHom
  let Sp2 : StatedSp 2 (ZMod 3) →* StatedSp 2 F := spMap e.toRingHom
  have cL : (θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1) = (θ0.comp (longBlock F 2 1)).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_longBlock e.toRingHom 1 A)
  have cS : (θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_shortBlock e.toRingHom zero_ne_one A)
  refine ⟨θ0.comp Sp2, ?_, ?_, ?_, ?_⟩
  · rw [cL]
    exact hinjL.comp (slMap_injective e 2)
  · rw [cS]
    exact hinjS.comp (slMap_injective e 2)
  · calc (longBlock (ZMod 3) 2 1).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1)).range := (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (longBlock F 2 1)).range := by
          rw [cL]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = U := hU
  · calc (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).range := by
          rw [cS]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
            (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = V := hV

end Pairs

theorem natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  simpa using GaloisField.card 3 1 one_ne_zero

theorem nonempty_ringEquiv_galoisField_three : Nonempty (ZMod 3 ≃+* GaloisField 3 1) := by
  have := Fintype.ofFinite (GaloisField 3 1)
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, natCard_galoisField_three])⟩


end CFSG.ClassicalInvolution.Q3.Q3Z
