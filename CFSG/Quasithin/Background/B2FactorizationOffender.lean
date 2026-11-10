module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem omegaOneOf_le (X : Subgroup G) : omegaOneOf X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem omegaOneCenterOf_le_centerOf (X : Subgroup G) : omegaOneCenterOf X ≤ centerOf X :=
  omegaOneOf_le _

theorem thompsonJ_le_baum (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le_self S) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  exact (omegaOneCenterOf_le_centerOf _ hx).2

theorem baum_le (S : Subgroup G) : baum S ≤ S := inf_le_left

end B2F

section Lemma220

variable [Finite G] {V R : Subgroup G}

theorem inf_centralizer_thompsonJ_le (hV : IsElemAbelian 2 V) (hVR : V ≤ R) :
    V ⊓ Subgroup.centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R) := by
  rw [← (omegaOne_centralizer_thompsonJ R).1]
  intro v hv
  exact Subgroup.subset_closure ⟨⟨hVR hv.1, hv.2⟩, hV.2 v hv.1⟩

theorem B2_20 (hV : IsElemAbelian 2 V) (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G))
    {A : Subgroup (MulAut (IntMod V hV))}
    (hu : ∀ B, IsFFStarOffender (autI hV R) B → B = A)
    (hAC : A = autI hV R ⊓ centSub (fixV A)) :
    A = autI hV (thompsonJ R) ∧ autI hV (thompsonJ R) = autI hV (baum R) := by
  have hne : (offenderImages hV R).Nonempty := (offenderImages_nonempty_iff_not_le hV).2 hJ
  have hP : ∀ B ∈ offenderImages hV R, B = A := fun B hB =>
    hu B (offenderImages_isFFStarOffender hV hVR hRN hB)
  have hJA : autI hV (thompsonJ R) = A := by
    rw [autI_thompsonJ hV hRN]
    refine le_antisymm (iSup_le fun B => iSup_le fun hB => iSup_le fun _ => (hP B hB).le) ?_
    obtain ⟨B, hB⟩ := hne
    have hBA := hP B hB
    rw [← hBA]
    exact le_iSup₂_of_le B hB
      (le_iSup_of_le (offenderImages_isFFStarOffender hV hVR hRN hB).1 le_rfl)
  refine ⟨hJA.symm, le_antisymm (autI_mono hV (B2F.thompsonJ_le_baum R)) ?_⟩
  have hJN : thompsonJ R ≤ Subgroup.normalizer (V : Set G) :=
    (thompsonJ_le_self R).trans hRN
  calc autI hV (baum R) ≤ autI hV R ⊓ centSub (fixV A) := by
        refine le_inf (autI_mono hV (B2F.baum_le R)) ?_
        intro φ hφ
        obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
        rw [mem_centSub]
        intro u hu'
        have hu1 : u ∈ fixV (autI hV (thompsonJ R)) := by rwa [hJA]
        have hu2 := (mem_fixV_autI hV hJN u).1 hu1
        have hE : u.val ∈ omegaOneCenterOf (thompsonJ R) :=
          inf_centralizer_thompsonJ_le hV hVR ⟨u.val_mem, hu2⟩
        have hcomm : (x : G) * u.val = u.val * x :=
          (Subgroup.mem_centralizer_iff.1 hx.2 u.val hE).symm
        refine IntMod.val_injective ?_
        rw [convI_apply_val, hcomm, mul_inv_cancel_right]
    _ = A := hAC.symm
    _ = autI hV (thompsonJ R) := hJA.symm

end Lemma220

section Lemma210

variable [Finite G] {V : Subgroup G}


theorem map_conj_map_conj {W : Type*} [CommGroup W] (a b : MulAut W) (B : Subgroup (MulAut W)) :
    (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      B.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem conjAut_eq_map {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

theorem isFFStarOffender_mono {W : Type*} [CommGroup W] {X Y A : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (h : IsFFStarOffender X A) : IsFFStarOffender Y A :=
  ⟨h.1.trans hXY, h.2⟩


end Lemma210

end CFSG.Quasithin
