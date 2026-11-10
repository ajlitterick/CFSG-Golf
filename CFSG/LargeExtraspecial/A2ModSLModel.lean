module

public import CFSG.LargeExtraspecial.A2ModSLd
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Universal.SpecialLinearExtras

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix CFSG.Assembly.LowTwoRank

variable {n : ℕ}

theorem eq_zero_or_eq_one_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (x : F) : x = 0 ∨ x = 1 := by
  rcases zmodTwo_eq_zero_or_one (ringEquivZModTwo F hF x) with h | h
  · exact .inl ((map_eq_zero_iff _ (ringEquivZModTwo F hF).injective).mp h)
  · exact .inr ((ringEquivZModTwo F hF).injective (h.trans (map_one _).symm))

theorem sl_center_eq_bot_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  rcases eq_zero_or_eq_one_of_card_two hF r with rfl | rfl
  · rw [Fintype.card_fin, zero_pow hn.ne'] at hr
    exact absurd hr zero_ne_one
  · exact Subtype.ext (by rw [← hA, map_one, Matrix.SpecialLinearGroup.coe_one])

noncomputable def statedProjSLEquiv (m : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    StatedProj (StatedSL m K) ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
  (((projectiveSpecialLinearGroupEquivStatedProj m K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (sl_center_eq_bot_of_card_two hK))).trans
    QuotientGroup.quotientBot).trans (slEquiv (ringEquivZModTwo K hK))


theorem statedLieAdmissible_PSL_two_one {m : ℕ} (hm : 3 ≤ m) : StatedLieAdmissible .PSL m 2 1 :=
  ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp [Prod.ext_iff] at h; omega,
    fun h => by simp [Prod.ext_iff] at h⟩

theorem statedClassicalModel_of_mulEquiv {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : StatedClassicalModel X .PSL m 2 1 :=
  ⟨statedLieAdmissible_PSL_two_one hm, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (statedProjSLEquiv m (ZMod 2) (Nat.card_zmod 2)).symm⟩⟩

theorem lieModel_of_mulEquiv {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : CFSG.Blueprint.LieModel X .PSL m 2 1 :=
  .inl ⟨by decide, statedClassicalModel_of_mulEquiv hm e⟩


open CFSG.LieType.Universal in
theorem map_slEquiv_rootGroup {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') (m : ℕ)
    (γ : Fin m → ℤ) :
    (SpecialLinear.rootGroup m F γ).map (slEquiv e).toMonoidHom =
      SpecialLinear.rootGroup m F' γ := by
  simp only [SpecialLinear.rootGroup, Subgroup.map_iSup]
  refine iSup_congr fun i => iSup_congr fun j => iSup_congr fun hij => iSup_congr fun _ => ?_
  exact map_slEquiv_range_transvectionHom e hij

open CFSG.LieType.Universal in
theorem map_slEquiv_rootDatum_rootGroup {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    (m : ℕ) (γ : Fin m → ℤ) :
    ((SpecialLinear.rootDatum m F).rootGroup γ).map (slEquiv e).toMonoidHom =
      (SpecialLinear.rootDatum m F').rootGroup γ :=
  map_slEquiv_rootGroup e m γ

open CFSG.LieType.Universal in
theorem map_comp_slEquiv_symm_rootGroup {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    {m : ℕ} {G : Type*} [Group G] (Ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (γ : Fin m → ℤ) :
    ((SpecialLinear.rootDatum m F').rootGroup γ).map (Ψ.comp (slEquiv e).symm.toMonoidHom) =
      ((SpecialLinear.rootDatum m F).rootGroup γ).map Ψ := by
  rw [← Subgroup.map_map, slEquiv_symm, map_slEquiv_rootDatum_rootGroup]

end CFSG.LargeExtraspecial.A2Mod
