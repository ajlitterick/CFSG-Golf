module

public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.SteinbergBRBlockParabolicDInf

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct

variable {F : Type*} [Field F]

variable (F) in
@[expose] noncomputable def natTheta (s : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Matrix (Fin 2) (Fin 1) F) ⋊[phiL F (Fin 1)] SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 3) F :=
  (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom.comp (thetaL F (Fin 2) (Fin 1))

variable (F) in
@[expose] noncomputable def dualTheta (s : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Matrix (Fin 1) (Fin 2) F) ⋊[phiR F (Fin 1)] SpecialLinearGroup (Fin 2) F →*
      SpecialLinearGroup (Fin 3) F :=
  (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom.comp (thetaR F (Fin 1) (Fin 2))


theorem natTheta_conj (s : SpecialLinearGroup (Fin 3) F) (A : SpecialLinearGroup (Fin 2) F)
    (X : Multiplicative (Matrix (Fin 2) (Fin 1) F)) :
    natTheta F s (inr A) * natTheta F s (inl X) * (natTheta F s (inr A))⁻¹ =
      natTheta F s (inl (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X))) := by
  rw [← map_inv (natTheta F s), ← map_inv inr, ← map_mul, ← map_mul, ← inl_aut]
  rfl

theorem dualTheta_conj (s : SpecialLinearGroup (Fin 3) F) (D : SpecialLinearGroup (Fin 2) F)
    (X : Multiplicative (Matrix (Fin 1) (Fin 2) F)) :
    dualTheta F s (inr D) * dualTheta F s (inl X) * (dualTheta F s (inr D))⁻¹ =
      dualTheta F s (inl (Multiplicative.ofAdd (Multiplicative.toAdd X * (D⁻¹).val))) := by
  rw [← map_inv (dualTheta F s), ← map_inv inr, ← map_mul, ← map_mul, ← inl_aut]
  rfl

theorem natTheta_spec [Finite F] (hSL : commutator (SpecialLinearGroup (Fin 2) F) = ⊤)
    {s : SpecialLinearGroup (Fin 3) F} {W : Submodule F (Fin 3 → F)}
    (hs : (flagSpace 3 F 2).map (mulVecLin s.val) = W) :
    Function.Injective (natTheta F s) ∧
    (natTheta F s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((natTheta F s).comp inl).range = radU F W ∧
    (natTheta F s).range ⊓ scalars 3 F = ⊥ := by
  have hJ := perfectResidual_stabilizer_eq (show 2 + 1 = 3 from rfl) hs parJL_le_parQ
    (perfectResidual_parQ_eq_parJL hSL)
  have hrange : (natTheta F s).range = (parJL F (Fin 2) (Fin 1)).map
      (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom := by
    rw [natTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F _ s).injective.comp thetaL_injective, hrange.trans hJ.symm, ?_, ?_⟩
  · have hcomp : (natTheta F s).comp inl =
        (transportSL F (show 2 + 1 = 3 from rfl) s).toMonoidHom.comp (uniHom F (Fin 2) (Fin 1)) :=
      MonoidHom.ext fun x => congrArg (transportSL F _ s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport _ hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_right _ s fun g hg => (mem_parJL.1 hg).2

theorem dualTheta_spec [Finite F] (hSL : commutator (SpecialLinearGroup (Fin 2) F) = ⊤)
    {s : SpecialLinearGroup (Fin 3) F} {W : Submodule F (Fin 3 → F)}
    (hs : (flagSpace 3 F 1).map (mulVecLin s.val) = W) :
    Function.Injective (dualTheta F s) ∧
    (dualTheta F s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((dualTheta F s).comp inl).range = radU F W ∧
    (dualTheta F s).range ⊓ scalars 3 F = ⊥ := by
  have hJ := perfectResidual_stabilizer_eq (show 1 + 2 = 3 from rfl) hs parJR_le_parQ
    (perfectResidual_parQ_eq_parJR hSL)
  have hrange : (dualTheta F s).range = (parJR F (Fin 1) (Fin 2)).map
      (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom := by
    rw [dualTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F _ s).injective.comp thetaR_injective, hrange.trans hJ.symm, ?_, ?_⟩
  · have hcomp : (dualTheta F s).comp inl =
        (transportSL F (show 1 + 2 = 3 from rfl) s).toMonoidHom.comp (uniHom F (Fin 1) (Fin 2)) :=
      MonoidHom.ext fun x => congrArg (transportSL F _ s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport _ hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_left _ s fun g hg => (mem_parJR.1 hg).2

omit [Field F] in
theorem card_multiplicative_matrix [Finite F] (a b : ℕ) :
    Nat.card (Multiplicative (Matrix (Fin a) (Fin b) F)) = Nat.card F ^ (b * a) := by
  rw [Nat.card_congr Multiplicative.toAdd, Matrix.card_matrix, Nat.card_fin, Nat.card_fin]

theorem isPGroup_multiplicative_matrix {p : ℕ} [CharP F p] (a b : ℕ) :
    IsPGroup p (Multiplicative (Matrix (Fin a) (Fin b) F)) := fun g => ⟨1, by
  apply Multiplicative.toAdd.injective
  rw [pow_one, toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]⟩


theorem not_dvd_pow_sub_one {p q k : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hk : k ≠ 0) (hq : 1 ≤ q) :
    ¬ p ∣ q ^ k - 1 := by
  intro h
  have h1 : p ∣ q ^ k := dvd_pow hpq hk
  have h2 : q ^ k - 1 + 1 = q ^ k := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  rw [← h2] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))


theorem card_SL_two' [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [card_SL_eq (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem card_SL_three' [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num)]


end CFSG.LieType.SteinbergBR.BlockPar

namespace CFSG.LieType

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct
  CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar


end CFSG.LieType
