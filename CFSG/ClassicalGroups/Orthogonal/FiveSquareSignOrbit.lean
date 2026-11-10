module
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
public import CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
open CFSG.Quasithin
open QuadraticMap
open scoped commutatorElement

public section
namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit
local instance instAddCommGroupV : AddCommGroup (Fin 5 → F) :=
  { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }
abbrev G := ↥derived
@[expose]
noncomputable def frameSigns : Subgroup G :=
  (signChangeSubgroup stdFrame.e).subgroupOf derived
private def diagMat : Matrix (Fin 2) (Fin 2) F := !![(-1 : F), 0; 0, 1]
private noncomputable def diagNegOneO2 : CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2 F where
  val := Matrix.GeneralLinearGroup.mkOfDetNeZero diagMat (by rw [diagMat, Matrix.det_fin_two]; decide)
  property := by
    change Matrix.transpose diagMat * diagMat = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> decide
private theorem reflect_r24_e2 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 2) = e 4 :=
  Generic.reflect_sub_apply_left F (i := 2) (j := 4) (by decide)

private theorem reflect_r24_e4 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 4) = e 2 :=
  Generic.reflect_sub_apply_right F (i := 2) (j := 4) (by decide)

private theorem reflect_s12_e1 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 1) = e 2 :=
  Generic.reflect_sub_apply_left F (i := 1) (j := 2) (by decide)

private theorem reflect_s12_e2 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 2) = e 1 :=
  Generic.reflect_sub_apply_right F (i := 1) (j := 2) (by decide)

private theorem reflect_r24_e0 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 0) = e 0 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 0)
    (by decide) (by decide) (by decide)

private theorem reflect_r24_e1 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 1) = e 1 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 1)
    (by decide) (by decide) (by decide)

private theorem reflect_r24_e3 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4) (e 3) = e 3 :=
  Generic.reflect_sub_apply_of_ne F (i := 2) (j := 4) (k := 3)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e0 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 0) = e 0 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 0)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e3 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 3) = e 3 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 3)
    (by decide) (by decide) (by decide)

private theorem reflect_s12_e4 :
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 4) = e 4 :=
  Generic.reflect_sub_apply_of_ne F (i := 1) (j := 2) (k := 4)
    (by decide) (by decide) (by decide)

private noncomputable def cycle124 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  ⁅CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4),
    CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)⁆
private theorem cycle124_e0 : cycle124 (e 0) = e 0 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 0)))) = e 0
  rw [reflect_s12_e0, reflect_r24_e0, reflect_s12_e0, reflect_r24_e0]
private theorem cycle124_e1 : cycle124 (e 1) = e 2 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 1)))) = e 2
  rw [reflect_s12_e1, reflect_r24_e2, reflect_s12_e4, reflect_r24_e4]
private theorem cycle124_e2 : cycle124 (e 2) = e 4 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 2)))) = e 4
  rw [reflect_s12_e2, reflect_r24_e1, reflect_s12_e1, reflect_r24_e2]
private theorem cycle124_e3 : cycle124 (e 3) = e 3 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 3)))) = e 3
  rw [reflect_s12_e3, reflect_r24_e3, reflect_s12_e3, reflect_r24_e3]
private theorem cycle124_e4 : cycle124 (e 4) = e 1 := by
  rw [cycle124, commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  change CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
      (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2)
        (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 2 - e 4)
          (CFSG.ClassicalGroups.Orthogonal.reflect (Generic.Q F) (e 1 - e 2) (e 4)))) = e 1
  rw [reflect_s12_e4, reflect_r24_e4, reflect_s12_e2, reflect_r24_e1]
public theorem sign_t : signEquiv stdFrame.e ({0, 1} : Finset (Fin 5)) = stdFrame.t := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 1} : Finset (Fin 5))) (stdFrame.e i) = stdFrame.t (stdFrame.e i)
  rw [signEquiv_apply_basis, FrameData.t_e]
  fin_cases i <;> simp <;> rfl
public theorem sign_z : signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5)) = stdFrame.z := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5))) (stdFrame.e i) = stdFrame.z (stdFrame.e i)
  rw [signEquiv_apply_basis, FrameData.z_e]
  fin_cases i <;> simp <;> rfl
private theorem sign_beta :
    signEquiv stdFrame.e ({0, 2} : Finset (Fin 5)) =
      stdFrame.betaO diagNegOneO2 diagNegOneO2 := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e i) =
    (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e i)
  fin_cases i
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 0) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 0)
    rw [signEquiv_apply_basis, FrameData.beta_e_zero]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 1) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 1)
    rw [signEquiv_apply_basis, FrameData.beta_e_one]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 2) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 2)
    rw [signEquiv_apply_basis, FrameData.beta_e_two]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 3) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 3)
    rw [signEquiv_apply_basis, FrameData.beta_e_three]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
  · change (signEquiv stdFrame.e ({0, 2} : Finset (Fin 5))) (stdFrame.e 4) =
      (stdFrame.betaO diagNegOneO2 diagNegOneO2 : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e 4)
    rw [signEquiv_apply_basis, FrameData.beta_e_four]
    funext j
    fin_cases j <;>
      simp [diagMat, diagNegOneO2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, stdFrame_e,
        Generic.e_apply, Pi.single_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply] <;> decide
private noncomputable def betaGi : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  stdFrame.betaO diagNegOneO2 diagNegOneO2
private theorem betaGi_mem_derived : betaGi ∈ derived := stdFrame.betaO_diag_mem_commutator diagNegOneO2
private theorem t_mem_derived : stdFrame.t ∈ derived := stdFrame.t_mem_commutator
private theorem z_mem_derived : stdFrame.z ∈ derived := stdFrame.z_mem_commutator
private theorem cycle124_mem_derived : cycle124 ∈ derived :=
  Subgroup.commutator_mem_commutator
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Generic.Q F) (e 2 - e 4))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Generic.Q F) (e 1 - e 2))
private def cPerm : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 4
private theorem cPerm_apply (i : Fin 5) : cPerm i =
    if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 4 else if i = 3 then 3 else 1 := by
  fin_cases i <;> decide
private theorem cycle124_apply_basis (i : Fin 5) : cycle124 (e i) = e (cPerm i) := by
  rw [cPerm_apply]
  fin_cases i
  · simpa [Generic.e_apply] using cycle124_e0
  · simpa [Generic.e_apply] using cycle124_e1
  · simpa [Generic.e_apply] using cycle124_e2
  · simpa [Generic.e_apply] using cycle124_e3
  · simpa [Generic.e_apply] using cycle124_e4
theorem conj_signEquiv {g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)} {σ : Equiv.Perm (Fin 5)}
    (hg : ∀ i, g (stdFrame.e i) = stdFrame.e (σ i)) (S : Finset (Fin 5)) :
    g * signEquiv stdFrame.e S * g⁻¹ = signEquiv stdFrame.e (S.image σ) := by
  apply LinearEquiv.toLinearMap_injective
  apply stdFrame.e.ext
  intro i
  have hg_inv : g⁻¹ (stdFrame.e i) = stdFrame.e (σ.symm i) := by
    apply g.injective
    calc g (g⁻¹ (stdFrame.e i)) = stdFrame.e i := LinearEquiv.apply_symm_apply g _
      _ = g (stdFrame.e (σ.symm i)) := by rw [hg, Equiv.apply_symm_apply]
  change (((g * signEquiv stdFrame.e S * g⁻¹ : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F))) (stdFrame.e i)) =
    (signEquiv stdFrame.e (S.image σ) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (stdFrame.e i)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg_inv,
    signEquiv_apply_basis, map_smul, hg, signEquiv_apply_basis, Equiv.apply_symm_apply]
  by_cases hi : σ.symm i ∈ S
  · have hmem : i ∈ S.image σ := by
      refine Finset.mem_image.mpr ⟨σ.symm i, hi, ?_⟩; simp
    rw [if_pos hi, if_pos hmem]
  · have hnot : i ∉ S.image σ := by
      intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      have hji' : j = σ.symm i := by simpa using congrArg σ.symm hji
      exact hi (hji' ▸ hj)
    rw [if_neg hi, if_neg hnot]
private theorem sign_c4 :
    cycle124 * betaGi * cycle124⁻¹ = signEquiv stdFrame.e ({0, 4} : Finset (Fin 5)) := by
  rw [show betaGi = signEquiv stdFrame.e ({0, 2} : Finset (Fin 5)) from sign_beta.symm]
  rw [conj_signEquiv (g := cycle124) (σ := cPerm) cycle124_apply_basis]
  congr 1
private theorem c4_mem_derived : cycle124 * betaGi * cycle124⁻¹ ∈ derived :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ cycle124_mem_derived betaGi_mem_derived)
    (Subgroup.inv_mem _ cycle124_mem_derived)
local instance instFiniteLinearEquiv : Finite ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
  Finite.of_injective (fun f : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) => f.toFun) (by
      intro f g h
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext
      intro x
      exact congrFun h x)
open CFSG.Open

private def genSet (a b c d : Bool) : Finset (Fin 5) :=
  symmDiff (symmDiff (symmDiff (if a then ({0, 1} : Finset (Fin 5)) else ∅)
    (if b then {0, 2} else ∅)) (if c then {0, 1, 2, 3} else ∅))
    (if d then {0, 4} else ∅)

private noncomputable def genProd (a b c d : Bool) : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) :=
  (((if a then stdFrame.t else 1) * (if b then betaGi else 1)) *
    (if c then stdFrame.z else 1)) * (if d then cycle124 * betaGi * cycle124⁻¹ else 1)

private theorem genProd_mem_derived (a b c d : Bool) : genProd a b c d ∈ derived := by
  have ht := t_mem_derived
  have hb := betaGi_mem_derived
  have hz := z_mem_derived
  have hc := c4_mem_derived
  have ht' := t_mem_derived
  have hb' : stdFrame.beta diagNegOneO2 diagNegOneO2 ∈ derived := by simpa [betaGi] using betaGi_mem_derived
  have hz' := z_mem_derived
  have hc' : cycle124 * stdFrame.beta diagNegOneO2 diagNegOneO2 * cycle124⁻¹ ∈ derived := by
    simpa [betaGi] using c4_mem_derived
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp only [genProd] <;>
    repeat' first | exact Subgroup.one_mem _ | exact ht' | exact hb' | exact hz' | exact hc' |
      apply Subgroup.mul_mem

private theorem signEquiv_genSet (a b c d : Bool) :
    signEquiv stdFrame.e (genSet a b c d) = genProd a b c d := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp [genSet, genProd, betaGi, ← signEquiv_mul, sign_t, sign_z, sign_beta, sign_c4,
      signEquiv_empty, sign_c4.symm]

private theorem even_finset_decomp (S : Finset (Fin 5)) (hS : Even S.card) :
    ∃ a b c d : Bool, S = genSet a b c d := by
  revert S
  decide

theorem even_sign_mem_derived (S : Finset (Fin 5)) (hS : Even S.card) :
    signEquiv stdFrame.e S ∈ derived := by
  obtain ⟨a, b, c, d, rfl⟩ := even_finset_decomp S hS
  rw [signEquiv_genSet]
  exact genProd_mem_derived a b c d

private theorem det_eq_one_of_mem_derived (g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) (hg : g ∈ derived) :
    LinearEquiv.det g = 1 := by
  let detHom : ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) →* Fˣ := LinearEquiv.det
  have hcomm : derived ≤ commutator ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
    Subgroup.commutator_mono le_top le_top
  have hker : commutator ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) ≤ detHom.ker :=
    Abelianization.commutator_subset_ker detHom
  simpa [MonoidHom.mem_ker, detHom] using hker (hcomm hg)

theorem mem_frameSigns_iff {g : G} :
    g ∈ frameSigns ↔ ∃ S : Finset (Fin 5), Even S.card ∧
      (g : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e S := by
  constructor
  · intro hg
    rw [frameSigns, Subgroup.mem_subgroupOf] at hg
    obtain ⟨S, hS⟩ := hg
    refine ⟨S, ?_, hS⟩
    have hdet : (LinearEquiv.det (signEquiv stdFrame.e S) : F) = 1 := by
      rw [← hS]
      exact congrArg Units.val (det_eq_one_of_mem_derived g.val g.2)
    rw [det_signEquiv] at hdet
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : F) ≠ 1)).mp hdet
  · rintro ⟨S, hEven, hval⟩
    rw [frameSigns, Subgroup.mem_subgroupOf]
    exact ⟨S, hval⟩

@[expose]
noncomputable def signMask (b : frameSigns) : Finset (Fin 5) :=
  Classical.choose (mem_frameSigns_iff.mp b.2)

theorem signMask_spec (b : frameSigns) :
    (b : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) = signEquiv stdFrame.e (signMask b) :=
  (Classical.choose_spec (mem_frameSigns_iff.mp b.2)).2


theorem even_card_signMask (b : frameSigns) : Even (signMask b).card :=
  (Classical.choose_spec (mem_frameSigns_iff.mp b.2)).1


@[expose]
noncomputable def frameSignsOfEven (S : Finset (Fin 5)) (hS : Even S.card) : frameSigns :=
  (⟨(⟨signEquiv stdFrame.e S, even_sign_mem_derived S hS⟩ : G),
    mem_frameSigns_iff.mpr ⟨S, hS, rfl⟩⟩ : frameSigns)


private theorem frameSignsToEven_injective :
    Function.Injective (fun b : frameSigns =>
      (⟨signMask b, even_card_signMask b⟩ : {S : Finset (Fin 5) // Even S.card})) := by
  intro b1 b2 h
  have hsign : signMask b1 = signMask b2 := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  rw [signMask_spec b1, signMask_spec b2, hsign]

private theorem frameSignsOfEven_injective :
    Function.Injective (fun S : {S : Finset (Fin 5) // Even S.card} =>
      frameSignsOfEven S.1 S.2) := by
  intro S T h
  have hval : signEquiv stdFrame.e S.1 = signEquiv stdFrame.e T.1 := by
    have := congrArg (fun b : frameSigns => (b : G).val) h
    simpa [frameSignsOfEven] using this
  exact Subtype.ext (CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow.signEquiv_injective
    (by decide : (2 : F) ≠ 0) stdFrame.e hval)

theorem card_frameSigns : Nat.card frameSigns = 16 := by
  have hcard : Nat.card {S : Finset (Fin 5) // Even S.card} = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide
  apply le_antisymm
  · have h := Nat.card_le_card_of_injective _ frameSignsToEven_injective
    rwa [hcard] at h
  · have h := Nat.card_le_card_of_injective _ frameSignsOfEven_injective
    rwa [hcard] at h

private theorem isElemAbelian_signChangeSubgroup :
    CFSG.Open.IsElemAbelian 2 (signChangeSubgroup stdFrame.e) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨S, hS⟩ := a.2
    obtain ⟨T, hT⟩ := b.2
    apply Subtype.ext
    change (a : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) * b = b * a
    rw [hS, hT]
    exact signEquiv_comm stdFrame.e S T
  · obtain ⟨S, hS⟩ := hx
    rw [hS]
    exact signEquiv_mul_self stdFrame.e S

theorem isElemAbelian_frameSigns : CFSG.Open.IsElemAbelian 2 frameSigns :=
  isElemAbelian_signChangeSubgroup.subgroupOf derived


end CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit

end
