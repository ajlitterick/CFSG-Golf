module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 CFSG.RankThree.E6
open scoped Pointwise

namespace EvenF4QPlus

@[expose] def qplusRoot : Fin 4 → Fin Tag.F4.rank → ℤ :=
  ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]]

theorem isRoot_qplusRoot (i : Fin 4) : IsRoot .F4 (qplusRoot i) := by
  rw [isRoot_iff_mem_f4RootList]
  revert i
  decide

theorem iform_qplusRoot (i j : Fin 4) :
    iform (qplusRoot i) (qplusRoot j) = if i = j then 4 else 0 := by
  revert i j
  decide

theorem not_mem_add_sub_qplusRoot :
    ∀ i j : Fin 4, i ≠ j → qplusRoot i + qplusRoot j ∉ f4RootList ∧
      qplusRoot i - qplusRoot j ∉ f4RootList := by
  decide

theorem iform_qplusRoot_eq_zero {i j : Fin 4} (hij : i ≠ j) :
    iform (qplusRoot i) (qplusRoot j) = 0 := by
  rw [iform_qplusRoot, ite_eq_right hij]

theorem rootReflection_qplusRoot_prod_smul (v : Fin Tag.F4.rank → ℤ) :
    (rootReflection (qplusRoot 0) * rootReflection (qplusRoot 1) * rootReflection (qplusRoot 2) *
      rootReflection (qplusRoot 3)) • v = -v := by
  set w := rootReflection (qplusRoot 0) * rootReflection (qplusRoot 1) *
    rootReflection (qplusRoot 2) * rootReflection (qplusRoot 3) with hw
  have hcol : ∀ k : Fin Tag.F4.rank,
      w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) = -Pi.single k 1 := by
    intro k
    simp only [hw, mul_smul, rootReflection_smul (isRoot_qplusRoot _)]
    revert k
    decide
  have hM : weylMatrix w = -1 := by
    ext i j
    rw [weylMatrix_apply, hcol j, Matrix.neg_apply, Matrix.one_apply, Pi.neg_apply,
      Pi.single_apply]
  rw [← weylMatrix_mulVec, hM, Matrix.neg_mulVec, Matrix.one_mulVec]

section Hom

variable (L : Type) [Field L]

theorem commute_rootSL2_qplusRoot
    {i j : Fin 4} (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 .F4 L (qplusRoot i) A) (rootSL2 .F4 L (qplusRoot j) B) := by
  obtain ⟨hp, hm⟩ := not_mem_add_sub_qplusRoot i j hij
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .F4 L
    (isRoot_qplusRoot i) (isRoot_qplusRoot j) (iform_qplusRoot_eq_zero hij)
    (fun h => hp (isRoot_iff_mem_f4RootList.1 h)) (fun h => hm (isRoot_iff_mem_f4RootList.1 h))
    _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

@[expose] def qplusHom :
    SL2 L →* ModGL .F4 L where
  toFun A := rootSL2 .F4 L (qplusRoot 0) A * rootSL2 .F4 L (qplusRoot 1) A *
    rootSL2 .F4 L (qplusRoot 2) A * rootSL2 .F4 L (qplusRoot 3) A
  map_one' := by simp only [map_one, mul_one]
  map_mul' A B := by
    have c : ∀ i j : Fin 4, i ≠ j →
        Commute (rootSL2 .F4 L (qplusRoot i) B) (rootSL2 .F4 L (qplusRoot j) A) :=
      fun i j h => commute_rootSL2_qplusRoot L h B A
    simp only [map_mul]
    rw [(c 0 1 (by decide)).mul_mul_mul_comm,
      ((c 0 2 (by decide)).mul_left (c 1 2 (by decide))).mul_mul_mul_comm,
      (((c 0 3 (by decide)).mul_left (c 1 3 (by decide))).mul_left
        (c 2 3 (by decide))).mul_mul_mul_comm]

theorem qplusHom_apply
    (A : SL2 L) :
    qplusHom L A = rootSL2 .F4 L (qplusRoot 0) A * rootSL2 .F4 L (qplusRoot 1) A *
      rootSL2 .F4 L (qplusRoot 2) A * rootSL2 .F4 L (qplusRoot 3) A :=
  rfl

theorem qplusHom_mem_adjointGroup
    (A : SL2 L) : qplusHom L A ∈ adjointGroup .F4 L := by
  have h := fun i => (exceptional_Lang_root_rank_one_data .F4 L (qplusRoot i)).2.2.2.2.1 A
  rw [qplusHom_apply]
  exact mul_mem (mul_mem (mul_mem (h 0) (h 1)) (h 2)) (h 3)

theorem entrywise_qplusHom
    (σ : L →+* L) (A : SL2 L) :
    Units.map (entrywiseHom σ) (qplusHom L A) =
      qplusHom L (Matrix.SpecialLinearGroup.map σ A) := by
  simp only [qplusHom_apply, map_mul, entrywise_rootSL2_of_field]

theorem qplusHom_mul_entrywise_inv_eq
    (σ : L →+* L) {A B : SL2 L}
    (hAB : A * B = Matrix.SpecialLinearGroup.map σ A) :
    qplusHom L A⁻¹ * (Units.map (entrywiseHom σ) (qplusHom L A⁻¹))⁻¹ = qplusHom L B := by
  rw [entrywise_qplusHom, ← map_inv (qplusHom L), ← map_mul (qplusHom L),
    map_inv (Matrix.SpecialLinearGroup.map σ), inv_inv, ← hAB, inv_mul_cancel_left]


end Hom

section Fixed

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem conjEntrywiseImage_eq_fixed_of_tag
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) [Finite K₂]
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL τ K₂}
    (hg : g ∈ adjointGroup τ K₂) (hz : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) :
    conjEntrywiseImage K g = adjointGroup τ K₂ ⊓
      (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) := by
  have hfix := frobenius_fixed_eq_map_of_bijective (k := K) (τ := τ) hτ
    (σ : K₂ →+* K₂) hσ (Finite.injective_iff_bijective.1 σ.injective)
  have hzg : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = g := by
    rw [hz, inv_mul_cancel_right]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF : baseChangeGL (algebraMap K K₂) x ∈ adjointGroup τ K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxσ⟩ := Subgroup.mem_inf.1 hxF
    have hxσ' : Units.map (entrywiseHom (σ : K₂ →+* K₂)) (baseChangeGL (algebraMap K K₂) x) =
        baseChangeGL (algebraMap K K₂) x := hxσ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg hxC) (inv_mem hg)
    · change twistedEntrywise z (σ : K₂ →+* K₂)
          (g * baseChangeGL (algebraMap K K₂) x * g⁻¹) =
        g * baseChangeGL (algebraMap K K₂) x * g⁻¹
      rw [twistedEntrywise_apply, map_mul, map_mul, map_inv, hxσ']
      calc z * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g * baseChangeGL (algebraMap K K₂) x *
            (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) * z⁻¹ =
          (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) * baseChangeGL (algebraMap K K₂) x *
            (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := by group
        _ = g * baseChangeGL (algebraMap K K₂) x * g⁻¹ := by rw [hzg]
  · intro hy
    obtain ⟨hyC, hyF⟩ := Subgroup.mem_inf.1 hy
    have hyF' : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹ = y := hyF
    have hσy : Units.map (entrywiseHom (σ : K₂ →+* K₂)) y = z⁻¹ * y * z := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) y =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹) * z := by group
        _ = z⁻¹ * y * z := by rw [hyF']
    have hσg : Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = z⁻¹ * g := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) g =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) := by group
        _ = z⁻¹ * g := by rw [hzg]
    have hu : g⁻¹ * y * g ∈ adjointGroup τ K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hyC) hg, ?_⟩
      change Units.map (entrywiseHom (σ : K₂ →+* K₂)) (g⁻¹ * y * g) = g⁻¹ * y * g
      rw [map_mul, map_mul, map_inv, hσy, hσg]
      group
    rw [hfix] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxu]
    group

end Fixed

section Torus

variable {L : Type} [Field L]


end Torus


section RankOne

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]


omit [Finite K] in
theorem specialLinearGroup_map_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K K₂)) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun X : SL2 K₂ => (X : Matrix (Fin 2) (Fin 2) K₂) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h1
  exact (algebraMap K K₂).injective h1

theorem conjSL_injective (P : GL (Fin 2) K₂) : Function.Injective (conjSL P) := fun A B h => by
  have h1 := congrArg (conjSL P⁻¹) h
  rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1


end RankOne

section Criterion

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem torusRootChar_rootDiagUnit {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (rootDiagUnit τ a) α = ((rootChar a α : Lˣ) : L) :=
  torusRootChar_eq_of_apply hα (rootDiag_rootVec a hα)


end Criterion

end EvenF4QPlus

open EvenF4QPlus


end CFSG.RankThree.Chevalley
