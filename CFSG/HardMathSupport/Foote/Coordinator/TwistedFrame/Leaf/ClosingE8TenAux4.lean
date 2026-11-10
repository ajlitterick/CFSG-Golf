module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux3
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

section Poly

variable {L : Type} [Field L]

theorem poly_extract {M : Type*} [AddCommGroup M] [Module L M] (U : Submodule L M)
    (C : Finset L) {m : ℕ} (e : Fin m → ℕ) (he : Function.Injective e)
    (hlt : ∀ i, e i < C.card) (v : Fin m → M)
    (h : ∀ c ∈ C, ∑ i, c ^ e i • v i ∈ U) : ∀ i, v i ∈ U := by
  intro i₀
  by_contra hni
  obtain ⟨φ, hφU, hφ⟩ : ∃ φ : Module.Dual L M, (∀ u ∈ U, φ u = 0) ∧ φ (v i₀) ≠ 0 := by
    have hq : Submodule.Quotient.mk (p := U) (v i₀) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual L (M ⧸ U), ψ (Submodule.Quotient.mk (v i₀)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq ((Module.forall_dual_apply_eq_zero_iff L _).1 hcon)
    refine ⟨ψ.comp U.mkQ, fun u hu => ?_, hψ⟩
    simp [(Submodule.Quotient.mk_eq_zero U).2 hu]
  set P : Polynomial L := ∑ i, Polynomial.C (φ (v i)) * Polynomial.X ^ e i with hP
  have hcard : 0 < C.card := lt_of_le_of_lt (Nat.zero_le _) (hlt i₀)
  have hdeg : P.natDegree < C.card := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := C.card - 1) ?_)
      (Nat.sub_lt hcard one_pos)
    intro i _
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := hlt i
    omega
  have hev : ∀ c ∈ C, P.eval c = 0 := by
    intro c hc
    have h1 := hφU _ (h c hc)
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    rw [hP, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hP0 : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P C hev hdeg
  have hcoeff : P.coeff (e i₀) = φ (v i₀) := by
    rw [hP, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (he h').symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  exact hφ (by rw [← hcoeff, hP0]; simp)

end Poly

section Desc

variable {K L : Type} [Field K] [Field L]


end Desc

section Descent

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]


theorem E8_fixed_eq {M : Type} [Field M] (σ : M ≃+* M) :
    entrywiseFixedGroup Tag.E8 σ = fixedFieldImage Tag.E8 σ := by
  refine le_antisymm ?_ fixedFieldImage_le
  intro g hg
  have hmul : g ∈ (entrywiseFixedTorus Tag.E8 σ : Set (ModGL Tag.E8 M)) *
      (fixedFieldImage Tag.E8 σ : Set (ModGL Tag.E8 M)) := by
    rw [← coe_entrywiseFixedGroup_eq_mul]
    exact hg
  obtain ⟨h, hh, j, hj, rfl⟩ := hmul
  refine mul_mem ?_ hj
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hσa : ∀ i, σ (a i : M) = a i := by
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E8 a) =
        rootDiagUnit Tag.E8 a := (Subgroup.mem_inf.1 hhΓ).2
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E8 a) =
        rootDiagUnit Tag.E8 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF')
    intro i
    exact congrArg Units.val (congrFun h1 i)
  let a' : Fin Tag.E8.rank → (fixSubfield σ)ˣ := fun i =>
    Units.mk0 (⟨(a i : M), hσa i⟩ : fixSubfield σ) (fun h0 => (a i).ne_zero
      (congrArg Subtype.val h0))
  have ha' : (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (a' i)) = a := by
    funext i
    exact Units.ext rfl
  refine ⟨rootDiagUnit Tag.E8 a', ?_, ?_⟩
  · exact CFSG.RankThree.PartOne.KE.rootDiagUnit_E8_mem_adjointGroup a'
  · rw [baseChangeGL_rootDiagUnit, ha']

theorem descent_E8 (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    {y : ModGL Tag.E8 L} (hy : y ∈ adjointGroup Tag.E8 L) (hfix : Frob Fr y = y) :
    ∃ y₀ ∈ adjointGroup Tag.E8 K, baseChangeGL (algebraMap K L) y₀ = y := by
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij with hσ
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap K L) := fun c hc =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hy' : y ∈ entrywiseFixedGroup Tag.E8 σ := ⟨hy, by
    change Units.map (entrywiseHom σ.toRingHom) y = y
    exact hfix⟩
  rw [E8_fixed_eq σ] at hy'
  obtain ⟨y', hy'mem, rfl⟩ := hy'
  have hKfix : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a := fun a => by
    change Fr _ = _
    rw [hFr, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  let ι' : K →+* fixSubfield σ :=
    { toFun := fun a => ⟨algebraMap K L a, hKfix a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hbij' : Function.Bijective ι' := by
    refine ⟨fun a b h => (algebraMap K L).injective (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨a, ha⟩ := hσfix c.1 c.2
    exact ⟨a, Subtype.ext ha⟩
  set e : K ≃+* fixSubfield σ := RingEquiv.ofBijective ι' hbij' with he
  refine ⟨baseChangeGL e.symm.toRingHom y', baseChangeGL_mem_adjointGroup e.symm.toRingHom hy'mem, ?_⟩
  rw [baseChangeGL_baseChangeGL]
  congr 2
  ext c
  obtain ⟨a, rfl⟩ := hbij'.2 c
  change algebraMap K L (e.symm (e a)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

end Descent

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
