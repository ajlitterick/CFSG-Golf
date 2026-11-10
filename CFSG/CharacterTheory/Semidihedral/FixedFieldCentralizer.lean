module

public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
public import CFSG.CharacterTheory.Semidihedral.FixedFieldCentralizerGamma

public section

namespace CFSG.Semidihedral.FixedFieldCentralizer

noncomputable section

set_option maxHeartbeats 800000

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.FixedFieldData
open CFSG.Semidihedral.OddFieldLift
open scoped MatrixGroups Pointwise

universe u v w

theorem pgl_map_injective {K : Type u} {F : Type v} [Field K] [Field F]
    (i : K →+* F) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk U =>
    rw [MonoidHom.mem_ker, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
    obtain ⟨c, hc⟩ := hg
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨U.val 0 0, Matrix.ext fun a b => i.injective ?_⟩
    have h00 : c = i (U.val 0 0) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_true,
        Matrix.GeneralLinearGroup.map_apply] using hh
    have hab : (if a = b then c else 0) = i (U.val a b) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M a b) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.GeneralLinearGroup.map_apply] using hh
    by_cases h : a = b
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_left h] using
        h00.symm.trans (by simpa only [ite_eq_left h] using hab)
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_right h, map_zero] using
        (by simpa only [ite_eq_right h] using hab : 0 = i (U.val a b))

theorem gl_mul_scalar_entry {F : Type u} [Field F]
    (U : Matrix.GeneralLinearGroup (Fin 2) F) (c : Fˣ) (i j : Fin 2) :
    (U * Matrix.GeneralLinearGroup.scalar (Fin 2) c).val i j = U.val i j * c := by
  simp [Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mul_diagonal]

theorem gl_exists_nonzero_entry {F : Type u} [Field F]
    (U : Matrix.GeneralLinearGroup (Fin 2) F) : ∃ i j, U.val i j ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : U.val = 0 := Matrix.ext h
  have hdet : Matrix.det U.val ≠ 0 := U.det.ne_zero
  exact hdet (by rw [hzero]; simp)

theorem pgl_normalized_representative {F : Type u} [Field F] (g : PGL2 F) :
    ∃ (V : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2),
      Matrix.ProjGenLinGroup.mk V = g ∧ V.val i j = 1 := by
  obtain ⟨U, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨i, j, hij⟩ := gl_exists_nonzero_entry U
  let c : Fˣ := Units.mk0 (U.val i j) hij
  refine ⟨U * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, i, j, ?_, ?_⟩
  · rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  · rw [gl_mul_scalar_entry]
    exact mul_inv_cancel₀ hij

theorem normalized_projective_fixed {F : Type u} [Field F]
    (V : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) (hij : V.val i j = 1)
    (sigma : F ≃+* F)
    (hfix : pgl2FieldAut F sigma (Matrix.ProjGenLinGroup.mk V) =
      Matrix.ProjGenLinGroup.mk V) : Matrix.GeneralLinearGroup.map sigma.toRingHom V = V := by
  have hmap : pgl2FieldAut F sigma (Matrix.ProjGenLinGroup.mk V) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom V) := by
    rw [pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk sigma V
  rw [hmap, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hfix
  obtain ⟨c, hc⟩ := hfix
  have hc1 : c = 1 := by
    apply Units.ext
    have hentry := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) F => U.val i j) hc
    simpa only [gl_mul_scalar_entry, Matrix.GeneralLinearGroup.map_apply,
      RingEquiv.toRingHom_eq_coe, hij, map_one, one_mul, Units.val_one] using hentry
  simpa only [hc1, map_one, mul_one] using hc

abbrev F0 (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) := FixedPoints.subfield A F

@[expose] def pglInclusion (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    PGL2 (F0 F A) →* PGL2 F := Matrix.ProjGenLinGroup.map (F0 F A).subtype

theorem gl_descends {F : Type u} [Field F] (A : Subgroup (F ≃+* F))
    (V : Matrix.GeneralLinearGroup (Fin 2) F)
    (hfix : ∀ (sigma : A) i j, (sigma : F ≃+* F) (V.val i j) = V.val i j) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A),
      Matrix.GeneralLinearGroup.map (F0 F A).subtype U = V := by
  let W : Matrix (Fin 2) (Fin 2) (F0 F A) := fun i j => ⟨V.val i j, fun sigma => hfix sigma i j⟩
  have hmap : W.map (F0 F A).subtype = V.val := rfl
  have hdet : Matrix.det W ≠ 0 := by
    intro h
    have hh := congrArg (F0 F A).subtype h
    rw [map_zero] at hh
    have hmapdet : (F0 F A).subtype (Matrix.det W) = Matrix.det V.val := by
      simpa only [RingHom.mapMatrix_apply, hmap] using (F0 F A).subtype.map_det W
    exact V.det.ne_zero (hmapdet.symm.trans hh)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero W hdet, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem pgl_fixed_iff (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) (g : PGL2 F) :
    (∀ sigma : A, pgl2FieldAut F sigma g = g) ↔ g ∈ (pglInclusion F A).range := by
  constructor
  · intro hg
    obtain ⟨V, i, j, hV, hij⟩ := pgl_normalized_representative g
    have hfixed : ∀ (sigma : A) a b, (sigma : F ≃+* F) (V.val a b) = V.val a b := by
      intro sigma a b
      have h := normalized_projective_fixed V i j hij sigma (by rw [hV]; exact hg sigma)
      exact congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) F => U.val a b) h
    obtain ⟨U, hU⟩ := gl_descends A V hfixed
    refine ⟨Matrix.ProjGenLinGroup.mk U, ?_⟩
    rw [pglInclusion, Matrix.ProjGenLinGroup.map_mk, hU, hV]
  · rintro ⟨g0, rfl⟩ sigma
    induction g0 using Matrix.ProjGenLinGroup.induction_on with
    | mk U =>
      rw [pglInclusion, Matrix.ProjGenLinGroup.map_mk, pgl2FieldAut_apply]
      have hmap := pgl2RingEquiv_mk sigma.val (Matrix.GeneralLinearGroup.map (F0 F A).subtype U)
      apply hmap.trans
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact (U.val i j).property sigma

theorem coordinatePGLAction_field (F : Type u) [Field F] [Finite F]
    (sigma : F ≃+* F) (g : PGL2 F) :
    coordinatePGLAction F (pgl2FieldAut F sigma g) =
      fieldExtension F sigma * coordinatePGLAction F g * (fieldExtension F sigma)⁻¹ := by
  have h := congrArg (coordinateSemilinearAction F)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut F) sigma g)
  simpa only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] using h

theorem coordinatePGLAction_commute_iff (F : Type u) [Field F] [Finite F]
    (sigma : F ≃+* F) (g : PGL2 F) :
    Commute (coordinatePGLAction F g) (fieldExtension F sigma) ↔
      pgl2FieldAut F sigma g = g := by
  constructor
  · intro h
    apply coordinatePGLAction_injective F
    rw [coordinatePGLAction_field, h.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    have hh := coordinatePGLAction_field F sigma g
    rw [h] at hh
    exact eq_mul_inv_iff_mul_eq.mp hh

@[expose] def fixedGLAction (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Matrix.GeneralLinearGroup (Fin 2) (F0 F A) →* Equiv.Perm (Omega F) :=
  (coordinatePGLAction F).comp
    (Matrix.ProjGenLinGroup.mk.comp (Matrix.GeneralLinearGroup.map (F0 F A).subtype))

@[expose] def D0 (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Subgroup (Equiv.Perm (Omega F)) := (fixedGLAction F A).range

@[expose] def pglToCoordinateD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : PGL2 (F0 F A) →* coordinateD F :=
  (pglEquivCoordinateD F).toMonoidHom.comp (pglInclusion F A)


@[expose] def D0InD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Subgroup (coordinateD F) := (pglToCoordinateD F A).range

theorem pglToCoordinateD_injective (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Function.Injective (pglToCoordinateD F A) :=
  (pglEquivCoordinateD F).injective.comp (pgl_map_injective (F0 F A).subtype)

@[expose] def pglEquivD0InD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : PGL2 (F0 F A) ≃* D0InD F A :=
  MonoidHom.ofInjective (pglToCoordinateD_injective F A)

@[expose] def coordinateDEquivD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD (F0 F A) ≃* D0InD F A :=
  (pglEquivCoordinateD (F0 F A)).symm.trans (pglEquivD0InD F A)

theorem coordinateDEquivD0_matrix (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A)) :
    ((coordinateDEquivD0 F A (pglEquivCoordinateD (F0 F A)
      (Matrix.ProjGenLinGroup.mk U)) : coordinateD F) : Equiv.Perm (Omega F)) =
        fixedGLAction F A U := by
  change ((pglToCoordinateD F A ((pglEquivCoordinateD (F0 F A)).symm
    (pglEquivCoordinateD (F0 F A) (Matrix.ProjGenLinGroup.mk U)))) :
      Equiv.Perm (Omega F)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem D0InD_map_subtype (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (D0InD F A).map (coordinateD F).subtype = D0 F A := by
  rw [D0InD, ← MonoidHom.range_comp]
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨U, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    exact ⟨U, rfl⟩
  · rintro _ ⟨U, rfl⟩
    exact ⟨Matrix.ProjGenLinGroup.mk U, rfl⟩

theorem D0InD_mem_iff (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (g : coordinateD F) :
    g ∈ D0InD F A ↔ ∀ sigma : A, Commute (g : Equiv.Perm (Omega F)) (fieldExtension F sigma) := by
  let v := (pglEquivCoordinateD F).symm g
  have hv : coordinatePGLAction F v = (g : Equiv.Perm (Omega F)) :=
    congrArg Subtype.val ((pglEquivCoordinateD F).apply_symm_apply g)
  have hmem : g ∈ D0InD F A ↔ v ∈ (pglInclusion F A).range := by
    constructor
    · rintro ⟨g0, hg0⟩
      refine ⟨g0, ?_⟩
      apply (pglEquivCoordinateD F).injective
      exact hg0.trans ((pglEquivCoordinateD F).apply_symm_apply g).symm
    · rintro ⟨g0, hg0⟩
      exact ⟨g0, by
        change pglEquivCoordinateD F (pglInclusion F A g0) = g
        rw [hg0, MulEquiv.apply_symm_apply]⟩
  rw [hmem, ← pgl_fixed_iff]
  exact forall_congr' fun sigma => (coordinatePGLAction_commute_iff F sigma v).symm.trans
    (by rw [hv])

theorem fixed_field_projective_centralizer (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    (Subgroup.centralizer (ambientLiftedField F A : Set (Equiv.Perm (Omega F)))).comap
      (coordinateD F).subtype = D0InD F A := by
  ext g
  rw [D0InD_mem_iff]
  change (∀ a ∈ ambientLiftedField F A, a * (g : Equiv.Perm (Omega F)) =
      (g : Equiv.Perm (Omega F)) * a) ↔ _
  constructor
  · intro h sigma
    exact (h (fieldExtension F sigma)
      ((ambientLiftedField_mem F A _).mpr ⟨sigma, sigma.property, rfl⟩)).symm
  · intro h a ha
    obtain ⟨sigma, hsigma, rfl⟩ := (ambientLiftedField_mem F A a).mp ha
    exact (h ⟨sigma, hsigma⟩).eq.symm

theorem D0InD_card (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    Nat.card (D0InD F A) = Nat.card (F0 F A) * (Nat.card (F0 F A) ^ 2 - 1) := by
  rw [← Nat.card_congr (pglEquivD0InD F A).toEquiv]
  exact pgl2_card_formula (F0 F A)

theorem centralizer_preimage_odd {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hc : pi.ker ≤ Subgroup.center H)
    (h2 : ∀ k ∈ pi.ker, k ^ 2 = 1) (U : Subgroup H)
    (d : ℕ) (hd : Odd d) (hU : ∀ x ∈ U, x ^ d = 1) :
    Subgroup.centralizer (U : Set H) =
      (Subgroup.centralizer (U.map pi : Set Q)).comap pi := by
  ext h
  constructor
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨e, he, rfl⟩
    have hec := congrArg pi (Subgroup.mem_centralizer_iff.mp hh e he)
    simpa only [map_mul] using hec
  · intro hh
    let f : U →* H := (MulAut.conj h).toMonoidHom.comp U.subtype
    let g : U →* H := U.subtype
    have hfg : ∀ e : U, (f e)⁻¹ * g e ∈ pi.ker := by
      intro e
      have hh' := Subgroup.mem_centralizer_iff.mp hh (pi e) ⟨e, e.property, rfl⟩
      change pi ((h * (e : H) * h⁻¹)⁻¹ * e) = 1
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hh', mul_assoc,
        mul_inv_cancel, mul_one, inv_mul_cancel]
    let delta := CFSG.Semidihedral.CentralPrimeExtensions.centralDifference pi.ker hc f g hfg
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    let eU : U := ⟨e, he⟩
    have heUd : eU ^ d = 1 := Subtype.ext (hU e he)
    have hdeltad : (delta eU) ^ d = 1 := by rw [← map_pow, heUd, map_one]
    have hdelta2 : (delta eU) ^ 2 = 1 := Subtype.ext (h2 _ (delta eU).property)
    have hdelta1 : delta eU = 1 := by
      obtain ⟨n, hn⟩ := hd
      rw [hn, pow_succ, pow_mul, hdelta2, one_pow, one_mul] at hdeltad
      exact hdeltad
    have hefix : h * e * h⁻¹ = e := by
      have hh := congrArg (fun k : pi.ker => (k : H)) hdelta1
      exact inv_mul_eq_one.mp hh
    exact (mul_inv_eq_iff_eq_mul.mp hefix).symm

theorem kernel_exponent_two {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) : ∀ k ∈ pi.ker, k ^ 2 = 1 := by
  intro k hk
  have hcard : Nat.card pi.ker = 2 := by rw [hker, Nat.card_zpowers, hz]
  have hh := congrArg (fun x : pi.ker => (x : H))
    (pow_card_eq_one' (x := (⟨k, hk⟩ : pi.ker)))
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcard] using hh

theorem exists_sylow_le_of_odd_index {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (hindex : Odd N.index) : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 N := Classical.choice inferInstance
  let U : Subgroup H := (P : Subgroup N).map N.subtype
  have hUp : IsPGroup 2 U := P.isPGroup'.map N.subtype
  have hUindex : Odd U.index := by
    rw [Subgroup.index_map_subtype]
    have hPodd : Odd (P : Subgroup N).index :=
      Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index h.two_dvd)
    exact hPodd.mul hindex
  refine ⟨hUp.toSylow hUindex.not_two_dvd_nat, ?_⟩
  change U ≤ N
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

theorem projective_card_odd_ratio {q0 d : ℕ} (hq0 : 3 ≤ q0)
    (hqodd : Odd q0) (hd : Odd d) :
    ∃ r : ℕ, Odd r ∧
      q0 ^ d * ((q0 ^ d) ^ 2 - 1) = r * (q0 * (q0 ^ 2 - 1)) := by
  let s := ∑ i ∈ Finset.range d, (q0 ^ 2) ^ i
  let r := q0 ^ (d - 1) * s
  have hdpos : 1 ≤ d := hd.pos
  have hq : q0 ^ d = q0 ^ (d - 1) * q0 := by rw [← pow_succ, Nat.sub_one_add_one (by omega)]
  have hgeom : (q0 ^ d) ^ 2 - 1 = s * (q0 ^ 2 - 1) := by
    have hh := geom_sum_mul_of_one_le (show 1 ≤ q0 ^ 2 by nlinarith) d
    simpa only [s, ← pow_mul, Nat.mul_comm 2 d] using hh.symm
  refine ⟨r, hqodd.pow.mul (odd_geometric_sum hqodd hd), ?_⟩
  rw [hgeom, hq]
  dsimp only [r]
  ring


@[expose] def dToGamma (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD F →* Gamma F A :=
  (linearInclusion F).codRestrict (Gamma F A)
    (CFSG.Semidihedral.FixedFieldCentralizerGamma.linearInclusion_mem_Gamma F A)


@[expose] def gammaD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Subgroup (Gamma F A) := (D0InD F A).map (dToGamma F A)


theorem gammaField_le_centralizer (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    gammaField F A ≤ Subgroup.centralizer (gammaField F A : Set (Gamma F A)) := by
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let : IsCyclic (gammaField F A) := (gammaFieldEquiv F A).isCyclic.mpr inferInstance
  have hc : IsMulCommutative (gammaField F A) := inferInstance
  intro a ha
  apply Subgroup.mem_centralizer_iff.mpr
  intro b hb
  exact congrArg Subtype.val (hc.is_comm.comm (⟨b, hb⟩ : gammaField F A) ⟨a, ha⟩)


abbrev M0 {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) := (gammaD0 F A).comap pi


theorem E_map_pi {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    (E F A pi z hzc hker).map pi = gammaField F A := by
  ext a
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he.1
  · intro ha
    obtain ⟨e, he⟩ := (piOnE F A pi hpi z hz hzc hker hd).surjective ⟨a, ha⟩
    exact ⟨e, e.property, congrArg Subtype.val he⟩

theorem E_centralizer_preimage {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Subgroup.centralizer (E F A pi z hzc hker : Set H) =
      (Subgroup.centralizer (gammaField F A : Set (Gamma F A))).comap pi := by
  rw [centralizer_preimage_odd pi (kernel_central pi z hzc hker)
    (kernel_exponent_two pi z hz hker) (E F A pi z hzc hker)
    (Nat.card A) hd (fun _ he => he.2), E_map_pi F A pi hpi z hz hzc hker hd]


theorem E_le_centralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    E F A pi z hzc hker ≤ Subgroup.centralizer (E F A pi z hzc hker : Set H) := by
  rw [E_centralizer_preimage F A pi hpi z hz hzc hker hd]
  intro e he
  exact gammaField_le_centralizer F A he.1


theorem gammaLinear_index (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (gammaLinear F A).index = Nat.card A :=
  (gamma_isComplement F A).symm.index_eq_card.trans (gammaField_card F A)


theorem preimage_card {H : Type v} {Q : Type w} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (N : Subgroup Q) :
    Nat.card (N.comap pi) = Nat.card pi.ker * Nat.card N := by
  let f := preimageProjection pi N
  have hker : f.ker = pi.ker.subgroupOf (N.comap pi) := by
    ext x
    exact ⟨fun h => congrArg Subtype.val (show f x = 1 from h),
      fun h => Subtype.ext h⟩
  have hc : Nat.card f.ker = Nat.card pi.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pi.ker_le_comap N)).toEquiv
  have h := Subgroup.card_ker_mul_card_of_surjective (preimageProjection_surjective pi hpi N)
  rw [hc] at h
  exact h.symm


end

end CFSG.Semidihedral.FixedFieldCentralizer
