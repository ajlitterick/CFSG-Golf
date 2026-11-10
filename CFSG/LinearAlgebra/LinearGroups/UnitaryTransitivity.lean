module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Eichler

variable {σ : K →+* K}

@[expose] def eichlerMap (B : V →ₛₗ[σ] V →ₗ[K] K) (e y : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + (B e).smulRight (y + c • e) - (B y).smulRight e

theorem eichlerMap_apply (B : V →ₛₗ[σ] V →ₗ[K] K) (e y : V) (c : K) (x : V) :
    eichlerMap B e y c x = x + B e x • (y + c • e) - B y x • e := by
  simp [eichlerMap]

theorem eichlerMap_zero (B : V →ₛₗ[σ] V →ₗ[K] K) (e : V) (d : K) :
    eichlerMap B e 0 d = hermTransvection B e d := by
  ext x
  simp only [eichlerMap_apply, hermTransvection_apply, map_zero, LinearMap.zero_apply, zero_smul,
    sub_zero, zero_add, smul_smul]
  rw [mul_comm]

theorem eichlerMap_comp {B : V →ₛₗ[σ] V →ₗ[K] K} {e y y' : V} (he : B e e = 0)
    (hey' : B e y' = 0) (hye : B y e = 0) (c c' : K) :
    eichlerMap B e y c ∘ₗ eichlerMap B e y' c' = eichlerMap B e (y + y') (c + c' - B y y') := by
  ext x
  simp only [LinearMap.comp_apply, eichlerMap_apply, map_add, map_sub, map_smul,
    LinearMap.add_apply, he, hey', hye]
  module

theorem eichlerMap_isometry {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.IsSymm) {e y : V} (he : B e e = 0)
    (hey : B e y = 0) {c : K} (hc : c + σ c + B y y = 0) (x x' : V) :
    B (eichlerMap B e y c x) (eichlerMap B e y c x') = B x x' := by
  have hxe : ∀ z, B z e = σ (B e z) := fun z => (hB.eq e z).symm
  have hxy : ∀ z, B z y = σ (B y z) := fun z => (hB.eq y z).symm
  have hye : B y e = 0 := by rw [hxe, hey, map_zero]
  simp only [eichlerMap_apply, map_add, map_sub, map_smulₛₗ, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he, hey, hye, hxe x, hxy x,
    mul_zero, add_zero, sub_zero]
  linear_combination σ (B e x) * B e x' * hc

theorem det_eichlerMap [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {e y : V}
    (he : B e e = 0) (hey : B e y = 0) (hye : B y e = 0) (c : K) :
    LinearMap.det (eichlerMap B e y c) = 1 := by
  have hcomp : eichlerMap B e y c =
      LinearMap.transvection (B e) (y + c • e) ∘ₗ LinearMap.transvection (-B y) e := by
    ext x
    simp only [eichlerMap_apply, LinearMap.comp_apply, LinearMap.transvection.apply, map_add,
      map_neg, map_smul, LinearMap.neg_apply, he, neg_smul]
    module
  rw [hcomp, LinearMap.det_comp, LinearMap.transvection.det, LinearMap.transvection.det]
  simp [he, hey, hye]

end Eichler

section Frames

variable {σ : K →+* K}

theorem linearIndependent_of_mem_orthonormalFrames {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (B (v j)) hg
  simpa [map_sum, map_smul, mem_orthonormalFrames.mp hv] using this

@[expose] noncomputable def frameBasis [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) (hr : r = Module.finrank K V) :
    Module.Basis (Fin r) K V :=
  Module.Basis.mk (linearIndependent_of_mem_orthonormalFrames hv)
    (Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card (linearIndependent_of_mem_orthonormalFrames hv), Fintype.card_fin,
        hr])).ge

theorem coe_frameBasis [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) (hr : r = Module.finrank K V) :
    ⇑(frameBasis hv hr) = v :=
  Module.Basis.coe_mk _ _

theorem span_pair_nondegenerate {B : V →ₛₗ[σ] V →ₗ[K] K} {u₁ u₂ : V}
    (hG : B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁ ≠ 0) :
    Module.finrank K (Submodule.span K {u₁, u₂}) = 2 ∧
      (B.domRestrict₁₂ (Submodule.span K {u₁, u₂})
        (Submodule.span K {u₁, u₂})).SeparatingLeft := by
  have key : ∀ s t : K, B (s • u₁ + t • u₂) u₁ = 0 → B (s • u₁ + t • u₂) u₂ = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    have hs : σ s * (B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁) = 0 := by
      linear_combination B u₂ u₂ * h1 - B u₂ u₁ * h2
    have ht : σ t * (B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁) = 0 := by
      linear_combination B u₁ u₁ * h2 - B u₁ u₂ * h1
    exact ⟨(map_eq_zero σ).mp ((mul_eq_zero.mp hs).resolve_right hG),
      (map_eq_zero σ).mp ((mul_eq_zero.mp ht).resolve_right hG)⟩
  have hli : LinearIndependent K ![u₁, u₂] := LinearIndependent.pair_iff.mpr fun s t hst =>
    key s t (by rw [hst, map_zero, LinearMap.zero_apply])
      (by rw [hst, map_zero, LinearMap.zero_apply])
  have hrange : Set.range ![u₁, u₂] = {u₁, u₂} := by
    ext x
    simp [eq_comm, or_comm]
  refine ⟨by rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin], ?_⟩
  rintro ⟨z, hz⟩ hz0
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
  have h1 := hz0 ⟨u₁, Submodule.subset_span (by simp)⟩
  have h2 := hz0 ⟨u₂, Submodule.subset_span (by simp)⟩
  rw [LinearMap.domRestrict₁₂_apply] at h1 h2
  obtain ⟨rfl, rfl⟩ := key s t h1 h2
  exact Subtype.ext (by simp)

end Frames

@[expose] def unitaryTransvections (h : UnitaryFieldData p f K) (B : V →ₛₗ[h.bar] V →ₗ[K] K) :
    Set (LinearMap.GeneralLinearGroup K V) :=
  {T | ∃ (a : V) (ha : B a a = 0), ∃ c ∈ h.traceZero, T = hermTransvectionGL B ha c}


theorem exists_isotropic_of_finrank_two (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = 2) : ∃ a : V, a ≠ 0 ∧ B a a = 0 := by
  have hc := (unitary_hermitian_vector_count h hB hBl hn (by norm_num)).2.2
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = ((p ^ f : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hq] at hc
  have hq1 : 1 < q := by
    rw [hq]
    exact_mod_cast h.one_lt_pow
  have hpos : (0 : ℤ) < Nat.card {v : V // v ≠ 0 ∧ B v v = 0} := by
    rw [hc]
    apply mul_pos
    · nlinarith
    · norm_num
      linarith
  obtain ⟨⟨a, ha0, ha⟩⟩ := (Nat.card_pos_iff.mp (by exact_mod_cast hpos)).1
  exact ⟨a, ha0, ha⟩

theorem exists_isometry_det_eq_fix (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    {r : ℕ} (e : Module.Basis (Fin (r + 1)) K V) (he : ⇑e ∈ orthonormalFrames B (r + 1)) {c : K}
    (hc : h.norm c = 1) :
    ∃ φ : V →ₗ[K] V, (∀ x y, B (φ x) (φ y) = B x y) ∧ LinearMap.det φ = c ∧
      ∀ i : Fin r, φ (e i.succ) = e i.succ := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin (r + 1) → K, d = Function.update (1 : Fin (r + 1) → K) 0 c :=
    ⟨_, rfl⟩
  have hdn : ∀ i, d i * h.bar (d i) = 1 := by
    intro i
    by_cases hi : i = 0
    · rw [hd, hi, Function.update_self]
      exact hc
    · rw [hd, Function.update_of_ne hi, Pi.one_apply, map_one, one_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : V →ₗ[K] V, φ = Matrix.toLin e e (Matrix.diagonal d) := ⟨_, rfl⟩
  have hφe : ∀ i, φ (e i) = d i • e i := fun i => by
    rw [hφ, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  refine ⟨φ, isometry_of_mem_orthonormalFrames e he (mem_orthonormalFrames.mpr fun i j => ?_), ?_,
    fun i => ?_⟩
  · simp only [hφe, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mem_orthonormalFrames.mp he,
      RingHom.id_apply]
    split_ifs with hij
    · subst hij
      linear_combination hdn i
    · simp only [mul_zero]
  · rw [hφ, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_succ, hd,
      Function.update_self]
    simp [Fin.succ_ne_zero]
  · rw [hφe, hd, Function.update_of_ne (Fin.succ_ne_zero i), Pi.one_apply, one_smul]

theorem exists_norm_one_perp_of_isotropic (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 3 ≤ Module.finrank K V) {a : V} (ha0 : a ≠ 0) (ha : B a a = 0) :
    ∃ w : V, B w w = 1 ∧ B a w = 0 := by
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
  obtain ⟨-, -, -, hWsep, hWdim⟩ := hsplit b hab hbb
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hB.domRestrict _) hWsep
  have hpos : 0 < Module.finrank K ((Submodule.span K {a, b}).orthogonalBilin B) := by omega
  refine ⟨(e ⟨0, hpos⟩ : V), ?_, ?_⟩
  · have := he ⟨0, hpos⟩ ⟨0, hpos⟩
    rw [LinearMap.domRestrict₁₂_apply] at this
    simpa using this
  · exact (Submodule.mem_orthogonalBilin.mp (e ⟨0, hpos⟩).2) a (Submodule.subset_span (by simp))

theorem unitary_transvection_commutator (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 3 ≤ Module.finrank K V) {a : V} (ha : B a a = 0) {t : K} (ht : t ∈ h.traceZero) :
    ∃ g₁ ∈ sesqSpecialUnitaryGroup B, ∃ g₂ ∈ sesqSpecialUnitaryGroup B,
      hermTransvectionGL B ha t = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
    rw [mul_one, inv_one, mul_one, mul_one]
    refine Units.ext ?_
    rw [coe_hermTransvectionGL, Units.val_one]
    ext x
    simp [hermTransvection_apply]
  obtain ⟨w, hww, haw⟩ := exists_norm_one_perp_of_isotropic h hB hBl hn ha0 ha
  have hwa : B w a = 0 := by rw [← hB.eq a w, haw, map_zero]
  obtain ⟨r, hr⟩ : ∃ r : K, h.bar r - r = t := by
    have : t ∈ h.barSub.range := by rw [h.range_barSub]; exact ht
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, UnitaryFieldData.barSub_apply]⟩
  obtain ⟨c, hc⟩ := h.traceLin_surjective (-1)
  have hc' : c + h.bar c + B w w = 0 := by
    have := congrArg Subtype.val hc
    simp only [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
    rw [hww, this]
    simp
  obtain ⟨d, hd⟩ := h.traceLin_surjective (-⟨h.norm r, h.norm_mem_fixedField r⟩)
  have hrw : B (r • w) (r • w) = h.norm r := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hww, mul_one,
      UnitaryFieldData.norm, RingHom.id_apply]
  have hd' : d + h.bar d + B (r • w) (r • w) = 0 := by
    have := congrArg Subtype.val hd
    simp only [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
    rw [hrw, this]
    simp
  have har : B a (r • w) = 0 := by rw [map_smul, haw, smul_zero]
  have hra : B (r • w) a = 0 := by rw [map_smulₛₗ, LinearMap.smul_apply, hwa, smul_zero]
  have hE₁ := eichlerMap_isometry hB ha haw hc'
  have hE₂ := eichlerMap_isometry hB ha har hd'
  have hg₁ : ((isometryUnit hBl hE₁ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) ∈
      sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup, coe_isometryUnit]
    exact ⟨(isometryUnit hBl hE₁).2, det_eichlerMap ha haw hwa c⟩
  have hg₂ : ((isometryUnit hBl hE₂ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) ∈
      sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup, coe_isometryUnit]
    exact ⟨(isometryUnit hBl hE₂).2, det_eichlerMap ha har hra d⟩
  refine ⟨_, hg₁, _, hg₂, ?_⟩
  have hrel : ((isometryUnit hBl hE₁ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) *
        (isometryUnit hBl hE₂ : sesqUnitaryGroup B) =
      hermTransvectionGL B ha t * ((isometryUnit hBl hE₂ : sesqUnitaryGroup B) *
        (isometryUnit hBl hE₁ : sesqUnitaryGroup B)) := by
    refine Units.ext ?_
    simp only [Units.val_mul, coe_hermTransvectionGL, coe_isometryUnit, Module.End.mul_eq_comp]
    rw [eichlerMap_comp ha har hwa, eichlerMap_comp ha haw hra, ← eichlerMap_zero,
      eichlerMap_comp ha (by rw [map_add, har, haw, add_zero]) (by simp)]
    congr 1
    · abel
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hww, mul_one, map_zero,
        LinearMap.zero_apply, sub_zero, ← hr]
      ring
  rw [hrel]
  group

section SUTwo

theorem hyperbolic_entries (h : UnitaryFieldData p f K) {α β γ δ : K}
    (e1 : h.bar α * γ + h.bar γ * α = 0) (e2 : h.bar β * δ + h.bar δ * β = 0)
    (e3 : h.bar α * δ + h.bar γ * β = 1) (e4 : α * δ - β * γ = 1) :
    h.bar α = α ∧ h.bar δ = δ ∧ γ + h.bar γ = 0 ∧ β + h.bar β = 0 := by
  have e3' : α * h.bar δ + γ * h.bar β = 1 := by
    have := congrArg h.bar e3
    simpa only [map_add, map_mul, h.bar_bar, map_one] using this
  have hα : h.bar α = α := by linear_combination (-h.bar α) * e4 + α * e3 - β * e1
  have hδ : h.bar δ = δ := by linear_combination (-h.bar δ) * e4 + δ * e3' - γ * e2
  have hγα : α * (γ + h.bar γ) = 0 := by linear_combination e1 - γ * hα
  have hγβ : β * (γ + h.bar γ) = 0 := by linear_combination e3 - e4 - δ * hα
  have hβδ : δ * (β + h.bar β) = 0 := by linear_combination e2 - β * hδ
  have hβγ : γ * (β + h.bar β) = 0 := by linear_combination e3' - e4 - α * hδ
  refine ⟨hα, hδ, ?_, ?_⟩
  · by_cases hα0 : α = 0
    · have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [hα0] at e4
        simp at e4
      exact (mul_eq_zero.mp hγβ).resolve_left hβ0
    · exact (mul_eq_zero.mp hγα).resolve_left hα0
  · by_cases hδ0 : δ = 0
    · have hγ0 : γ ≠ 0 := by
        rintro rfl
        rw [hδ0] at e4
        simp at e4
      exact (mul_eq_zero.mp hβγ).resolve_left hγ0
    · exact (mul_eq_zero.mp hβδ).resolve_left hδ0


end SUTwo


theorem exists_ne_zero_norm_ne_one (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    ∃ s : K, s ≠ 0 ∧ h.norm s ≠ 1 := by
  by_contra! hcon
  have := h.finite
  have hle : Nat.card Kˣ ≤ Nat.card {t : K // h.norm t = 1} :=
    Nat.card_le_card_of_injective (fun u => ⟨u, hcon u u.ne_zero⟩)
      fun u v huv => Units.ext (congrArg Subtype.val huv)
  rw [card_norm_eq_one h, Nat.card_units, h.card_eq_sq, Nat.sub_le_iff_le_add] at hle
  nlinarith


end CFSG.LinearGroups
