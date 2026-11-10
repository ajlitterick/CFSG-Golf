module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_dual_of_sub_mem_span {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {X : V} (hX : X ≠ 0) (T : V →ₗ[ZMod p] V)
    (hT : ∀ v, T v - v ∈ (ZMod p) ∙ X) : ∃ f : Module.Dual (ZMod p) V, ∀ v, T v = v + f v • X := by
  let S : V →ₗ[ZMod p] ((ZMod p) ∙ X) := LinearMap.codRestrict _ (T - LinearMap.id) fun v => hT v
  refine ⟨(LinearEquiv.coord (ZMod p) V X hX).toLinearMap ∘ₗ S, fun v => ?_⟩
  have h := LinearEquiv.coord_apply_smul (ZMod p) V X hX (S v)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, LinearMap.codRestrict_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  abel

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem eq_of_mem_zpowers_of_noTransvection (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {x : ↥Bs} (hx : x ≠ 1) {φ ψ : MulAut ↥Bs}
    (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) (hφx : φ x = x) (hψx : ψ x = x)
    (hmod : ∀ b : ↥Bs, (ψ b)⁻¹ * φ b ∈ Subgroup.zpowers x) : φ = ψ := by
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  have hθ : ψ⁻¹ * φ ∈ ggInduced ⊤ Bs := mul_mem_ggInduced (inv_mem_ggInduced hψ) hφ
  have hψix : ψ⁻¹ x = x := by
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [hψx]
      _ = x := MulAut.inv_apply_self _ _ _
  have hθx : (ψ⁻¹ * φ) x = x := by rw [MulAut.mul_apply, hφx, hψix]
  have hθmod : ∀ b : ↥Bs, b⁻¹ * (ψ⁻¹ * φ) b ∈ Subgroup.zpowers x := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : ψ⁻¹ ((ψ b)⁻¹ * φ b) = b⁻¹ * (ψ⁻¹ * φ) b := by
      rw [map_mul, map_inv, MulAut.inv_apply_self, MulAut.mul_apply]
    rw [← h1, ← hk, map_zpow, hψix]
  have hX0 : ι (Additive.ofMul x) ≠ 0 := by
    intro h
    apply hx
    have h2 : Additive.ofMul x = Additive.ofMul (1 : ↥Bs) := ι.injective (by rw [h, ofMul_one,
      map_zero])
    exact Additive.ofMul.injective h2
  have hT : ∀ v, ggLin (p := p) ι (ψ⁻¹ * φ) v - v ∈ (ZMod p) ∙ ι (Additive.ofMul x) := by
    intro v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hθmod (Additive.toMul (ι.symm v)))
    have hv : v = ι (Additive.ofMul (Additive.toMul (ι.symm v))) := by
      rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    rw [hv, ggLin_apply_ofMul]
    have h1 : ι (Additive.ofMul ((ψ⁻¹ * φ) (Additive.toMul (ι.symm v)))) -
        ι (Additive.ofMul (Additive.toMul (ι.symm v))) =
        ι (Additive.ofMul ((Additive.toMul (ι.symm v))⁻¹ *
          (ψ⁻¹ * φ) (Additive.toMul (ι.symm v)))) := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg]
      abel
    rw [h1, ← hk, ofMul_zpow, map_zsmul]
    exact zsmul_mem (Submodule.mem_span_singleton_self _) k
  obtain ⟨f, hf⟩ := exists_dual_of_sub_mem_span hX0 (ggLin (p := p) ι (ψ⁻¹ * φ)).toLinearMap hT
  have hfX : f (ι (Additive.ofMul x)) = 0 := by
    have h := hf (ι (Additive.ofMul x))
    rw [LinearEquiv.coe_coe, ggLin_apply_ofMul, hθx, left_eq_add, smul_eq_zero] at h
    exact h.resolve_right hX0
  by_cases hf0 : f = 0
  · have hT1 : ggLin (p := p) ι (ψ⁻¹ * φ) = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have h := hf v
      rw [hf0, LinearMap.zero_apply, zero_smul, add_zero, LinearEquiv.coe_coe] at h
      rw [h]
      rfl
    have h1 : ψ⁻¹ * φ = 1 := ggLin_injective ι (by rw [hT1, map_one])
    calc φ = ψ * (ψ⁻¹ * φ) := by group
      _ = ψ := by rw [h1, mul_one]
  · exact absurd (ggIsTransvection_of_apply ι hX0 hf0 hfX fun v => by
      rw [← hf v, LinearEquiv.coe_coe]) (hNT _ hθ)

theorem ggAutomizer_apply_eq_of_le_centralizer {H : Subgroup G} {x : ↥Bs}
    (hH : H ≤ Subgroup.centralizer ({(x : G)} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer H Bs) : φ x = x := by
  refine Subgroup.closure_induction (p := fun ψ _ => ψ x = x) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, hgH, -, hg⟩
    apply Subtype.ext
    rw [hg]
    have hc := Subgroup.mem_centralizer_iff.mp (hH hgH) (x : G) (Set.mem_singleton _)
    rw [← hc]
    group
  · rfl
  · intro ψ χ _ _ h1 h2
    rw [MulAut.mul_apply, h2, h1]
  · intro ψ _ h
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ _ _

end GG


end CFSG.StandardType
