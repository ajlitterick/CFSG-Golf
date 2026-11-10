module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.Dihedral.BlueprintDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Semidihedral.LocalPrimeFailure

open CFSG.Open CFSG.DihedralBlueprint

variable {G : Type} [Group G]


theorem exists_sylow_of_isSylowIn [Finite G] {ell : ℕ} {H : Subgroup G} {M : Subgroup H}
    {Q : Subgroup G} (hQ : IsSylowIn ell Q (M.map H.subtype)) :
    ∃ Q₁ : Sylow ell M, ((Q₁ : Subgroup M).map M.subtype).map H.subtype = Q := by
  obtain ⟨hQle, hQp, hmax⟩ := hQ
  let φ : M →* G := H.subtype.comp M.subtype
  have hφ : Function.Injective φ := H.subtype_injective.comp M.subtype_injective
  have hrange : φ.range = M.map H.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨Q₁, hQ₁⟩ := (hQp.comap_of_injective φ hφ).exists_le_sylow
  refine ⟨Q₁, ?_⟩
  rw [Subgroup.map_map]
  refine hmax _ ?_ (Q₁.isPGroup'.map φ) ?_
  · rw [← hrange]
    exact Subgroup.map_le_range φ _
  · calc Q = (Q.comap φ).map φ := (Subgroup.map_comap_eq_self (hQle.trans hrange.ge)).symm
      _ ≤ (Q₁ : Subgroup M).map φ := Subgroup.map_mono hQ₁

theorem map_subtype_centralizer (H : Subgroup G) (A : Subgroup H) :
    (Subgroup.centralizer (A : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ((A.map H.subtype : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx a ha)
  · rintro x ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx a ⟨a, ha, rfl⟩)

theorem map_centralizer_eq_inf {C : Subgroup G} (PC : Subgroup C) :
    (Subgroup.centralizer (PC : Set C)).map C.subtype =
      Subgroup.normalizer ((PC.map C.subtype : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((PC.map C.subtype : Subgroup G) : Set G) ⊓ C := by
  have h := map_subtype_centralizer C PC
  apply le_antisymm
  · rw [h]
    rintro x ⟨hxC, hx⟩
    exact ⟨⟨Subgroup.centralizer_le_normalizer _ hx, hx⟩, hxC⟩
  · rw [h]
    rintro x ⟨⟨-, hx⟩, hxC⟩
    exact ⟨hxC, hx⟩


theorem commutator_mem_of_factor {H R : Subgroup G} {t : G} (htH : t ∈ H)
    (hRn : H ≤ Subgroup.normalizer (R : Set G))
    (hfac : ∀ x ∈ H, ∃ a ∈ R, ∃ c ∈ Subgroup.centralizer ({t} : Set G), a * c = x) :
    ∀ x ∈ H, x * t * x⁻¹ * t⁻¹ ∈ R := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hfac x hx
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have h : a * c * t * (a * c)⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by
    calc a * c * t * (a * c)⁻¹ * t⁻¹ = a * (c * t * c⁻¹) * a⁻¹ * t⁻¹ := by group
      _ = a * (t * a⁻¹ * t⁻¹) := by rw [hct]; group
  rw [h]
  exact R.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hRn htH) a⁻¹).mp (R.inv_mem ha))


end CFSG.Semidihedral.LocalPrimeFailure
