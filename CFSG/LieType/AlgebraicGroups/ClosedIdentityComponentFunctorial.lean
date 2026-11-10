module

public import CFSG.LieType.AlgebraicGroups.CentralizerComponentInduction
import CFSG.Mathlib.GroupTheory.NormalizerTorsion

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {k : Type} [Field k]

theorem finiteIndex_subgroupOf_of_finite_left_factor {Z E T : Subgroup (ModGL τ k)}
    [Finite E] (hEZ : E ≤ Z) (hZ : ∀ z ∈ Z, ∃ e ∈ E, ∃ t ∈ T, z = e * t) :
    (T.subgroupOf Z).FiniteIndex := by
  have hsurj : Function.Surjective (fun e : E =>
      (QuotientGroup.mk (⟨e, hEZ e.2⟩ : Z) : Z ⧸ T.subgroupOf Z)) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he, t, ht, hzt⟩ := hZ z z.2
    have heZ : e ∈ Z := hEZ he
    refine ⟨⟨e, he⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    change e⁻¹ * (z : ModGL τ k) ∈ T
    rw [hzt, inv_mul_cancel_left]
    exact ht
  have : Finite (Z ⧸ T.subgroupOf Z) := Finite.of_surjective _ hsurj
  exact Subgroup.finiteIndex_of_finite_quotient

theorem closedIdentityComponent_inf_eq_of_le
    (G T : Subgroup (ModGL τ k)) (hG : closedIdentityComponent G ≤ T) :
    closedIdentityComponent (G ⊓ T) = closedIdentityComponent G := by
  apply le_antisymm (closedIdentityComponent_mono inf_le_left)
  exact subset_closedIdentityComponent (le_inf (closedIdentityComponent_le G) hG)
    (closedIdentityComponent G).one_mem (isPointIrreducible_closedIdentityComponent G)

theorem closedIdentityComponent_le_of_isPointClosed_finiteIndex
    {Z T : Subgroup (ModGL τ k)}
    (hT : IsPointClosed k (transportPoints (modGLPoint τ k) (T : Set (ModGL τ k))))
    [(T.subgroupOf Z).FiniteIndex] : closedIdentityComponent Z ≤ T := by
  let e := modGLZariski τ k
  let Z' := Z.map e.toMonoidHom
  let T' := T.map e.toMonoidHom
  have hTc : IsClosed (T' : Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
    rw [isPointClosed_iff_isClosed_image] at hT
    exact hT
  let f := e.toMonoidHom.subgroupMap Z
  have hf : Function.Surjective f := e.toMonoidHom.subgroupMap_surjective Z
  have hK : ((T.subgroupOf Z).map f) = T'.subgroupOf Z' := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_map_of_mem e.toMonoidHom hz
    · intro hx
      obtain ⟨z, rfl⟩ := hf x
      have hzT : (z : ModGL τ k) ∈ T := by
        change e (z : ModGL τ k) ∈ T.map e.toMonoidHom at hx
        simpa only [MulEquiv.symm_apply_apply] using (Subgroup.mem_map_equiv).mp hx
      exact ⟨z, hzT, rfl⟩
  have : (T'.subgroupOf Z').FiniteIndex := hK ▸ Subgroup.FiniteIndex.map_of_surjective (T.subgroupOf Z) hf
  have hle : SeminaireExp3.ZariskiGL.identityComponent Z' ≤ T' :=
    SeminaireExp3.ZariskiGL.identityComponent_le_of_isClosed hTc
  intro g hg
  have h : e g ∈ T' := hle (mem_closedIdentityComponent.mp hg)
  simpa only [MulEquiv.symm_apply_apply] using (Subgroup.mem_map_equiv).mp h

theorem isPointIrreducible_map_conj {S : Subgroup (ModGL τ k)}
    (hS : IsPointIrreducible k (transportPoints (modGLPoint τ k) (S : Set (ModGL τ k))))
    (g : ModGL τ k) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      (S.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))) := by
  rw [isPointIrreducible_iff_isIrreducible_image] at hS ⊢
  have h := hS.image (fun x => modGLZariski τ k g * x * (modGLZariski τ k g)⁻¹)
    ((continuous_mul_const _).comp (continuous_const_mul _)).continuousOn
  convert h using 1
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨modGLZariski τ k z, ⟨z, hz, rfl⟩, ?_⟩
    change modGLZariski τ k g * modGLZariski τ k z * (modGLZariski τ k g)⁻¹ =
      modGLZariski τ k (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(MulAut.conj g) z, mem_map_of_mem _ hz, by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]⟩

theorem closedIdentityComponent_map_conj_le (Z : Subgroup (ModGL τ k))
    (g : ModGL τ k) :
    (closedIdentityComponent Z).map (MulAut.conj g).toMonoidHom ≤
      closedIdentityComponent (Z.map (MulAut.conj g).toMonoidHom) :=
  subset_closedIdentityComponent (Subgroup.map_mono (closedIdentityComponent_le Z))
    (Subgroup.one_mem _) (isPointIrreducible_map_conj
      (isPointIrreducible_closedIdentityComponent Z) g)

theorem closedIdentityComponent_map_conj (Z : Subgroup (ModGL τ k))
    (g : ModGL τ k) :
    closedIdentityComponent (Z.map (MulAut.conj g).toMonoidHom) =
      (closedIdentityComponent Z).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ (closedIdentityComponent_map_conj_le Z g)
  have h := closedIdentityComponent_map_conj_le
    (Z.map (MulAut.conj g).toMonoidHom) g⁻¹
  have hc : ((MulAut.conj g⁻¹).toMonoidHom).comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (ModGL τ k) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [Subgroup.map_map, hc, Subgroup.map_id] at h
  intro x hx
  have hm : g⁻¹ * x * g ∈ closedIdentityComponent Z :=
    h (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx)
  exact ⟨g⁻¹ * x * g, hm, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩


theorem map_adjoint_centralizer_conj (E : Subgroup (ModGL τ k))
    {g : ModGL τ k} (hg : g ∈ adjointGroup τ k) :
    (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))).map (MulAut.conj g).toMonoidHom =
      adjointGroup τ k ⊓ centralizer
        (E.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(adjointGroup τ k).mul_mem ((adjointGroup τ k).mul_mem hg hy.1)
      ((adjointGroup τ k).inv_mem hg), ?_⟩
    change g * y * g⁻¹ ∈ centralizer (E.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))
    rw [mem_centralizer_iff]
    rintro z ⟨e, he, rfl⟩
    have hye := mem_centralizer_iff.mp hy.2 e he
    change (g * e * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * e * g⁻¹)
    calc _ = g * (e * y) * g⁻¹ := by group
      _ = g * (y * e) * g⁻¹ := by rw [hye]
      _ = _ := by group
  · rintro ⟨hxG, hxE⟩
    refine ⟨g⁻¹ * x * g, ⟨(adjointGroup τ k).mul_mem
      ((adjointGroup τ k).mul_mem ((adjointGroup τ k).inv_mem hg) hxG) hg, ?_⟩, ?_⟩
    · change g⁻¹ * x * g ∈ centralizer (E : Set (ModGL τ k))
      rw [mem_centralizer_iff]
      intro e he
      have h := mem_centralizer_iff.mp hxE ((MulAut.conj g) e) (mem_map_of_mem _ he)
      change (g * e * g⁻¹) * x = x * (g * e * g⁻¹) at h
      calc _ = g⁻¹ * ((g * e * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * e * g⁻¹)) * g := by rw [h]
        _ = _ := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group


theorem mem_normalizer_connected_adjoint_centralizer
    (E : Subgroup (ModGL τ k)) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k) (hgE : g ∈ normalizer (E : Set (ModGL τ k))) :
    g ∈ normalizer (closedIdentityComponent
      (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))) : Set (ModGL τ k)) := by
  have hmap := map_adjoint_centralizer_conj E hg
  change (adjointGroup τ k ⊓ centralizer (E : Set (ModGL τ k))).map (MulAut.conj g) =
      adjointGroup τ k ⊓ centralizer
        ((E.map (MulAut.conj g) : Subgroup (ModGL τ k)) : Set (ModGL τ k)) at hmap
  rw [mem_normalizer_iff_map_conj_eq.mp hgE] at hmap
  apply normalizer_le_normalizer_closedIdentityComponent
  exact mem_normalizer_iff_map_conj_eq.mpr hmap


end CFSG.LieType.AlgebraicGroups
