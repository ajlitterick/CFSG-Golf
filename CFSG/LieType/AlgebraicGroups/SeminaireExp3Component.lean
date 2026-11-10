module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open Topology Pointwise TopologicalSpace

section TranslationGroup

variable {G : Type*} [Group G] [TopologicalSpace G]

section Translation

variable [SeparatelyContinuousMul G]

theorem isPreirreducible_mul {X Y : Set G} (hX : IsPreirreducible X) (hY : IsPreirreducible Y) :
    IsPreirreducible (X * Y) := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hX ⊢
  intro Z₁ Z₂ hZ₁ hZ₂ hXY
  have hcl : ∀ Z : Set G, IsClosed Z → IsClosed {x | ∀ y ∈ Y, x * y ∈ Z} := fun Z hZ => by
    have : {x | ∀ y ∈ Y, x * y ∈ Z} = ⋂ y ∈ Y, (· * y) ⁻¹' Z := by
      ext x
      simp
    rw [this]
    exact isClosed_biInter fun y _ => hZ.preimage (continuous_mul_const y)
  have hcover : X ⊆ {x | ∀ y ∈ Y, x * y ∈ Z₁} ∪ {x | ∀ y ∈ Y, x * y ∈ Z₂} := by
    intro x hx
    have hxY := (isPreirreducible_iff_isClosed_union_isClosed.1
      (hY.image _ (continuous_const_mul x).continuousOn)) Z₁ Z₂ hZ₁ hZ₂
      (by rintro _ ⟨y, hy, rfl⟩; exact hXY (Set.mul_mem_mul hx hy))
    rcases hxY with h | h
    · exact Or.inl fun y hy => h ⟨y, hy, rfl⟩
    · exact Or.inr fun y hy => h ⟨y, hy, rfl⟩
  rcases hX _ _ (hcl Z₁ hZ₁) (hcl Z₂ hZ₂) hcover with h | h
  · exact Or.inl (by rintro _ ⟨x, hx, y, hy, rfl⟩; exact h hx y hy)
  · exact Or.inr (by rintro _ ⟨x, hx, y, hy, rfl⟩; exact h hx y hy)


theorem isIrreducible_smul {X : Set G} (hX : IsIrreducible X) (g : G) : IsIrreducible (g • X) := by
  rw [← Set.image_smul]
  exact hX.image _ (continuous_const_mul g).continuousOn

theorem smul_mem_irreducibleComponents {C : Set G} (hC : C ∈ irreducibleComponents G) (g : G) :
    g • C ∈ irreducibleComponents G := by
  refine ⟨isIrreducible_smul hC.1 g, fun D hD hCD => ?_⟩
  have h : g⁻¹ • D ⊆ C := hC.2 (isIrreducible_smul hD g⁻¹) fun c hc =>
    ⟨g * c, hCD (Set.smul_mem_smul_set hc), by simp [smul_eq_mul]⟩
  intro d hd
  exact ⟨g⁻¹ * d, h ⟨d, hd, rfl⟩, by simp [smul_eq_mul]⟩

end Translation

theorem isIrreducible_inv [ContinuousInv G] {X : Set G} (hX : IsIrreducible X) :
    IsIrreducible X⁻¹ := by
  rw [← Set.image_inv_eq_inv]
  exact hX.image _ continuous_inv.continuousOn

variable [SeparatelyContinuousMul G] [ContinuousInv G]

omit [ContinuousInv G] in
theorem irreducibleComponent_one_mul {Y : Set G} (hY : IsIrreducible Y) (h1 : (1 : G) ∈ Y) :
    irreducibleComponent (1 : G) * Y = irreducibleComponent 1 :=
  eq_irreducibleComponent
    (isPreirreducible_mul isIrreducible_irreducibleComponent.isPreirreducible hY.isPreirreducible)
    fun c hc => ⟨c, hc, 1, h1, mul_one c⟩

omit [ContinuousInv G] in
theorem subset_irreducibleComponent_one {Y : Set G} (hY : IsIrreducible Y) (h1 : (1 : G) ∈ Y) :
    Y ⊆ irreducibleComponent 1 := fun y hy => by
  rw [← irreducibleComponent_one_mul hY h1]
  exact ⟨1, mem_irreducibleComponent, y, hy, one_mul y⟩

variable (G) in
@[expose] def identityComponent : Subgroup G where
  carrier := irreducibleComponent 1
  one_mem' := mem_irreducibleComponent
  mul_mem' {a b} ha hb := by
    rw [← irreducibleComponent_one_mul isIrreducible_irreducibleComponent
      mem_irreducibleComponent]
    exact Set.mul_mem_mul ha hb
  inv_mem' {a} ha :=
    subset_irreducibleComponent_one (isIrreducible_inv isIrreducible_irreducibleComponent)
      (by rw [Set.mem_inv, inv_one]; exact mem_irreducibleComponent) (Set.inv_mem_inv.2 ha)

theorem coe_identityComponent : (identityComponent G : Set G) = irreducibleComponent 1 :=
  rfl

theorem isClosed_identityComponent : IsClosed (identityComponent G : Set G) :=
  isClosed_irreducibleComponent

theorem isIrreducible_identityComponent : IsIrreducible (identityComponent G : Set G) :=
  isIrreducible_irreducibleComponent

theorem identityComponent_mem_irreducibleComponents :
    (identityComponent G : Set G) ∈ irreducibleComponents G :=
  irreducibleComponent_mem_irreducibleComponents 1

theorem subset_identityComponent {Y : Set G} (hY : IsIrreducible Y) (h1 : (1 : G) ∈ Y) :
    Y ⊆ identityComponent G :=
  subset_irreducibleComponent_one hY h1

instance identityComponent_normal : (identityComponent G).Normal where
  conj_mem n hn g := by
    have h := subset_identityComponent (Y := (fun x => g * x * g⁻¹) '' (identityComponent G))
      (isIrreducible_identityComponent.image _
        ((continuous_mul_const g⁻¹).comp (continuous_const_mul g)).continuousOn)
      ⟨1, one_mem _, by simp⟩
    exact h ⟨n, hn, rfl⟩


variable [NoetherianSpace G]

instance identityComponent_finiteIndex : (identityComponent G).FiniteIndex := by
  have : Finite (irreducibleComponents G) := NoetherianSpace.finite_irreducibleComponents
  let f : G ⧸ identityComponent G → irreducibleComponents G := fun q =>
    ⟨q.out • (identityComponent G : Set G),
      smul_mem_irreducibleComponents identityComponent_mem_irreducibleComponents _⟩
  have hf : Function.Injective f := by
    intro q q' h
    have h' : q.out • (identityComponent G : Set G) = q'.out • (identityComponent G : Set G) :=
      congrArg Subtype.val h
    have hmem : q'.out ∈ q.out • (identityComponent G : Set G) := by
      rw [h']
      exact ⟨1, one_mem _, mul_one _⟩
    obtain ⟨x, hx, hxq⟩ := hmem
    have hxq' : q.out * x = q'.out := hxq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, ← hxq',
      inv_mul_cancel_left]
    exact hx
  have : Finite (G ⧸ identityComponent G) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem isOpen_identityComponent : IsOpen (identityComponent G : Set G) :=
  (identityComponent G).isOpen_of_isClosed_of_finiteIndex isClosed_identityComponent

theorem coe_identityComponent_eq_connectedComponent :
    (identityComponent G : Set G) = connectedComponent 1 :=
  (isIrreducible_identityComponent.isPreirreducible.isPreconnected.subset_connectedComponent
    (one_mem _)).antisymm
    (IsClopen.connectedComponent_subset ⟨isClosed_identityComponent, isOpen_identityComponent⟩
      (one_mem _))

theorem identityComponent_le_of_isClosed (K : Subgroup G) [K.FiniteIndex]
    (hK : IsClosed (K : Set G)) : identityComponent G ≤ K := by
  intro x hx
  rw [← SetLike.mem_coe, coe_identityComponent_eq_connectedComponent] at hx
  exact IsClopen.connectedComponent_subset ⟨hK, K.isOpen_of_isClosed_of_finiteIndex hK⟩
    K.one_mem hx


end TranslationGroup

section Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

instance subgroup_separatelyContinuousMul [SeparatelyContinuousMul G] (K : Subgroup G) :
    SeparatelyContinuousMul K :=
  IsInducing.separatelyContinuousMul K.subtype ⟨rfl⟩

instance subgroup_continuousInv [ContinuousInv G] (K : Subgroup G) : ContinuousInv K :=
  ContinuousInv.induced K.subtype

instance subgroup_noetherianSpace [NoetherianSpace G] (K : Subgroup G) : NoetherianSpace K :=
  IsInducing.subtypeVal.noetherianSpace

end Subgroup

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k]

@[expose] def identityComponent (K : Subgroup (ZariskiGL ι k)) : Subgroup (ZariskiGL ι k) :=
  (SeminaireExp3.identityComponent K).map K.subtype

theorem identityComponent_subgroupOf (K : Subgroup (ZariskiGL ι k)) :
    (identityComponent K).subgroupOf K = SeminaireExp3.identityComponent K :=
  Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem coe_identityComponent (K : Subgroup (ZariskiGL ι k)) :
    (identityComponent K : Set (ZariskiGL ι k)) =
      Subtype.val '' (SeminaireExp3.identityComponent K : Set K) :=
  rfl

theorem identityComponent_le (K : Subgroup (ZariskiGL ι k)) : identityComponent K ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2


theorem isClosed_identityComponent {K : Subgroup (ZariskiGL ι k)}
    (hK : IsClosed (K : Set (ZariskiGL ι k))) :
    IsClosed (identityComponent K : Set (ZariskiGL ι k)) := by
  have h := SeminaireExp3.isClosed_identityComponent (G := ↥K)
  rw [coe_identityComponent]
  exact hK.isClosedMap_subtype_val _ h

theorem isIrreducible_identityComponent (K : Subgroup (ZariskiGL ι k)) :
    IsIrreducible (identityComponent K : Set (ZariskiGL ι k)) := by
  rw [coe_identityComponent]
  exact SeminaireExp3.isIrreducible_identityComponent.image _ continuous_subtype_val.continuousOn

instance identityComponent_normal (K : Subgroup (ZariskiGL ι k)) :
    ((identityComponent K).subgroupOf K).Normal := by
  rw [identityComponent_subgroupOf]
  infer_instance

instance identityComponent_finiteIndex (K : Subgroup (ZariskiGL ι k)) :
    ((identityComponent K).subgroupOf K).FiniteIndex := by
  rw [identityComponent_subgroupOf]
  infer_instance

theorem identityComponent_le_of_isClosed {K L : Subgroup (ZariskiGL ι k)}
    (hL : IsClosed (L : Set (ZariskiGL ι k))) [(L.subgroupOf K).FiniteIndex] :
    identityComponent K ≤ L := by
  have hcl : IsClosed ((L.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hL.preimage continuous_subtype_val
  have h := SeminaireExp3.identityComponent_le_of_isClosed (L.subgroupOf K) hcl
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (h hx)


end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
