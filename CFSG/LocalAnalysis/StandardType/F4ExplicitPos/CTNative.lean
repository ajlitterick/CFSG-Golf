module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Quasisimple
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedImage
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CTNative

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem roots_eq_setOf_isRoot_native (hA : TauCeti.IsFiniteType τ.cartan) :
    CFSG.LieType.RootSystem.roots hA ∅ = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ :=
        (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, CFSG.LieType.RootSystem.weylAction_mul_apply,
          CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple i * w,
          j, ?_⟩
        rw [CFSG.LieType.RootSystem.weylAction_mul_apply, ← hw,
          CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem weylAction_simple_eq_reflect_native (hA : TauCeti.IsFiniteType τ.cartan)
    (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    CFSG.LieType.RootSystem.weylAction hA
        ((CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple i) γ =
      reflect τ i γ := by
  rw [CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
  rfl

theorem eq_single_or_neg_of_support_native
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {i : Fin τ.rank} (h : ∀ k, k ≠ i → γ k = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 := by
  have e : γ = γ i • Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [h k hk, Pi.single_eq_of_ne hk]
  rcases hγ.eq_one_or_neg_one_of_eq_smul e with h1 | h1
  · left
    rw [e, h1, one_smul]
  · right
    rw [e, h1, neg_one_smul]

theorem adjDatum_roots_native
    (F : RootOperatorFamily τ) (K : Type) [Field K] :
    (adjDatum F K).roots = {γ | IsRoot τ γ} :=
  roots_eq_setOf_isRoot_native _

theorem mem_adjDatum_roots_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} :
    γ ∈ (adjDatum F K).roots ↔ IsRoot τ γ := by
  rw [adjDatum_roots_native F K]
  rfl

theorem xPar_of_isRoot_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c = F.eltElement ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem rootGroup_of_isRoot_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    rootGroup F K γ = F.rootSubgroup K ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem xPar_mem_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c ∈ rootGroup F K γ := by
  rw [xPar_of_isRoot_native h, rootGroup_of_isRoot_native h]
  exact F.eltElement_mem_rootSubgroup _ c

theorem exists_of_mem_rootGroup_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ)
    {g : adjointGroup τ K} (hg : g ∈ rootGroup F K γ) :
    ∃ c : K, g = F.eltElement ⟨γ, h⟩ c := by
  rw [rootGroup_of_isRoot_native h] at hg
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
  exact ⟨c, rfl⟩

theorem mem_rootGroup_iff_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ)
    (g : adjointGroup τ K) : g ∈ rootGroup F K γ ↔ ∃ c, xPar F γ c = g := by
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_native h hg
    exact ⟨c, xPar_of_isRoot_native h c⟩
  · rintro ⟨c, rfl⟩
    exact xPar_mem_native h c

theorem xPar_simple_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c = F.eltElement (simpleRoot τ i) c :=
  xPar_of_isRoot_native (isRoot_single τ i) c

theorem xPar_neg_simple_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot τ i) c :=
  xPar_of_isRoot_native (isRoot_neg_single τ i) c

theorem endHom_eltElement_native
    {F : RootOperatorFamily τ} (α : Root τ) (c : K) :
    endHom K (F.eltElement α c) = F.elt K α c :=
  rfl

theorem xPar_single_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_left (xPar_mem_native (isRoot_single τ i) c)

theorem xPar_neg_single_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_right (xPar_mem_native (isRoot_neg_single τ i) c)

theorem xyx_eq_weylElt_native
    {F : RootOperatorFamily τ} {i : Fin τ.rank} {t : K} (ht : t ≠ 0) :
    F.eltElement (simpleRoot τ i) t * F.eltElement (-simpleRoot τ i) (-t⁻¹) *
        F.eltElement (simpleRoot τ i) t =
      ⟨weylElt τ K i (Units.mk0 t ht), weylElt_mem_adjointGroup i _⟩ := by
  refine endHom_injective ?_
  rw [map_mul, map_mul, endHom_xElt, endHom_yElt, endHom_apply, coe_weylElt]
  simp

theorem weylElement_xPar_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t =
      torusElement τ K i t * CFSG.LieType.Chevalley.weylElement τ K i := by
  rw [CFSG.LieType.Steinberg.weylElement, xPar_simple_native, xPar_neg_simple_native]
  have h := xyx_eq_weylElt_native (F := F) (i := i) (Units.ne_zero t)
  rw [Units.val_inv_eq_inv_val, h]
  refine Subtype.ext ?_
  change weylElt τ K i (Units.mk0 (t : K) _) = torusElt τ K i t * weylElt τ K i 1
  rw [torusElt_mul_weylElt_one, Units.mk0_val]

theorem steinbergWeyl_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t ∈
      CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  mul_mem (mul_mem (xPar_single_mem_rankOne_native i _) (xPar_neg_single_mem_rankOne_native i _))
    (xPar_single_mem_rankOne_native i _)

theorem torusElement_one_eq_native
    (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.torusElement τ K i 1 = 1 :=
  Subtype.ext (torusElt_one i)

theorem weylElement_eq_xPar_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i =
      CFSG.LieType.Steinberg.weylElement (xPar F) i 1 := by
  rw [weylElement_xPar_native, torusElement_one_eq_native, one_mul]

theorem weylElement_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K)
        i := by
  rw [weylElement_eq_xPar_native (F := F) i]
  exact steinbergWeyl_mem_rankOne_native (F := F) i 1

theorem torus_le_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    torus K i ≤ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i := by
  rintro _ ⟨t, rfl⟩
  have h : torusHom K i t = CFSG.LieType.Steinberg.weylElement (xPar F) i t *
      (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElement_xPar_native (F := F) i t).symm
  rw [h]
  exact mul_mem (steinbergWeyl_mem_rankOne_native (F := F) i t)
    (inv_mem (weylElement_mem_rankOne_native (F := F) i))

theorem weylElement_conj_mem_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    CFSG.LieType.Chevalley.weylElement τ K i * x *
        (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ ∈ rootGroup F K (reflect τ i γ) := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_native hγ x).1 hx
  rw [xPar_of_isRoot_native hγ, F.weylElement_mul_eltElement_mul_inv,
    show simple τ i • (⟨γ, hγ⟩ : Root τ) = ⟨reflect τ i γ, IsRoot.reflect i hγ⟩ from
      Subtype.ext (simple_smul i γ), ← xPar_of_isRoot_native (IsRoot.reflect i hγ)]
  exact xPar_mem_native (IsRoot.reflect i hγ) _

theorem torusElement_conj_mem_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    torusElement τ K i t * x * (torusElement τ K i t)⁻¹ ∈ rootGroup F K γ := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_native hγ x).1 hx
  rw [xPar_of_isRoot_native hγ, F.torusElement_mul_eltElement_mul_inv,
    ← xPar_of_isRoot_native hγ]
  exact xPar_mem_native hγ _

theorem weylElement_braid_native
    (hA : TauCeti.IsFiniteType τ.cartan) (i j : Fin τ.rank) :
    ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) i j).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod =
      ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) j i).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod := by
  refine Subtype.ext ?_
  rw [← Subgroup.coe_subtype, map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact prod_braidWord_weylElt hA K i j

theorem iSup_rootGroup_eq_top_native
    {F : RootOperatorFamily τ} :
    ⨆ γ ∈ {γ | IsRoot τ γ}, rootGroup F K γ = ⊤ := by
  set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have e : g = xPar F (Pi.single i 1) c := endHom_injective (by
      rw [xPar_simple_native, endHom_eltElement_native, F.elt_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_single τ i) (xPar_mem_native (isRoot_single τ i) c))
  · have e : g = xPar F (-Pi.single i 1) c := endHom_injective (by
      rw [xPar_neg_simple_native, endHom_eltElement_native, F.elt_neg_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (-Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_neg_single τ i) (xPar_mem_native (isRoot_neg_single τ i) c))

theorem adjDatum_isCTGroupDatum_native
    (F : RootOperatorFamily τ) (K : Type) [Field K] :
    CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (adjDatum F K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (adjDatum F K).isFiniteType) (adjDatum F K).roots
      (adjDatum F K).rootGroup (CFSG.LieType.Chevalley.weylElement τ K) (torus K) where
  n_mem i := weylElement_mem_rankOne_native (F := F) i
  conj_mem i γ hγ x hx := by
    change _ ∈ rootGroup F K _
    rw [weylAction_simple_eq_reflect_native (isFiniteType_cartan τ)]
    exact weylElement_conj_mem_native (F := F) i (mem_adjDatum_roots_native.1 hγ) hx
  braid i j := weylElement_braid_native (isFiniteType_cartan τ) i j
  H_le i := torus_le_rankOne_native (F := F) i
  sq_mem i := ⟨-1, Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (weylElt_one_sq τ K i).symm)⟩
  H_conj_mem l γ hγ h hh x hx := by
    obtain ⟨t, rfl⟩ := hh
    exact torusElement_conj_mem_native (F := F) l t (mem_adjDatum_roots_native.1 hγ) hx
  conj_H_mem j l h hh := by
    obtain ⟨t, rfl⟩ := hh
    have e : CFSG.LieType.Chevalley.weylElement τ K j * torusHom K l t *
        (CFSG.LieType.Chevalley.weylElement τ K j)⁻¹ =
          torusHom K l t * torusHom K j (t ^ (-τ.cartan l j)) :=
      Subtype.ext (weylElt_one_mul_torusElt_mul_inv τ K j l t)
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right ⟨t, rfl⟩) (Subgroup.mem_sup_left ⟨_, rfl⟩)
  le_rankOne i γ hγ hsupp := by
    rcases eq_single_or_neg_of_support_native (mem_adjDatum_roots_native.1 hγ) hsupp with
      rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := by
    rw [adjDatum_roots_native F K]
    exact iSup_rootGroup_eq_top_native (F := F)

theorem f4_isCTGroupDatum_native
    (K : Type) [Field K] :
    CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (f4Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (f4Datum K).isFiniteType) (f4Datum K).roots
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K) :=
  adjDatum_isCTGroupDatum_native (rootOperatorFamily .F4) K

end CFSG.StandardType.F4ExplicitPos.CTNative

public section

namespace CFSG.StandardType.F4ExplicitPos.CTNative

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem isQuasisimple_f4_native
    (k : Type) [Field k] [CharP k 2] [Finite k] :
    CFSG.IsQuasisimple ↥(adjointGroup .F4 k) :=
  Quasisimple.isQuasisimple_f4_native_of_ct k (f4_isCTGroupDatum_native k)

end CFSG.StandardType.F4ExplicitPos.CTNative

public noncomputable section
namespace CFSG.StandardType.F4ExplicitPos.CTNative
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.F4ExplicitPos.FixedImage
open CFSG.HardMathSupport.Solomon.Coordinator


section


end


end CFSG.StandardType.F4ExplicitPos.CTNative
end

end

end

end
