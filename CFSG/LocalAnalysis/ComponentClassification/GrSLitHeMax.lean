module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL2
public import CFSG.LocalAnalysis.ComponentClassification.GSLitMaximalTriple

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem catalog_fusionZStar_of_isPComponent {X : Type} [Group X] [Finite X]
    (hK : Assembly.KProper Blueprint.Catalog X) {F M : Subgroup X} (hF : F ≠ ⊤) (hMF : M ≤ F)
    (hM : IsPComponent 2 (M.subgroupOf F)) : Blueprint.Catalog (M ⧸ Open.fusionZStar M) := by
  obtain ⟨hs, hna, -, -⟩ := fusionZStar_quotient_of_isPComponent hMF hM
  set L : Subgroup X := (Open.fusionZStar M).map M.subtype with hLdef
  have hL : L.subgroupOf M = Open.fusionZStar M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hMt : M ≠ ⊤ := fun h => hF (eq_top_iff.mpr (h ▸ hMF))
  have : (L.subgroupOf M).Normal := hL ▸ inferInstance
  let e : (M ⧸ L.subgroupOf M) ≃* (M ⧸ Open.fusionZStar M) := QuotientGroup.quotientMulEquivOfEq hL
  have hs' : IsSimpleGroup (M ⧸ L.subgroupOf M) := e.isSimpleGroup
  have hna' : ∃ x y : M ⧸ L.subgroupOf M, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact SectionRank.catalog_of_mulEquiv e.symm
    (hK M L hMt (by rw [hLdef]; exact map_subtype_le _) hs' hna')

@[expose] def HeldNotProperFixedInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ FixedCommutingProduct.fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (FixedCommutingProduct.fixedSubgroup σ)) → P ≠ ⊤ →
      ¬ Nonempty (P ⧸ Open.fusionZStar P ≃* Blueprint.NativeSporadic.He)

@[expose] def L34UnbalancedKGroupInput : Prop :=
  ∀ (M : Type) [Group M] [Finite M], SectionRank.IsKGroupCat M →
    ∀ (a x : M) (J : Subgroup M), GSUnbalancingTriple a x J →
      IsL34Type (J ⧸ Open.fusionZStar J) →
      ∃ K : Subgroup M, IsPComponent 2 K ∧
        ((IsL34Type (K ⧸ Open.fusionZStar K) ∧ J ⊔ pPrimeCore 2 M = K ⊔ pPrimeCore 2 M) ∨
          (Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) ∧
            J ≤ K ⊔ pPrimeCore 2 M) ∨
          (IsL34Type (K ⧸ Open.fusionZStar K) ∧ conjugate K a ≠ K ∧
            J ≤ K ⊔ conjugate K a ⊔ pPrimeCore 2 M))

theorem simpleFixedComponents_notHeld (h : HeldNotProperFixedInput) :
    SimpleFixedComponents (fun K _ => Blueprint.Catalog K) fun K _ => ¬ IsHeldType K :=
  fun S _ _ hs hna hc σ hσ P hPF hP hPne => h S hs hna hc σ hσ P hPF hP hPne

theorem properFixedComponents_notHeld (h : HeldNotProperFixedInput) :
    ProperFixedComponents (fun K _ => Blueprint.Catalog K) fun K _ => ¬ IsHeldType K :=
  properFixedComponents_of_simple (fun _ _ _ _ e hc => SectionRank.catalog_of_mulEquiv e hc)
    (fun _ _ _ _ e hn hH => hn (hH.map fun f => e.symm.trans f)) (simpleFixedComponents_notHeld h)


end CFSG.ComponentClassification.GrSLit
