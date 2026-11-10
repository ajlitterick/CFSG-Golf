module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOddTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Open.FusionDefs

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement

@[expose] def UList (S : Type) [Group S] : Prop :=
  OddLieType S ∨ (∃ n : ℕ, Odd n ∧ 7 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    LieModel S .PSL 3 2 2 ∨ Nonempty (S ≃* NativeSporadic.He)

theorem oddLieType_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : OddLieType S) : OddLieType T := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, hadm, LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem uList_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : UList S) :
    UList T := by
  rcases h with h | ⟨n, hn, h7, ⟨e'⟩⟩ | h | h
  · exact .inl (oddLieType_of_mulEquiv e h)
  · exact .inr (.inl ⟨n, hn, h7, ⟨e.symm.trans e'⟩⟩)
  · exact .inr (.inr (.inl (LieType.CurtisTits.lieModel_of_mulEquiv e h)))
  · obtain ⟨e'⟩ := h
    exact .inr (.inr (.inr ⟨e.symm.trans e'⟩))

theorem uList_of_uOutcome {B : Type} [Group B] (h : OutcomeLocal.UOutcome B) :
    UList (GeneralizedFitting.subgroup B) := by
  rcases h with h | ⟨n, hn, h7, he, -⟩ | ⟨h | h, -⟩
  · exact .inl h
  · exact .inr (.inl ⟨n, hn, h7, he⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = pPrimeCore 2 X :=
  (CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm

theorem map_centralPreimage_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (R : Subgroup A) [R.Normal] (R' : Subgroup B) [R'.Normal] (h : R.map e.toMonoidHom = R') :
    (centralPreimage R).map e.toMonoidHom = centralPreimage R' := by
  ext b
  rw [mem_map_equiv, mem_centralPreimage_iff, mem_centralPreimage_iff]
  constructor
  · intro hb m
    rw [← h]
    exact ⟨_, hb (e.symm m), by
      rw [MulEquiv.coe_toMonoidHom, map_commutatorElement, e.apply_symm_apply,
        e.apply_symm_apply]⟩
  · intro hb m
    have hm := hb (e m)
    rw [← h] at hm
    obtain ⟨r, hr, hre⟩ := hm
    have hr' : r = ⁅e.symm b, m⁆ := by
      apply e.injective
      rw [← MulEquiv.coe_toMonoidHom, hre, MulEquiv.coe_toMonoidHom, map_commutatorElement,
        e.apply_symm_apply]
    exact hr' ▸ hr

theorem fusionZStar_eq_centralPreimage (L : Type*) [Group L] :
    Open.fusionZStar L = centralPreimage (pPrimeCore 2 L) := by
  ext l
  change l ∈ centralPreimage (Open.fusionOddCore L) ↔ _
  rw [mem_centralPreimage_iff, mem_centralPreimage_iff]
  rw [show Open.fusionOddCore L = pPrimeCore 2 L from oddCore_eq_pPrimeCore_two L]

noncomputable def hullSectionEquiv {G : Type*} [Group G] {L H : Subgroup G} (hLH : L ≤ H) :
    hullSection L H ≃* L ⧸ Open.fusionZStar L :=
  (QuotientGroup.congr _ (centralPreimage (pPrimeCore 2 L)) (subgroupOfEquivOfLe hLH)
    (map_centralPreimage_mulEquiv _ _ _ (pPrimeCore_map_iso 2 _))).trans
    (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_centralPreimage L).symm)


end CFSG.ComponentClassification.TBLit
