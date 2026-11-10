module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore derivedSeriesOf map_perfectCore)

section Centralizers

variable {G : Type*} [Group G]

theorem centralizer_sup_subgroup_eq_inf (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  rw [sup_eq_closure, centralizer_closure]
  ext x
  simp only [mem_centralizer_iff, Set.mem_union, SetLike.mem_coe, or_imp, forall_and, mem_inf]

theorem inf_centralizer_sup_centralizer (E T : Subgroup G) :
    E ⊓ centralizer ((T ⊔ centralizer (E : Set G) : Subgroup G) : Set G) =
      E ⊓ centralizer (T : Set G) := by
  rw [centralizer_sup_subgroup_eq_inf, ← inf_assoc, inf_right_comm,
    inf_eq_left.mpr (le_centralizer_iff.mpr le_rfl)]

theorem inf_centralizer_eq_of_sup_eq {E T T' : Subgroup G}
    (h : T ⊔ centralizer (E : Set G) = T' ⊔ centralizer (E : Set G)) :
    E ⊓ centralizer (T : Set G) = E ⊓ centralizer (T' : Set G) := by
  rw [← inf_centralizer_sup_centralizer, h, inf_centralizer_sup_centralizer]

theorem map_centralizer_eq_inf_centralizer {M : Type*} [Group M] {E : Subgroup G} (Φ : M ≃* E)
    (S : Subgroup M) :
    (centralizer (S : Set M)).map (E.subtype.comp Φ.toMonoidHom) =
      E ⊓ centralizer ((S.map (E.subtype.comp Φ.toMonoidHom) : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    refine mem_inf.2 ⟨(Φ m).2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have h := mem_centralizer_iff.1 hm s hs
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, MulEquiv.coe_toMonoidHom]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  · intro x hx
    obtain ⟨hxE, hxC⟩ := mem_inf.1 hx
    refine ⟨Φ.symm ⟨x, hxE⟩, mem_centralizer_iff.2 fun s hs => ?_, by simp⟩
    have h := mem_centralizer_iff.1 hxC (Φ s) ⟨s, hs, rfl⟩
    apply Φ.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact h

theorem injective_subtype_comp_mulEquiv {M : Type*} [Group M] {E : Subgroup G} (Φ : M ≃* E) :
    Function.Injective (E.subtype.comp Φ.toMonoidHom) :=
  E.subtype_injective.comp Φ.injective

variable [Finite G]

theorem perfectCore_inf_centralizer_eq_map_mulEquiv {M : Type*} [Group M] [Finite M] {E : Subgroup G}
    (Φ : M ≃* E) {S : Subgroup M} {T : Subgroup G}
    (hT : T ⊔ centralizer (E : Set G) =
      S.map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G)) :
    perfectCore (E ⊓ centralizer (T : Set G)) =
      (perfectCore (centralizer (S : Set M))).map (E.subtype.comp Φ.toMonoidHom) := by
  rw [inf_centralizer_eq_of_sup_eq hT, ← map_centralizer_eq_inf_centralizer, map_perfectCore]

theorem card_perfectCore_inf_centralizer_eq {M : Type*} [Group M] [Finite M] {E : Subgroup G}
    (Φ : M ≃* E) {S : Subgroup M} {T : Subgroup G}
    (hT : T ⊔ centralizer (E : Set G) =
      S.map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G)) :
    Nat.card (perfectCore (E ⊓ centralizer (T : Set G))) =
      Nat.card (perfectCore (centralizer (S : Set M))) := by
  rw [perfectCore_inf_centralizer_eq_map_mulEquiv Φ hT,
    Subgroup.card_map_of_injective (injective_subtype_comp_mulEquiv Φ)]

end Centralizers

section PieceCards

variable {G : Type*} [Group G]

@[expose] noncomputable def pieceCards (E T₁₂ T₁ T₂ : Subgroup G) : ℕ × ℕ × ℕ :=
  (Nat.card (perfectCore (E ⊓ centralizer (T₁₂ : Set G))),
    Nat.card (perfectCore (E ⊓ centralizer (T₁ : Set G))),
    Nat.card (perfectCore (E ⊓ centralizer (T₂ : Set G))))

theorem pieceCards_top (T₁₂ T₁ T₂ : Subgroup G) :
    pieceCards ⊤ T₁₂ T₁ T₂ =
      (Nat.card (perfectCore (centralizer (T₁₂ : Set G))),
        Nat.card (perfectCore (centralizer (T₁ : Set G))),
        Nat.card (perfectCore (centralizer (T₂ : Set G)))) := by
  simp only [pieceCards, top_inf_eq]

theorem pieceCards_eq_of_mulEquiv [Finite G] {M : Type*} [Group M] [Finite M] {E : Subgroup G}
    (Φ : M ≃* E) {S₁₂ S₁ S₂ : Subgroup M} {T₁₂ T₁ T₂ : Subgroup G}
    (h₁₂ : T₁₂ ⊔ centralizer (E : Set G) =
      S₁₂.map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G))
    (h₁ : T₁ ⊔ centralizer (E : Set G) =
      S₁.map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G))
    (h₂ : T₂ ⊔ centralizer (E : Set G) =
      S₂.map (E.subtype.comp Φ.toMonoidHom) ⊔ centralizer (E : Set G)) :
    pieceCards E T₁₂ T₁ T₂ = pieceCards ⊤ S₁₂ S₁ S₂ := by
  rw [pieceCards_top, pieceCards, card_perfectCore_inf_centralizer_eq Φ h₁₂,
    card_perfectCore_inf_centralizer_eq Φ h₁, card_perfectCore_inf_centralizer_eq Φ h₂]

end PieceCards

section Prod

variable {M₁ M₂ : Type*} [Group M₁] [Group M₂]

theorem derivedSeriesOf_prod (H : Subgroup M₁) (K : Subgroup M₂) (n : ℕ) :
    derivedSeriesOf (H.prod K) n = (derivedSeriesOf H n).prod (derivedSeriesOf K n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_succ,
      CFSG.Quasithin.derivedSeriesOf_succ, ih, commutator_prod_prod]

theorem perfectCore_prod (H : Subgroup M₁) (K : Subgroup M₂) :
    perfectCore (H.prod K) = (perfectCore H).prod (perfectCore K) := by
  ext x
  simp only [perfectCore, derivedSeriesOf_prod, mem_iInf, mem_prod, forall_and]


end Prod

section Exclusion


end Exclusion

end CFSG.SeitzReduction.F4Pilot
