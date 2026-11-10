module

public import CFSG.Sporadic.Recognition.JankoWongPresTables
public import CFSG.Sporadic.Recognition.JankoWongPresRelations
public import CFSG.Sporadic.McL

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open CFSG.CosetTable CFSG.Sporadic.McL

abbrev jwPresented (neg : Bool) : Type := PG 6 (jwRels neg)


@[expose] abbrev JWFacts (neg : Bool) : Prop :=
  (Finite (jwPresented neg) ∧ Nat.card (jwPresented neg) ≤ 898128000) ∧ jwTabCheck neg = true

section Model


noncomputable def jwPhi (neg : Bool) (h : jwTabCheck neg = true) : jwPresented neg →* J :=
  PresentedGroup.toGroup (f := jwGen neg) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_jwGen_eq_one neg h hw

theorem jwPhi_of (neg : Bool) (h : jwTabCheck neg = true) (i : Fin 6) :
    jwPhi neg h (PresentedGroup.of i) = jwGen neg i :=
  PresentedGroup.toGroup.of _


theorem jwPhi_surjective (neg : Bool) (h : jwTabCheck neg = true) :
    Function.Surjective (jwPhi neg h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_jwGen neg h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, jwPhi_of neg h i⟩

theorem jwPhi_bijective {neg : Bool} (h : JWFacts neg) :
    Function.Bijective (jwPhi neg h.2) := by
  obtain ⟨hfin, hcard⟩ := h.1
  have := hfin
  refine (jwPhi_surjective neg _).bijective_of_nat_card_le ?_
  rw [card_J]
  exact hcard

noncomputable def jwPresentedEquivJ {neg : Bool} (h : JWFacts neg) :
    jwPresented neg ≃* J :=
  MulEquiv.ofBijective _ (jwPhi_bijective h)

noncomputable def jwPresentedEquivMcL {neg : Bool} (h : JWFacts neg) :
    jwPresented neg ≃* CFSG.Blueprint.NativeSporadic.McL :=
  (jwPresentedEquivJ h).trans mclEquivJ.symm

theorem isSimpleGroup_jwPresented {neg : Bool} (h : JWFacts neg) :
    IsSimpleGroup (jwPresented neg) := by
  exact @MulEquiv.isSimpleGroup (jwPresented neg) _ J _ isSimpleGroup_J (jwPresentedEquivJ h)


end Model

theorem lift_gen_rels {G : Type*} [Group G] (neg : Bool) (e : JWElements G)
    (hp : ∀ p ∈ jwPairs neg, e.eval p.1 = e.eval p.2) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ (jwRels neg).map FreeGroup.mk},
      FreeGroup.lift e.gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hw
  rw [JWElements.lift_mk, JWElements.eval_append, JWElements.eval_inv, hp p hpm, mul_inv_cancel]

section Recognition


theorem exists_mulEquiv_mcl_of_pairs {G : Type*} [Group G] {neg : Bool} (e : JWElements G)
    (h : JWFacts neg) (hp : ∀ p ∈ jwPairs neg, e.eval p.1 = e.eval p.2)
    (hK : Subgroup.closure e.gens ≠ ⊥) :
    Nonempty (Subgroup.closure e.gens ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  have hsimple := isSimpleGroup_jwPresented h
  let ψ : jwPresented neg →* G := PresentedGroup.toGroup (lift_gen_rels neg e hp)
  have hrange : ψ.range = Subgroup.closure e.gens := by
    have hcomp : (ψ ∘ PresentedGroup.of) = e.gen := funext fun i => PresentedGroup.toGroup.of _
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← e.range_gen, ← Set.range_comp, hcomp]
  have hker : ψ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h0
    · exact h0
    · exfalso
      apply hK
      rw [← hrange, MonoidHom.range_eq_bot_iff]
      exact MonoidHom.ker_eq_top_iff.1 h0
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (jwPresentedEquivMcL h)⟩


theorem exists_mulEquiv_mcl_of_relations {G : Type*} [Group G] {ι : ℤˣ} {e : JWElements G}
    (hrel : JWRelations ι e) (hc : JWFacts false ∧ JWFacts true)
    (hK : Subgroup.closure e.gens ≠ ⊥) :
    Nonempty (Subgroup.closure e.gens ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  refine exists_mulEquiv_mcl_of_pairs e ?_ hrel.eval_pairs hK
  rcases Int.units_eq_one_or ι with rfl | rfl
  · have : decide ((1 : ℤˣ) = -1) = false := by decide
    rw [this]; exact hc.1
  · have : decide ((-1 : ℤˣ) = -1) = true := by decide
    rw [this]; exact hc.2


end Recognition

end CFSG.Sporadic.Recognition.JankoWong
