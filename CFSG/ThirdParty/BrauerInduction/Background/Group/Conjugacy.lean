module

-- The previous copy's imports, in place of upstream's `Mathlib.GroupTheory.Nilpotent`. With that
-- import, `Module (ZMod p) (Fin n → ZMod p)` fails to synthesize in some importers (for example
-- `CFSG.Quasithin.Background.SmithB45MatRep`), although their transitive imports are the same.
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Rank
public import Mathlib.Tactic.NormNum.GCD
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugacy and centralizers

This file contains helper lemmas about conjugacy, centralizers, conjugacy
classes, and the orbit-stabilizer formula for the conjugation action.
-/

universe u
variable {G : Type u} [Group G]

/--
Taking inverses preserves conjugacy: `a` is conjugate to `b` iff `a⁻¹` is
conjugate to `b⁻¹`.
-/
lemma IsConj.inv {a b : G} : IsConj a b ↔ IsConj a⁻¹ b⁻¹  := by
  simp only [isConj_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩  := h
    use c
    rw[← hc, conj_inv]
  · intro h
    obtain ⟨c, hc⟩  := h
    use c
    have h := congr_arg (fun x => x⁻¹) hc
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at h
    exact h

/--
Conjugacy in a subgroup implies conjugacy in the ambient group.
-/
lemma IsConj.of_subgroup {H : Subgroup G} {x y : H} (h : IsConj x y) :
    IsConj (x : G) (y : G) := by
  rcases h with ⟨c, hc⟩
  use Units.map H.subtype c
  simp only [Units.coe_map, Subgroup.subtype_apply]
  unfold SemiconjBy at *
  -- Now norm_cast can see "↑(c * x) = ↑(y * c)" and pull the arrows out
  norm_cast

/-- Conjugate elements have the same order. -/
lemma IsConj.orderOf_eq
   {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  apply SemiconjBy.orderOf_eq c
  simp only [SemiconjBy, ← hc, inv_mul_cancel_right]

/--
The chosen representative of a conjugacy class maps back to that conjugacy
class.
-/
@[simp]
lemma ConjClasses.mk_out (C : ConjClasses G) :
    ConjClasses.mk C.out = C := by
      apply Quotient.out_eq C

namespace Subgroup

/--
The centralizer of the singleton `{1}` is the whole group.
-/
lemma centralizer_singleton_one :
    Subgroup.centralizer ({1} : Set G) = ⊤ := by
  ext x
  simp [Subgroup.mem_centralizer_iff]

/--
The centralizer of `g⁻¹` is the same as the centralizer of `g`.
-/
lemma centralizer_singleton_inv (g : G) :
    Subgroup.centralizer ({g⁻¹} : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

lemma card_centralizer_inv (g : G) :
    Nat.card (Subgroup.centralizer ({g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  rw [Subgroup.centralizer_singleton_inv]


/--
Conjugation by `x` gives an equivalence between the centralizer of
`x⁻¹ * g * x` and the centralizer of `g`.
-/
noncomputable def centralizerEquiv (x g : G) :
    centralizer {x⁻¹ * g * x} ≃ centralizer {g} := by
  let φ : G ≃* G := MulAut.conj x
  refine
  { toFun := ?toFun
    , invFun := ?invFun
    , left_inv := ?left_inv
    , right_inv := ?right_inv }
  · intro h
    rcases h with ⟨h, hh⟩
    refine ⟨φ h, ?_⟩
    rw [mem_centralizer_singleton_iff] at hh
    have hx : (x * h * x⁻¹) * g = g * (x * h * x⁻¹) := by
          have := congrArg (fun t => x * t * x⁻¹) hh
          group at this
          group
          exact this
    rw [mem_centralizer_singleton_iff]
    exact SemiconjBy.eq hx
  · intro h
    rcases h with ⟨h, hh⟩
    refine ⟨φ.symm h, ?_⟩
    rw [mem_centralizer_singleton_iff] at hh
    have hx : (x⁻¹ * h * x) * (x⁻¹ * g * x) = (x⁻¹ * g * x) * (x⁻¹ * h * x) := by
      group
      rw[mul_assoc (b:= h), hh]
      simp[mul_assoc]
    rw [mem_centralizer_singleton_iff]
    exact hx
  · intro h; simp [φ, ← mul_assoc]
  · intro h; simp [φ, ← mul_assoc]

/--
Conjugate elements have equivalent centralizers.
-/
noncomputable def centralizerEquivOfIsConj
    {g h : G} (h_conj : IsConj g h) :
    centralizer ({g} : Set G) ≃
      centralizer ({h} : Set G) := by
  let c := Classical.choose h_conj
  have hc := Classical.choose_spec h_conj
  have hh :
      h = (c : G) * g * (c : G)⁻¹ := by
    calc
      h = (h * (c : G)) * (c : G)⁻¹ := by
        simp
      _ = ((c : G) * g) * (c : G)⁻¹ := by
        rw [hc.eq]
      _ = (c : G) * g * (c : G)⁻¹ := by
        rw [mul_assoc]
  rw[hh]
  simpa only [inv_inv] using
    (centralizerEquiv ((c : G)⁻¹) g).symm

/--
Conjugate elements have centralizers of the same cardinality.
-/
lemma card_centralizer_of_isConj
    {g h : G} (h_conj : IsConj g h) :
    Nat.card (centralizer ({g} : Set G)) =
      Nat.card (centralizer ({h} : Set G)) :=
  Nat.card_congr (centralizerEquivOfIsConj h_conj)


end Subgroup

/--
For the conjugation action of a finite group on itself, the size of the
conjugacy class of `g` times the size of the centralizer of `g` is the order of
the group.
-/
lemma MulAction.card_conjClass_mul_card_centralizer [Fintype G] (g : G) :
    (Nat.card (MulAction.orbit (ConjAct G) g)) *
        (Nat.card ↥(Subgroup.centralizer ({g} : Set G)))
      = Fintype.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  change
    (MulAction.orbit (ConjAct G) g).ncard *
        Nat.card ↥(MulAction.stabilizer (ConjAct G) g)
      = Fintype.card G
  haveI : Fintype ↥(MulAction.orbit (ConjAct G) g) :=
    Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (ConjAct G) g) :=
    Fintype.ofFinite _
  have horbit :
      (MulAction.orbit (ConjAct G) g).ncard =
        Fintype.card ↥(MulAction.orbit (ConjAct G) g) := by
    change
      Nat.card ↥(MulAction.orbit (ConjAct G) g) =
        Fintype.card ↥(MulAction.orbit (ConjAct G) g)
    exact Nat.card_eq_fintype_card
  have hstab :
      Nat.card ↥(MulAction.stabilizer (ConjAct G) g) =
        Fintype.card ↥(MulAction.stabilizer (ConjAct G) g) := by
    exact Nat.card_eq_fintype_card
  rw [horbit, hstab]
  exact
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) g
