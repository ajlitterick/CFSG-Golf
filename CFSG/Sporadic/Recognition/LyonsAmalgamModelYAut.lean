module

public import CFSG.Sporadic.Recognition.LyonsAmalgamModelY
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly1080

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def pairG {X : Type*} [Group X] (x y : X) (l : ℤ) : X :=
  if l = 1 then x else if l = -1 then x⁻¹ else if l = 2 then y else y⁻¹

@[expose] def RelPair {X : Type*} [Group X] (x y : X) : Prop :=
  (∀ w ∈ autRelators, wordG (pairG x y) w = 1) ∧ (∀ w ∈ autWitnesses, wordG (pairG x y) w ≠ 1)

theorem wordG_pairG_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (x y : X) (w : List ℤ) :
    wordG (pairG (f x) (f y)) w = f (wordG (pairG x y) w) := by
  have h : ∀ l, pairG (f x) (f y) l = f (pairG x y l) := fun l => by
    unfold pairG
    split_ifs <;> simp
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => h l

theorem relPair_map_iff {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {x y : X} : RelPair (f x) (f y) ↔ RelPair x y := by
  simp only [RelPair, wordG_pairG_map, ne_eq, map_eq_one_iff f hf]

theorem relPair_mulEquiv_iff {X Y : Type*} [Group X] [Group Y] (α : X ≃* Y) {x y : X} :
    RelPair (α x) (α y) ↔ RelPair x y :=
  relPair_map_iff (f := α.toMonoidHom) α.injective

theorem card_mulAut_le_card_pairs {X : Type*} [Group X] [Finite X] (a b : X)
    (hab : Subgroup.closure ({a, b} : Set X) = ⊤) (P : X → X → Prop)
    (hP : ∀ (α : MulAut X) (x y : X), P x y → P (α x) (α y)) (hPab : P a b) :
    Nat.card (MulAut X) ≤ Nat.card {p : X × X // P p.1 p.2} := by
  let f : MulAut X → {p : X × X // P p.1 p.2} := fun α => ⟨(α a, α b), hP α a b hPab⟩
  refine Nat.card_le_card_of_injective f fun α β hαβ => ?_
  have h1 : α a = β a := congrArg (fun q => q.1.1) hαβ
  have h2 : α b = β b := congrArg (fun q => q.1.2) hαβ
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ Subgroup.closure ({a, b} : Set X) := by
    rw [hab]
    exact Subgroup.mem_top x
  exact MonoidHom.eqOn_closure (f := α.toMonoidHom) (g := β.toMonoidHom) (s := {a, b})
    (by
      rintro z (rfl | rfl)
      · exact h1
      · exact h2) hx

theorem rep_pairLet {x y xi yi : Table} {xg yg : Perm (Fin deg)} (hx : Rep deg x xg)
    (hxi : Rep deg xi xg⁻¹) (hy : Rep deg y yg) (hyi : Rep deg yi yg⁻¹) (l : ℤ) :
    Rep deg (pairLet x y xi yi l) (pairG xg yg l) := by
  unfold pairLet pairG
  split_ifs <;> assumption

theorem relTest_iff {x y : Table} {xg yg : Perm (Fin deg)} (hx : Rep deg x xg)
    (hy : Rep deg y yg) : relTest x y = true ↔ RelPair xg yg := by
  have hxo := invOK_invT_of_rep deg_lt hx
  have hyo := invOK_invT_of_rep deg_lt hy
  have hxi : Rep deg (invT deg x) xg⁻¹ := hx.inv_of_invOK hxo
  have hyi : Rep deg (invT deg y) yg⁻¹ := hy.inv_of_invOK hyo
  have hw : ∀ w : List ℤ, List.Forall₂ (Rep deg)
      (w.map (pairLet x y (invT deg x) (invT deg y))) (w.map (pairG xg yg)) := fun w => by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun l _ => rep_pairLet hx hxi hy hyi l
  have hpow : ∀ w : List ℤ,
      powFixW deg (w.map (pairLet x y (invT deg x) (invT deg y))) 1 = true ↔
        wordG (pairG xg yg) w = 1 := fun w => by
    rw [powFixW_iff perm_faithful (hw w) 1, pow_one]
    rfl
  simp only [relTest, RelPair, hxo, hyo, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw' => (hpow w).1 (h1 w hw'), fun w hw' hw1 => ?_⟩
    have := h2 w hw'
    rw [(hpow w).2 hw1] at this
    exact Bool.noConfusion this
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw' => (hpow w).2 (h1 w hw'), fun w hw' => ?_⟩
    cases hb : powFixW deg (w.map (pairLet x y (invT deg x) (invT deg y))) 1
    · rfl
    · exact absurd ((hpow w).1 hb) (h2 w hw')


theorem closure_pair_subtype_eq_top {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (hab : Subgroup.closure ({a, b} : Set G) = H) (ha : a ∈ H) (hb : b ∈ H) :
    Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set H) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  have h1 : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [MonoidHom.map_closure, Set.image_pair, h1]
  exact hab

end CFSG.Sporadic.Recognition.LyonsSims.Ly1080
