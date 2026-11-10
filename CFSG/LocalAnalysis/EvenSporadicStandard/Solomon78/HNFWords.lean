module

public import CFSG.Sporadic.Schreier.ONPermArr
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {H : Type*} [Group H]

@[expose] def letterVal (gs : ℕ → H) (l : ℤ) : H :=
  if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹

@[expose] def wordProd (gs : ℕ → H) (w : List ℤ) : H := (w.map (letterVal gs)).prod

@[simp] theorem wordProd_nil (gs : ℕ → H) : wordProd gs [] = 1 := rfl

@[simp] theorem wordProd_cons (gs : ℕ → H) (l : ℤ) (w : List ℤ) :
    wordProd gs (l :: w) = letterVal gs l * wordProd gs w := by
  simp [wordProd]

theorem wordProd_append (gs : ℕ → H) (u v : List ℤ) :
    wordProd gs (u ++ v) = wordProd gs u * wordProd gs v := by
  simp [wordProd]

@[expose] def conjBy (x u : H) : H := x * u * x⁻¹

theorem conjBy_def (x u : H) : conjBy x u = x * u * x⁻¹ := rfl

theorem letterVal_neg (gs : ℕ → H) {l : ℤ} (hl : l ≠ 0) :
    letterVal gs (-l) = (letterVal gs l)⁻¹ := by
  unfold letterVal
  by_cases h : 0 < l
  · have h' : ¬ 0 < -l := by omega
    rw [ite_eq_right h', ite_eq_left h]
    simp
  · have h' : 0 < -l := by omega
    rw [ite_eq_left h', ite_eq_right h]
    simp


@[expose] def invWord (w : List ℤ) : List ℤ := w.reverse.map (fun l => -l)

theorem wordProd_invWord (gs : ℕ → H) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → wordProd gs (invWord w) = (wordProd gs w)⁻¹
  | [], _ => by simp [invWord]
  | l :: w, hw => by
    have hl : l ≠ 0 := hw l (List.mem_cons_self)
    have ih := wordProd_invWord gs w (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have e : invWord (l :: w) = invWord w ++ [-l] := by simp [invWord]
    rw [e, wordProd_append, ih]
    simp [letterVal_neg gs hl]


end CFSG.EvenSporadicStandard.Solomon78
