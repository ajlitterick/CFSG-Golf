module

public import Certificates.Data.CFSGNative.H13.J4Chain
public import CFSG.Sporadic.J4.Setup
public import CFSG.Perm.VectorChain

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open scoped Matrix

@[expose] def RowV : Type := Fin 112 → ZMod 2

@[expose] def toRowV (w : Fin 112 → ZMod 2) : RowV := w

@[expose] def ofRowV (w : RowV) : Fin 112 → ZMod 2 := w

instance rowVAction : MulAction (GL (Fin 112) (ZMod 2)) RowV where
  smul g w := toRowV (ofRowV w ᵥ* (((g⁻¹ : GL (Fin 112) (ZMod 2))) :
    Matrix (Fin 112) (Fin 112) (ZMod 2)))
  one_smul w := by
    show toRowV (ofRowV w ᵥ* ((((1 : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) = w
    rw [inv_one, Units.val_one, Matrix.vecMul_one]; rfl
  mul_smul g h w := by
    show toRowV (ofRowV w ᵥ* ((((g * h)⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) =
      toRowV (ofRowV (toRowV (ofRowV w ᵥ* (((h⁻¹ : GL (Fin 112) (ZMod 2))) :
        Matrix (Fin 112) (Fin 112) (ZMod 2)))) ᵥ* (((g⁻¹ : GL (Fin 112) (ZMod 2))) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)))
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]; rfl


@[expose] def PrRep (g : GL (Fin 112) (ZMod 2)) (x : Pr) : Prop :=
  rowsMatrix x.1 = (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) ∧
    rowsMatrix x.2 = ((g⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))

theorem PrRep.one : PrRep 1 prOne := by
  refine ⟨?_, ?_⟩ <;> simp only [prOne, rowsMatrix_idRows, inv_one, Units.val_one]

theorem PrRep.mul {g h : GL (Fin 112) (ZMod 2)} {x y : Pr} (hg : PrRep g x) (hh : PrRep h y) :
    PrRep (g * h) (prMul x y) := by
  refine ⟨?_, ?_⟩
  · simp only [prMul, rowsMatrix_mulRows, hg.1, hh.1, Units.val_mul]
  · simp only [prMul, rowsMatrix_mulRows, hg.2, hh.2, _root_.mul_inv_rev, Units.val_mul]

theorem PrRep.inv {g : GL (Fin 112) (ZMod 2)} {x : Pr} (hg : PrRep g x) :
    PrRep g⁻¹ (prInv x) :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem PrRep.pow {g : GL (Fin 112) (ZMod 2)} {x : Pr} (hg : PrRep g x) (e : ℕ) :
    PrRep (g ^ e) (prPow x e) := by
  induction e with
  | zero => rw [pow_zero]; exact PrRep.one
  | succ e ih => rw [pow_succ]; exact ih.mul hg

theorem PrRep.eq_one {g : GL (Fin 112) (ZMod 2)} (hg : PrRep g prOne) : g = 1 := by
  apply Units.ext
  rw [← hg.1, Units.val_one]
  exact rowsMatrix_idRows

@[expose] def FamRep (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) : Prop :=
  ∀ i, PrRep (gs i) (xs[i]?.getD prOne)

theorem FamRep.letter {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    (l : ℤ) : PrRep (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹)
      (prLetter xs l) := by
  unfold prLetter
  split_ifs
  · exact h _
  · exact (h _).inv

theorem FamRep.word {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    (w : List ℤ) : PrRep (wordProd gs w) (prWord xs w) := by
  unfold wordProd prWord
  suffices ∀ (acc : Pr) (g : GL (Fin 112) (ZMod 2)), PrRep g acc →
      PrRep (g * (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod)
        (w.foldl (fun acc l => prMul acc (prLetter xs l)) acc) by
    simpa using this prOne 1 PrRep.one
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hg.mul (h.letter l))

theorem FamRep.eq_one {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} (h : FamRep gs xs)
    {i : ℕ} (hi : xs.size ≤ i) : gs i = 1 := by
  have := h i
  rw [Array.getElem?_eq_none_iff.2 hi, Option.getD_none] at this
  exact this.eq_one

@[expose] def levelGensGL (gs : ℕ → GL (Fin 112) (ZMod 2)) :
    List (List (List ℤ)) → List (ℕ → GL (Fin 112) (ZMod 2))
  | [] => [gs]
  | ws :: rest => gs :: levelGensGL (fun i => wordProd gs (ws.getD i [])) rest


section Level

variable {sg : ℕ → GL (Fin 112) (ZMod 2)} {gens : Array Pr}

@[expose] def pathGL (sg : ℕ → GL (Fin 112) (ZMod 2)) (p : List ℕ) : GL (Fin 112) (ZMod 2) :=
  (p.map sg).prod


end Level

section Chain

variable {gs : ℕ → GL (Fin 112) (ZMod 2)} {xs : Array Pr} {bs : List V2}
  {ws : List (List (List ℤ))}

@[expose] def levelGL (gs : ℕ → GL (Fin 112) (ZMod 2)) (ws : List (List (List ℤ))) (j : ℕ) :
    ℕ → GL (Fin 112) (ZMod 2) :=
  (levelGensGL gs ws).getD j fun _ => 1

@[expose] def trGL (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) (bs : List V2)
    (ws : List (List (List ℤ))) (j k : ℕ) : GL (Fin 112) (ZMod 2) :=
  pathGL (levelGL gs ws j) (mkLevels xs bs ws)[j]!.paths[k]!

@[expose] def levelSet (gs : ℕ → GL (Fin 112) (ZMod 2)) (xs : Array Pr) (bs : List V2)
    (ws : List (List (List ℤ))) (j : ℕ) : Set (GL (Fin 112) (ZMod 2)) :=
  {g | ∃ i < (mkLevels xs bs ws)[j]!.gens.size, levelGL gs ws j i = g}


theorem prod_map_toList {α : Type*} [Inhabited α] (L : Array α) (f : α → ℕ) :
    (L.toList.map f).prod = ∏ j ∈ Finset.range L.size, f L[j]! := by
  rw [Finset.prod_range fun j => f L[j]!, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_ofFn]
    rw [getElem!_pos L n (by simpa using h1)]


end Chain

end CFSG.Quasithin.H13.J4
