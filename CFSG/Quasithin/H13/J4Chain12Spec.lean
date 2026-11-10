module

public import Certificates.Data.CFSGNative.H13.J4Chain12
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Sporadic.J4.Setup

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Sporadic.J4 (wordProd wordProd_mem)
open scoped Matrix


@[expose] def ColV12 : Type := Fin 12 → ZMod 2

@[expose] def toColV12 (x : Fin 12 → ZMod 2) : ColV12 := x

@[expose] def ofColV12 (x : ColV12) : Fin 12 → ZMod 2 := x

instance colV12Action : MulAction (GL (Fin 12) (ZMod 2)) ColV12 where
  smul g x := toColV12 ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ ofColV12 x)
  one_smul x := by
    show toColV12 (((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
      ofColV12 x) = x
    rw [Units.val_one, Matrix.one_mulVec]; rfl
  mul_smul g h x := by
    show toColV12 (((g * h : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
      ofColV12 x) = toColV12 ((g : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        ofColV12 (toColV12 ((h : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ ofColV12 x)))
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]; rfl

instance : Finite ColV12 := inferInstanceAs (Finite (Fin 12 → ZMod 2))


@[expose] def PrRep12 (g : GL (Fin 12) (ZMod 2)) (x : Pr12) : Prop :=
  rowsMatrix 12 x.1 = (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∧
    rowsMatrix 12 x.2 = ((g⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))

theorem PrRep12.one : PrRep12 1 pr12One := by
  refine ⟨?_, ?_⟩ <;> simp only [pr12One, rowsMatrix_idRows, inv_one, Units.val_one]

theorem PrRep12.mul {g h : GL (Fin 12) (ZMod 2)} {x y : Pr12} (hg : PrRep12 g x)
    (hh : PrRep12 h y) : PrRep12 (g * h) (pr12Mul x y) := by
  refine ⟨?_, ?_⟩
  · simp only [pr12Mul, rowsMatrix_mulRows, hg.1, hh.1, Units.val_mul]
  · simp only [pr12Mul, rowsMatrix_mulRows, hg.2, hh.2, _root_.mul_inv_rev, Units.val_mul]

theorem PrRep12.inv {g : GL (Fin 12) (ZMod 2)} {x : Pr12} (hg : PrRep12 g x) :
    PrRep12 g⁻¹ (pr12Inv x) :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem PrRep12.eq_one {g : GL (Fin 12) (ZMod 2)} (hg : PrRep12 g pr12One) : g = 1 := by
  apply Units.ext
  rw [← hg.1, Units.val_one]
  exact rowsMatrix_idRows 12

@[expose] def FamRep12 (gs : ℕ → GL (Fin 12) (ZMod 2)) (xs : Array Pr12) : Prop :=
  ∀ i, PrRep12 (gs i) (xs[i]?.getD pr12One)

theorem FamRep12.word {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12} (h : FamRep12 gs xs)
    (w : List ℤ) : PrRep12 (wordProd gs w) (pr12Word xs w) := by
  unfold wordProd pr12Word
  suffices ∀ (acc : Pr12) (g : GL (Fin 12) (ZMod 2)), PrRep12 g acc →
      PrRep12 (g * (w.map fun l => if 0 < l then gs (l.toNat - 1)
          else (gs ((-l).toNat - 1))⁻¹).prod)
        (w.foldl (fun acc l => pr12Mul acc (pr12Letter xs l)) acc) by
    simpa using this pr12One 1 PrRep12.one
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ih _ _ (hg.mul ?_)
    unfold pr12Letter
    split_ifs
    · exact h _
    · exact (h _).inv

theorem FamRep12.eq_one {gs : ℕ → GL (Fin 12) (ZMod 2)} {xs : Array Pr12} (h : FamRep12 gs xs)
    {i : ℕ} (hi : xs.size ≤ i) : gs i = 1 := by
  have := h i
  rw [Array.getElem?_eq_none_iff.2 hi, Option.getD_none] at this
  exact this.eq_one


end CFSG.Quasithin.H13.J4
