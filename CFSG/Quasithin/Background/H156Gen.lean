module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def maskHom (n k : ℕ) (cs : List ℕ) : Wn n →* Wn k where
  toFun v := Multiplicative.ofAdd (∑ j : Fin n, Multiplicative.toAdd v j • bvec k (cs.getD j 0))
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, add_smul, Finset.sum_add_distrib, ofAdd_add]

theorem maskHom_toW {n k : ℕ} {cs : List ℕ} (hcs : cs.length = n) (m : ℕ) :
    maskHom n k cs (toW n m) = toW k (actM cs m) := by
  unfold maskHom toW
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  congr 1
  rw [bvec_actM k cs m, hcs, ← Fin.sum_univ_eq_sum_range
    (fun j => if m.testBit j then bvec k (cs.getD j 0) else 0) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

@[expose] def colMat (n : ℕ) (cs : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => bvec n (cs.getD j 0) i

theorem mulVec_colMat {n : ℕ} {cs : List ℕ} (hcs : cs.length = n) (m : ℕ) :
    (colMat n cs).mulVec (bvec n m) = bvec n (actM cs m) := by
  funext i
  rw [bvec_actM n cs m, hcs, Finset.sum_apply, ← Fin.sum_univ_eq_sum_range
    (fun j => (if m.testBit j then bvec n (cs.getD j 0) else 0) i) n]
  simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply n m j]
  by_cases h : m.testBit j = true
  · simp [h]
  · simp [h]

@[expose] def mkGL (n : ℕ) (cs ics : List ℕ) (h1 : colMat n cs * colMat n ics = 1)
    (h2 : colMat n ics * colMat n cs = 1) : GL (Fin n) (ZMod 2) :=
  ⟨colMat n cs, colMat n ics, h1, h2⟩

theorem natHom_mkGL {n : ℕ} {cs ics : List ℕ} (hcs : cs.length = n)
    (h1 : colMat n cs * colMat n ics = 1) (h2 : colMat n ics * colMat n cs = 1) (m : ℕ) :
    natHom n (ZMod 2) (mkGL n cs ics h1 h2) (toW n m) = toW n (actM cs m) := by
  show Multiplicative.ofAdd ((colMat n cs).mulVec (bvec n m)) = _
  rw [mulVec_colMat hcs]
  rfl

@[expose] def invTGL (n : ℕ) : GL (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2) where
  toFun a := ⟨((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
    ((a : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ, by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp [Matrix.transpose_mul]


theorem natHom_injective (n : ℕ) : Function.Injective (natHom n (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro a h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun φ : MulAut (Multiplicative (Fin n → ZMod 2)) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))) i) h
  simp only [natHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    toAdd_ofAdd, MulAut.one_apply, Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

@[expose] def ix (i : Fin 3) (j : Fin 2) : Fin 6 := ⟨i + 3 * j, by omega⟩

abbrev Mat32 : Type := Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))

@[expose] def matOfW : Wn 6 →* Mat32 where
  toFun v := Multiplicative.ofAdd (Matrix.of fun i j => Multiplicative.toAdd v (ix i j))
  map_one' := by
    ext i j
    simp
  map_mul' v w := by
    ext i j
    simp


section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem congrHom_apply_eg (eg : V ≃* W) (g : MulAut V) (v : V) :
    congrHom eg g (eg v) = eg (g v) := by
  rw [congrHom_apply, MulEquiv.symm_apply_apply]


end Transport

end CFSG.Quasithin.H156
