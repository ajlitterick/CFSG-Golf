
module

public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.RowInputs

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Matrix Pointwise

@[expose] def RowV : Type := Fin 248 → ZMod 2

instance : AddCommGroup RowV := inferInstanceAs (AddCommGroup (Fin 248 → ZMod 2))

instance : Module (ZMod 2) RowV := inferInstanceAs (Module (ZMod 2) (Fin 248 → ZMod 2))

instance : DecidableEq RowV := inferInstanceAs (DecidableEq (Fin 248 → ZMod 2))

instance : Fintype RowV := inferInstanceAs (Fintype (Fin 248 → ZMod 2))

@[expose] def toRow (v : Fin 248 → ZMod 2) : RowV := v

@[expose] def ofRow (v : RowV) : Fin 248 → ZMod 2 := v

@[simp] theorem ofRow_toRow (v : Fin 248 → ZMod 2) : ofRow (toRow v) = v := rfl

@[simp] theorem toRow_ofRow (v : RowV) : toRow (ofRow v) = v := rfl

theorem toRow_add (u v : Fin 248 → ZMod 2) : toRow (u + v) = toRow u + toRow v := rfl


theorem span_pair_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (u v : M) :
    (Submodule.span (ZMod 2) {u, v} : Set M) = {0, u, v, u + v} := by
  ext w
  simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  constructor
  · rintro ⟨s, t, rfl⟩
    rcases hz s with rfl | rfl <;> rcases hz t with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩


@[expose] def rowPlane (k : Key) : Set RowV :=
  {0, toRow k.u.toVec, toRow k.v.toVec, toRow k.u.toVec + toRow k.v.toVec}

theorem rowPlane_eq_image (k : Key) : rowPlane k = toRow '' keyPlane k := by
  simp only [rowPlane, keyPlane, Set.image_insert_eq, Set.image_singleton]
  rfl


theorem rowPlane_canon (p q : V4) :
    rowPlane (canon p q) = {0, toRow p.toVec, toRow q.toVec, toRow p.toVec + toRow q.toVec} := by
  rw [rowPlane_eq_image, keyPlane_canon]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem rowPlane_eq_span (k : Key) :
    rowPlane k = (Submodule.span (ZMod 2) {toRow k.u.toVec, toRow k.v.toVec} : Set RowV) := by
  rw [span_pair_eq]
  rfl


theorem frApply_frTable_vecMul (R : Array V4) (v : V4) :
    (frApply (frTable R) v).toVec = Matrix.vecMul v.toVec (rowsMatrix R) := by
  rw [frApply_frTable_toVec]
  funext i
  simp only [Matrix.vecMul, dotProduct, rowsMatrix_apply]

noncomputable abbrev formFInv : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix formInvRows

@[expose] noncomputable def psi (u : V) : RowV := toRow (formF *ᵥ u)


theorem psi_zero : psi 0 = 0 := by
  simp only [psi, Matrix.mulVec_zero]
  rfl

@[expose] def rowKeyOf (k : Key) : Key := imageKey (frTable (transposeRows fcRows)) k

theorem rowPlane_rowKeyOf (k : Key) : rowPlane (rowKeyOf k) = psi '' keyPlane k := by
  rw [rowPlane_eq_image, rowKeyOf, keyPlane_imageKey, Set.image_image]
  rfl

end CFSG.Sporadic.ThSchreier
