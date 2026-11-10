
module

public import CFSG.Monster.Existence.TwoPoint.Fi23S4Base
public import CFSG.Monster.Existence.TwoPoint.GammaExclData

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

@[expose] noncomputable def gxElem (k : ℕ) : MGriess :=
  if k < 10 then fiE k else if k = 10 then gammaZero else if k = 11 then fiAlpha else fiBeta

@[expose] noncomputable def gxW (h : List ℕ) : MGriess := (h.map fun c => fiE (gxSigma c)).prod

@[expose] noncomputable def gxT (j : ℕ) : MGriess :=
  gxW (gxWord j) * gammaZero * (gxW (gxWord j))⁻¹

noncomputable def xHat (j : ℕ) : MGriess :=
  if _h : 0 < j ∧ gxParent j < j then xHat (gxParent j) * gxT j else 1
termination_by j
decreasing_by exact _h.2

@[expose] noncomputable def deltaHat (j : ℕ) : MGriess := xHat j * fiAlpha * (xHat j)⁻¹

@[expose] noncomputable def betaPrime : MGriess := fiAlpha * fiBeta * fiAlpha

theorem xHat_zero : xHat 0 = 1 := by
  rw [xHat, dite_eq_right (by omega)]

theorem xHat_succ {j : ℕ} (h0 : 0 < j) (h23 : j < 23) : xHat j = xHat (gxParent j) * gxT j := by
  rw [xHat, dite_eq_left ⟨h0, gxParent_lt h0 h23⟩]

theorem gxW_eq_prod (h : List ℕ) : gxW h = ((h.map gxSigma).map gxElem).prod := by
  unfold gxW
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  show fiE (gxSigma c) = gxElem (gxSigma c)
  unfold gxElem
  rw [ite_eq_left (gxSigma_lt c)]

theorem xHat_one : xHat 1 = gammaZero := by
  rw [xHat_succ (by omega) (by omega)]
  have e0 : gxParent 1 = 0 := by decide
  have e1 : gxWord 1 = [] := by decide
  rw [e0, xHat_zero, gxT, e1]
  simp [gxW]

@[expose] def gxElemWord (k : ℕ) : List Native.Gen :=
  if k < 10 then fiWU[k]! else if k = 10 then s4WGamma else if k = 11 then fiWAlpha else fiWBeta

theorem fiMkW_gxElemWord (k : ℕ) : fiMkW (gxElemWord k) = gxElem k := by
  unfold gxElemWord gxElem
  split_ifs <;> rfl

@[expose] def gxProdWord (L : List ℕ) : List Native.Gen := (L.reverse.map gxElemWord).flatten

theorem gxProdWord_cons (k : ℕ) (L : List ℕ) :
    gxProdWord (k :: L) = gxProdWord L ++ gxElemWord k := by
  simp [gxProdWord, List.reverse_cons]

theorem fiMkW_gxProdWord (L : List ℕ) : fiMkW (gxProdWord L) = (L.map gxElem).prod := by
  induction L with
  | nil => simpa [gxProdWord] using fiMkW_nil
  | cons k L ih =>
    rw [gxProdWord_cons, fiMkW_append, fiMkW_gxElemWord, ih, List.map_cons, List.prod_cons]


end CFSG.Monster.Existence
