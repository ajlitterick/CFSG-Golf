module

public import Certificates.Data.Kernel.L5.EngRec
public import CFSG.Certificates.Kernel.L5.EngWit

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2

variable {n : Nat} [Group (Idx n)]

theorem getD_toArray_map_elemsI (f : Idx n → Nat) (a : Idx n) :
    ((elemsI n).map f).toArray.getD a.v 0 = f a := by
  have ha : a.v < (List.finRange n).length := by
    rw [List.length_finRange]
    exact Idx.v_lt a
  have h1 : (List.finRange n)[a.v]? = some a.i := by
    rw [List.getElem?_eq_getElem ha, Option.some.injEq]
    exact Fin.ext (by simp [Idx.v])
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, elemsI,
    List.getElem?_map, h1]
  rfl

theorem getD_map_mkHomCtx {reps : List (Idx n)} {k : Nat} (hk : k < reps.length) :
    (reps.map mkHomCtx).getD k default = mkHomCtx (reps.getD k 1) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some]

theorem ctxOK_mkHomCtx (t : Idx n) : ctxOK t (mkHomCtx t) = ctxOK t (ctxR (mkHomCtx t).gens) :=
  rfl


end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
