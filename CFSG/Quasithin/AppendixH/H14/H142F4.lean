module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH


@[expose] def frobGF4 : GF4 ≃+* GF4 where
  toFun c := c * c
  invFun c := c * c
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
  map_add' := by decide


end CFSG.Quasithin.AppendixH.H14
