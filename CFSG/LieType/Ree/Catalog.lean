module

public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Ree.Intertwiner

public section

namespace CFSG.LieType.Ree.ReeTag

open CFSG.Blueprint


theorem tag_F4 : F4.tag = .F4 :=
  rfl


theorem relationExponent_eq (t : ReeTag) (a : ℕ) (i : Fin t.tag.rank) :
    (if i ∈ t.longSet then t.prime ^ a else t.prime ^ (a + 1)) = t.prime ^ a * t.exponent i := by
  unfold exponent
  split_ifs <;> ring

end CFSG.LieType.Ree.ReeTag
