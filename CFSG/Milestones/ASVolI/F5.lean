module

public import CFSG.Quasithin.Background.SimsF5Asm7

public section

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF


@[expose] def Q8SqK : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.zpowers (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem Q8SqK_le_center : Q8SqK ≤ Subgroup.center (QuaternionGroup 2 × QuaternionGroup 2) := by
  rw [Q8SqK, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  rintro ⟨g1, g2⟩
  have h : ∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by decide
  exact Prod.ext (h g1) (h g2)

instance Q8SqK.normal : Q8SqK.Normal := Subgroup.normal_of_le_center Q8SqK_le_center


end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5


section F52


end F52

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Abstract


end Abstract


end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


section F53


end F53


section F54


end F54


section F55


end F55


section F56


end F56

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


section AbstractGraph


end AbstractGraph

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section AbstractUS


end AbstractUS

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5 CFSG.Quasithin.Asc94
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


section F57


end F57


namespace ChF5S

open CFSG.ASVolI.ChF5 Matrix
open scoped commutatorElement
open scoped Pointwise


open scoped commutatorElement
open scoped Pointwise


end ChF5S


end CFSG.ASVolI
