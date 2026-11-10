module

public import CFSG.Milestones.ASVolI.B4Natural
public import CFSG.Quasithin.Background.SmithB49
public import CFSG.Quasithin.Background.SmithB51LnRealB

public section

namespace CFSG.ASVolI

section Offender

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin


end Offender

section FieldTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {K : Type} [Field K]


variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(StatedSL n K) →* ↥G}


end FieldTwo

section QuotNat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π' : ↥(StatedSL n (ZMod 2)) →* ↥G}


end QuotNat

section QuotDual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {V : Type} [CommGroup V] {U : Subgroup V}


variable {G : Subgroup (MulAut V)} {π' : ↥(StatedSL n (ZMod 2)) →* ↥G}


end QuotDual

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent


end Final

end CFSG.ASVolI
