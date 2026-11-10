
module

public import CFSG.Monster.B.TwoA.Base.GeomObjBase
public import CFSG.Monster.B.TwoA.Base.PetersenData

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module Relation

open scoped IsMulCommutative

attribute [local instance] parAction


@[expose] def RAdj (R : Set ParGeom) (x y : ParGeom) : Prop := x ∈ R ∧ y ∈ R ∧ parInc x y

abbrev RReach (R : Set ParGeom) : ParGeom → ParGeom → Prop := ReflTransGen (RAdj R)

theorem RAdj.symm {R : Set ParGeom} {x y : ParGeom} (h : RAdj R x y) : RAdj R y x :=
  ⟨h.2.1, h.1, parInc_symm h.2.2⟩

theorem RReach.symm {R : Set ParGeom} {x y : ParGeom} (h : RReach R x y) : RReach R y x := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head hbc.symm ih

theorem RAdj.reach {R : Set ParGeom} {x y : ParGeom} (hx : x ∈ R) (hy : y ∈ R)
    (h : parInc x y) : RReach R x y := ReflTransGen.single ⟨hx, hy, h⟩


theorem RReach.smul {R : Set ParGeom} (g : Shat) {x y : ParGeom} (h : RReach R x y) :
    RReach ((g • ·) '' R) (g • x) (g • y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ⟨⟨_, hbc.1, rfl⟩, ⟨_, hbc.2.1, rfl⟩, (parInc_smul_iff g _ _).2 hbc.2.2⟩


theorem RReach.smul_of {R : Set ParGeom} {h : Shat} (hR : ∀ x ∈ R, h • x ∈ R) {u v : ParGeom}
    (huv : RReach R u v) : RReach R (h • u) (h • v) := by
  induction huv with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hR _ hbc.1, hR _ hbc.2.1, (parInc_smul_iff h _ _).2 hbc.2.2⟩


end CFSG.Monster.B.TwoA
