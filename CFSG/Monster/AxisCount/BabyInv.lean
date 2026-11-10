module

public import CFSG.Monster.AxisCount.BabyIdent
public import CFSG.Monster.AxisCount.BabyShort

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
  Matrix

@[expose] noncomputable def xStarCoord (v : SpaceB) : ℚ :=
  bform v ((0, Xlift rStar, 0) : SpaceB)

theorem xStarCoord_apply_of_mem_Jstar {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) (v : SpaceB) :
    xStarCoord (g v) = xStarCoord v := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 (Jstar_le_Gvis hg)
  have h1 := conjQ_rStar_of_mem_Jstar hg
  have h2 : thetaEquiv p ((0, Xlift rStar, 0) : SpaceB) = (0, Xlift rStar, 0) := by
    show theta p _ = _
    rw [theta_Xlift, h1]
  calc xStarCoord (thetaEquiv p v)
      = bform (thetaEquiv p v) (thetaEquiv p ((0, Xlift rStar, 0) : SpaceB)) := by
        rw [h2]; rfl
    _ = bform v ((0, Xlift rStar, 0) : SpaceB) := bform_theta p _ _

theorem xStarCoord_smul_of_mem_Jstar {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) (v : SpaceB) :
    xStarCoord (g • v) = xStarCoord v :=
  xStarCoord_apply_of_mem_Jstar hg v

theorem Xlift_rStar_eq : Xlift rStar = Pi.single ⟨coordOf rStar, isShortCoord_rStar⟩ 1 := by
  have hc0 : centralCoord rStar = 0 := centralCoord_rMinus 0 1
  rw [Xlift_eq isShortCoord_rStar, hc0]
  simp [sgn]

theorem xStarCoord_interp (d : Native.DVec) :
    xStarCoord (interp d) = (d.D.getD 300 0 : ℚ) / 2 ^ d.e := by
  have hpos : posOf (⟨coordOf rStar, isShortCoord_rStar⟩ : ShortIdx) = 0 :=
    (HS.posOf_eq_zero_iff _).2 rfl
  rw [xStarCoord, bform_apply]
  simp only [Submodule.coe_zero, trace_zero, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero, Xlift_rStar_eq, Pi.single_apply, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  show interpX d _ = _
  rw [interpX, hpos]

@[expose] def babyTrNum : Fin 10 → ℕ := ![4, 4, 8, 8, 104, 232, 192, 3976, 3080, 3136]

@[expose] def babyTrExp : Fin 10 → ℕ := ![0, 0, 2, 2, 4, 5, 5, 7, 7, 7]

@[expose] def babyXNum : Fin 10 → ℕ := ![2, 0, 1, 0, 1, 1, 1, 13, 5, 3]

@[expose] def babyXExp : Fin 10 → ℕ := ![0, 0, 2, 0, 4, 5, 4, 7, 7, 6]


@[expose] def invOK : Bool := vtabOK &&
  (List.finRange 10).all fun j =>
    HS.trA2N vtab[(j : ℕ)]! * 4 ^ babyTrExp j == (babyTrNum j : ℤ) * 4 ^ vtab[(j : ℕ)]!.e &&
      vtab[(j : ℕ)]!.D.getD 300 0 * 2 ^ babyXExp j == (babyXNum j : ℤ) * 2 ^ vtab[(j : ℕ)]!.e


end CFSG.Monster.AxisCount.Baby
