module

public import CFSG.Monster.Existence.BabyW3Swap
public import CFSG.Monster.GMS.Facts.TableV

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.Spin CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Census CFSG.Monster.Existence.Census
  CFSG.Monster.GMS


theorem rhoGvis_zQ_comm (g : Gvis) : g * rhoGvis zQ = rhoGvis zQ * g := by
  apply Subtype.ext
  have h := Gvis_conj_xmat g.2
  show (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)
  calc (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat =
      (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
        (g : SpaceB ≃ₗ[ℚ] SpaceB) := by group
    _ = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [h]


@[expose] noncomputable def uW3 :
    MGriess := ⟨yW3, Gmat_le_AutO (Cgen_le y3C.2).1⟩


theorem uW3_mem_cent :
    uW3 ∈ cent tGriess :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext tStar_comm_yW3.symm)

theorem orderOf_uW3 :
    orderOf uW3 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext yW3_mul_self) (fun h => y3C_ne_one
    (Subtype.ext (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h)))

theorem uW3_ne_tGriess :
    uW3 ≠ tGriess := fun h => y3C_ne_tStarC
  (Subtype.ext (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h))

theorem exists_swap_uW3 :
    ∃ g ∈ cent tGriess, g * uW3 * g⁻¹ = tGriess * uW3 := by
  obtain ⟨c₀, hc₀⟩ := y3Bar_census.1
  refine ⟨⟨(c₀ : SpaceB ≃ₗ[ℚ] SpaceB), Gmat_le_AutO (Cgen_le c₀.2).1⟩,
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (commute_tStar_of_mem_Cgen c₀.2)),
    Subtype.ext (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB)) hc₀)⟩


theorem mem_Cgen_of_mem_cent2_uW3
    {v : MGriess} (hv : v ∈ cent2 tGriess uW3) :
    (v : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen := by
  have hvu : (v : SpaceB ≃ₗ[ℚ] SpaceB) * yW3 = yW3 * (v : SpaceB ≃ₗ[ℚ] SpaceB) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv.2)
  have hvt : (v : SpaceB ≃ₗ[ℚ] SpaceB) * tStar = tStar * (v : SpaceB ≃ₗ[ℚ] SpaceB) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv.1)
  have hgA : gW3 ∈ AutO := Gmat_le_AutO gW3_mem_Gmat
  have hw : (⟨gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3,
      mul_mem (mul_mem (inv_mem hgA) v.2) hgA⟩ : MGriess) ∈ cent xGriess := by
    refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    show gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 * xmat =
      xmat * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3)
    calc gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 * xmat =
        gW3⁻¹ * ((v : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3 * xmat * gW3⁻¹)) * gW3 := by group
      _ = gW3⁻¹ * ((gW3 * xmat * gW3⁻¹) * (v : SpaceB ≃ₗ[ℚ] SpaceB)) * gW3 := by
          rw [show gW3 * xmat * gW3⁻¹ = yW3 from rfl, hvu]
      _ = xmat * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3) := by group
  have hwG : gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 ∈ Gvis := by
    rw [← map_cent_xGriess]
    exact ⟨_, hw, rfl⟩
  have hvG : (v : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := by
    have := mul_mem (mul_mem gW3_mem_Gmat (Hmat_le_Gmat hwG)) (inv_mem gW3_mem_Gmat)
    have e : gW3 * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3) * gW3⁻¹ =
        (v : SpaceB ≃ₗ[ℚ] SpaceB) := by group
    rwa [e] at this
  exact AxisCount.HS.centralizer_tStar_le_Cgen _ hvG hvt

theorem natCard_cent2_tGriess_uW3 :
    Nat.card ↥(cent2 tGriess uW3) = tableVOrderU := by
  rw [show tableVOrderU = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 from rfl, ← natCard_centralizer_y3C]
  refine Nat.card_congr
    { toFun := fun v => ⟨⟨(v.1 : SpaceB ≃ₗ[ℚ] SpaceB), mem_Cgen_of_mem_cent2_uW3 v.2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB))
            (Subgroup.mem_centralizer_singleton_iff.1 v.2.2)))⟩
      invFun := fun c => ⟨⟨(c.1 : Cgen).1, Gmat_le_AutO (Cgen_le c.1.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (commute_tStar_of_mem_Cgen c.1.2)),
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB))
            (Subgroup.mem_centralizer_singleton_iff.1 c.2)))⟩
      left_inv := fun v => rfl
      right_inv := fun c => rfl }


end CFSG.Monster.Existence
