module

public import CFSG.YGroups.Y443.Native.AlignAlg
public import CFSG.YGroups.Y443.Tri.Parabolic2
public import Certificates.Certificate16004
public import Certificates.Certificate6007
public import Certificates.Certificate10093
public import Certificates.Certificate10098
public import Certificates.Certificate10103
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10123
public import Certificates.Certificate10127

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Open

theorem y443RhoM_axL {s : ℕ} (hs : s ≤ 11) : y443RhoM (axL s) = axL (ρL s) := by
  refine Subtype.ext ?_
  rw [y443RhoM_coe, coe_axL, coe_axL, map_mul, y443Rho_gen (show 0 < 12 by norm_num),
    y443Rho_gen (show s < 12 by omega)]
  rfl

theorem y443RhoM_evalM : ∀ l : List ℕ, (∀ c ∈ l, c ≤ 11) →
    y443RhoM (evalM l) = evalM (l.map ρL)
  | [], _ => by simp [evalM]
  | [_], _ => by simp [evalM]
  | a :: b :: l, h => by
    simp only [evalM, List.map_cons, map_mul, map_inv]
    rw [y443RhoM_axL (h a (by simp)), y443RhoM_axL (h b (by simp)),
      y443RhoM_evalM l (fun c hc => h c (by simp [hc]))]


theorem slet_map_ρL_le : ∀ c ∈ slet.map ρL, c ≤ 11 :=
  Certificates.certificate16004.2

theorem y443C'_eq_evalM : y443C' = evalM (slet.map ρL) := by
  show y443RhoM y443C = _
  rw [y443C_eq_evalM, y443RhoM_evalM slet slet_le]

theorem fM_y443C'_eq_evalGL :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = evalGL (slet.map ρL) := by
  rw [y443C'_eq_evalM, fM_evalM _ slet_map_ρL_le]


end CFSG.YGroups.Y443
