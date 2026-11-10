
module

public import CFSG.Monster.B.TwoA.Base.SevenPairCBase

public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import Certificates.Certificate3064

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem glCert2_ok :
    natCertOK actW2 2 (fun m => decide (m < 16)) (codeMat 2 1) glCert2 = true :=
  Certificates.certificate3064.1

theorem glCert3_ok :
    natCertOK actW3 5 (fun m => decide (m < 512)) (codeMat 3 1) glCert3 = true :=
  Certificates.certificate3064.2.1

theorem glCert2_size : glCert2.pts.size = 6 :=
  Certificates.certificate3064.2.2.1

theorem glCert3_size : glCert3.pts.size = 168 :=
  Certificates.certificate3064.2.2.2

theorem closure_unitW2 : Subgroup.closure (unitW2 '' {k | k < 2}) = ⊤
    := by
  have hact : ∀ k < 2, ∀ a, (fun m => decide (m < 16)) a = true →
      decMat 2 (actW2 k a) = unitW2 k • decMat 2 a := by
    intro k hk a _
    rw [actW2, decMat_codeMat2, Units.smul_def, coe_unitW2 hk, smul_eq_mul]
  have hinj : ∀ a b, (fun m => decide (m < 16)) a = true → (fun m => decide (m < 16)) b = true →
      decMat 2 a = decMat 2 b → a = b := by
    intro a b ha hb hab
    rw [← codeMat_decMat2 a (of_decide_eq_true ha), ← codeMat_decMat2 b (of_decide_eq_true hb),
      hab]
  have h := ncard_orbit_of_natCertOK glCert2_ok hact hinj
  rw [glCert2_size, decMat_codeMat2] at h
  apply Subgroup.eq_top_of_le_card
  rw [natCard_GL_two]
  have h3 := MulAction.index_stabilizer (Subgroup.closure (unitW2 '' {k | k < 2}))
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
  rw [h] at h3
  have h4 := (MulAction.stabilizer (Subgroup.closure (unitW2 '' {k | k < 2}))
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))).card_mul_index
  rw [h3] at h4
  rw [← h4]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

theorem closure_unitW3 : Subgroup.closure (unitW3 '' {k | k < 5}) = ⊤
    := by
  have hact : ∀ k < 5, ∀ a, (fun m => decide (m < 512)) a = true →
      decMat 3 (actW3 k a) = unitW3 k • decMat 3 a := by
    intro k hk a _
    rw [actW3, decMat_codeMat3, Units.smul_def, coe_unitW3 hk, smul_eq_mul]
  have hinj : ∀ a b, (fun m => decide (m < 512)) a = true →
      (fun m => decide (m < 512)) b = true → decMat 3 a = decMat 3 b → a = b := by
    intro a b ha hb hab
    rw [← codeMat_decMat3 a (of_decide_eq_true ha), ← codeMat_decMat3 b (of_decide_eq_true hb),
      hab]
  have h := ncard_orbit_of_natCertOK glCert3_ok hact hinj
  rw [glCert3_size, decMat_codeMat3] at h
  apply Subgroup.eq_top_of_le_card
  rw [natCard_GL_three']
  have h3 := MulAction.index_stabilizer (Subgroup.closure (unitW3 '' {k | k < 5}))
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [h] at h3
  have h4 := (MulAction.stabilizer (Subgroup.closure (unitW3 '' {k | k < 5}))
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))).card_mul_index
  rw [h3] at h4
  rw [← h4]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

theorem glHom2_surjective : Function.Surjective glHom2 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_unitW2, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨witF2 k, glHom2_witF2 k hk⟩

theorem glHom3_surjective : Function.Surjective glHom3 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_unitW3, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨witF3 k, glHom3_witF3 k hk⟩


end CFSG.Monster.B.TwoA
