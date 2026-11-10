module

public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.AxisCount.CoverLetters
public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public meta import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public meta import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public meta import CFSG.Monster.Existence.TwoPoint.HNRigid
public meta import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs
public import Certificates.Certificate6091
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public meta import CFSG.Open.MonsterY443Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.AxisCount


theorem trace_order_of_conj {X K M : SpaceB ≃ₗ[ℚ] SpaceB} (hKX : K * X = M * K)
    (hM3 : M * M * M = 1) {T : ℚ}
    (hT : LinearMap.trace ℚ SpaceB (M : SpaceB →ₗ[ℚ] SpaceB) = T) (hT' : T ≠ 196884) :
    LinearMap.trace ℚ SpaceB (X : SpaceB →ₗ[ℚ] SpaceB) = T ∧ X * X * X = 1 ∧ X ≠ 1 := by
  have hX : K * X * K⁻¹ = M := by rw [hKX, mul_inv_cancel_right]
  have hX' : X = K⁻¹ * M * K := by
    rw [← hX]; group
  refine ⟨?_, ?_, ?_⟩
  · rw [← hT, ← hX]
    exact (CFSG.Monster.B.trace_conj K X).symm
  · rw [hX']
    calc K⁻¹ * M * K * (K⁻¹ * M * K) * (K⁻¹ * M * K) = K⁻¹ * (M * M * M) * K := by group
      _ = 1 := by rw [hM3]; group
  · intro h1
    rw [h1] at hX
    have h2 : M = 1 := by rw [← hX]; group
    rw [h2] at hT
    have h3 : LinearMap.trace ℚ SpaceB
        (((1 : SpaceB ≃ₗ[ℚ] SpaceB)) : SpaceB →ₗ[ℚ] SpaceB) = 196884 := by
      show LinearMap.trace ℚ SpaceB LinearMap.id = _
      rw [LinearMap.trace_id, finrank_B]
      rfl
    rw [h3] at hT
    exact hT' hT.symm


theorem valid_permMonoA : Native.permValid permMonoA = true :=
  Certificates.certificate6091.1

theorem check_conjA :
    wordLin (wordThreeA ++ wordKA) = wordLin (wordKA ++ wordMonoA) :=
  Certificates.certificate6091.2.1

theorem check_cubeA :
    wordLin (wordMonoA ++ wordMonoA ++ wordMonoA) = 1 :=
  Certificates.certificate6091.2.2.1

theorem check_traceA : permTraceCheck permMonoA 783 = true :=
  Certificates.certificate6091.2.2.2.1

theorem trace_wordMonoA :
    LinearMap.trace ℚ SpaceB
      ((wordLin wordMonoA : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 783 := by
  have h := trace_wordLin_perm valid_permMonoA check_traceA
  exact_mod_cast h

theorem conj_relA :
    wordLin wordKA * wordLin wordThreeA = wordLin wordMonoA * wordLin wordKA := by
  have h := check_conjA
  rwa [wordLin_append, wordLin_append] at h

theorem cube_monoA :
    wordLin wordMonoA * wordLin wordMonoA * wordLin wordMonoA = 1 := by
  have h := check_cubeA
  simpa [wordLin_append, mul_assoc] using h

theorem threeDataA :
    LinearMap.trace ℚ SpaceB (wordLin wordThreeA : SpaceB →ₗ[ℚ] SpaceB) = 783 ∧
      wordLin wordThreeA * wordLin wordThreeA * wordLin wordThreeA = 1 ∧
      wordLin wordThreeA ≠ 1 :=
  trace_order_of_conj conj_relA cube_monoA trace_wordMonoA (by norm_num)

theorem trace_threeARep :
    LinearMap.trace ℚ SpaceB ((threeARep.val : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 783 :=
  (threeDataA).1


theorem valid_permMonoC : Native.permValid permMonoC = true :=
  Certificates.certificate6091.2.2.2.2.1

theorem check_conjC :
    wordLin (wordThreeC ++ wordKC) = wordLin (wordKC ++ wordMonoC) :=
  Certificates.certificate6091.2.2.2.2.2.1

theorem check_cubeC :
    wordLin (wordMonoC ++ wordMonoC ++ wordMonoC) = 1 :=
  Certificates.certificate6091.2.2.2.2.2.2.1

theorem check_traceC : permTraceCheck permMonoC 0 = true :=
  Certificates.certificate6091.2.2.2.2.2.2.2

theorem trace_wordMonoC :
    LinearMap.trace ℚ SpaceB
      ((wordLin wordMonoC : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 0 := by
  have h := trace_wordLin_perm valid_permMonoC check_traceC
  exact_mod_cast h

theorem conj_relC :
    wordLin wordKC * wordLin wordThreeC = wordLin wordMonoC * wordLin wordKC := by
  have h := check_conjC
  rwa [wordLin_append, wordLin_append] at h

theorem cube_monoC :
    wordLin wordMonoC * wordLin wordMonoC * wordLin wordMonoC = 1 := by
  have h := check_cubeC
  simpa [wordLin_append, mul_assoc] using h

theorem threeDataC :
    LinearMap.trace ℚ SpaceB (wordLin wordThreeC : SpaceB →ₗ[ℚ] SpaceB) = 0 ∧
      wordLin wordThreeC * wordLin wordThreeC * wordLin wordThreeC = 1 ∧
      wordLin wordThreeC ≠ 1 :=
  trace_order_of_conj conj_relC cube_monoC trace_wordMonoC (by norm_num)

theorem trace_threeCRep :
    LinearMap.trace ℚ SpaceB ((threeCRep.val : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 0 :=
  (threeDataC).1


end CFSG.Monster.Existence
