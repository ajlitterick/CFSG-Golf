module

public import Certificates.Kernel.BabyMonster.ChainN
public import CFSG.Certificates.Kernel.BabyMonster.ZRk.All
public import CFSG.Certificates.Kernel.BabyMonster.Three.All

public section

namespace CFSG.KC.BM.ZRkGlue

open CFSG.KC.BM CFSG.KC.BM.Fix

theorem zRk_mul : stripMat ZRk.P * (stripMat Three.Z + 1) = stripMat ZRk.Q :=
  stripMat_mul_add_one Three.wf_Z ZRk.wf_P (by bm_stripsx CFSG.KC.BM.ZRk.rk_ 69)

theorem zRk_cert : stripMat ZRk.P * (stripMat Three.Z + 1) = stripMat ZRk.Q ∧
    LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // i.val < 2916} => stripMat ZRk.Q i) ∧
    (∀ i : Fin 4370, 2916 ≤ i.val → stripMat ZRk.Q i = 0) ∧
    LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // 2916 ≤ i.val} => stripMat ZRk.P i) :=
  ⟨zRk_mul, (shapeOK_sound ZRk.wf_Q ZRk.shape).1, (shapeOK_sound ZRk.wf_Q ZRk.shape).2,
    echFrom_sound ZRk.wf_P ZRk.ech⟩

end CFSG.KC.BM.ZRkGlue

end
