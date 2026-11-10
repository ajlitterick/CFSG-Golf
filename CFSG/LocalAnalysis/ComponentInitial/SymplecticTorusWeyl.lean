module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] [Finite k] [Finite E]
  {π : E →* StatedSp r k}

noncomputable def torusEquiv : (Fin r → kˣ) ≃* torus r k :=
  MonoidHom.ofInjective (torusHom_injective (r := r) (k := k))

omit [Finite k] in
theorem coe_torusEquiv (t : Fin r → kˣ) :
    ((torusEquiv t : torus r k) : StatedSp r k) = torusHom t :=
  MonoidHom.ofInjective_apply _

noncomputable def liftTorusEquiv (hS : Hyp π) : (Fin r → kˣ) ≃* liftTorus π :=
  (MonoidHom.ofInjective (thetaHom_injective hS)).trans (MulEquiv.subgroupCongr (range_thetaHom hS))


noncomputable def thetaEquiv (hS : Hyp π) : torus r k ≃* liftTorus π :=
  (torusEquiv (r := r) (k := k)).symm.trans (liftTorusEquiv hS)


theorem sLift_sq_mem (hS : Hyp π) (i : Fin r) : sLift π i ^ 2 ∈ liftTorus π := by
  rw [sq]
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho_mul_self]
    exact hLiftRho_mem hS _ _
  · rw [sLift_of_not_lt h, vLift_mul_self]
    exact hLift_mem _ _


end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
