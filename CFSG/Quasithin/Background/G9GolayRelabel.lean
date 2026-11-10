module

public import CFSG.Quasithin.Background.G9GolayModels
public import CFSG.Monster.Code.Weights
public import CFSG.Blueprint.SourceBinaryGolayCodeProperties

public section

namespace CFSG.Quasithin.G11


theorem golay_permAct_mul (σ τ : Equiv.Perm (Fin 24)) (w : GolayAmbient) :
    permAct (σ * τ) w = permAct σ (permAct τ w) := by
  funext i
  simp only [permAct, mul_inv_rev, Equiv.Perm.mul_apply]

theorem golay_permAct_one (w : GolayAmbient) : permAct (1 : Equiv.Perm (Fin 24)) w = w := by
  funext i
  simp only [permAct, inv_one, Equiv.Perm.one_apply]

theorem golay_permAct_add (σ : Equiv.Perm (Fin 24)) (v w : GolayAmbient) :
    permAct σ (v + w) = permAct σ v + permAct σ w := by
  funext i
  rfl


theorem golay_permAct_inv_cancel (σ : Equiv.Perm (Fin 24)) (w : GolayAmbient) :
    permAct σ (permAct σ⁻¹ w) = w := by
  rw [← golay_permAct_mul, mul_inv_cancel, golay_permAct_one]

theorem golay_permAct_injective (σ : Equiv.Perm (Fin 24)) :
    Function.Injective (permAct σ : GolayAmbient → GolayAmbient) := by
  intro a b h
  have h1 : permAct σ⁻¹ (permAct σ a) = a := by
    have := golay_permAct_inv_cancel σ⁻¹ a
    rwa [inv_inv] at this
  have h2 : permAct σ⁻¹ (permAct σ b) = b := by
    have := golay_permAct_inv_cancel σ⁻¹ b
    rwa [inv_inv] at this
  have hh := congrArg (permAct σ⁻¹) h
  rwa [h1, h2] at hh


end CFSG.Quasithin.G11
