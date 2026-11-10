module

public import CFSG.Quasithin.Background.JonesParshallSp4H1

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]


theorem spX_mul (a b d a' b' d' : F) : spX a b d * spX a' b' d' = spX (a + a') (b + b') (d + d') :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, spX_smul, spX_smul, spX_smul]
    congr 1 <;> ring

theorem spY_mul (a b d a' b' d' : F) : spY a b d * spY a' b' d' = spY (a + a') (b + b') (d + d') :=
  sp4_ext fun x y z w => by
    rw [Subgroup.coe_mul, mul_smul, spY_smul, spY_smul, spY_smul]
    congr 1 <;> ring


section Theorem

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def additiveIx (F : Type) [Field F] : Additive (Multiplicative (Ix → F)) ≃+ (Ix → F) where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [CharP F 2] in
theorem BinaryNaturalSp4Derived.intertwiner {ρ : Representation (ZMod 2) Γ W}
    (h : BinaryNaturalSp4Derived ρ F) :
    ∃ (θ : Γ ≃* ↥⁅sp4 F, sp4 F⁆) (β : W ≃+ (Ix → F)),
      ∀ γ w, β (ρ γ w) = ((θ γ : ↥⁅sp4 F, sp4 F⁆) : GL Ix F) • β w := by
  obtain ⟨θ₀, β₀, hw⟩ := h
  let θ₁ : Γ ≃* ↥⁅sp4 F, sp4 F⁆ := θ₀
  have ha := Witness.ambient (D := FFModel.nat ⁅sp4 F, sp4 F⁆) (θ := θ₁) rfl rfl hw
  refine ⟨θ₁, (β₀.trans (secEquivAmb _ rfl rfl).toAdditive).trans (additiveIx F),
    fun γ w => ?_⟩
  exact congrArg (additiveIx F) (ha γ w)


end Theorem

end CFSG.Quasithin.JonesParshall
