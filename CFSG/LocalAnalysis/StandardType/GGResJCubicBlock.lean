module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.ResJCubicBlock

section Linear

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]

noncomputable def frob : E →ₗ[K] E :=
  (FiniteField.frobeniusAlgHom K E).toLinearMap


variable {s : ℕ} [NeZero s]


end Linear

section Zeta

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)


end Zeta

section Commutator

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)


end Commutator

section GroupModel

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
variable (hdeg : Module.finrank K E = 3)
variable (y : Fin s → E) (hy0 : ∀ i, y i ≠ 0)

abbrev GLV (K E : Type*) [Field K] [Field E] [Algebra K E] [Fintype K] (s : ℕ) :=
  (Fin s → E) ≃ₗ[K] (Fin s → E)

abbrev SLV (K E : Type*) [Field K] [Field E] [Algebra K E] [Fintype K] (s : ℕ) :=
  SpecialLinearGroup K (Fin s → E)

noncomputable abbrev conjSL (Y : GLV K E s) (g : SLV K E s) : SLV K E s :=
  SpecialLinearGroup.congr_linearEquiv (R := K) (V := Fin s → E) (W := Fin s → E) Y g

omit [Fintype E] [FiniteDimensional K E] [NeZero s] in
theorem conjSL_coe (Y : GLV K E s) (g : SLV K E s) :
    ((conjSL (K := K) (E := E) (s := s) Y g : SLV K E s) : GLV K E s) =
      Y * (g : GLV K E s) * Y⁻¹ := by
  simp only [conjSL, SpecialLinearGroup.congr_linearEquiv_coe_apply]
  ext v
  simp [LinearEquiv.mul_apply]


end GroupModel

end CFSG.StandardType.ResJCubicBlock
