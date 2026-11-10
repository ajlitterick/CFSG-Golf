module

public import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG48

public section

namespace CFSG.Quasithin.SimsG4

namespace OrthA

open LinearMap (BilinForm)

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def centreSet (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Set V :=
  {r | Q r = 1 ∧ ∃ d ∈ transvSet G₀, ∀ x, d x = x + QuadraticMap.polar Q x r • r}

@[expose] def centreField (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) : Subfield F :=
  Subfield.closure {a | ∃ r ∈ centreSet Q G₀, ∃ s ∈ centreSet Q G₀, a = QuadraticMap.polar Q r s}

@[expose] def centreForm (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Submodule (centreField Q G₀) V :=
  Submodule.span (centreField Q G₀) (centreSet Q G₀)


theorem polar_mem_centreField {Q : QuadraticForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {x y : V}
    (hx : x ∈ centreForm Q G₀) (hy : y ∈ centreForm Q G₀) :
    QuadraticMap.polar Q x y ∈ centreField Q G₀ := by
  induction hx using Submodule.span_induction with
  | mem r hr =>
    induction hy using Submodule.span_induction with
    | mem s hs => exact Subfield.subset_closure ⟨r, hr, s, hs, rfl⟩
    | zero => rw [QuadraticMap.polar_zero_right]; exact zero_mem _
    | add y y' _ _ h h' => rw [QuadraticMap.polar_add_right]; exact add_mem h h'
    | smul a y _ h =>
      rw [Subfield.smul_def, QuadraticMap.polar_smul_right, smul_eq_mul]
      exact mul_mem a.2 h
  | zero => rw [QuadraticMap.polar_zero_left]; exact zero_mem _
  | add x x' _ _ h h' => rw [QuadraticMap.polar_add_left]; exact add_mem h h'
  | smul a x _ h =>
    rw [Subfield.smul_def, QuadraticMap.polar_smul_left, smul_eq_mul]
    exact mul_mem a.2 h


section Form


end Form

section Restriction


end Restriction


end OrthA

end CFSG.Quasithin.SimsG4
