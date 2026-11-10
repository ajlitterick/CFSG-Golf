module

public import CFSG.Quasithin.Background.SimsG4OrthAForm
public import CFSG.Quasithin.Background.SimsG4OrthAModel

public section

namespace CFSG.Quasithin.SimsG4


namespace OrthA

open LinearMap (BilinForm)


variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

section Transfer

variable {F₀ : Subfield F} {I : Submodule F₀ V} {G₀ : Subgroup (V ≃ₗ[F] V)}
  (hGI : ∀ g ∈ G₀, ∀ x ∈ I, g x ∈ I) {T : Set (I ≃ₗ[F₀] I)}


variable {B : BilinForm F V}


end Transfer

section Space

variable (Q : QuadraticForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))


variable {Q G₀}


end Space

structure OrthHyp (B : BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) (Q : QuadraticForm F V) :
    Prop where
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0
  finrank_eq : Module.finrank F V = 4
  le_sp : G₀ ≤ spGroup B
  transv_nonempty : (transvSet G₀).Nonempty
  irred : IsIrredOnV (transvGen G₀)
  polar_eq : ∀ x y, QuadraticMap.polar Q x y = B x y
  isometry : ∀ g ∈ G₀, ∀ x, Q (g x) = Q x

namespace OrthHyp

variable [Finite F] [CharP F 2] {B : BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}
  {Q : QuadraticForm F V} (h : OrthHyp B G₀ Q)

include h


theorem val : ∀ x ∈ centreForm Q G₀, ∀ y ∈ centreForm Q G₀, B x y ∈ centreField Q G₀ :=
  fun x hx y hy => h.polar_eq x y ▸ polar_mem_centreField hx hy


end OrthHyp

end OrthA

open OrthA


end CFSG.Quasithin.SimsG4
