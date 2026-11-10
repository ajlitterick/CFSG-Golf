module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank

open scoped IsMulCommutative

section General

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Group E] [CFSG.IsElementaryAbelian p E]

@[expose] noncomputable def mulAutToGL {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) (Additive E)) :
    MulAut E →* Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
  MonoidHom.toHomUnits
    { toFun := fun σ => LinearMap.toMatrix b b
        ((MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap p)
      map_one' := by
        rw [← LinearMap.toMatrix_id b]
        congr 1
      map_mul' := fun σ τ => by
        rw [← LinearMap.toMatrix_mul]
        congr 1 }

theorem mulAutToGL_injective {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) (Additive E)) :
    Function.Injective (mulAutToGL (E := E) b) := by
  intro σ τ h
  have h1 := congrArg Units.val h
  change LinearMap.toMatrix b b _ = LinearMap.toMatrix b b _ at h1
  have h2 := (LinearMap.toMatrix b b).injective h1
  apply MulEquiv.ext
  intro x
  have h3 := LinearMap.congr_fun h2 (Additive.ofMul x)
  exact h3

theorem card_mulAut_dvd_GL [Finite E] {n : ℕ} (hE : Nat.card E = p ^ n) :
    Nat.card (MulAut E) ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  have hdim : Module.finrank (ZMod p) (Additive E) = n := by
    have : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    rw [Nat.card_zmod] at h
    change Nat.card E = _ at h
    rw [hE] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hdim
  haveI : Fintype (ZMod p) := ZMod.fintype p
  have hGL := Matrix.card_GL_field n (𝔽 := ZMod p)
  rw [ZMod.card] at hGL
  rw [← hGL]
  exact Subgroup.card_dvd_of_injective _ (mulAutToGL_injective b)

end General


end CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank
