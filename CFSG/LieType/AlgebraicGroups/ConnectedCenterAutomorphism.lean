module

public import CFSG.LieType.AlgebraicGroups.CanonicalReductiveFactors
public import CFSG.LieType.AlgebraicGroups.CentralIsogenyLift
public import CFSG.LieType.AlgebraicGroups.CentralProductMorphism
public import TauCeti.Algebra.AlgebraicGroup.Center.Isomorphism

public noncomputable section

open CategoryTheory AlgebraicGeometry WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (M : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k)


section Core

variable (σ : M →ₐc[k] M)
omit [IsAlgClosed k] in
theorem aut_bijective (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    Function.Bijective σ := by
  constructor
  · intro x y hxy
    have hx : σ (σ (σ x)) = x := by
      simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
        congrArg (fun f : M →ₐc[k] M => f x) hσ3
    have hy : σ (σ (σ y)) = y := by
      simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
        congrArg (fun f : M →ₐc[k] M => f y) hσ3
    calc
      x = σ (σ (σ x)) := hx.symm
      _ = σ (σ (σ y)) := congrArg (fun z => σ (σ z)) hxy
      _ = y := hy
  · intro y
    refine ⟨σ (σ y), ?_⟩
    simpa only [BialgHom.comp_apply, BialgHom.id_apply] using
      congrArg (fun f : M →ₐc[k] M => f y) hσ3

noncomputable def autIso (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    M.obj ≅ M.obj :=
  _root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective σ (aut_bijective M σ hσ3))

omit [IsAlgClosed k] in
@[simp]
theorem autIso_hom_hom (hσ3 : (σ.comp σ).comp σ = BialgHom.id k M) :
    (autIso M σ hσ3).hom.hom = σ := by
  rw [autIso, _root_.CommHopfAlgCat.isoMk_hom, _root_.CommHopfAlgCat.hom_ofHom]
  rfl


end Core


end CFSG.LieType.AlgebraicGroups.CanonicalReductive
