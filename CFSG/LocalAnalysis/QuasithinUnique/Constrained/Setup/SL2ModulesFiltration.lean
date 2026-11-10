module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesSplit
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Basic

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {V : Type*} [AddCommGroup V] [Module k V]


end Basic

section Glue

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {V V₁ V₂ V₃ : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]


end Glue

section Tensor

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*}

omit [Algebra F k] [CharP k 2] in
def projZ : ((Option (Option ι) → Fin 2) → k) →ₗ[k] ((ι → Fin 2) → k) where
  toFun v y := v (optCons 0 (optCons 1 y))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra F k] [CharP k 2] in
def projS : ((Option (Option ι) → Fin 2) → k) →ₗ[k] ((Option ι → Fin 2) → k) where
  toFun v x := v (optCons (x none) (optCons (x none) (fun z => x (some z))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra F k] [CharP k 2] in
theorem projZ_liftZ (u : (ι → Fin 2) → k) : projZ (liftZ u) = u := by
  funext y
  show liftZ u (optCons 0 (optCons 1 y)) = u y
  rw [liftZ_apply, ite_eq_left (by decide)]

omit [Algebra F k] [CharP k 2] in
theorem projS_liftS (w : (Option ι → Fin 2) → k) : projS (liftS w) = w := by
  funext x
  show liftS w (optCons (x none) (optCons (x none) (fun z => x (some z)))) = w x
  rw [liftS_apply, ite_eq_left rfl]
  congr 1
  funext o
  cases o <;> rfl

omit [Algebra F k] [CharP k 2] in
theorem projS_liftZ (u : (ι → Fin 2) → k) : projS (liftZ u) = 0 := by
  funext x
  show liftZ u (optCons (x none) (optCons (x none) (fun z => x (some z)))) = 0
  rw [liftZ_apply, ite_eq_right (fun h => h rfl)]

omit [Algebra F k] in
theorem projQ_liftZ (u : (ι → Fin 2) → k) : projQ (liftZ u) = 0 := by
  funext y
  rw [projQ_apply, liftZ_apply, liftZ_apply, ite_eq_left (by decide), ite_eq_left (by decide)]
  exact CharTwo.add_self_eq_zero (u y)

omit [Algebra F k] [CharP k 2] in
theorem projQ_liftS (w : (Option ι → Fin 2) → k) : projQ (liftS w) = 0 := by
  funext y
  rw [projQ_apply, liftS_apply, liftS_apply, ite_eq_right (by decide), ite_eq_right (by decide)]
  exact add_zero 0


end Tensor

end CFSG.QuasithinUnique.Setup.SL2Modules
