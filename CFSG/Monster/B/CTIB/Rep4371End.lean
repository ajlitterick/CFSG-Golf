module

public import CFSG.Monster.B.CTIB.Rep4371SpinBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371
  Matrix
open CFSG.Monster.B.Co2 (v0)

@[expose] noncomputable def basisV2048 :
    Module.Basis (Fin 2048) ℚ V2048 :=
  (Module.Basis.span linearIndependent_RbT).map (LinearEquiv.ofEq _ _ V2048_eq_span.symm)

theorem coe_basisV2048
    (t : Fin 2048) : (basisV2048 t : Vst) = Rbasis (tIdx t) := by
  rw [basisV2048, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

theorem basisV2048_repr (x : V2048) (t : Fin 2048) :
    basisV2048.repr x t = Rbasis.repr (x : Vst) (tIdx t) := by
  have h : (Finsupp.lapply t).comp basisV2048.repr.toLinearMap =
      (Finsupp.lapply (tIdx t)).comp (Rbasis.repr.toLinearMap.comp V2048.subtype) := by
    refine basisV2048.ext fun s => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply, Submodule.subtype_apply, coe_basisV2048]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hst : s = t
    · rw [ite_eq_left hst, ite_eq_left (congrArg tIdx hst)]
    · rw [ite_eq_right hst, ite_eq_right (fun h' => hst (tIdx_injective h'))]
  exact LinearMap.congr_fun h x

@[expose] noncomputable def resV2048
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    Module.End ℚ V2048 :=
  (rhoV h : Vst →ₗ[ℚ] Vst).restrict (Jhat_preserves hh).2.2


@[expose] noncomputable def resE (e : Ehat) : Module.End ℚ V2048 :=
  resV2048 (h := ehatS e) (Ehat_le_Jhat e.2)


end CFSG.Monster.B.CTIB
