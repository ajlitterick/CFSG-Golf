
module

public import CFSG.Monster.B.TwoA.Unitary.LinThreeBase
import all CFSG.Monster.B.TwoA.Unitary.LinThreeBase

public import CFSG.Monster.B.TwoA.Unitary.WStab
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary.LinThree

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.LinearGroups CFSG.Monster.B.TwoA
open CFSG.Monster.Code (AutPerm)
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

theorem closure_nativeGen :
    Subgroup.closure (Set.range nativeGen) = P₂ := by
  have e : (AutPerm.subtype ∘ n6Aut) = nativeGen := funext fun k => (nativeGen_eq k).symm
  rw [P₂_eq_map, ← closure_n6Aut, MonoidHom.map_closure, ← Set.range_comp, e]

attribute [local instance] restAction

theorem closure_genP :
    Subgroup.closure (Set.range genP) = ⊤ := by
  apply Subgroup.map_injective (f := P₂.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact closure_nativeGen

theorem range_rhoN_le :
    rhoN.range ≤ rhoS.range := by
  rw [MonoidHom.range_eq_map, ← closure_genP, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨genElt k, (rhoN_genP k).symm⟩

theorem range_rhoN_eq :
    rhoN.range = rhoS.range := by
  have : Finite rhoS.range := Nat.finite_of_card_ne_zero (by rw [natCard_range_rhoS]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge range_rhoN_le ?_
  rw [natCard_range_rhoS, ← Nat.card_congr (MonoidHom.ofInjective rhoN_injective).toEquiv,
    natCard_P₂]

@[expose] noncomputable def psi :
    P₂ ≃* SigmaL3 :=
  (MonoidHom.ofInjective rhoN_injective).trans ((MulEquiv.subgroupCongr range_rhoN_eq).trans
    (MonoidHom.ofInjective rhoS_injective).symm)

theorem rhoS_psi
    (p : P₂) : rhoS (psi p) = rhoN p := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective rhoS_injective)
    ((MulEquiv.subgroupCongr range_rhoN_eq) ((MonoidHom.ofInjective rhoN_injective) p))
  exact congrArg Subtype.val h

theorem psi_smul_j
    (p : P₂) (i : NativeCoord) : psi p • j i = j (restP p i) :=
  (congrArg (fun f : Equiv.Perm PlanePoint => f (j i)) (rhoS_psi p)).trans (rhoN_j p i)

theorem psi_genP
    (k : Fin 6) : psi (genP k) = genElt k :=
  rhoS_injective ((rhoS_psi _).trans (rhoN_genP k))

theorem closure_genElt :
    Subgroup.closure (Set.range genElt) = ⊤ := by
  have h : Set.range genElt = psi.toMonoidHom '' Set.range genP := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun k => (psi_genP k).symm)
  rw [h, ← MonoidHom.map_closure, closure_genP,
    Subgroup.map_top_of_surjective _ psi.surjective]


end CFSG.Monster.B.TwoA.Unitary.LinThree
