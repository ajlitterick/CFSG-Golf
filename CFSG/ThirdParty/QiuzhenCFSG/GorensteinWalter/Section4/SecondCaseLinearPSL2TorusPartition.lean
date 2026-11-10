module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-`p` partition for a selected PSL₂ torus

This is the small Huppert-partition adapter needed by equation (11).  It
removes the characteristic Sylow family and the opposite torus family when
`p` is an odd prime dividing the selected torus, and transports the result
through a model equivalence.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open BenderSuzuki
open BenderSuzuki.External
open scoped MatrixGroups


/-- Transport a unique torus-family partition through a group equivalence. -/
public theorem transport_psl2_torus_family_partition
    {Q K : Type u} [Group Q] [Finite Q] [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (e : Q ≃* PSL2 K) (U : Subgroup (PSL2 K))
    (hpart : ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = U.map (MulAut.conj g).toMonoidHom}, x ∈ T.1) :
    ∀ x : Q, orderOf x = p →
      ∃! T : {T : Subgroup Q // ∃ g : Q,
        T = (U.map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  intro x hx
  let y : PSL2 K := e x
  have hy : orderOf y = p := by
    rw [e.orderOf_eq]
    exact hx
  obtain ⟨T, hTy, hTuniq⟩ := hpart y hy
  rcases T.2 with ⟨g, hg⟩
  let TQ : Subgroup Q := T.1.map e.symm.toMonoidHom
  have hTQmem : x ∈ TQ := by
    refine Subgroup.mem_map.mpr ⟨y, hTy, ?_⟩
    simp [y, TQ]
  have hTQfamily : ∃ g : Q, TQ =
      (U.map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rcases T.2 with ⟨g, hg⟩
    refine ⟨e.symm g, ?_⟩
    dsimp [TQ]
    rw [hg, Subgroup.map_map]
    rw [Subgroup.map_map]
    apply congrArg (fun f : PSL2 K →* Q => Subgroup.map f U)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨⟨TQ, hTQfamily⟩, hTQmem, ?_⟩
  intro T' hT'x
  let TP : Subgroup (PSL2 K) := T'.1.map e.toMonoidHom
  have hTPfamily : ∃ g : PSL2 K, TP = U.map (MulAut.conj g).toMonoidHom := by
    rcases T'.2 with ⟨g', hg'⟩
    refine ⟨e g', ?_⟩
    dsimp [TP]
    rw [hg', Subgroup.map_map]
    rw [Subgroup.map_map]
    apply congrArg (fun f : PSL2 K →* PSL2 K => Subgroup.map f U)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hTPmem : e x ∈ TP := by
    dsimp [TP]
    exact Subgroup.mem_map.mpr ⟨x, hT'x, rfl⟩
  have hEqP : TP = T.1 := by
    exact congrArg Subtype.val (hTuniq ⟨TP, hTPfamily⟩ hTPmem)
  have hmapEq : T'.1.map e.toMonoidHom = TQ.map e.toMonoidHom := by
    calc
      T'.1.map e.toMonoidHom = TP := rfl
      _ = T.1 := hEqP
      _ = TQ.map e.toMonoidHom := by
        dsimp [TQ]
        rw [Subgroup.map_map]
        change T.1 = Subgroup.map
          (e.toMonoidHom.comp e.symm.toMonoidHom) T.1
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
          ext z
          simp
        rw [hcomp]
        simp
  exact Subtype.ext (Subgroup.map_injective e.injective hmapEq)

end CFSG.GorensteinWalter
