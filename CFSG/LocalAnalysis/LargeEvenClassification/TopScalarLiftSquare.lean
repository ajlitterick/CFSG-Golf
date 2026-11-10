module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalarNorm
public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryCoordinateRoots

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem central_power_involution_primitive_lift_square {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (hcard : Nat.card (normalElementarySquareKernel A hcommutative) = 4)
    (exponent : ℕ) (δ : MulAut A)
    (hpower : ∀ a : A, δ a = a ^ (1 + 2 ^ (exponent + 2)))
    (hsquare : δ ^ 2 = 1) (hnontrivial : δ ≠ 1)
    (t : S) (hlift : MulAut.conjNormal (H := A) t = δ) :
    ∃ square : A, (square : S) = t ^ 2 ∧ ∀ a : A, square ≠ a ^ 2 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  have hcentral (s : S) : Commute δ (MulAut.conjNormal (H := A) s) := by
    apply MulEquiv.ext
    intro a
    change δ (MulAut.conjNormal (H := A) s a) = MulAut.conjNormal (H := A) s (δ a)
    rw [hpower, hpower, map_pow]
  have hprincipal : abelianAutomorphismUnits A δ ∈ principalFourSubgroup (AddMonoid.End (Additive A)) := by
    refine ⟨(2 ^ exponent : ℕ) • (1 : AddMonoid.End (Additive A)), ?_⟩
    apply AddMonoid.End.ext
    intro a
    change Additive.ofMul (δ a.toMul) = a + 4 • ((2 ^ exponent : ℕ) • a)
    rw [hpower]
    change (1 + 2 ^ (exponent + 2) : ℕ) • a = a + 4 • ((2 ^ exponent : ℕ) • a)
    rw [add_nsmul, one_nsmul, smul_smul, pow_add]
    congr 1
    norm_num
    rw [Nat.mul_comm]
  obtain ⟨hnormKernel, hnormSurjective⟩ := abelian_principal_norm (hpgroup.to_subgroup A) δ hprincipal
  obtain ⟨hmem, hobstruction⟩ := central_action_involution_norm_obstruction A hcommutative
    hselfCentralizing hnoEight δ hsquare hnontrivial hcentral hnormKernel hcard t hlift
  let square : A := ⟨t ^ 2, hmem⟩
  refine ⟨square, rfl, ?_⟩
  intro a hsquarePower
  obtain ⟨b, hb⟩ := hnormSurjective a
  exact hobstruction b (congrArg (fun a : A => a.val) (hsquarePower.trans hb.symm))


end CFSG.LargeEvenClassification.Helpers
