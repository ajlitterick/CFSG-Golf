module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2

public noncomputable section
namespace CFSG.StandardType.F4ExplicitPos.FiveToralKernel

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] public def f4CharValue (m : Fin 4 → ZMod 5) (v : Fin Tag.F4.rank → ℤ) : ZMod 5 :=
  ∑ i : Fin 4, (v i : ZMod 5) * m i

@[expose] public def f4CharMask (m : Fin 4 → ZMod 5) : Finset (Fin 48) :=
  Finset.univ.filter fun k => f4CharValue m (CFSG.RankThree.PartOne.KF4.f4RootVec k) = 0

@[expose] public def f4RootDot (i j : Fin 48) : ℚ :=
  (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec i)) ⬝ᵥ
    (CFSG.LieType.Chevalley.f4Euclid (CFSG.RankThree.PartOne.KF4.f4RootVec j))

@[expose] public def f4Nonorth (i j : Fin 48) : Prop := f4RootDot i j ≠ 0

@[expose] public def f4PathTwo (S : Finset (Fin 48)) (i j : Fin 48) : Prop :=
  i = j ∨ f4Nonorth i j ∨ ∃ k ∈ S, f4Nonorth i k ∧ f4Nonorth k j

@[expose] public def f4MaskGood (m : Fin 4 → ZMod 5) : Prop :=
  let S := f4CharMask m
  S.card = 8 ∨ (S.card = 18 ∧ ∀ i ∈ S, ∀ j ∈ S, f4PathTwo S i j)

public instance f4MaskGood_decidable (m : Fin 4 → ZMod 5) : Decidable (f4MaskGood m) := by
  unfold f4MaskGood f4PathTwo f4Nonorth
  infer_instance


open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section NativeKernelComponents


end NativeKernelComponents

section NativeEighteenRootShape
open CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.F4ExplicitPos
  CFSG.RankThree.PartOne.KF4


end NativeEighteenRootShape

end CFSG.StandardType.F4ExplicitPos.FiveToralKernel
