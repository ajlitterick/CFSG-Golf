module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

open CFSG.BenderSuzuki.MatrixGroups


theorem oddPrimeInvertersAndSplitFusion_of_mulEquiv_psl2
    {F : Type*} [Group F] {k : Type}
    [Field k] [Finite k] {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (e : F ≃* PSL2MatrixGroup k) : OddPrimeInvertersAndSplitFusion F (Nat.card k) :=
  (psl2_oddPrimeInvertersAndSplitFusion hf hk).of_mulEquiv e

theorem oddPrimeInvertersAndSplitFusion_of_mulEquiv_suzukiMatrixGroup
    {F : Type*} [Group F]
    {m : ℕ} (hm : 1 ≤ m) (e : F ≃* SuzukiMatrixGroup m) :
    OddPrimeInvertersAndSplitFusion F (2 ^ (2 * m + 1)) :=
  (suzukiMatrixGroup_oddPrimeInvertersAndSplitFusion m hm).of_mulEquiv e


end CFSG.ShultStronglyClosedTI.OddPrimeInverters
