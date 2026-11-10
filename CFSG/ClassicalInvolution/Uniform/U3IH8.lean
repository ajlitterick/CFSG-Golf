module

public import CFSG.ClassicalInvolution.Uniform.U3Thm4
public import CFSG.ClassicalInvolution.Uniform.U3Thm7
public import CFSG.ClassicalInvolution.Uniform.UBranch

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly

theorem ih8RestU_three_of (hG2D4 : Ih8G2D4EdgeU) (hThree : Ih8ThreeU) (hTwin : Ih8TwinShapeU)
    (h5 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm5BelowU 3 1 n)
    (hMu : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → MuTableBelowU 3 1 n)
    (h3 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n) : IH8RestU 3 1 :=
  fun n hn => ⟨h5 n hn, thm6TypedBelowU_three_of_citBelowT hn,
    thm7TypedBelowU_three_of hTwin hn, thm8TypedBelowU_three_of hG2D4 hThree hn, hMu n hn,
    h3 n hn⟩


end CFSG.ClassicalInvolution.Uniform
