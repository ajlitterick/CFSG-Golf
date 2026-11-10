module

public import CFSG.ClassicalInvolution.Uniform.UBranch
public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

variable {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem nonempty_equiv_of_memberU (h : IsClassicalMemberU (.sl2 3 1) K z) :
    Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :=
  h.nonempty_equiv_sl2Three (by norm_num [MemberType.IsSolvableType])


theorem normalizerQuotientTwoGeneratedStar_of_memberU
    (h : IsClassicalMemberU (.sl2 3 1) K z) : NormalizerQuotientTwoGeneratedStar K :=
  normalizerQuotientTwoGeneratedStar_three (nonempty_equiv_of_memberU h).some


theorem centSylow_three_of_memberU [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ K ∈ Ω, ∃ z : G, IsClassicalMemberU (.sl2 3 1) K z) :
    Asc77.AscL62.CentSylow Ω :=
  centSylow_three fun K hK => (hΩ K hK).elim fun _ hz => nonempty_equiv_of_memberU hz


section Branch


end Branch

end CFSG.ClassicalInvolution.Q3.Q3T6
