module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Fan28
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteFinal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtFiveZc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PXi
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P53a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P54
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P510Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512dMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Main2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515bFin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517c
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P519
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62D
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P66
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Tail
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmL512
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmL517
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421Final
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.Recognition.F112TitsB2
public import CFSG.Quasithin.Recognition.F112TitsMain3
public import CFSG.Quasithin.Recognition.F112WAssembly
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Assembly
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KLoc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExD10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbel
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace AsmI2

theorem exists_zz (F : FanTree Γ G) (h40 : Fan40 F) (ℓ : Line Γ) :
    ∃ z : G, z ∈ ℓ.ZZ ∧ z ≠ 1 := by
  have hadj : Γ.Adj (ℓ.vert 0) (ℓ.vert (0 + 1)) := ℓ.adj 0
  have hE2 := F.edge_two _ _ hadj
  have hEfin := F.finite_stabilizer_inf (ℓ.vert 0) (ℓ.vert (0 + 1))
  have hEnt : Nontrivial ↥(MulAction.stabilizer G (ℓ.vert 0) ⊓
      MulAction.stabilizer G (ℓ.vert (0 + 1))) := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (F.nbrStab_ne_bot h40 (ℓ.vert 0))
    refine nontrivial_of_ne ⟨(k : G), F.nbrStab_le_edge (ℓ.vert 0) hadj k.2⟩ 1 fun h =>
      hk (Subtype.ext ?_)
    simpa using congrArg Subtype.val h
  obtain ⟨z, hzE, hz1, hzz, hzc⟩ := exists_central_involution_of_isPGroup hE2
  exact ⟨z, ⟨hzz, 0, hzE, fun h hh => hzc h hh⟩, hz1⟩

end AsmI2

end CFSG.Quasithin.Fan86
