module

public import CFSG.Milestones.ASVolI.F4L3
public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdIso
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Levi
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabB
public import CFSG.Walter.JRFacts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Gamma

public section

namespace CFSG.ASVolI

section Setup

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.ASVolI.ChF


end Setup

section D1

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2]


end D1

section Model

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}


end Model

section CardIso

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts.OddChar
  CFSG.RankThree.PartTwo.Sec8.Item8ModelProof CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd


end CardIso

section InnDiag

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}


end InnDiag

section Transport

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.QTGen4.DSGen4.L34


end Transport

section InnDiag2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.QTGen4.DSGen4.L34


end InnDiag2

section FieldPart

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F]


variable {E : Type} [Group E] {ρ : E →* MulAut (projectiveSL 3 F)}


end FieldPart

section Diag

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}


variable [Finite F]


end Diag

section Struct

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.H13.F431.L3.P3 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E}


end Struct

section BtDiag

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.GH74.QTGen4.DSGen4.L34

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E]
  {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)}


end BtDiag

section Clause3

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF

structure burnsideF447_Ctx {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] (f : ℕ)
    (Φ : projectiveSL 3 F →* E) (ρ : E →* MulAut (projectiveSL 3 F)) (Gp : Subgroup E) :
    Prop where
  hf : 2 ≤ f
  hF : Nat.card F = 2 ^ f
  hΦ : Function.Injective Φ
  hρ : Function.Injective ρ
  hrange : Φ.range = Gp
  hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹
  hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F

variable {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type} [Group E] [Finite E]
  {f : ℕ} {Φ : projectiveSL 3 F →* E} {ρ : E →* MulAut (projectiveSL 3 F)} {Gp : Subgroup E}

theorem burnsideF447_Ctx.hq (C : burnsideF447_Ctx f Φ ρ Gp) : 2 < Nat.card F := by
  rw [C.hF]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) C.hf


end Clause3

section NT

open CFSG.Timmesfeld


end NT

section Clause3b

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end Clause3b

section Clause3E

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag


end Clause3E

section Transport2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF


end Transport2

section Levi

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour


end Levi

section YbarMem

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ASVolI.ChF


end YbarMem

section YbarBot

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF


end YbarBot

section Clause1E

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.H13.F431.L3.P3
  CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag


end Clause1E

section Clause1M

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF


end Clause1M

section Sl2

open CFSG.Open


end Sl2

section Blk

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3


end Blk

section Lam

open CFSG.Open CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3


end Lam

section YChar

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF


end YChar

section YChar2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end YChar2

section DiagLemmas

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end DiagLemmas

section PkgBasic

open CFSG.Open


end PkgBasic

section PkgE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end PkgE

section Pkg

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF


end Pkg

section PkgE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end PkgE2

section Transp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3


end Transp

section SE

open CFSG.Open CFSG.BenderSuzuki CFSG.Semidihedral.ParameterFive


end SE

section ClauseTwoM

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF


end ClauseTwoM

section Twist

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.ASVolI.ChF CFSG.GH74.QTGen4.DSGen4.L34


end Twist

section Final

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3


section Target


end Target

end Final

end CFSG.ASVolI
