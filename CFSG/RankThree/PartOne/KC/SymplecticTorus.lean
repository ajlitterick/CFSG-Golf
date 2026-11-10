module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spScalarKernel (r : ℕ) (K : Type) [Field K] : Subgroup (gsp r K) :=
  (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) : Kˣ →* GL (Fin r ⊕ Fin r) K).range.comap
    (gsp r K).subtype

theorem mem_spScalarKernel {A : gsp r K} :
    A ∈ spScalarKernel r K ↔ ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) =
      Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

variable (r K) in
@[expose] noncomputable def spCentralizerD (t : MulAut (StatedProj (StatedSp r K))) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  (conjAut r K).range ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp r K))))

variable (r K) in
@[expose] noncomputable def spCenterN (t : MulAut (StatedProj (StatedSp r K))) :
    Subgroup (MulAut (StatedProj (StatedSp r K))) :=
  (Subgroup.center ↥(spCentralizerD r K t)).map (spCentralizerD r K t).subtype


instance spScalarKernel_normal : (spScalarKernel r K).Normal where
  conj_mem A hA g := by
    obtain ⟨c, hc⟩ := mem_spScalarKernel.mp hA
    have h : g * A * g⁻¹ = A := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc,
        ← (commute_scalar_gl c (g : GL (Fin r ⊕ Fin r) K)).eq, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [h]
    exact hA


end CFSG.RankThree.PartOne.KCSpComm

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCSpIsotypic
open scoped commutatorElement


end CFSG.RankThree.PartOne
