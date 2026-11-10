module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DQS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Bnd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6FixHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement


variable {Ω : Type} [Group Ω] [Finite Ω]


theorem s265d_false_of_central_commutators {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hBle : Nat.card B ≤ 3 ^ 4) {E : Subgroup Ω}
    (hEel : IsElemAbelian 3 E) (hEle : E ≤ S ⊔ Subgroup.zpowers x) (hE5 : 3 ^ 5 ≤ Nat.card E)
    (hmax : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S) : False := by
  have cfg := h.cfg
  have hTB : (⁅T, B⁆ : Subgroup Ω) ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    have hb' := (Subgroup.mem_normalizer_iff.1 (cfg.bnorm hb) t⁻¹).1 (T.inv_mem ht)
    rw [commutatorElement_def]
    have : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
    rw [this]
    exact T.mul_mem ht hb'
  have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) := cfg.two.to_le hTB
  have hTBc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (S267.ModelGen.comm_of_mem_centMod cfg.normal cfg.core (hcomm t ht b hb) hs).symm
  have hSN : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.1 hTBc).trans (Subgroup.centralizer_le_normalizer _)
    · exact (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 cfg.xcen)).trans
        (Subgroup.center_le_normalizer _)
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_three hEel hmax hTB2 (hEle.trans hSN)
  have h2 := cfg.rank
  omega

section Main


end Main

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
