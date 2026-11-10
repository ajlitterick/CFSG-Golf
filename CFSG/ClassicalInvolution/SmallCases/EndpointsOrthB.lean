module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthNodes
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthLayerB
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthClosure
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinOdd_subgroup_of_pair
  spBlock spBlock_one_eq_longBlock spBlock_zero_eq_shortBlock pair_normalize_sp')
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock shortBlock
  planeGroup IsHyperbolicPlane exists_planeGroup_eq_conj_longBlock symplecticBlockPair_le_sup
  mem_fundamentalSubgroups_PSp_iff)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem planeGroup_perfect_sp4 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    {P : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hP : IsHyperbolicPlane P) :
    planeGroup P ≤ ⁅planeGroup P, planeGroup P⁆ := by
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
  rw [hg]
  refine conjSub_perfect (A := (longBlock F 2 1).range) ?_ g
  exact range_perfect_of_sl2 h4 (longBlock F 2 1)

theorem omega9_closure [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω) {K₀ K₁ K₂ Us : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) {z : G}
    (hz : IsClassicalMember p f K₀ z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSp 2 Ω z) (c02 : Commutes K₀ K₂) (c0s : Commutes K₀ Us)
    (c1s : Commutes K₁ Us) (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hs : ∃ W, SymplecticBlockPair (GaloisField p f) W K₂ Us) :
    ∃ Ψ : spinGroup (Spin.quadOdd 4 (GaloisField p f)) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Function.Surjective Ψ ∧ Ψ.range = K₀ ⊔ K₁ ⊔ K₂ ⊔ Us ∧
      ∀ L : Subgroup G, L ∈ Ω ↔
        ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f)), L = R.map Ψ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set F := GaloisField p f with hFdef
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_galoisField hp2
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf, by norm_num, hp2⟩
  have hadmP : StatedLieAdmissible .PSp 2 p f :=
    ⟨Fact.out, hf, le_rfl, fun h => by have := congrArg Prod.snd h; simp at this; omega⟩
  let U : Fin 4 → Subgroup G := ![K₀, K₁, K₂, Us]
  have hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exacts [c02, c0s, c1s]
  have hpair : ∀ i j : Fin 4, i.val + 1 = j.val → j.val + 1 < 4 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;> simp at hij hj
    exacts [p01, p12]
  have hsp : ∀ i j : Fin 4, i.val + 2 = 4 → j.val + 1 = 4 →
      ∃ W, SymplecticBlockPair F W (U i) (U j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj
    exact hs
  obtain ⟨Ψ, hker, hrange, hΨ⟩ := weakCT_spinOdd_subgroup_of_pair hadm hF h4 U hcomm hpair hsp
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (oddDatum 4 F) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd 4 p f Fact.out hfundM
      hadm (by decide) (by decide)
  set n0 : Fin 4 := zeroB (by norm_num) with hn0
  have hlong0 : n0.val + 1 < 4 := by simp [n0, zeroB_val]
  have hN₀ : (rankOne (oddDatum 4 F).rootGroup n0).map Ψ = K₀ := hΨ n0
  have hN₂ : (rankOne (oddDatum 4 F).rootGroup (⟨2, by norm_num⟩ : Fin 4)).map Ψ = K₂ := hΨ _
  have hTc : ∀ k : Fin 4, k.val ≠ 1 → Commutes ((rootθB 4 F).map Ψ) (U k) := by
    intro k hk
    rw [← hΨ k]
    exact commutes_map_hom Ψ (commutes_rootθB_rankOne hn3 h2 hk)
  have hΩΨ : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 F), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT (rankOne (oddDatum 4 F).rootGroup n0)
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0) R hR
    rw [hg, map_conjSub_eq, hN₀]
    exact hΩ.conjInvariant _ _ hK₀
  obtain ⟨W, hW⟩ := hs
  obtain ⟨φ, hφrange, hφker, -, hφU, hφV⟩ := pair_normalize_sp' hW
  rw [spBlock_one_eq_longBlock] at hφU
  have hφL : (longBlock F 2 1).range.map φ = K₂ :=
    (MonoidHom.range_comp φ (longBlock F 2 1)).symm.trans hφU
  have hWle : W ≤ K₂ ⊔ Us := symplecticBlockPair_le_sup hW
  have hK₂le : K₂ ≤ Ψ.range := by rw [hrange]; exact le_iSup U 2
  have hUsle : Us ≤ Ψ.range := by rw [hrange]; exact le_iSup U 3
  have hφle : φ.range ≤ Ψ.range := by
    rw [hφrange]
    exact hWle.trans (sup_le hK₂le hUsle)
  have hrangeComm : Commutes (K₂ ⊔ Us) K₀ := commutes_sup_of_both c02.symm c0s.symm
  have hTcomm : Commutes ((rootθB 4 F).map Ψ) (K₂ ⊔ Us) :=
    fun x hx y hy => by
      have h1 : Commutes (K₂ ⊔ Us) ((rootθB 4 F).map Ψ) :=
        commutes_sup_of_both (hTc 2 (by simp)).symm (hTc 3 (by simp)).symm
      exact (h1 y hy x hx).symm
  have hcount := hshape.ncard_locFamily_le (show (StatedLieTag.PSp) ≠ .trialityD4 by decide)
    (CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadmP)
  have hclos := surjective_of_layer_closure hΩ hconn hK₀ hsingle hz hP1
    (FT := fundamentalSubgroups .POmegaOdd (oddDatum 4 F))
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hscT R hR R' hR') Ψ hΩΨ
    (N₀R := rankOne (oddDatum 4 F).rootGroup n0) (TR := rootθB 4 F)
    (rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0) (rootθB_mem_fundamentalSubgroups hn3)
    (by rw [hN₀]; exact hTc n0 (by simp [n0, zeroB_val]))
    (KY := StatedSp 2 F)
    (Y := fundamentalSubgroups .PSp (modelUniv .PSp 2 p f Fact.out).D) φ hφker
    (fun R hR => by
      obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
      exact planeGroup_perfect_sp4 h4 hP)
    (fun R hR => by
      obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
      obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
      obtain ⟨h, hh⟩ : φ g ∈ Ψ.range := hφle ⟨g, rfl⟩
      refine ⟨conjSub h (rankOne (oddDatum 4 F).rootGroup
        (⟨2, by norm_num⟩ : Fin 4)), conjSub_mem_fundamentalSubgroups
          (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (by simp)) h, ?_⟩
      rw [hg]
      change Subgroup.map φ (conjSub g (longBlock (GaloisField p f) 2 1).range) = _
      rw [map_conjSub_eq, map_conjSub_eq, hφL, hN₂, hh])
    (fun R hR => by
      obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
      rw [hN₀]
      intro x hx y hy
      have hx' : x ∈ K₂ ⊔ Us := hWle (hφrange ▸ (Subgroup.map_le_range φ _ hx))
      exact hrangeComm x hx' y hy)
    (fun R hR => by
      obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
      intro x hx y hy
      have hy' : y ∈ K₂ ⊔ Us := hWle (hφrange ▸ (Subgroup.map_le_range φ _ hy))
      exact hTcomm x hx y hy')
    hcount
  refine ⟨Ψ, hker, hclos.2, ?_, hclos.1⟩
  rw [hrange]
  refine le_antisymm (iSup_le fun k => ?_)
    (sup_le (sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)) (le_iSup U 3))
  fin_cases k
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right


theorem omega9_lieSystem [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω) {K₀ K₁ K₂ Us : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) {z : G}
    (hz : IsClassicalMember p f K₀ z) (hP1 : LocalOddCentral Ω {z})
    (hshape : LocalShapeT p f 2 .PSp 2 Ω z) (c02 : Commutes K₀ K₂) (c0s : Commutes K₀ Us)
    (c1s : Commutes K₁ Us) (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hs : ∃ W, SymplecticBlockPair (GaloisField p f) W K₂ Us) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = 4 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf, by norm_num, hp2⟩
  obtain ⟨Ψ, hker, hsurj, -, hΩΨ⟩ := omega9_closure hp2 hq hΩ hconn hK₀ hsingle hz hP1 hshape c02
    c0s c1s p01 p12 hs
  have hn3 : 3 ≤ 4 := by norm_num
  set n0 : Fin 4 := zeroB (by norm_num) with hn0
  have hlong0 : n0.val + 1 < 4 := by simp [n0, zeroB_val]
  exact exists_lieSystemData_of_fundamental (t := .POmegaOdd) trivial hadm Ψ hsurj hker
    ⟨_, rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0⟩ hΩΨ


end CFSG.ClassicalInvolution.RouteD
