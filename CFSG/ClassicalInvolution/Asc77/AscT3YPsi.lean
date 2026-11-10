module

public import CFSG.ClassicalInvolution.Asc77.AscT3RStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Psi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.y_psi (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) :
    ∃ ψ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) →*
        RingAut (GaloisField p f),
      ∀ x : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)),
        ψ x = 1 ↔ (x : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  classical
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hKop : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.one_le_iff_ne_zero.mpr hf, hFcard⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hFcard]
    omega
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.late_mem_K
  obtain ⟨eK⟩ := hz₀.nonempty_equiv
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  obtain ⟨v, hv, hord, hvN⟩ := d.r9_vdata
  obtain ⟨hεv, hρv⟩ := d.r9_eps_v c8 hu huK eK hFodd hKop h4 hv hord hvN
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.to_le inf_le_left
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hRT : R ≤ T := le_inf d.hRS (d.hR.1.trans Subgroup.le_normalizer)
  have hR'T : R' ≤ T := le_inf d.hR'S (d.hR'.1.trans d.late_K'_le)
  have hVT : V ≤ T := le_inf d.hVS (d.hVW.trans d.late_W_le_N_K)
  have hvT : v ∈ T := hVT hvV
  have hRp : ∀ y ∈ T, phiG K eK y = 1 → y ∈ R' := fun y hyT hy1 =>
    d.r9_cStar_S c8 hu huK hyT.1 ((phiG_eq_one_iff hyT.2).mp hy1)
  have hRp' : ∀ y ∈ R', phiG K eK y = 1 := fun y hy =>
    (phiG_eq_one_iff (hTN (hR'T hy))).mpr (d.r9_K'_le_cStar (d.hR'.1 hy))
  have hRR'V_le_X : R ⊔ R' ⊔ V ≤ X :=
    sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX
  have hψker : ∀ x ∈ T, psi hKop K eK v x = 1 → x ∈ X := fun x hxT hψ =>
    hRR'V_le_X (mem_of_psi_eq_one hFodd h4 hT2 hTN hRT d.hR hRp hvV hvT hεv hxT hψ)
  have hψone : ∀ x ∈ (S : Subgroup G) ⊓ X, psi hKop K eK v x = 1 := by
    intro x hx
    have hx' : x ∈ R ⊔ R' ⊔ V := (d.late_SX c3).symm ▸ hx
    exact psi_eq_one_of_mem hρv hεv hTN d.hR.1 hRT hR'T hRp' hvT hv hx'
  have hXT : ∀ x ∈ T, x ∈ X → psi hKop K eK v x = 1 := fun x hxT hxX => hψone x ⟨hxT.1, hxX⟩
  refine ⟨{ toFun := fun x => psi hKop K eK v (x : G)
            map_one' := psi_one v
            map_mul' := fun x y => psi_mul hρv (hTN x.2) (hTN y.2) }, fun x => ?_⟩
  exact ⟨fun h => hψker x x.2 h, fun h => hXT x x.2 h⟩


theorem Std20.y_comm_T (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) {x y : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))
    (hy : y ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) :
    ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨ψ, hψ⟩ := d.y_psi c3 c8
  have h1 : ψ ⁅(⟨x, hx⟩ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))),
      (⟨y, hy⟩ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)))⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm _ _ _
  have h2 := (hψ _).mp h1
  simpa [commutatorElement_def] using h2


end Psi

end CFSG.ClassicalInvolution.Asc77.T3CII
