module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Sections
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

namespace Red

theorem moves_all (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) (C : ComponentIndex K) : w • C ≠ C := by
  obtain ⟨j, rfl⟩ := R.orbit_eq hw hmove C
  intro h
  have h1 : w ^ (j + 1) • C₀ = w ^ j • C₀ := by
    rw [pow_succ', mul_smul]
    exact h
  have h2 := R.pow_smul_eq hw hmove h1
  have h3 : j + 1 ≡ j + 0 [MOD p] := h2
  have h4 := Nat.ModEq.add_left_cancel' j h3
  have h5 : p ∣ 1 := Nat.modEq_zero_iff_dvd.1 h4
  exact R.prime.one_lt.ne' (Nat.dvd_one.1 h5)

theorem card_comp (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) : Fintype.card (ComponentIndex K) = p := by
  have hwp : w ^ p = 1 := R.conf.elem.2 w hw
  have hbij : Function.Bijective (fun j : Fin p => w ^ (j : ℕ) • C₀) := by
    constructor
    · intro i j h
      have := R.pow_smul_eq hw hmove h
      rw [Nat.ModEq, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
      exact Fin.ext this
    · intro C
      obtain ⟨j, hj⟩ := R.orbit_eq hw hmove C
      refine ⟨⟨j % p, Nat.mod_lt _ R.prime.pos⟩, ?_⟩
      show w ^ (j % p) • C₀ = C
      rw [← pow_eq_pow_mod j hwp]
      exact hj
  rw [← Fintype.card_fin p]
  exact (Fintype.card_of_bijective hbij).symm

theorem exists_diag_section (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C : ComponentIndex K}
    (hmove : w • C ≠ C) :
    ∃ (U : Subgroup K) (f : U →* C.1), U ≤ centralizer ({w} : Set K) ∧
      Function.Surjective f := by
  let U : Subgroup K := centralizer ({w} : Set K) ⊓ layer K
  let f : U →* C.1 := (coord R.hZ C).comp (Subgroup.inclusion (inf_le_right : U ≤ layer K))
  refine ⟨U, f, inf_le_left, fun c => ?_⟩
  obtain ⟨y, hy, hwy, hcoord, -, -⟩ := R.exists_diag hw hmove c.2
  have hyw : y * w = w * y := (mul_inv_eq_iff_eq_mul.1 hwy).symm
  have hyU : y ∈ U := ⟨mem_centralizer_singleton_iff.2 hyw, hy⟩
  refine ⟨⟨y, hyU⟩, Subtype.ext ?_⟩
  have h0 := hcoord 0
  simp only [pow_zero, one_smul, one_mul, inv_one, mul_one] at h0
  exact h0

theorem involvedInSymm_comp (R : Red n p K P z D)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1))
    (hemb : CentralizerSectionEmbeds p D z) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) (C : ComponentIndex K) : InvolvedInSymm p C.1 := by
  haveI := R.fact
  have hall := R.moves_all hw hmove
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
  haveI := hsimple
  obtain ⟨U, f, hU, hf⟩ := R.exists_diag_section hw (hall C)
  obtain ⟨U', f', hU', hf'⟩ := hemb w hw (R.not_mem_zpowers hw (hall C)) C.1
    (dvd_card_comp R.core C) ⟨U, f, hU, hf⟩
  exact R.involvedInSymm_of_section hOut hw hall (R.card_comp hw hmove) hnonab
    (dvd_card_comp R.core C) U' hU' f' hf'


end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
