module

public import CFSG.CharacterTheory.DihedralTIFusion.DualOrbits
public import CFSG.CharacterTheory.Blocks.NormTwo
public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.OddOrderBasics.Induction

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed TwoRankLowerBound.Helpers BrauerThirdMainTheorem.Helpers

variable {N : Type} [Group N] [Fintype N] {K : Subgroup N} [K.Normal]

theorem conjugateNormalCharacter_eq_iff_mem (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {μ : K → ℂ}
    (hμ : μ ∈ BlocksIrr K \ {1}) (a b : N) :
    conjugateNormalCharacter K μ a = conjugateNormalCharacter K μ b ↔ a⁻¹ * b ∈ K := by
  rw [conjugateNormalCharacter_eq_iff, QuotientGroup.eq, mem_characterInertiaSubgroup_iff,
    conjugateNormalCharacter_eq_self_iff hab hfree hμ.1 hμ.2]

theorem sum_conj_out_eq_sum_orbit (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {μ : K → ℂ}
    (hμ : μ ∈ BlocksIrr K \ {1}) :
    ∑ q : N ⧸ K, conjugateNormalCharacter K μ (Quotient.out q) =
        ∑ ν ∈ Finset.univ.image (conjugateNormalCharacter K μ), ν ∧
      (Finset.univ.image (conjugateNormalCharacter K μ)).card = K.index := by
  set f : N ⧸ K → K → ℂ := fun q => conjugateNormalCharacter K μ (Quotient.out q) with hf
  have hinj : Function.Injective f := by
    intro q q' h
    have h2 : ((Quotient.out q : N) : N ⧸ K) = (Quotient.out q' : N) :=
      QuotientGroup.eq.mpr ((conjugateNormalCharacter_eq_iff_mem hab hfree hμ _ _).mp h)
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  have himage : Finset.univ.image (conjugateNormalCharacter K μ) = Finset.univ.image f := by
    ext ν
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), (conjugateNormalCharacter_eq_iff_mem hab hfree hμ _ _).mpr
        (QuotientGroup.eq.mp (QuotientGroup.out_eq' _))⟩
    · rintro ⟨q, rfl⟩
      exact ⟨Quotient.out q, rfl⟩
  rw [himage, Finset.sum_image fun q _ q' _ h => hinj h, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact ⟨rfl, rfl⟩

theorem inner_induced_induced (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {μ ν : K → ℂ}
    (hμ : μ ∈ BlocksIrr K \ {1}) (hν : ν ∈ BlocksIrr K \ {1}) :
    BlocksInnerProduct (inducedFunction K μ) (inducedFunction K ν) =
      if μ ∈ Set.range (conjugateNormalCharacter K ν) then 1 else 0 := by
  have h := (OddOrderBasics.normal_subgroup_induced_inner_products K (fun q => Quotient.out q)
    QuotientGroup.out_eq' μ ν hμ.1 hν.1).2.1
  rw [h]
  split_ifs with hmem
  · obtain ⟨n₀, hn₀⟩ := hmem
    have hfilter : (Finset.univ.filter fun q : N ⧸ K =>
        μ = conjugateNormalCharacter K ν (Quotient.out q)) = {(n₀ : N ⧸ K)} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [← hn₀, conjugateNormalCharacter_eq_iff_mem hab hfree hν, ← QuotientGroup.eq,
        QuotientGroup.out_eq', eq_comm]
    rw [hfilter, Finset.card_singleton, Nat.cast_one]
  · have hfilter : (Finset.univ.filter fun q : N ⧸ K =>
        μ = conjugateNormalCharacter K ν (Quotient.out q)) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hmem ⟨_, h.symm⟩
    rw [hfilter, Finset.card_empty, Nat.cast_zero]

theorem induced_nontrivial_character (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {μ : K → ℂ}
    (hμ : μ ∈ BlocksIrr K \ {1}) :
    inducedFunction K μ ∈ BlocksIrr N \ {1} ∧ inducedFunction K μ 1 = K.index ∧
      (∀ n ∉ K, inducedFunction K μ n = 0) ∧
      (fun k : K => inducedFunction K μ k) =
        ∑ ν ∈ Finset.univ.image (conjugateNormalCharacter K μ), ν ∧
      (Finset.univ.image (conjugateNormalCharacter K μ)).card = K.index := by
  have : IsMulCommutative K := hab
  have hdeg : inducedFunction K μ 1 = K.index := by
    rw [(OddOrderBasics.induced_class_function_identities K).2.2.1,
      (blocksIrr_linear hμ.1).1, mul_one]
  have hnorm : BlocksInnerProduct (inducedFunction K μ) (inducedFunction K μ) = 1 := by
    rw [inner_induced_induced hab hfree hμ hμ, ite_eq_left ⟨1, conjugateNormalCharacter_one K μ⟩]
  have hvirt : inducedFunction K μ ∈ BlocksVChar N :=
    CFSG.inducedFunction_mem_blocksVChar K (AddSubgroup.subset_closure hμ.1)
  have hirr : inducedFunction K μ ∈ BlocksIrr N := by
    obtain ⟨χ, hχ | hχ⟩ := blocksVChar_norm_one_signed_irreducible hvirt hnorm
    · rw [hχ]
      exact χ.2
    · exfalso
      have hpos := blocksIrr_identity_re_pos χ
      have h1 := congrArg Complex.re (congrFun hχ 1)
      rw [hdeg, Pi.neg_apply, Complex.neg_re, Complex.natCast_re] at h1
      have : (0 : ℝ) ≤ K.index := Nat.cast_nonneg _
      linarith
  have hprincipal : inducedFunction K μ ≠ 1 := by
    intro h1
    have hrec := blocksInnerProduct_inducedFunction_left K μ 1 (fun _ _ => rfl)
    rw [h1, Semidihedral.Principal.blocksInnerProduct_of_mem_blocksIrr (f := (1 : N → ℂ))
      (g := 1) (trivial_mem_irr N) (trivial_mem_irr N), ite_eq_left rfl] at hrec
    have h0 : BlocksInnerProduct μ (fun h : K => (1 : N → ℂ) h) = 0 := by
      rw [show (fun h : K => (1 : N → ℂ) h) = (1 : K → ℂ) from rfl,
        Semidihedral.Principal.blocksInnerProduct_of_mem_blocksIrr (g := (1 : K → ℂ)) hμ.1
          (trivial_mem_irr K)]
      exact ite_eq_right fun h => hμ.2 h
    rw [h0] at hrec
    exact one_ne_zero hrec
  obtain ⟨hsum, hcard⟩ := sum_conj_out_eq_sum_orbit hab hfree hμ
  refine ⟨⟨hirr, hprincipal⟩, hdeg,
    (OddOrderBasics.induced_class_function_identities K).2.2.2 inferInstance μ, ?_, hcard⟩
  rw [(OddOrderBasics.normal_subgroup_induced_inner_products K (fun q => Quotient.out q)
    QuotientGroup.out_eq' μ μ hμ.1 hμ.1).1, hsum]


end CFSG.DihedralTIFusion
