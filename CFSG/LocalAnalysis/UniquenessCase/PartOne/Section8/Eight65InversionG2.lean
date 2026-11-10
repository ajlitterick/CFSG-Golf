module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QHeis
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.AGLEmbedding.KFactProofs.G2Q
open scoped commutatorElement

section Frobenius

variable {L : Type} [Field L]

theorem nw0_sq : (nw0 : ModGL .G2 L) ^ 2 = 1 := by
  have h : (nw0 : ModGL .G2 L) = (n0 * n1) ^ 3 := by
    rw [nw0, yq, pow_succ, pow_two]
    group
  calc (nw0 : ModGL .G2 L) ^ 2 = ((n0 * n1) ^ 3) ^ 2 := by rw [h]
    _ = ((n0 * n1) ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]
    _ = (yq : ModGL .G2 L) ^ 3 := by rw [show (n0 * n1) ^ 2 = (yq : ModGL .G2 L) from rfl]
    _ = 1 := yq_pow_three

end Frobenius

variable {L : Type} [Field L]


variable {L : Type} [Field L]


theorem tz_mul_comm (s t s' t' : Lˣ) :
    (tz s t : ModGL .G2 L) * tz s' t' = tz s' t' * tz s t := by
  rw [tz_mul, tz_mul, mul_comm s s', mul_comm t t']

theorem yq_fix_tz_center (ω : Lˣ) (hω3 : ω ^ 3 = 1) :
    (yq : ModGL .G2 L) * tz 1 ω⁻¹ * yq⁻¹ = tz 1 ω⁻¹ := by
  have hω2 : ω ^ 2 = ω⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← pow_succ', show 2 + 1 = 3 by norm_num, hω3])
  have h3 : (ω⁻¹) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  have h2 : ((ω⁻¹) ^ 2)⁻¹ = ω⁻¹ := by
    rw [inv_pow, inv_inv, hω2]
  rw [yq_tz]
  congr 1
  · simp [h3]
  · simpa using h2

theorem extSub_eq_closure {G : Type} [Group G] {T : Subgroup G} {y : G} (hExt : Ext3 T y) :
    extSub hExt = Subgroup.closure (T ∪ {y}) := by
  apply le_antisymm
  · intro g hg
    rw [mem_extSub_iff hExt] at hg
    obtain ⟨t, ht, k, rfl⟩ := hg
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_union_left _ ht))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton y))) k)
  · refine (Subgroup.closure_le _).2 ?_
    intro g hg
    rw [Set.mem_union] at hg
    rcases hg with hg | hg
    · exact le_extSub hExt hg
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact y_mem_extSub hExt

theorem exists_rational_conj_fixed (K : Type) [Field K] [Finite K] :
    ∃ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) ∧
      ∀ n ∈ adjointGroup .G2 (AlgebraicClosure K),
        ∃ g ∈ adjointGroup .G2 (AlgebraicClosure K),
          Units.map (entrywiseHom F) g = g * n ∧
          ∀ s ∈ adjointGroup .G2 (AlgebraicClosure K),
            n * Units.map (entrywiseHom F) s * n⁻¹ = s →
            g * s * g⁻¹ ∈ (adjointGroup .G2 K).map
              (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  refine ⟨F, hF, fun n hn => ?_⟩
  obtain ⟨S₁, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .G2
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hn⟩
  set g : ModGL .G2 L := (g₀ : ModGL .G2 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  refine ⟨g, g₀.2, hFg, fun s hs hns => ?_⟩
  have hfix := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    (τ := .G2) (Or.inl rfl) K (AlgebraicClosure K) F hF).1
  rw [← hfix]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g₀.2 hs) (inv_mem g₀.2), ?_⟩
  change Units.map (entrywiseHom F) (g * s * g⁻¹) = g * s * g⁻¹
  rw [map_mul, map_mul, map_inv, hFg]
  calc g * n * Units.map (entrywiseHom F) s * (g * n)⁻¹
      = g * (n * Units.map (entrywiseHom F) s * n⁻¹) * g⁻¹ := by group
    _ = g * s * g⁻¹ := by rw [hns]


section Concrete


end Concrete

section Specialisations


end Specialisations


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
