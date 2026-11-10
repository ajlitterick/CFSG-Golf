module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerPSL

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Matrix
open CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem isComponentOf_map_block {H : Type*} {T : Type} [Group H] [Group T] (π : H →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) (A : H) (B : Subgroup H)
    (hBq : CFSG.IsQuasisimple ↥B) (hBC : B ≤ Subgroup.centralizer ({A} : Set H))
    (hBnorm : ∀ g ∈ Subgroup.centralizer ({A} : Set H), ∀ f ∈ B, g * f * g⁻¹ ∈ B) :
    IsComponentOf (Subgroup.centralizer ({π A} : Set T)) (B.map π) := by
  have hBnc : ¬ B ≤ π.ker := fun hle => not_le_center_of_isQuasisimple hBq (hle.trans hker)
  set D₀ : Subgroup T := B.map π with hD₀
  have hD₀q : CFSG.IsQuasisimple ↥D₀ := CFSG.LocalCores.isQuasisimple_map hBq π hBnc
  set CA : Subgroup H := Subgroup.centralizer ({A} : Set H) with hCA
  set C0 : Subgroup T := CA.map π with hC0
  set Cx : Subgroup T := Subgroup.centralizer ({π A} : Set T) with hCx
  have hC0Cx : C0 ≤ Cx := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g * A = A * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hg']
  have hD₀C0 : D₀ ≤ C0 := Subgroup.map_mono hBC
  have hconj1 : ∀ g ∈ Cx, ∀ h ∈ C0, g * h * g⁻¹ ∈ C0 := by
    intro g hg h hh
    obtain ⟨G, rfl⟩ := hπ g
    obtain ⟨H', hH', rfl⟩ := hh
    refine ⟨G * H' * G⁻¹, ?_, by simp [map_mul, map_inv]⟩
    refine conj_mem_centralizer_of_commutator_central ?_ hH'
    refine hker (MonoidHom.mem_ker.mpr ?_)
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hconj0 : ∀ g ∈ C0, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀ := by
    intro g hg d hd
    obtain ⟨H', hH', rfl⟩ := hg
    obtain ⟨b₀, hb₀, rfl⟩ := hd
    exact ⟨H' * b₀ * H'⁻¹, hBnorm _ hH' _ hb₀, by simp [map_mul, map_inv]⟩
  have hCxN : Cx ≤ Subgroup.normalizer (C0 : Set T) := fun g hg =>
    mem_normalizer_of_forall_conj (hconj1 g hg) (fun x hx => by
      simpa using hconj1 g⁻¹ (Cx.inv_mem hg) x hx)
  refine ⟨hD₀C0.trans hC0Cx, hD₀q, ?_⟩
  have hD1C1 : D₀.subgroupOf Cx ≤ C0.subgroupOf Cx := fun g hg => hD₀C0 hg
  have hn1 : (C0.subgroupOf Cx).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC0Cx]
    exact hCxN
  have hn2 : ((D₀.subgroupOf Cx).subgroupOf (C0.subgroupOf Cx)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1C1]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgC0 : (g : T) ∈ C0 := hg
    constructor
    · intro hh
      exact hconj0 _ hgC0 _ hh
    · intro hh
      have := hconj0 _ (C0.inv_mem hgC0) _ hh
      exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
  exact Subgroup.IsSubnormal.trans hD1C1 hn2.isSubnormal hn1.isSubnormal

theorem exists_component_of_block {H : Type*} {T : Type} [Group H] [Group T] (π : H →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) (A : H) (B : Subgroup H)
    (hBq : CFSG.IsQuasisimple ↥B) (hBC : B ≤ Subgroup.centralizer ({A} : Set H))
    (hBnorm : ∀ g ∈ Subgroup.centralizer ({A} : Set H), ∀ f ∈ B, g * f * g⁻¹ ∈ B) :
    ∃ D : Subgroup T, CFSG.IsQuasisimple ↥D ∧ D ≤ Subgroup.centralizer ({π A} : Set T) ∧
      (D.subgroupOf (Subgroup.centralizer ({π A} : Set T))).IsSubnormal :=
  let h := isComponentOf_map_block π hπ hker A B hBq hBC hBnorm
  ⟨_, h.2.1, h.1, h.2.2⟩

theorem squarefree_minpoly_toLin'_of_pow_scalar {n p : ℕ} {K : Type} [Field K] (hpK : (p : K) ≠ 0)
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) := by
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p = algebraMap K (Matrix (Fin n) (Fin n) K) c := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  have haeval : Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
    have hX : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) =
        Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
  exact KCPrimary.squarefree_minpoly_of_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree haeval


open CFSG.Blueprint CFSG.Assembly.LowTwoRank in
theorem statedClassicalModel_of_lieModel_classical {T : Type} [Group T] {t : StatedLieTag}
    (ht : t ∈ classicalTags) {n p f : ℕ} (h : LieModel T t n p f) :
    StatedClassicalModel T t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

end CFSG.RankThree.PartOne
