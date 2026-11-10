module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndNode
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.RankThree.CALinearPlane
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem tpta_isElemAbelian_map_ggInducedAut {L : Type} [Group L] {R : Type} [Group R]
    {p : ℕ} (θ : L ⧸ Subgroup.center L ≃* R) {E : Subgroup (MulAut L)}
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map (ggInducedAut θ)) :=
  TableB.isElemAbelian_map hE (ggInducedAut θ)

theorem tpta_eq_zpowers_of_card_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hE : IsElemAbelian p E)
    (hcard : Nat.card E ≤ p) : E = Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := hE.2 y hy
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hzy : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.mpr hy
  have hcardz : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hzy (by rw [hcardz]; exact hcard)).symm


theorem tpta_fixing_coordBlockSL_le_zpowers
    {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hd : 4 ≤ d) (hpd : Nat.Coprime p d)
    {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    {a : MulAut L'} (ha : a ∈ A)
    {i₀ : Fin d} {t : Fin d → K}
    (ht0 : ∀ j, j ≠ i₀ → t j ≠ t i₀) (ht1 : ∀ i j, i ≠ i₀ → j ≠ i₀ → t i = t j)
    {D : SpecialLinearGroup (Fin d) K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (hDp : D ^ p = 1)
    (hact : ∀ s, a (φ s) = φ (D * s * D⁻¹))
    (hdiag : ∀ a' ∈ A, ∃ D' : SpecialLinearGroup (Fin d) K,
      (∃ t' : Fin d → K, (D' : Matrix (Fin d) (Fin d) K) = diagonal t') ∧ D' ^ p = 1 ∧
      ∀ s, a' (φ s) = φ (D' * s * D'⁻¹))
    (j₁ : Fin d) (hj₁ : j₁ ≠ i₀)
    (hprim : IsPrimitiveRoot (t i₀ / t j₁) p) :
    ∀ a' ∈ A, (∀ j ∈ (coordBlockSL K ({i₀}ᶜ : Finset (Fin d))).map φ, a' j = j) →
      a' ∈ Subgroup.zpowers a := by
  intro a' ha' hfix
  obtain ⟨D', ⟨t', hD'⟩, hD'p, ha'act⟩ := hdiag a' ha'
  have hcomm : ∀ s ∈ coordBlockSL K ({i₀}ᶜ : Finset (Fin d)), s * D' = D' * s := by
    intro s hs
    have h1 : a' (φ s) = φ s := hfix _ (Subgroup.mem_map_of_mem φ hs)
    rw [ha'act] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (TypeA.mem_centralizer_of_apply_eq hφker hpd hD'p h1)
  have hconst := TypeA.const_of_commute_coordBlockSL (i₀ := i₀) hD' hcomm
  have ht'p : ∀ i, t' i ^ p = 1 := by
    intro i
    have h1 : (D' : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hD'p]; rfl
    rw [hD', diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  have ht'j1 : t' j₁ ≠ 0 := fun h => by
    have h1 := ht'p j₁
    rw [h, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  have htp : ∀ i, t i ^ p = 1 := by
    intro i
    have h1 : (D : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hDp]; rfl
    rw [hD, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  have htj1 : t j₁ ≠ 0 := fun h => by
    have h1 := htp j₁
    rw [h, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  have hkt' : (t' i₀ / t' j₁) ^ p = 1 := by
    rw [div_pow, ht'p, ht'p, div_one]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hkt'
  have hc : ∀ i, t' i = (t' j₁ / (t j₁) ^ k) * t i ^ k := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      have e1 : t' i₀ = t' j₁ * (t i₀ / t j₁) ^ k := by rw [hk]; field_simp
      rw [e1]
      change t' j₁ * (t i₀ / t j₁) ^ k = (t' j₁ / t j₁ ^ k) * t i₀ ^ k
      rw [div_pow]
      field_simp
    · rw [hconst i j₁ hi hj₁, ht1 i j₁ hi hj₁]
      change t' j₁ = (t' j₁ / t j₁ ^ k) * t j₁ ^ k
      field_simp
  have hDk : ((D ^ k : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => t i ^ k) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hD, diagonal_pow]; rfl
  have hconj : ∀ s, D' * s * D'⁻¹ = D ^ k * s * (D ^ k)⁻¹ := fun s =>
    TypeA.conj_eq_of_diagonal_smul (c := t' j₁ / (t j₁) ^ k) hD' hDk hc (by omega) s
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [zpow_natCast]
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  rw [TypeA.pow_act hact k s, ha'act, hconj]

end CFSG.StandardType

end
