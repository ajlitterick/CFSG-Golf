module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Chains
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4Torus

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps

theorem f4FrameCandidates_orthogonal : ∀ L ∈ f4FrameCandidates,
    (∀ p ∈ L, 24 ≤ p ∧ p < 48) ∧
      (L.map (orbitCertRoot .F4)).Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel


variable {K : Type} [Field K] [CharP K 2]

theorem commute_f4x_of_f4CollComm_eq_nil {p q : ℕ} (hp : 24 ≤ p ∧ p ≤ 47)
    (hq : 24 ≤ q ∧ q ≤ 47) (h : p ≠ q → f4CollComm p q = []) (s t : K) :
    Commute (f4x K p s) (f4x K q t) := by
  by_cases hpq : p = q
  · subst hpq
    change f4x K p s * f4x K p t = f4x K p t * f4x K p s
    rw [f4x, f4x, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have h0 := h hpq
    rw [f4CollComm_eq hp.1 hp.2 hq.1 hq.2 hpq, List.map_eq_nil_iff] at h0
    have hc := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K p q hp.1 hp.2 hq.1 hq.2 hpq s t
    rw [h0, List.map_nil, List.prod_nil] at hc
    exact commutatorElement_eq_one_iff_commute.1 hc


variable [Finite K]

theorem exists_conj_of_mem_f4FrameCandidates_of_ne_zero {L : List ℕ}
    (hL : L ∈ f4FrameCandidates) (e : (Fin Tag.F4.rank → ℤ) → K)
    (he : ∀ p ∈ L, e (orbitCertRoot .F4 p) ≠ 0) :
    ∃ g ∈ adjointGroup .F4 K,
      g * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * g⁻¹ = f4x K 47 1 ∨
      g * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * g⁻¹ =
        f4x K 47 1 * f4x K 44 1 ∨
      g * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * g⁻¹ =
        f4x K 41 1 * f4x K 45 1 := by
  obtain ⟨hpos, horth⟩ := f4FrameCandidates_orthogonal L hL
  have hF : ∀ σ ∈ L.map (orbitCertRoot .F4), IsRoot .F4 σ := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hσ
    exact isRoot_decodeVec_witness
      (by rw [show Tag.F4.witnesses.roots.length = 48 from rfl]; exact (hpos p hp).2)
  have hc : ∀ σ ∈ L.map (orbitCertRoot .F4), e σ ≠ 0 := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hσ
    exact he p hp
  obtain ⟨h, hhC, -, -, hh⟩ := exists_torus_conj_frame_prod noG2_F4 hF horth e hc
  simp only [List.map_map] at hh
  obtain ⟨g, hg, hgL⟩ := exists_conj_of_mem_f4FrameCandidates (K := K) hL
  have key : (g * h) * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * (g * h)⁻¹ =
      g * f4CollProd K L * g⁻¹ := by
    have hh' : h * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * h⁻¹ =
        f4CollProd K L := hh
    rw [← hh']
    group
  exact ⟨g * h, mul_mem hg hhC, by rw [key]; exact hgL⟩

theorem exists_mulAut_of_mem_f4FrameCandidates_of_ne_zero {L : List ℕ}
    (hL : L ∈ f4FrameCandidates) (e : (Fin Tag.F4.rank → ℤ) → K)
    (he : ∀ p ∈ L, e (orbitCertRoot .F4 p) ≠ 0)
    (hx : (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod ∈ adjointGroup .F4 K) :
    ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩,
        ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩} : Set (adjointGroup .F4 K)),
      ψ s = ⟨(L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod, hx⟩ := by
  obtain ⟨g, hg, h⟩ := exists_conj_of_mem_f4FrameCandidates_of_ne_zero hL e he
  have key : ∀ y : adjointGroup .F4 K,
      (g * (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod * g⁻¹ = y) →
      MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K)⁻¹ y =
        ⟨(L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod, hx⟩ := by
    intro y hy
    apply Subtype.ext
    simp only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hy]
    group
  refine ⟨MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K)⁻¹, ?_⟩
  rcases h with h | h | h
  · exact ⟨_, Set.mem_insert _ _, key _ h⟩
  · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _), key _ h⟩
  · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), key _ h⟩


end CFSG.SeitzReduction
