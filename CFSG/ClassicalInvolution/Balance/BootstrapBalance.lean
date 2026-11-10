module

public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.ToralBalanceFrame
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_isCentralInvolution {a z : G} {K : Subgroup G} (hKΩ : K ∈ Ω)
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G)) (hz : IsCentralInvolution K z)
    (hzC : z ∈ Subgroup.centralizer ({a} : Set G)) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨z, hzC⟩ * y = y * oddQuotMk a ⟨z, hzC⟩ := by
  have hzmem : oddQuotMk a ⟨z, hzC⟩ ∈ modOdd a K := oddQuotMk_mem_modOdd hz.mem hzC
  rcases hL with hL | ⟨-, hL⟩
  · exact hL K hKΩ hKC _ hzmem y hy
  · rcases hL K hKΩ hKC with h | h
    · rw [← h] at hy
      obtain ⟨k, hkK, rfl⟩ := hy
      have hkK' : (k : G) ∈ K := hkK
      have hzk : z * (k : G) = (k : G) * z := hz.central k hkK'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext hzk)
    · exact h _ hzmem y hy

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_mem_group (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω)
    (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {a : G} (ha : a ∈ T.group) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {f : G} (hf : f ∈ T.group)
    (hfC : f ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hmem : ∀ {z : G}, z ∈ T.group → z ∈ Subgroup.centralizer ({a} : Set G) := fun hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (T.comm_of_mem hz ha)
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : T.group ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    have hzA : z ∈ T.group := Subgroup.subset_closure hz
    refine ⟨⟨z, hmem hzA⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₁ (hcen T.le_centralizer₁)
        ⟨T.mem₁, T.ne_one₁, T.sq₁, fun k hk => (T.central₁ k hk).symm⟩ _ hL y hy).symm
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₂ (hcen T.le_centralizer₂)
        ⟨T.mem₂, T.ne_one₂, T.sq₂, fun k hk => (T.central₂ k hk).symm⟩ _ hL y hy).symm
    · exact (oddQuotMk_centralizes_of_isCentralInvolution hΩ₃ (hcen T.le_centralizer₃)
        ⟨T.mem₃, T.ne_one₃, T.sq₃, fun k hk => (T.central₃ k hk).symm⟩ _ hL y hy).symm
  obtain ⟨q, hq, hqf⟩ := hsub hf
  have hqe : q = ⟨f, hfC⟩ := Subtype.ext hqf
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm


end CFSG.ClassicalInvolution.Balance.Bootstrap
