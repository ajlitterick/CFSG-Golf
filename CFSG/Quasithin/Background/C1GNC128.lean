
module

public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C1GN

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := by
  refine le_inf (thompsonJ_le T) ?_
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf (thompsonJ T) he).2 j hj).symm

omit [Finite G] in
theorem conjSub_le_of_mem {M K : Subgroup G} {t : G} (ht : t ∈ M) (hK : K ≤ M) :
    B6.conjSub t K ≤ M := by
  intro x hx
  have h : t⁻¹ * x * t ∈ K := B6.mem_conjSub.1 hx
  have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ M := M.mul_mem (M.mul_mem ht (hK h)) (M.inv_mem ht)
  have h3 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
  rwa [h3] at h2

omit [Finite G] in
theorem conjClosure_eq_iSup {T : Subgroup G} {r : ℕ} (K : Fin r → Subgroup G)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j)
    (htrans : ∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j) (i : Fin r) :
    conjClosure (K i) T = ⨆ j, K j := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨j, hj⟩ := hperm h hh i
    have h1 : h * z * h⁻¹ ∈ B6.conjSub h (K i) := by
      rw [B6.mem_conjSub]
      have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      rwa [this]
    rw [hj] at h1
    exact Subgroup.mem_iSup_of_mem j h1
  · refine iSup_le fun j => ?_
    obtain ⟨t, ht, htj⟩ := htrans i j
    intro x hx
    rw [← htj, B6.mem_conjSub] at hx
    have h1 := mem_conjClosure ht hx
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [h2] at h1

omit [Finite G] in
theorem isChiBlock_of_isChi0Block {X U K : Subgroup G} (hX : IsBlock2 X K) (h : IsChi0Block U K) :
    IsChiBlock X K := by
  refine ⟨hX, ?_⟩
  rcases h.2 with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨3, by decide, le_rfl, h⟩
  · exact Or.inr ⟨5, by decide, by norm_num, h⟩

omit [Finite G] in
theorem commutator_le_of_le_normalizer {L J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (L : Set G)) : ⁅L, J⁆ ≤ L := by
  refine Subgroup.commutator_le.2 fun l hl j hj => ?_
  have h1 : j * l⁻¹ * j⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hJ hj) l⁻¹).1 (L.inv_mem hl)
  have h2 : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact L.mul_mem hl h1

theorem isTwoReducedIn_VZ {X T : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X) :
    IsTwoReducedIn X (VZ T X) :=
  isTwoReducedIn_conjClosure_of_sylowIn hT.1 hT.2.1 hT.2.2 hX le_rfl

@[expose] def chiBlocksOutside (X T M : Subgroup G) : Set (Subgroup G) :=
  {L | IsChiBlock X L ∧ ⁅L, thompsonJ T⁆ = L ∧ ¬ L ≤ M}


end C1GN

end CFSG.Quasithin
