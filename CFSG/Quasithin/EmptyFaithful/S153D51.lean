module

public import CFSG.Quasithin.EmptyFaithful.S153D50

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement


namespace S153D

section Generic

variable {G : Type} [Group G]

theorem normalizer_conjSub (g : G) (W : Subgroup G) :
    Subgroup.normalizer ((B6.conjSub g W : Subgroup G) : Set G) =
      B6.conjSub g (Subgroup.normalizer (W : Set G)) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have := h (g * z * g⁻¹)
    simp only [B6.mem_conjSub] at this
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e2 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h z
    simp only [B6.mem_conjSub]
    have := h (g⁻¹ * z * g)
    have e2 : g⁻¹ * (x * z * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e2]
    exact this

theorem isParabolic2_conjSub {L P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hP : IsParabolic2 L P) :
    IsParabolic2 L (B6.conjSub y P) := by
  obtain ⟨hPL, S', hS', hNS'⟩ := hP
  refine ⟨?_, B6.conjSub y S', ?_, ?_⟩
  · have := (B6.conjSub y).monotone hPL
    rwa [B6.conjSub_eq_self hy] at this
  · have := B6.isSylowTwoOf_conjSub hS' y
    rwa [B6.conjSub_eq_self hy] at this
  · rw [normalizer_conjSub]
    have h1 : L ⊓ B6.conjSub y (Subgroup.normalizer (S' : Set G)) =
        B6.conjSub y (L ⊓ Subgroup.normalizer (S' : Set G)) := by
      rw [OrderIso.map_inf, B6.conjSub_eq_self hy]
    rw [h1]
    exact (B6.conjSub y).monotone hNS'

theorem isMaxParabolic2_conjSub {L P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hP : IsMaxParabolic2 L P) :
    IsMaxParabolic2 L (B6.conjSub y P) := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  have hy' : y⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hy
  have hinv : ∀ X : Subgroup G, B6.conjSub y⁻¹ (B6.conjSub y X) = X := fun X => by
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  refine ⟨isParabolic2_conjSub hy hpar, fun h => hne ?_, fun Q hQ hQne hle => ?_⟩
  · have := congrArg (B6.conjSub y⁻¹) h
    rwa [hinv, B6.conjSub_eq_self hy'] at this
  · have h1 : P ≤ B6.conjSub y⁻¹ Q := by
      have := (B6.conjSub y⁻¹).monotone hle
      rwa [hinv] at this
    have h2 : B6.conjSub y⁻¹ Q = P := by
      refine hmax _ (isParabolic2_conjSub hy' hQ) (fun hQL => hQne ?_) h1
      have := congrArg (B6.conjSub y) hQL
      rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one, B6.conjSub_eq_self hy] at this
    have := congrArg (B6.conjSub y) h2
    rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at this

theorem le_normalizer_of_two {Yp P₁ P₂ : Subgroup G} (hYp : oTwoUpper Yp = Yp) (hne : P₁ ≠ P₂)
    (h1 : ∀ y ∈ Yp, B6.conjSub y P₁ = P₁ ∨ B6.conjSub y P₁ = P₂)
    (h2 : ∀ y ∈ Yp, B6.conjSub y P₂ = P₁ ∨ B6.conjSub y P₂ = P₂) :
    Yp ≤ Subgroup.normalizer (P₁ : Set G) := by
  rw [← hYp]
  refine oTwoUpper_le_of_pow_mem (fun x hx => ⟨1, ?_⟩)
  have hxx : B6.conjSub (x * x) P₁ = P₁ := by
    rw [B6.conjSub_mul]
    rcases h1 x hx with e | e
    · rw [e, e]
    · rcases h2 x hx with e' | e'
      · rw [e, e']
      · exact absurd ((B6.conjSub x).injective (e.trans e'.symm)) hne
  have : x ^ 2 ^ 1 = x * x := by rw [pow_one, pow_two]
  rw [this]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxx

section Finite

variable [Finite G]

theorem isSylowTwoOf_inf_of_isSubnormal {T H L : Subgroup G} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := B6.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

theorem le_of_normal_sylow {X Q D : Subgroup G} (hQ : IsSylowTwoOf Q X)
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hD : IsPGroup 2 D) (hDX : D ≤ X) : D ≤ Q := by
  obtain ⟨Q', hQ', hDQ'⟩ := B6.exists_isSylowTwoOf_ge hD hDX
  obtain ⟨g, hg, hgQ⟩ := B6.isSylowTwoOf_exists_conj hQ hQ'
  rw [hgQ, B6.conjSub_eq_self (hQn hg)] at hDQ'
  exact hDQ'

end Finite

end Generic

section Main


end Main

end S153D

end CFSG.Quasithin
