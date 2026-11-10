module

public import CFSG.Timmesfeld.RootSubgroupKernel
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}


theorem exists_rootSubgroup_of_closed (hD : IsRootInvolutionSet D) {d : G}
    (hclosed : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∈ rootSet D d) :
    ∃ A : Subgroup G, (A : Set G) = insert 1 (rootSet D d) ∧ ∀ a ∈ A, a * a = 1 := by
  have hmul : ∀ x ∈ insert (1 : G) (rootSet D d), ∀ y ∈ insert (1 : G) (rootSet D d),
      x * y ∈ insert (1 : G) (rootSet D d) := by
    rintro x (rfl | hx) y (rfl | hy)
    · exact Or.inl (mul_one 1)
    · rw [one_mul]; exact Or.inr hy
    · rw [mul_one]; exact Or.inr hx
    · by_cases hxy : x = y
      · subst hxy; exact Or.inl (hD.mul_self_eq_one hx.1)
      · exact Or.inr (hclosed x hx y hy hxy)
  have hinv : ∀ x ∈ insert (1 : G) (rootSet D d), x⁻¹ ∈ insert (1 : G) (rootSet D d) := by
    rintro x (rfl | hx)
    · exact Or.inl inv_one
    · rw [hD.inv_eq hx.1]; exact Or.inr hx
  refine ⟨{ carrier := insert 1 (rootSet D d)
            mul_mem' := fun hx hy => hmul _ hx _ hy
            one_mem' := Or.inl rfl
            inv_mem' := fun hx => hinv _ hx }, rfl, ?_⟩
  rintro x (rfl | hx)
  · exact mul_one 1
  · exact hD.mul_self_eq_one hx.1

theorem ncard_rootSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g d : G) :
    (rootSet D (g * d * g⁻¹)).ncard = (rootSet D d).ncard := by
  rw [rootSet_conj hclass, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]

theorem ncard_rootSet_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) : (rootSet D e).ncard = (rootSet D d).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd he)
  exact ncard_rootSet_conj hclass g d

end CFSG.Timmesfeld
