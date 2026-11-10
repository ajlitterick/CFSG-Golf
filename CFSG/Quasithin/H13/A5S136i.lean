module

public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section Gen

variable {G : Type} [Group G]


theorem le_normalizer_oTwoRes {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    H ≤ Subgroup.normalizer (oTwoRes N : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ x ∈ oTwoRes N,
      g * x * g⁻¹ ∈ oTwoRes N := by
    intro g hg x hx
    have hx' : x ∈ Subgroup.closure {y | y ∈ N ∧ ∃ m : ℕ, Odd m ∧ y ^ m = 1} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxN, m, hm, hxm⟩ := hx
      exact Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxN, m, hm,
        by rw [conj_pow, hxm, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact (oTwoRes N).mul_mem ihx ihy
    | inv x _ ih =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact (oTwoRes N).inv_mem ih
  intro h hh
  refine B6.mem_normalizer_of_forall_mem (key h (hHN hh)) fun x hx => ?_
  simpa using key h⁻¹ (Subgroup.inv_mem _ (hHN hh)) x hx

end Gen

namespace Setting


end Setting

end CFSG.Quasithin.H13.A5
