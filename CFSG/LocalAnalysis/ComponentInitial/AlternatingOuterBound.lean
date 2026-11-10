module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_isomorphism {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    (∃ e : Outer G ≃* Outer H,
      ∀ α : MulAut G, e (α : Outer G) = (((f.symm.trans α).trans f : MulAut H) : Outer H)) ∧
      (Group.IsSolvable (Outer G) ↔ Group.IsSolvable (Outer H)) := by
  refine ⟨⟨OuterAutomorphisms.equivalence f, fun α => ?_⟩, ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · rfl
  · exact Group.isSolvable_of_surjective (OuterAutomorphisms.equivalence f).surjective
  · exact Group.isSolvable_of_surjective (OuterAutomorphisms.equivalence f).symm.surjective

theorem pow_le_ordProj_two {n k : ℕ} (hn : n ≠ 0) (h : 2 ^ k ∣ n) : 2 ^ k ≤ ordProj[2] n :=
  Nat.pow_le_pow_right two_pos ((Nat.prime_two.pow_dvd_iff_le_factorization hn).1 h)


end CFSG.LocalAnalysis.ComponentInitial
