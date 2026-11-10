module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Sporadic.Bridge CFSG.Open TauCeti

section Trick

variable {P N : Type*} [Group P] [Group N]

theorem injective_of_isSimpleGroup_of_ne_one [IsSimpleGroup P] (φ : P →* N) (h : φ ≠ 1) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · exact hk
  · exact absurd (MonoidHom.ext fun x => MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)) h

theorem injective_of_isSimpleGroup_of_surjective [IsSimpleGroup P] [Nontrivial N] (φ : P →* N)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  refine injective_of_isSimpleGroup_of_ne_one φ fun h => ?_
  obtain ⟨y, hy⟩ := exists_ne (1 : N)
  obtain ⟨x, rfl⟩ := hφ y
  exact hy (by rw [h]; rfl)

@[expose] noncomputable def mulEquivOfSurjective [IsSimpleGroup P] [Nontrivial N] (φ : P →* N)
    (hφ : Function.Surjective φ) : P ≃* N :=
  MulEquiv.ofBijective φ ⟨injective_of_isSimpleGroup_of_surjective φ hφ, hφ⟩

end Trick

theorem nontrivial_of_two_le_natCard {J : Type*} {k : ℕ} (hk : 2 ≤ k) (h : k ≤ Nat.card J) :
    Nontrivial J :=
  have := Nat.finite_of_card_ne_zero (show Nat.card J ≠ 0 by omega)
  Finite.one_lt_card_iff_nontrivial.1 (by omega)

section Presentation

theorem nonempty_mulEquiv_of_relators (P : GroupPresentation) [IsSimpleGroup P.Group] {N : Type*}
    [Group N] [Nontrivial N] (img : ℕ → N) (hrel : ∀ v ∈ P.relatorLetters, wordProd img v = 1)
    (hgen : Subgroup.closure (img '' Set.Iio P.generatorCount) = ⊤) :
    Nonempty (P.Group ≃* N) := by
  have hsurj : Function.Surjective (presHom P img hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨presGen P i, presHom_presGen P img hrel hi⟩
  exact ⟨mulEquivOfSurjective _ hsurj⟩

theorem nonempty_mulEquiv_of_relators_two (P : GroupPresentation) [IsSimpleGroup P.Group]
    (hP : P.generatorCount = 2) {N : Type*} [Group N] [Nontrivial N] {x y : N}
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (fun i => if i = 0 then x else y) v = 1)
    (hgen : Subgroup.closure ({x, y} : Set N) = ⊤) : Nonempty (P.Group ≃* N) := by
  refine nonempty_mulEquiv_of_relators P (fun i => if i = 0 then x else y) hrel ?_
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, Set.mem_Iio.2 (by omega), by simp⟩
  · exact Subgroup.subset_closure ⟨1, Set.mem_Iio.2 (by omega), by simp⟩

end Presentation

section Witness


end Witness

end CFSG.QuasithinUnique.SQTK
