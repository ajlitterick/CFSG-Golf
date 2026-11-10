module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusElements
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShort
import CFSG.LieType.Steinberg.Classical.SpecialLinear
import CFSG.LieType.Steinberg.Classical.SpinOdd
import CFSG.LieType.Steinberg.Classical.SpinPlus
import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg

section Models

variable {p : ℕ} [Fact p.Prime]

theorem exists_chevalleyExtras_model (t : StatedLieTag) (n f : ℕ)
    (hadm : StatedLieAdmissible t n p f)
    (ht : (t = .PSL ∧ 3 ≤ n) ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    ∃ x C O, ChevalleyExtras (modelUniv t n p f Fact.out).D (GaloisField p f) x C O := by
  rcases ht with ⟨rfl, hn3⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by omega
    obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (SpecialLinear.rootDatum m (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, SL.chevalleyExtras hm O _ (SL.commutatorFormula O)⟩
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    show ∃ x C O, ChevalleyExtras
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p f Fact.out).D
      (GaloisField p f) x C O
    rw [CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn]
    obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Spin.plusDatum n (GaloisField p f) hn).isFiniteType rfl
    exact ⟨_, _, O, SpinPlus.chevalleyExtras hn O _ (SpinPlus.commutatorFormula hn O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Minuscule.e6Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Minuscule.e6Datum_commutatorFormula (GaloisField p f) _
      (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E6) O
    exact ⟨_, C, O, Minuscule.e6_chevalleyExtras (GaloisField p f) O C hC⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Minuscule.e7Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Minuscule.e7Datum_commutatorFormula (GaloisField p f) _
      (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E7) O
    exact ⟨_, C, O, Minuscule.e7_chevalleyExtras (GaloisField p f) O C hC⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Adjoint.e8Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Adjoint.e8_commutatorFormula (GaloisField p f) O
    exact ⟨_, C, O, Adjoint.e8_chevalleyExtras (GaloisField p f) O C hC⟩

theorem exists_chevalleyExtras_model_nonSimplyLaced (t : StatedLieTag) (n f : ℕ)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 2 ≤ n) ∨ t = .F4) :
    ∃ x C O, ChevalleyExtras (modelUniv t n p f Fact.out).D (GaloisField p f) x C O := by
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Symplectic.rootDatum n (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, Sp.chevalleyExtras hn O _ (Sp.commutatorFormula O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Spin.oddDatum n (GaloisField p f)).isFiniteType rfl
    exact ⟨_, _, O, SpinOdd.chevalleyExtras hn O _ (SpinOdd.commutatorFormula O)⟩
  · obtain ⟨O⟩ := nonempty_commOrder_ofCartan
      (Adjoint.f4Datum (GaloisField p f)).isFiniteType rfl
    obtain ⟨C, -, hC⟩ := Adjoint.f4_commutatorFormula (GaloisField p f) O
    exact ⟨_, C, O, Adjoint.f4_chevalleyExtras (GaloisField p f) O C hC⟩

end Models

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem componentHom_ker_le_center (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card) : (componentHom hΩ D j).ker ≤ Subgroup.center (compModel D j).K := by
  intro y hy
  have h1 : D.hom j y = 1 := by
    have : layerQuotientHom hΩ.conjInvariant a (D.hom j y) = 1 := hy
    exact (map_eq_one_iff _ (layerQuotientHom_injective hΩ.conjInvariant)).mp this
  exact D.ker_le_center j h1


end Provider

end CFSG.ClassicalInvolution.Balance
