module

public import CFSG.Quasithin.Background.A3Structure39Aut
public import CFSG.Quasithin.Background.A3Structure39Odd
public import CFSG.Quasithin.Background.A3Structure38Part3

public section

namespace CFSG.Quasithin

namespace A38

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfectCore_le_normalizer [Finite G] (h37 : A37Statement G) (h38 : A38Part3 G)
    {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) :
    perfectCore (⊤ : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
  rcases (h38 L hL).1 with hnorm | ⟨-, t, ht, -, -, hcl⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
    exact le_top
  · have hconj : ∀ g : G, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
      intro g
      refine eq_or_eq_of_le_sup h37 (cComp_conj hL) hL (cComp_conj hL) ?_
      refine le_trans ?_ hcl.le
      rintro _ ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure (Subgroup.mem_top g) hz
    have h2 := index_normalizer_eq_two hconj ht
    have hNn : (Subgroup.normalizer (L : Set G)).Normal := Subgroup.normal_of_index_eq_two h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (G ⧸ Subgroup.normalizer (L : Set G)) :=
      isCyclic_of_prime_card (p := 2) h2
    have hcomm : ∀ a b : G ⧸ Subgroup.normalizer (L : Set G), a * b = b * a := fun a b =>
      (IsCyclic.commGroup : CommGroup (G ⧸ Subgroup.normalizer (L : Set G))).mul_comm a b
    have hcom : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.normalizer (L : Set G) := by
      refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
      have key : (((⁅g, h⁆ : G) : G ⧸ Subgroup.normalizer (L : Set G))) = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
          hcomm (g : G ⧸ Subgroup.normalizer (L : Set G))
            (h : G ⧸ Subgroup.normalizer (L : Set G))]
        group
      exact (QuotientGroup.eq_one_iff _).mp key
    refine (perfectCore_le_derivedSeriesOf (⊤ : Subgroup G) 1).trans ?_
    rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
    exact hcom

theorem map_normalizer_le {Q : Type} [Group Q] (f : G →* Q) (H : Subgroup G) :
    (Subgroup.normalizer (H : Set G)).map f ≤
      Subgroup.normalizer ((H.map f : Subgroup Q) : Set Q) := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H := Subgroup.mem_normalizer_iff.mp hg
  have hginv : ∀ x : G, x ∈ H ↔ g⁻¹ * x * g ∈ H := by
    intro x
    have := hg' (g⁻¹ * x * g)
    simpa [mul_assoc] using this.symm
  show f g ∈ Subgroup.normalizer ((H.map f : Subgroup Q) : Set Q)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g * z * g⁻¹, (hg' z).mp hz, by simp⟩
  · rintro ⟨z', hz', hy⟩
    refine ⟨g⁻¹ * z' * g, (hginv z').mp hz', ?_⟩
    have h2 : f (g⁻¹ * z' * g) = (f g)⁻¹ * f z' * f g := by simp
    rw [h2, hy]
    group

theorem isQuasisimple_quot_oddCore_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple (A ⧸ CFSG.oddCore A)) : CFSG.IsQuasisimple (B ⧸ CFSG.oddCore B) := by
  have hmap : (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
    rw [oddCore_eq_pPrimeCore_two, oddCore_eq_pPrimeCore_two]
    exact CFSG.pPrimeCore_map_iso 2 e
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e hmap) h


end A38

end CFSG.Quasithin
