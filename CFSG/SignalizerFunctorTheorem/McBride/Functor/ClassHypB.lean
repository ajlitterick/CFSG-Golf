module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Class
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

@[expose] def hypBClass (p : ℕ) : SigClass.{u} :=
  fun _ _ _ _ X => signalizerMcBrideHypothesisB p X

theorem signalizerMcBrideHypothesisB_map_iff {G K : Type*} [Group G] [Finite G] [Group K]
    [Finite K] {p : ℕ} (f : G →* K) (hf : Function.Injective f) {X : Subgroup G} :
    signalizerMcBrideHypothesisB p X ↔ signalizerMcBrideHypothesisB p (X.map f) := by
  have hcard : Nat.card (X.map f) = Nat.card X := Subgroup.card_map_of_injective hf
  constructor
  · intro hX
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hX.1, hcard ▸ hX.2.1, ?_⟩
    intro S _ _ _ hS hnc
    exact signalizerMcBrideHypothesisA_of_isSectionOf hX ((isSectionOf_map_iff f hf X S).mp hS) hnc
  · intro hX
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hX.1, hcard ▸ hX.2.1, ?_⟩
    intro S _ _ _ hS hnc
    exact signalizerMcBrideHypothesisA_of_isSectionOf hX ((isSectionOf_map_iff f hf X S).mpr hS) hnc

theorem isSigClass_hypBClass (p : ℕ) : IsSigClass p (hypBClass.{u} p) where
  mono := by
    intro H _ _ A X Y hYX _ hX
    have hX' : signalizerMcBrideHypothesisB p X := hX
    obtain ⟨hp, hcop, h⟩ := signalizerMcBrideHypothesisB_iff.mp hX'
    exact signalizerMcBrideHypothesisB_iff.mpr ⟨hp,
      hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hYX),
      fun S _ _ _ hS hnc => h S (isSectionOf_of_le hYX hS) hnc⟩
  map_iff := fun H K _ _ _ _ f hf A X => signalizerMcBrideHypothesisB_map_iff f hf
  quotient := by
    intro H _ _ A X N _ _ _ _ hX
    have hX' : signalizerMcBrideHypothesisB p X := hX
    obtain ⟨hp, hcop, h⟩ := signalizerMcBrideHypothesisB_iff.mp hX'
    exact signalizerMcBrideHypothesisB_iff.mpr ⟨hp,
      hcop.coprime_dvd_right (Subgroup.card_map_dvd X _),
      fun S _ _ _ hS hnc => h S (isSectionOf_of_isSectionOf_map _ X hS) hnc⟩
  extension := by
    intro H _ _ A X N _ _ _ hNX _ hN hQ
    have hN' : signalizerMcBrideHypothesisB p N := hN
    have hQ' : signalizerMcBrideHypothesisB p (X.map (QuotientGroup.mk' N)) := hQ
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hN'.1, ?_, ?_⟩
    · rw [← card_map_mk'_mul_card hNX]
      exact Nat.Coprime.mul_right hQ'.2.1 hN'.2.1
    · intro S _ _ _ hS hnc
      rcases isSectionOf_normal_or_quotient hNX hS with h | h
      · exact signalizerMcBrideHypothesisA_of_isSectionOf hN' h hnc
      · exact signalizerMcBrideHypothesisA_of_isSectionOf hQ' h hnc

theorem signalizerMcBrideHypothesisB_map_conj {G : Type*} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} (g : G) (h : signalizerMcBrideHypothesisB p X) :
    signalizerMcBrideHypothesisB p (X.map (MulAut.conj g).toMonoidHom) :=
  (signalizerMcBrideHypothesisB_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mp h

theorem signalizerMcBrideHypothesisB_of_isPGroup {G : Type*} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) {X : Subgroup G} (hX : IsPGroup r X) :
    signalizerMcBrideHypothesisB p X := by
  have := Fact.mk hr
  refine ⟨hp, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).mpr hrp.symm)
  · intro K L hKX hLK _ hsimple hnc
    exfalso
    have hQ : IsPGroup r (K ⧸ L.subgroupOf K) := (hX.to_le hKX).to_quotient _
    have : Group.IsNilpotent (K ⧸ L.subgroupOf K) := hQ.isNilpotent
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)


end CFSG.SignalizerFunctorTheorem.McBride
