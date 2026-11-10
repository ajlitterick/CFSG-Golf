module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub InClass IsClassicalMember LocalOddCentral
  ExactMembers LieSystemData ConjInvariant)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerPatternB (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K β : Subgroup G) (t : G) : Prop :=
  ∃ j : Fin m → Subgroup G, (∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
    (∀ a : Fin m, 1 ≤ a.val → ⁅j a, j a⁆ = j a ∧ j a ≤ Subgroup.centralizer ({t} : Set G)) ∧
    (∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
    (∀ a : Fin m, a.val = 0 → ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j a))

theorem PartnerPatternB.of_conj {m : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K β : Subgroup G} {t : G} {j : Fin m → Subgroup G}
    (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) (hjK : ∀ a, Commutes K (j a))
    (hjperf : ∀ a : Fin m, ⁅j a, j a⁆ = j a)
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ a : Fin m, 1 ≤ a.val → conjSub y (j a) ≤ Subgroup.centralizer ({t} : Set G))
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternB p f m Ω K β t := by
  refine ⟨fun a => conjSub y (j a), fun a ha => hΩ y _ (hjΩ a ha),
    fun a => commutes_conjSub_of_mem_normalizer hy (hjK a), fun a ha => ⟨?_, hfix a ha⟩,
    fun a b hab => (hjc a b hab).conjSub y, ?_, ?_, hpair0⟩
  · show ⁅(j a).map (MulAut.conj y).toMonoidHom, (j a).map (MulAut.conj y).toMonoidHom⁆ =
      (j a).map (MulAut.conj y).toMonoidHom
    rw [← Subgroup.map_commutator, hjperf a]
  · intro a b hab hb
    obtain ⟨W, hW⟩ := hjp a b hab hb
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW y⟩
  · intro a b ha hb
    obtain ⟨W, hW⟩ := hjsp a b ha hb
    exact ⟨_, CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW
      (MulAut.conj y).toMonoidHom (MulAut.conj y).injective⟩

theorem PartnerPatternB.of_locAut [Finite G] {m : ℕ} {Ω : Set (Subgroup G)} {z : G}
    {K β : Subgroup G} (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    {j : Fin m → Subgroup G} (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω)
    (hjY : ∀ a, j a ≤ locLayer Ω z) (hjK : ∀ a, Commutes K (j a))
    (hjperf : ∀ a : Fin m, ⁅j a, j a⁆ = j a) (hKY : locLayer Ω z ≤ Subgroup.normalizer (K : Set G))
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j a) (j b))
    {y : G} (hy : y ∈ locLayer Ω z) {t : G} (ht : t * z * t⁻¹ = z)
    (hfix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j a)),
      Gaps.locAut hΩ.conjInvariant ht x = x)
    (hpair0 : ∀ a : Fin m, a.val = 0 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j a))) :
    PartnerPatternB p f m Ω K β t := by
  refine PartnerPatternB.of_conj hΩ.conjInvariant hjΩ hjK hjperf hjc hjp hjsp (hKY hy)
    (fun a ha => ?_) hpair0
  have hle : conjSub y (j a) ≤ locLayer Ω z := by
    intro x hx
    have h1 : y⁻¹ * x * y ∈ locLayer Ω z := hjY a (CFSG.ClassicalInvolution.Generic.mem_conjSub_iff.mp hx)
    have := (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy h1) ((locLayer Ω z).inv_mem hy)
    simpa [mul_assoc] using this
  have hperf : conjSub y (j a) ≤ ⁅conjSub y (j a), conjSub y (j a)⁆ := by
    show (j a).map (MulAut.conj y).toMonoidHom ≤ ⁅(j a).map (MulAut.conj y).toMonoidHom,
      (j a).map (MulAut.conj y).toMonoidHom⁆
    rw [← Subgroup.map_commutator, hjperf a]
  exact (locAut_fixed_iff_of_perfect hΩ hP1 ht hle hperf).mpr (hfix a ha)


end CFSG.ClassicalInvolution.RouteD
