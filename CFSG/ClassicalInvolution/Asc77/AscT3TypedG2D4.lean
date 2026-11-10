module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedClass
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Stab

variable {X : Type} [Group X]

@[expose] def conjStab (C : Set (Subgroup X)) : Subgroup X where
  carrier := {g | ∀ M, conjSub g M ∈ C ↔ M ∈ C}
  one_mem' := fun M => by simp
  mul_mem' := by
    intro g g' hg hg' M
    rw [conjSub_mul]
    exact (hg _).trans (hg' M)
  inv_mem' := by
    intro g hg M
    have := hg (conjSub g⁻¹ M)
    rw [conjSub_conjSub_inv] at this
    exact this.symm

theorem mem_conjStab_iff {C : Set (Subgroup X)} {g : X} :
    g ∈ conjStab C ↔ ∀ M, conjSub g M ∈ C ↔ M ∈ C := Iff.rfl

variable {Φ : Set (Subgroup X)}

theorem mem_conjStab_dstarComp (hΦ : ConjInvariant Φ) {K J : Subgroup X} (hK : K ∈ Φ)
    (hJ : J ∈ dstarComp Φ K) {x : X} (hx : conjSub x J = J) : x ∈ conjStab (dstarComp Φ K) := by
  obtain ⟨-, hKJ⟩ := mem_dstarComp_symm hK hJ
  have fwd : ∀ y : X, conjSub y J = J → ∀ M, M ∈ dstarComp Φ K →
      conjSub y M ∈ dstarComp Φ K := by
    intro y hy M hM
    have h2 := dstarComp_conj hΦ (hKJ.trans hM) y
    rw [hy] at h2
    exact hJ.trans h2
  have hx' : conjSub x⁻¹ J = J := by
    calc conjSub x⁻¹ J = conjSub x⁻¹ (conjSub x J) := by rw [hx]
      _ = J := conjSub_inv_conjSub x J
  intro M
  constructor
  · intro hM
    have := fwd x⁻¹ hx' _ hM
    rwa [conjSub_inv_conjSub] at this
  · exact fwd x hx M

end Stab

section Involution

variable {H G : Type} [Group H] [Group G]

theorem isUniqueInvolution_of_map {ψ : H →* G} (hinj : Function.Injective ψ) {R : Subgroup H}
    {z : G} (hz : IsUniqueInvolution (R.map ψ) z) :
    ∃ c : H, ψ c = z ∧ IsUniqueInvolution R c := by
  obtain ⟨c, hcR, hcz⟩ := hz.mem
  refine ⟨c, hcz, hcR, fun h => hz.ne_one ?_, hinj ?_, fun y hy hy2 => ?_⟩
  · rw [← hcz, h, map_one]
  · rw [map_mul, hcz, hz.sq, map_one]
  · have h1 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases hz.unique (ψ y) (Subgroup.mem_map_of_mem ψ hy) h1 with h2 | h2
    · left
      exact hinj (h2.trans (map_one ψ).symm)
    · right
      exact hinj (h2.trans hcz.symm)

theorem isUniqueInvolution_map_of_inj {ψ : H →* G} (hinj : Function.Injective ψ) {R : Subgroup H}
    {c : H} (hc : IsUniqueInvolution R c) : IsUniqueInvolution (R.map ψ) (ψ c) where
  mem := Subgroup.mem_map_of_mem ψ hc.mem
  ne_one := fun h => hc.ne_one (hinj (h.trans (map_one ψ).symm))
  sq := by rw [← map_mul, hc.sq, map_one]
  unique := by
    rintro _ ⟨r, hr, rfl⟩ hy
    have h1 : r * r = 1 := hinj (by rw [map_mul, hy, map_one])
    rcases hc.unique r hr h1 with h2 | h2
    · left
      rw [h2, map_one]
    · right
      rw [h2]

end Involution

section Component

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}
  {z j a : X}


theorem mem_dstarComp_of_commutes (hp : p ≠ 2) (hΦ : HypOmegaMod p f Φ) {K M : Subgroup X}
    (hM : M ∈ Φ) (hc : Commutes M K) : M ∈ dstarComp Φ K := by
  by_cases hMK : M = K
  · subst hMK
    exact Relation.ReflTransGen.refl
  · have hcomm : ⁅M, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
      exact K.one_mem
    have hMN : M ≤ Subgroup.normalizer (K : Set X) := le_normalizer_of_commutator_le hcomm
    obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := X)) bot_le
    have hnb : M ∈ omegaNbr Φ K := ⟨hM, hMK, R, hR, hRM.1, hRM.1.trans hMN⟩
    exact Relation.ReflTransGen.single ⟨hM, Or.inl (omegaNbr_subset_omegaStarNbr hp hΦ K hnb)⟩


end Component

end CFSG.ClassicalInvolution.Asc77.T3Typed
