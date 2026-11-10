module

public import CFSG.ClassicalInvolution.Asc77.AscT3XHyp
public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.x_isUniqueInvolution_conjSub (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (perfectCoreIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI := d.viol.hzK.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI.ne_one (congrArg Subtype.val h), Subtype.ext hI.sq, fun y hy hy2 => ?_⟩
  rcases hI.unique _ (le_conjSub_of_mem c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)


theorem Std20.x_false_of_le_normalizer (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (htwin : conjSub c₂ K ∉ twinSet (CoreAssembly.conjClass K) (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have hI := d.viol.hzK
  have hΩ := d.hyp
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hJ₁ : conjSub c₁ K ∈ CoreAssembly.conjClass K := ⟨c₁, rfl⟩
  have hJ₂ : conjSub c₂ K ∈ CoreAssembly.conjClass K := ⟨c₂, rfl⟩
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_perfectCore_eq hc₁ hc₂ h)
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hx) _).mp (conj_mem_conjSub hzKa)
    have h2 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈ conjSub c₁ K := Subgroup.map_mono hKaK h1
    have h3 : x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) = 1 := by
      calc x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) =
          x * ((c₁ * z * c₁⁻¹) * (c₁ * z * c₁⁻¹)) * x⁻¹ := by group
        _ = 1 := by rw [hI₁.sq]; group
    rcases hI₁.unique _ h2 h3 with h | h
    · exfalso
      apply hI₁.ne_one
      calc c₁ * z * c₁⁻¹ = x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (c₁ * z * c₁⁻¹) = x * (c₁ * z * c₁⁻¹) * x⁻¹ * x := by group
        _ = c₁ * z * c₁⁻¹ * x := by rw [h]
  have hRJ₂ : R₀ ≤ conjSub c₂ K := hRle.trans (Subgroup.map_mono hKaK)
  obtain ⟨V₀, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRJ₂ hRz)
  have hz₂V : c₂ * z * c₂⁻¹ ∈ V₀ := hRV (mem_of_le_member hI₂ hRJ₂ hR2 (by omega))
  have hcard : Nat.card R₀ ≤ Nat.card V₀ := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f d.branch.odd d.branch.five G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V₀ hV hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, hVc⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · have hVJ₂ : V₀ ≤ conjSub c₂ K := hV.1.trans inf_le_left
    have hVN : V₀ ≤ Subgroup.normalizer (conjSub c₁ K : Set G) :=
      le_normalizer_of_commutator_le (hVc.trans (oddCoreOf_le_self _))
    have hnbr : conjSub c₂ K ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub c₁ K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr c₁⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.late_nbr _ h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 c₁
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3


section Typed


end Typed

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
