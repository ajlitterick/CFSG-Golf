module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]


theorem normalizer_le_normalizer_centralizer (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ m ∈ Subgroup.normalizer (W : Set G), ∀ y ∈ Subgroup.centralizer (W : Set G),
      m * y * m⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro m hm y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) w).mp hw
    have h1 : m⁻¹ * w * m⁻¹⁻¹ * y = y * (m⁻¹ * w * m⁻¹⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hy) _ hw'
    calc w * (m * y * m⁻¹) = m * ((m⁻¹ * w * m⁻¹⁻¹) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * w * m⁻¹⁻¹)) * m⁻¹ := by rw [h1]
      _ = m * y * m⁻¹ * w := by group
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

theorem normalizer_le_normalizer_OCW [Finite G] (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
  fun _ hn => mem_normalizer_oddCoreOf_of_mem_normalizer (normalizer_le_normalizer_centralizer W hn)

theorem mem_normalizer_sup {A B : Subgroup G} {n : G} (hA : n ∈ Subgroup.normalizer (A : Set G))
    (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hA, hB]

theorem normalizer_le_normalizer_sup_OCW [Finite G] (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
  fun _ hn => mem_normalizer_sup hn (normalizer_le_normalizer_OCW W hn)

theorem OCW_le_normalizer (W : Subgroup G) : OCW W ≤ Subgroup.normalizer (W : Set G) :=
  (oddCoreOf_le_self _).trans (Subgroup.centralizer_le_normalizer (W : Set G))


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
