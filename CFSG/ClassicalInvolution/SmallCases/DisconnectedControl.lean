module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.TwoGroupCase.TightEmbedding
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

variable {G : Type*} [Group G]

section Components

@[expose] def deltaComp (J A : Subgroup G) : Set (Subgroup G) :=
  {B | Relation.ReflTransGen (commutingAdj J) A B}

@[expose] def ControlC (J : Subgroup G) : Prop :=
  ∀ t : G, t ≠ 1 → IsPGroup 2 (Subgroup.zpowers t) →
    ∀ A ∈ conjugateSet J, ∀ B ∈ conjugateSet J,
      A ≤ Subgroup.centralizer ({t} : Set G) → B ≤ Subgroup.centralizer ({t} : Set G) →
      B ∈ deltaComp J A


end Components

section Standard

private theorem normalizer_le_normalizer_centralizer (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ c ∈ Subgroup.centralizer (J : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g hg h
  · intro h'
    have := key g⁻¹ (inv_mem hg) _ h'
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this


end Standard

end CFSG.ClassicalInvolution
