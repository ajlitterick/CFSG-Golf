module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD edgeE)
open CFSG.LieType.CurtisTits (rankOne)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def E7TorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .POmegaPlus 6 (𝒞 K) z →
      ∀ c : ETCtx p f .POmegaPlus 6 (𝒞 K) K z, ∀ j : Fin 6 → Subgroup G,
        NodeSystem p f (edgeD 6) (𝒞 K) K z j →
        (∀ a, locImg (𝒞 K) z (j a) =
          (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z,
            TorusFixedP (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f
              Fact.out).D.rank) ht


@[expose] def E8TorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∀ c : ETCtx p f .E7 0 (𝒞 K) K z, ∀ j : Fin 7 → Subgroup G,
        NodeSystem p f (edgeE 7) (𝒞 K) K z j →
        (∀ a, locImg (𝒞 K) z (j a) =
          (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, TorusFixedE7 c ht

@[expose] def E8AttachmentsExcluded (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∀ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) (𝒞 K) K z j →
        ∀ β ∈ 𝒞 K, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ p₀ : Fin 7, (∀ a, a ≠ p₀ → Commutes β (j a)) →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j p₀)) → p₀ = 6

@[expose] def E7SignPerp (p f : ℕ) [Fact p.Prime] : Prop :=
  SignPerp (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D) (GaloisField p f)


theorem e8PartnerExists_of_inputs (hMFZ : Gaps.FundNoncentral p) (hG : E7SignPerp p f)
    (hT : E8TorusFixed p f) (hX : E8AttachmentsExcluded p f) : E8PartnerExists p f := by
  intro G _ _ _ hnab K z S hS
  exact exists_partnerAt_E8 hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.cls hS S.p1 (TypeEPattern.layerGeom_E7_of_signPerp S.five hG)
    (hT G hnab K z S hS) (hX G hnab K z S hS)

end CFSG.ClassicalInvolution.MilestoneAssembly
