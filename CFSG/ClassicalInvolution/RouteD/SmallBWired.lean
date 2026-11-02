module

public import CFSG.ClassicalInvolution.RouteD.SmallBFive
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.Generic.InductionMain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.CoreAssembly (conjClass single_class)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinBLastLongGe5 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ (m : ℕ) (_ : 5 ≤ m)
      (_ : m ≠ 6), LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∃ c : TCtx p f .POmegaOdd m (conjClass K) K z, ∀ β ∈ conjClass K, ∀ t : G,
        ∀ ht : IsClassicalMember p f β t,
          ∀ hKβ : (∃ W, LinearBlockStandardPair (GaloisField p f) W K β),
            HasFixedMember (conjClass K) K β z →
              ∀ (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
                (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2),
                Gaps.ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
                  Gaps.LastLongExcluded (p := p) (f := f) m v

@[expose] def TwinBSmallRest (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ m : ℕ,
      (m = 3 ∨ m = 4 ∨ m = 6) → LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t

theorem twinBPattern_of_parts (hMFZ : Gaps.FundNoncentral p) (hL : TwinBLastLongGe5 p f)
    (hR : TwinBSmallRest p f) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ m : ℕ, 3 ≤ m →
        LocalShapeT p f 2 .POmegaOdd m (conjClass K) z → ∀ β ∈ conjClass K, ∀ t : G,
          IsClassicalMember p f β t →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
          HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases hsmall : m = 3 ∨ m = 4 ∨ m = 6
  · exact hR G hnab K z S m hsmall hshape β hβ t ht hKβ hfix
  have h5 : 5 ≤ m := by omega
  have h6 : m ≠ 6 := fun h => hsmall (Or.inr (Or.inr h))
  obtain ⟨c, hc⟩ := hL G hnab K z S m h5 h6 hshape
  by_cases hm5 : m = 5
  · subst hm5
    exact Gaps.PartnerPatternBPair.of_fixed_member_five hMFZ c (single_class K) hshape hβ ht hKβ
      hfix (fun k₀ v hv => hc β hβ t ht hKβ hfix k₀ v hv)
  · exact Gaps.PartnerPatternBPair.of_fixed_member_seven (by omega) hMFZ c (single_class K) hshape
      hβ ht hKβ hfix (fun k₀ v hv => hc β hβ t ht hKβ hfix k₀ v hv)

end CFSG.ClassicalInvolution.RouteD
