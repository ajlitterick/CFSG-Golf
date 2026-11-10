module

public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Cover
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChainMain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Residuals

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} → J ≠ K → J ≠ T →
        IsClassicalMember p f J t →
        CentralizerGenerationStar (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G)) t

@[expose] def TwinYTransitive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ K₁ ∈ locFamily (𝒞 K) e.u, ∀ L ∈ locFamily (𝒞 K) e.u,
        ∃ g : locQuot (𝒞 K) e.u, conjSub g K₁ = L


@[expose] def TwinYRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
        ∀ i : Fin D.card, (∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i)) →
          D.tag i = (twinYModel (p ^ f) tY nY).1 ∧ D.rank i = (twinYModel (p ^ f) tY nY).2

end Residuals

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem TwinRow.tag_facts {t : StatedLieTag} {n : ℕ} (h : TwinRow t n) :
    t ≠ .G2 ∧ t ≠ .trialityD4 ∧ ¬ (t = .PSL ∧ n = 2) := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ |
    ⟨-, rfl, rfl⟩ <;> exact ⟨by decide, by decide, by simp⟩

theorem exists_frameMembers [IsSimpleGroup G] {K T : Subgroup G} {z : G} {tY : StatedLieTag}
    {nY : ℕ} (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ (J J' : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      IsClassicalMember p f J t ∧ t ≠ z ∧ IsClassicalMember p f J' t ∧ Commutes J J' ∧
      J' ∈ centralizingMembers (𝒞 K) {e.u} := by
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, hJ, hJK, hJT⟩ := exists_big_member S.inClass S.p1 rf d hKiso hTiso
  obtain ⟨t, hJt⟩ := S.inClass.classical J hJ.1
  have htz : t ≠ z := by
    intro htz
    subst htz
    obtain ⟨L', hL', hL'J, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d
      ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩ hT.mem
      hT.ne.symm hKiso hTiso hJ hJK hJT
    rcases S.cp_at_member hcen hJ.1 hJt hL' with h | h
    · exact hnc h
    · exact hL'J h
  obtain ⟨J', hJ'Ω, -, hJ'cls, hJJ', hJ'K, hJ'T⟩ := exists_twin_at_t S hT.mem hT.ne.symm hKiso
    hTiso clsT hJ hJK hJT hJt htz
  exact ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ'cls, hJJ',
    e.mem_centralizingMembers_u hJ'Ω hJ'K hJ'T⟩

end Members

section LieAtU

variable {p f : ℕ} [Fact p.Prime]

theorem twinElt_u_not_central {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G}
    {z : G} (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z) (e : TwinElt K T z)
    (hKT : Commutes K T) : e.u ≠ 1 ∧ ¬ ({e.u} : Set G) ⊆ Subgroup.center G := by
  have hu1 : e.u ≠ 1 := e.u_ne_one S.cls (S.exact K (CoreAssembly.mem_conjClass_self K))
    (odd_natCard_galoisField S.odd S.five) hKT
  exact ⟨hu1, singleton_not_subset_center hnab hu1⟩


end LieAtU

section Main


end Main

end CFSG.ClassicalInvolution.RouteD.TwinY
