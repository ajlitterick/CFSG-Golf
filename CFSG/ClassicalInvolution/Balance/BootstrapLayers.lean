module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersPair
public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Helpers


theorem not_commutes_self_of_isQuasisimple {X : Type*} [Group X] {L : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  intro h
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  obtain ⟨u, hu⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  apply hu
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h g g.2 x x.2)

theorem commutator_self_eq_of_le {X : Type*} [Group X] {R : Subgroup X} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)) h

omit [Finite G] in
theorem modOdd_le_or_commutes {a : G} {Y : Subgroup (OddQuot a)}
    (D' : LieDecomposition (memberImages Ω a) Y) (i : D'.ι)
    {K : Subgroup G} (hK : K ∈ centMembers Ω a) :
    modOdd a K ≤ D'.Q i ∨ ∀ x ∈ modOdd a K, ∀ y ∈ D'.Q i, x * y = y * x := by
  obtain ⟨i', hi'⟩ := D'.exists_le (modOdd a K) ⟨K, hK, rfl⟩
  by_cases hii' : i' = i
  · subst hii'
    exact Or.inl hi'
  · exact Or.inr fun x hx y hy => D'.commute i' i hii' x (hi' hx) y hy

omit [Finite G] in
theorem le_iSup_centralizer_of_centralizedGeneratedAt {a : G} {F₀ : Subgroup G}
    {L : Subgroup (OddQuot a)} (h : CentralizedGeneratedAt Ω a F₀ L) :
    L ≤ ⨆ g ∈ modOdd a F₀, ⨆ (_ : g ≠ 1),
      memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a)) := by
  refine h.trans (iSup₂_le fun K hKΩ => iSup_le fun hKC => iSup_le fun hex =>
    iSup_le fun _ => ?_)
  obtain ⟨g, hg, hg1, hcen⟩ := hex
  have hKJ : modOdd a K ≤ memberJoin Ω a :=
    le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K ⟨hKΩ, hKC⟩
  exact le_iSup₂_of_le g hg (le_iSup_of_le hg1 (le_inf hKJ hcen))

end Helpers

section Component

variable {a : G}


end Component

section Main

structure CommutingInputs (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (a : G) : Prop where
  single : ∀ D : LocalLieSystemAt p f Ω a, SingleClassComponents p f D
  perfect : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card),
    ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, R ≤ ⁅R, R⁆
  toral : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card),
    ModelFacts.CommutingFundamentalGeneration p (D.tag j) (D.rank j) (D.exp j)

omit [Finite G] in
theorem CommutingInputs.of_facts {a : G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hno : ∀ D : LocalLieSystemAt p f Ω a, ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hF3 : NoComponentOverF3 p f Ω a) (hMFC : ModelFacts.CommutingFundamentalFacts p) :
    CommutingInputs p f Ω a where
  single D := singleClassComponents_of_tags D (hno D)
  perfect D j := by
    have hq4 : 4 ≤ p ^ f := by omega
    refine LieSystemData.fundPerfect D hp2 hq4 (fun i _ => ?_) j
    have := five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq i).imp id And.right) (hF3 D i)
    omega
  toral D j := hMFC (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j)


end Main

section Triple


end Triple

section Chain


end Chain

end CFSG.ClassicalInvolution.Balance.Bootstrap
