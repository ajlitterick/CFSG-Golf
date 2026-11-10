module

public import CFSG.HardMathSupport.Dickson.Bal207.SpShapeIdx
public import CFSG.HardMathSupport.Dickson.Bal207.Center
import CFSG.Adapters.TauCetiLieModels
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

@[expose] def OrthCompIdx : TauCeti.LieTypeIndex → Prop
  | .D s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Even s ∧ 4 ≤ s
  | .twistedD s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Odd s ∧ 5 ≤ s
  | .twistedA r q => ((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ 2 ≤ r ∧ ¬(r = 2 ∧ IsTwoPow q 1)) ∨
      (r = 2 ∧ q.p = 3 ∧ q.exponent = 1)
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | _ => False

@[expose] def OrthCompType (Q : Type) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, OrthCompIdx d.1 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isoInvariant_orthCompType : IsoInvariant OrthCompType := by
  rintro Q Q' _ _ e ⟨d, hd, ⟨a⟩⟩
  exact ⟨d, hd, ⟨e.symm.trans a⟩⟩

theorem orthCompIdx_cases {d : TauCeti.LieTypeIndex} (h : OrthCompIdx d) :
    (Bal207Index 3 d ∧ ¬ IsG2EightIndex d) ∨ IsD4EightIdx d ∨ IsSmallTwistedIdx d ∨
      IsL2EightIndex d ∨ IsSpFirstClaimIdx d := by
  cases d with
  | D s q =>
    obtain ⟨hq, hs, h4⟩ := h
    rcases (show s = 4 ∨ 6 ≤ s by obtain ⟨k, hk⟩ := hs; omega) with rfl | h6
    · rcases hq with hq | hq
      · exact Or.inl ⟨⟨rfl, Or.inr ⟨hq, rfl⟩⟩, fun h => h⟩
      · exact Or.inr (Or.inl ⟨rfl, hq⟩)
    · exact Or.inl ⟨⟨rfl, Or.inl ⟨hq, hs, h6⟩⟩, fun h => h⟩
  | twistedD s q => exact Or.inl ⟨⟨rfl, h⟩, fun h => h⟩
  | A r q => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  | twistedA r q =>
    rcases h with ⟨hq, hr, hne⟩ | ⟨rfl, hq3⟩
    · by_cases h3 : 3 ∣ r + 1
      · by_cases h2 : r = 2
        · subst h2
          refine Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ?_⟩))
          exact hq.resolve_left fun h1 => hne ⟨rfl, h1⟩
        · by_cases h5 : r = 5 ∧ IsTwoPow q 1
          · exact Or.inl ⟨⟨rfl, Or.inr ⟨h5.2, h5.1⟩⟩, fun h => h⟩
          · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, h3, ?_, h5⟩)))
            obtain ⟨c, hc⟩ := h3
            omega
      · exact Or.inl ⟨⟨rfl, Or.inl ⟨hq, h3⟩⟩, fun h => h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl hq3⟩))
  | _ => exact h.elim


theorem orthCompType_of_model_plus {G : Type} [Group G] {s f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus s 2 f) (hf : f = 1 ∨ f = 3) (hs : Even s) :
    OrthCompType G := by
  have h4 : 4 ≤ s := hG.1.2.2
  have hf0 : 0 < f := by omega
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf0⟩
  have hv : (TauCeti.LieTypeIndex.D s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD s q hv (MulEquiv.refl _))
  refine ⟨⟨.D s q, hv⟩, ⟨?_, hs, h4⟩, ⟨e⟩⟩
  rcases hf with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem orthCompType_of_model_minus {G : Type} [Group G] {s f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus s 2 f) (hf : f = 1 ∨ f = 3) (hs : Odd s)
    (h5 : 5 ≤ s) : OrthCompType G := by
  have h4 : 4 ≤ s := hG.1.2.2
  have hf0 : 0 < f := by omega
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf0⟩
  have hv : (TauCeti.LieTypeIndex.twistedD s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD s q hv (MulEquiv.refl _))
  refine ⟨⟨.twistedD s q, hv⟩, ⟨?_, hs, h5⟩, ⟨e⟩⟩
  rcases hf with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem orthCompType_of_u33 {Y : Type} [Group Y] (h : IsLieQuot Y IsU33Idx) :
    OrthCompType (Y ⧸ Subgroup.center Y) := by
  obtain ⟨⟨d, hv⟩, hd, e⟩ := h
  cases d with
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := hd
    exact ⟨⟨.twistedA 2 q, hv⟩, Or.inr ⟨rfl, hq⟩, e⟩
  | _ => exact hd.elim

theorem exists_model_of_famOrth {Y : Type} [Group Y] (h : IsLieQuot Y (FamOrth 3)) :
    ∃ (t : StatedLieTag) (n f : ℕ), (f = 1 ∨ f = 3) ∧
      ((t = .POmegaPlus ∧ Even n ∧ (6 ≤ n ∨ (n = 4 ∧ f = 1))) ∨
        (t = .POmegaMinus ∧ Odd n ∧ 5 ≤ n)) ∧
      StatedClassicalModel (Y ⧸ Subgroup.center Y) t n 2 f := by
  obtain ⟨⟨d, hv⟩, ⟨hi, ho⟩, ⟨e⟩⟩ := h
  cases d with
  | D r q =>
    have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    obtain ⟨-, ⟨hq, hr, h6⟩ | ⟨⟨hp, h1⟩, rfl⟩⟩ := hi
    · have hp : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
      rw [hp] at hM
      refine ⟨.POmegaPlus, r, q.exponent, ?_, Or.inl ⟨rfl, hr, Or.inl h6⟩, hM⟩
      rcases hq with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rw [hp, h1] at hM
      exact ⟨.POmegaPlus, 4, 1, Or.inl rfl, Or.inl ⟨rfl, ⟨2, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩, hM⟩
  | twistedD r q =>
    have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    obtain ⟨-, hq, hr, h5⟩ := hi
    have hp : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    rw [hp] at hM
    refine ⟨.POmegaMinus, r, q.exponent, ?_, Or.inr ⟨rfl, hr, h5⟩, hM⟩
    rcases hq with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  | _ => exact ho.elim

section Center

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem famOrth_coprime_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : IsLieQuot K (FamOrth 3)) :
    Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
  obtain ⟨⟨dd, hv⟩, ⟨hd, ho⟩, ⟨e⟩⟩ := hK
  cases dd with
  | D r q =>
    obtain ⟨-, h⟩ := hd
    have hp2 : q.p = 2 := by
      rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_D r q hv (MulEquiv.refl _)
    rw [hp2] at hL
    have heven : Even (2 ^ q.exponent) := (Nat.even_pow' q.exponent_pos.ne').mpr even_two
    have hg : ¬ 3 ∣ (genericOrders .POmegaPlus r 2 q.exponent).1 := by
      simp only [genericOrders, if_pos heven]
      norm_num
    exact centerAux_coprime_of_card_le_one Nat.prime_three
      ((center_torsion_le hGA hq e hL Nat.prime_three).trans
        (centerAux_torsBound_eq_one (Or.inl rfl) hg).le)
  | twistedD r q =>
    obtain ⟨-, h, -⟩ := hd
    have hp2 : q.p = 2 := by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedD r q hv (MulEquiv.refl _)
    rw [hp2] at hL
    have hg : ¬ 3 ∣ (genericOrders .POmegaMinus r 2 q.exponent).1 := by
      simp only [genericOrders]
      exact centerAux_not_three_dvd_gcd (Or.inr rfl)
    exact centerAux_coprime_of_card_le_one Nat.prime_three
      ((center_torsion_le hGA hq e hL Nat.prime_three).trans
        (centerAux_torsBound_eq_one (Or.inl rfl) hg).le)
  | _ => exact ho.elim

end Center

@[expose] def D42TrialityShape : Prop :=
  ∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .POmegaPlus 4 2 1 →
    ∀ τ : MulAut S, τ ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ τ) →
      (∀ L L' : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup τ) →
        CFSG.Open.IsComponentOf L' (fixSubgroup τ) → L = L') ∧
      ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup τ) → IsLieQuot ↥L IsU33Idx

@[expose] def Bal207OrthFirstClaim (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamOrth 3) → Bal207PlusIH G A →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) →
        B ≤ Subgroup.normalizer (J : Set X) → IsLieQuot ↥J IsSpFirstClaimIdx →
          IsStronglyLocallyOneBalanced 3 B a J

end CFSG.HardMathSupport.Dickson.Bal207
