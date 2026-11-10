module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTransport
public import CFSG.Adapters.LinearCatalog
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def GGSeitzExcSpEightOvergroupInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .B 4 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
        ggFixedClosure E ≠ ⊤ → ∀ Y : Subgroup K, ggFixedClosure E ≤ Y → Y ≠ ⊤ →
          ¬ Group.IsSolvable ↥Y →
            IsSimpleGroup ↥(commutator ↥Y) ∧ LieModel ↥(commutator ↥Y) .POmegaPlus 4 2 1

@[expose] def GGSeitzExcSpEightCentralizerInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .B 4 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
        ggFixedClosure E ≠ ⊤ → IsPGroup 3 ↥(ggFixedSubgroup E)

@[expose] def GGSeitzExcSpSixOvergroupInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .B 3 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧ LieModel ↥(commutator ↥X) .PSU 4 2 1)

@[expose] def GGSeitzExcSpSixCentralizerInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 1 → d.1 = .B 3 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
        ggFixedClosure E ≠ ⊤ → IsPGroup 3 ↥(ggFixedSubgroup E)

@[expose] def GGSeitzExcLThreeFourOvergroupInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 2 → d.1 = .A 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ X : Subgroup K, X ≠ ⊤ → ¬ 3 ∣ X.index →
        Group.IsSolvable ↥X ∨
          (IsSimpleGroup ↥(commutator ↥X) ∧
            Nonempty (↥(commutator ↥X) ≃* alternatingGroup (Fin 6)))

@[expose] def GGSeitzExcLThreeFourCentralizerInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p = 2 → q.exponent = 2 → d.1 = .A 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
        IsPGroup 3 ↥(ggFixedSubgroup E)

theorem ggLieModel_symplectic_two {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hq1 : q.exponent = 1) (r : ℕ) (hr : 3 ≤ r)
    (hd : d.1 = .B r q) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : LieModel K .PSp r 2 1 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr e
  rw [hq2, hq1] at h
  exact Or.inl ⟨by decide, h⟩

theorem ggLieModel_lThreeFour {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hq3 : q.exponent = 2) (hd : d.1 = .A 2 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : LieModel K .PSL 3 2 2 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e1 : K ≃* StatedProj (StatedSL 3 (GaloisField q.p q.exponent)) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 _)
  have hF : Nat.card (GaloisField q.p q.exponent) = 2 ^ 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2, hq3]
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
    GaloisField q.p q.exponent, inferInstance, inferInstance, hF, ⟨e1⟩⟩


end CFSG.StandardType
