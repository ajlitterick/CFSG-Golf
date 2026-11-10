module

public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrth

public import CFSG.LocalAnalysis.StandardType.GGReflExtE6

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6ConsumerK

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer

public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic

public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse

public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb

public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryExactTwo

public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGResE6DepFieldK
public import CFSG.LocalAnalysis.StandardType.GGResE6DepFieldL
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelEq
public import CFSG.LocalAnalysis.StandardType.GGResSchurDvd
public import CFSG.LocalAnalysis.StandardType.GGResE6DepJ
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggResE6DepLabelInput_of_b36
    (hTP : GGNbrTablePNbrInputOnL GGRegimeB36L) (hLB : GGLBalanceInput) :
    GGResE6DepLabelInput := by
  intro G _ _ p B Bs x L D J y K hH _ hS
  have hp3 : p = 3 := hS.1
  subst hp3
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLMark : LargeEvenMarking L (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) (hS.e6_marking hH (Or.inl rfl))
  have hKMark : LargeEvenMarking K (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) (hS.e6_marking hH (Or.inr rfl))
  obtain ⟨labL, hLΛ, hlL, _, _, _, _, _, hL⟩ := largeEvenMarking_exists_hasLabel hLMark
  obtain ⟨labK, hKΛ, hlK, _, _, _, _, _, hK⟩ := largeEvenMarking_exists_hasLabel hKMark
  have hmL : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
      (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hLΛ hlL)
  obtain ⟨hlJ, _, hJp⟩ := hS.j_label hH hL hmL
  have hJΛ : LargeEvenInLambda2 (ggTPJLabel labL) := by
    rcases hL with ⟨ht, _⟩ | ⟨ht, _⟩ <;>
      simp [ggTPJLabel, ht, LargeEvenInLambda2] <;> exact hLΛ.1
  have hJA : GGA5Label (ggTPJLabel labL) := by
    rcases hL with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩
    · simp [ggTPJLabel, ht, GGA5Label, hdiv]
    · simp [ggTPJLabel, ht, GGA5Label, hdiv]
  have hreg : GGRegimeB36L 3 (Nat.card Bs) labL (ggTPJLabel labL) labK :=
    ⟨rfl, hS.2.1, by rcases hL with h | h; exact Or.inl h.1; exact Or.inr h.1⟩
  have hrow := hTP G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
    (hH.2.2.1.2 y K hH.2.2.2.2.1) hH.2.2.2.2.1
    labL (ggTPJLabel labL) labK hLΛ hJΛ hKΛ hreg hlL hlJ hlK
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hJp hH.2.2.2.2.1
  have hfield : labK.n = (ggTPJLabel labL).n :=
    ggResE6Dep_K_field_of_tablePRow hRig ggSchurDvdInput_holds hH
      hJΛ hKΛ hJA hK hlJ hlK hJK hrow
  have hfield' : labK.n = labL.n := by
    simpa [ggTPJLabel, apply_ite] using hfield
  have hEq : labK = labL := ggResE6Dep_label_eq hKΛ hLΛ hK hL hfield'
  subst hEq
  refine ⟨labK, hK, hmL, ?_⟩
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
    (ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hKΛ hlK)

section Certs


private theorem not_tablePRow_twA4_E6_narrow {X : LargeEvenLabel}
    (hX : GGE6DepLabel X) :
    ¬ GGTablePRow 3 (⟨.twA, 4, 1⟩ : LargeEvenLabel) X := by
  rcases X with ⟨tag, rank, n⟩
  rcases hX with ⟨ht, hdiv⟩ | ⟨ht, hdiv⟩ <;> subst ht <;> simp [GGTablePRow]

private theorem GGLabelIso.eq_of_twA4_narrow {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.twA, 4, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twA, 4, 1⟩ := by
  rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
  all_goals simp_all

private theorem GGLabelIso.eq_of_E6_narrow {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hl : GGE6DepLabel lab) : lab' = lab := by
  rcases hl with ⟨ht, -⟩ | ⟨ht, -⟩
  · rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
    · rfl
    · rcases hBC with ⟨hbc, -⟩; rw [ht] at hbc; simp at hbc
    · rw [hD3.1] at ht; simp at ht
    · rw [hA3.1] at ht; simp at ht
    · rw [htwD3.1] at ht; simp at ht
    · rw [htwA3.1] at ht; simp at ht
    · rw [hD2.1] at ht; simp at ht
    · rw [hA1.2] at ht; simp at ht
  · rcases h with rfl | hBC | hD3 | hA3 | htwD3 | htwA3 | hD2 | hA1
    · rfl
    · rcases hBC with ⟨hbc, -⟩; rw [ht] at hbc; simp at hbc
    · rw [hD3.1] at ht; simp at ht
    · rw [hA3.1] at ht; simp at ht
    · rw [htwD3.1] at ht; simp at ht
    · rw [htwA3.1] at ht; simp at ht
    · rw [hD2.1] at ht; simp at ht
    · rw [hA1.2] at ht; simp at ht


theorem exists_K_E6Label_of_endpoint_facts
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Idx)
    (he : ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpairK : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs) :
    ∃ labK : LargeEvenLabel, GGE6DepLabel labK ∧ LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMK : MK = CoxeterMatrix.E₆.reindex e :=
    ggIntCartan_E6_coxeter_reindex hCKK e he
  have hE6 : GGIsTypeE6 MK := ⟨e, hMK⟩
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 51840 :=
    card_ggAutomizer_of_typeE6 hE6 fK
  have h5 : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 5 ≤ Nat.card ↥(ggGamma K hN).range := by
    intro hN
    exact five_le_card_range_of_e6_datum hN ι φ h α hCKK hE6 hlin hpairK hφ
  have hMarkK : GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs K :=
    GGResHyp.e6_marking_of_endpoint_facts hH (Or.inr rfl) hcardBs h5 hcardK
  obtain ⟨labK, hK2, hlK, R, _, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hMarkK
  exact ⟨labK, hP.1, hK2, hlK⟩


theorem narrow_tableP_excludes_twA4_twE6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hres : GGTwE6ExactTwoPSU5Residual Bs L J)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    (e : Fin 6 ≃ Idx)
    (he : ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j)
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpairK : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs) :
    False := by
  obtain ⟨labK, hKE6, hK2, hlK⟩ :=
    exists_K_E6Label_of_endpoint_facts hH hcardBs hCKK e he fK ι φ h α hlin hpairK hφ
  obtain ⟨labL, labJ, hlabL, hlabJ, hL2, hlL, hMarkL, hJ2, hlJ, hMarkJ⟩ := hres
  have hR : GGRegimeB36L 3 (Nat.card Bs) labL labJ labK := by
    refine ⟨rfl, hcardBs, ?_⟩
    rw [hlabL]
    exact Or.inr rfl
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hrow := hB36 G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
    (hH.2.2.1.2 y K hnb) hnb labL labJ labK hL2 hJ2 hK2 hR hlL hlJ hlK
  obtain ⟨labJ', labK', hJ2', hK2', hrow, hlJ', hlK'⟩ := hrow
  have hisoJ : GGLabelIso (⟨.twA, 4, 1⟩ : LargeEvenLabel) labJ' := by
    simpa [hlabJ] using ggLabelRigidInput_holds _ _ _ hJ2 hJ2' hlJ hlJ'
  have hJeq : labJ' = ⟨.twA, 4, 1⟩ := GGLabelIso.eq_of_twA4_narrow hisoJ
  have hisoK : GGLabelIso labK labK' :=
    ggLabelRigidInput_holds _ _ _ hK2 hK2' hlK hlK'
  have hKeq : labK' = labK := GGLabelIso.eq_of_E6_narrow hisoK hKE6
  rw [hJeq, hKeq] at hrow
  exact not_tablePRow_twA4_E6_narrow hKE6 hrow


end Certs

section Certs


end Certs

section Certs


open CFSG CFSG.StandardType.Line63.H5


end Certs

open Module Matrix


open CFSG.Assembly


section ActualKOnlyE6Containment


end ActualKOnlyE6Containment


section AschbacherKOnlyIndependentContext


end AschbacherKOnlyIndependentContext


end CFSG.StandardType
