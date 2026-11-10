module

public import CFSG.Quasithin.Background.ASVolIRegistered
public import CFSG.LocalAnalysis.SectionRank.QTK.Main
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG24
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.Recognition.HNMultiplier

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups


@[expose] noncomputable def permRepF2 (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (Fin n → ZMod 2) where
  toFun σ := LinearMap.funLeft (ZMod 2) (ZMod 2) (σ.symm : Fin n → Fin n)
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [LinearMap.funLeft, Equiv.Perm.mul_def]

@[expose] def evenWeight (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx, mul_zero]

theorem evenWeight_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    evenWeight n ≤ (evenWeight n).comap (permRepF2 n σ) := by
  intro v hv
  have hv' : ∑ i, v i = 0 := hv
  show ∑ i, (permRepF2 n σ v) i = 0
  have : (∑ i : Fin n, (permRepF2 n σ v) i) = ∑ i : Fin n, v i := by
    simp only [permRepF2, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
    exact Equiv.sum_comp σ.symm v
  rw [this]; exact hv'

@[expose] noncomputable def evenWeightRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n) :=
  (permRepF2 n).subrepresentation (evenWeight n) (evenWeight_inv n)

@[expose] def constInEven (n : ℕ) : Submodule (ZMod 2) (evenWeight n) :=
  (Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}).comap (evenWeight n).subtype

theorem constInEven_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    constInEven n ≤ (constInEven n).comap (evenWeightRep n σ) := by
  intro v hv
  have hv' : (v : Fin n → ZMod 2) ∈
      Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := hv
  rw [Submodule.mem_span_singleton] at hv'
  obtain ⟨c, hc⟩ := hv'
  show ((evenWeightRep n σ v : evenWeight n) : Fin n → ZMod 2) ∈
    Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}
  rw [Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  funext i
  have := congrFun hc (σ.symm i)
  simpa [evenWeightRep, permRepF2, LinearMap.funLeft] using this

@[expose] noncomputable def symNaturalRep (n : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin n)) (evenWeight n ⧸ constInEven n) :=
  (evenWeightRep n).quotient (constInEven n) (constInEven_inv n)


section Zorn


end Zorn

section G2Module


end G2Module


end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups


section BurnsideI12


end BurnsideI12


section BurnsideI13_only13


end BurnsideI13_only13

section


end


section G24


end G24


section


end


section


end


end CFSG.ASVolI
