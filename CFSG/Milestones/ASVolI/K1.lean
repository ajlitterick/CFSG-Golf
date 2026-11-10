module

public import CFSG.Milestones.ASVolI.I8
public import CFSG.Quasithin.Background.SmithB42Alt6
public import CFSG.Quasithin.Background.SmithB45Alt6
public import CFSG.Quasithin.Background.SmithB45HatA6
public import CFSG.Quasithin.EmptyFaithful.LRed14B45
public import CFSG.Quasithin.Background.SmithB42Alt7
public import CFSG.Quasithin.Background.SmithB45Alt7
public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.Background.SmithB45Sp4Main
public import CFSG.Quasithin.Background.HSU3NPrime
public import CFSG.Quasithin.Background.SmithB45U33Main
public import CFSG.Quasithin.Background.SmithB45G2Main
public import CFSG.Quasithin.Background.SmithB42G2Main
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.H13.L32A753d
public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.Background.SmithB45Tits
public import CFSG.Quasithin.Background.SmithB45D4
public import CFSG.Quasithin.Background.SmithB42LnL42
public import CFSG.Quasithin.Background.SmithB42LnL52
public import CFSG.Quasithin.H13.A5Quad8
public import CFSG.Quasithin.Background.SmithB45LnL4Main
public import CFSG.Quasithin.Background.SmithB45LnL5Main
public import CFSG.Quasithin.Background.SmithB45SL3L32
public import CFSG.Quasithin.Background.SmithB45SL3Even
public import CFSG.Quasithin.Background.SmithB42SL3Even
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.B1More13
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.SmithB51SL3M
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A5S1520c
public import CFSG.Quasithin.H13.A5S1520d
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.L32A753b
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocRadMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped MatrixGroups


@[expose] def IsSLn (n q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ Nonempty (X ≃* ↥(StatedSL n K))


section Vocab2

variable {V : Type} [CommGroup V]


namespace OrthogonalFourCoordinates

variable {L : Subgroup (MulAut V)} {s : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]


end OrthogonalFourCoordinates

end Vocab2

section MarkedGeometry

variable {V : Type} [CommGroup V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]


end MarkedGeometry

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open


section BurnsideKA


end BurnsideKA

section


end


section BurnsideKE


end BurnsideKE

section


end


section BurnsideKB


end BurnsideKB


section BurnsideKC


section


end


section


end

section


end


section


end


section Conj

variable {W : Type*} [CommGroup W]


end Conj


end BurnsideKC

section


end


section


end


section


end


section


end


section BurnsideKD


end BurnsideKD

section


end


section


end


section BurnsideK3


section Ctx

open CFSG.Quasithin CFSG.Quasithin.B45Sp4 CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

@[expose] def burnsideK3_pi {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* ↥(antiSp K)) : ↥(antiSp K) →* (W ≃ₗ[ZMod 2] W) :=
  (binPsi θ).toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)


structure burnsideK3_Ctx (V : Type) [CommGroup V] (L : Subgroup (MulAut V)) (a : ℕ) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  W : Type
  [instAC : AddCommGroup W]
  [instMod : Module (ZMod 2) W]
  [instFW : Finite W]
  hK : Nat.card K = 2 ^ (2 * a)
  θ : V ≃* Multiplicative W
  θL : ↥L ≃* ↥(antiSp K)
  [irr : Fact (repOf (burnsideK3_pi θ θL)).IsIrreducible]
  hD : Nat.card (EndRing (repOf (burnsideK3_pi θ θL))) = 2 ^ a
  hdim : Module.finrank (EndRing (repOf (burnsideK3_pi θ θL))) W = 16
  j : ℕ
  φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K)
  hφ : ∀ (g : ↥(antiSp K)) (w : W),
    (φ (burnsideK3_pi θ θL g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (antiSpEquiv K ((minorAut K ^ j) g))) (φ w)

attribute [instance] burnsideK3_Ctx.instField burnsideK3_Ctx.instFinite burnsideK3_Ctx.instChar
  burnsideK3_Ctx.instAC burnsideK3_Ctx.instMod burnsideK3_Ctx.instFW burnsideK3_Ctx.irr


open CFSG.Quasithin.B45Sp4 in
@[expose] noncomputable def burnsideK3_twAdd {K : Type} [Field K] [CharP K 2] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a)) (y : ↥(StatedSp 2 K)) :
    ↥(hermA a (Fin 2 ⊕ Fin 2) K) ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K) where
  toFun Y := ⟨tw a (spMat y) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    tw_mem_hermA hK _ Y.2⟩
  invFun Y := ⟨tw a (spMat y⁻¹) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    tw_mem_hermA hK _ Y.2⟩
  left_inv Y := by
    apply Subtype.ext
    show tw a (spM y⁻¹) (tw a (spM y) _) = _
    rw [← tw_mul, ← spM_mul, inv_mul_cancel, spM_one, tw_one]
  right_inv Y := by
    apply Subtype.ext
    show tw a (spM y) (tw a (spM y⁻¹) _) = _
    rw [← tw_mul, ← spM_mul, mul_inv_cancel, spM_one, tw_one]
  map_add' Y Z := by
    apply Subtype.ext
    exact tw_add a _ _ _


structure burnsideK3_Coord (V : Type) [CommGroup V] (L : Subgroup (MulAut V)) (a : ℕ) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  W : Type
  [instAC : AddCommGroup W]
  [instMod : Module (ZMod 2) W]
  hK : Nat.card K = 2 ^ (2 * a)
  θ : V ≃* Multiplicative W
  δ : ↥L ≃* ↥(StatedSp 2 K)
  φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K)
  hφL : ∀ (l : ↥L) (w : W),
    (φ (binPsi θ (l : MulAut V) w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (δ l)) (φ w)

attribute [instance] burnsideK3_Coord.instField burnsideK3_Coord.instFinite
  burnsideK3_Coord.instChar burnsideK3_Coord.instAC burnsideK3_Coord.instMod


@[reducible, expose] noncomputable def burnsideK3_Coord.conj {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {a : ℕ} (c : burnsideK3_Coord V L a) (y : ↥(StatedSp 2 c.K)) : burnsideK3_Coord V L a where
  K := c.K
  W := c.W
  hK := c.hK
  θ := c.θ
  δ := c.δ.trans (MulAut.conj y)
  φ := c.φ.trans (burnsideK3_twAdd c.hK y)
  hφL := fun l w => by
    show (tw a (spMat y) ((c.φ (binPsi c.θ (l : MulAut V) w) :
      ↥(hermA a (Fin 2 ⊕ Fin 2) c.K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) c.K)) =
      tw a (spMat (y * c.δ l * y⁻¹)) (tw a (spMat y) ((c.φ w : ↥(hermA a (Fin 2 ⊕ Fin 2) c.K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) c.K))
    rw [c.hφL, ← tw_mul, ← tw_mul]
    show tw a (spM y * spM (c.δ l)) _ = tw a (spM (y * c.δ l * y⁻¹) * spM y) _
    rw [← spM_mul, ← spM_mul, mul_assoc, inv_mul_cancel, mul_one]


section Sym

open Matrix


end Sym

section FixF

open CFSG.Quasithin.B45Sp4


end FixF


section Inn

open CFSG.Quasithin CFSG.Quasithin.B42Sp4 CFSG.Quasithin.B45Sp4 CFSG.Quasithin.H.Sp4 CFSG.Assembly.LowTwoRank
open scoped Matrix


end Inn

section Out

open CFSG.Quasithin CFSG.Quasithin.B45Sp4 CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open scoped Matrix


end Out


end Ctx

end BurnsideK3

section


end


section


end


section


end


section


end

end CFSG.ASVolI
