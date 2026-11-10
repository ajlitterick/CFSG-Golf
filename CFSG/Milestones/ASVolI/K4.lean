module

public import CFSG.Milestones.ASVolI.K1
public import CFSG.Quasithin.Background.HFCode22Dual
public import CFSG.Quasithin.Background.SmithB45Holds
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import Certificates.Certificate7275
public import Certificates.Certificate7276
public import Certificates.Certificate7277
public import Certificates.Certificate7278
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.S153ZO
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Monster.Code


section M24Vocab

variable {V : Type} [CommGroup V] {M : Subgroup (MulAut V)}


end M24Vocab

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Monster.Code

@[expose] def K_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (∃ s : TauCeti.SporadicName, IsSporadic s (Lbar L)) →
    ((IsSporadic .M12 ↥L ∧ M12Ten L ⊤ ⊥ ∧ Nat.card V = 2 ^ 10) ∨
      (Mhat22Twelve L ⊤ ⊥ ∧ Nat.card V = 2 ^ 12) ∨
      (IsSporadic .M22 ↥L ∧ (MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 10) ∨
      (IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 11) ∨
      (IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥) ∧
        Nat.card V = 2 ^ 11) ∨
      (IsSporadic .J2 ↥L ∧ J2Twelve L ⊤ ⊥ ∧ Nat.card V = 2 ^ 12)) ∧
    ¬ IsFFModule G ∧ qc 1 < qhatOf G

section BurnsideKF

open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour CFSG.Quasithin.H in

open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H
  CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1 in


open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in

open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.Family in


end BurnsideKF

section
open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin CFSG.Quasithin.B45Mat CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique


end


section BurnsideKG


end BurnsideKG

section


end


section


end


section BurnsideK42


section Chain
variable {G X : Type*} [Group G] [MulAction G X]


end Chain

section ElemAbelian


end ElemAbelian

section Zpowers


end Zpowers

section Arr
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

abbrev burnsideK42_K : Type := ↥CFSG.Monster.Code.AutPerm


@[expose] def burnsideK42_e0 : G6.PermMod 24 := Multiplicative.ofAdd (bvec 24 e0mask)


section TArr


end TArr

noncomputable abbrev burnsideK42_rho : burnsideK42_K →* MulAut W11 :=
  rhoC11 CFSG.Monster.Code.AutPerm le_rfl


section TArr2


end TArr2


section Conj


end Conj

end Arr

section Mod
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

@[expose] def burnsideK42_MO0 : Subgroup burnsideK42_K :=
  (m24Fix burnsideK42_e0).subgroupOf CFSG.Monster.Code.AutPerm


structure burnsideK42_Std {V : Type} [CommGroup V] (θ : burnsideK42_K →* MulAut V)
    (ε : V ≃* W11) (V5 : Subgroup V) : Prop where
  hε : ∀ (γ : burnsideK42_K) (v : V), ε (θ γ v) = burnsideK42_rho γ (ε v)
  inv : ∀ γ ∈ burnsideK42_MO0, ∀ v ∈ V5, θ γ v ∈ V5
  card : Nat.card V5 = 32

variable {V : Type} [CommGroup V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}


variable [Finite V]


section Z0
variable
  {z0K : burnsideK42_K} (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hz0


end Z0


section Dz
variable
  (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
  (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hS hz0


end Dz


section DZfacts


end DZfacts


section SCb
variable (hS : burnsideK42_Std θ ε V5)
include hS


end SCb

section SC
variable
  (hS : burnsideK42_Std θ ε V5) {z0K : burnsideK42_K}
  (hz0 : HasArr (z0K : Equiv.Perm (Fin 24)) z0Arr)
include hS hz0


end SC

end Mod

section PCoreGen


end PCoreGen

section SylowC
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end SylowC

section Arrays
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end Arrays

section Sylow2
open scoped Pointwise


end Sylow2

section PCoreK
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end PCoreK

section Parts
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end Parts

section PCoreK2
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end PCoreK2

section VLevel
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end VLevel

section VLevel2
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}


end VLevel2

section SubgroupAlg


end SubgroupAlg

section QuadW
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end QuadW

section FourK
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end FourK

section Conj4
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}


end Conj4

section StdMain
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data

variable {V : Type} [CommGroup V] [Finite V] {θ : burnsideK42_K →* MulAut V} {ε : V ≃* W11}
  {V5 : Subgroup V}


end StdMain

section Remark
open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.K43Data


end Remark

end BurnsideK42

section


end


section


end


section


end

@[expose] def K_4_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (((IsSporadic .M24 ↥L ∧ (MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥)) ∨
        (IsSporadic .M23 ↥L ∧ (MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥)) ∨
        (IsSporadic .M22 ↥L ∧ MathieuCocode22 L ⊤ ⊥)) → qc 2 < qOf G) ∧
    ((IsSporadic .M22 ↥L ∧ MathieuCode22 L ⊤ ⊥) → qc 2 ≤ qOf G)

section


end

@[expose] def K_4_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsSporadic .M12 ↥L → M12Ten L ⊤ ⊥ → qc 2 < qOf G

section


end

@[expose] def K_4_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsSporadic .J2 ↥L → J2Twelve L ⊤ ⊥ →
      (L.subgroupOf G).index ≤ 2 ∧ (∀ A, ¬ IsFFStarOffender G A) ∧ qc 1 < qhatOf G ∧
      qhatOf G = qc 2 ∧ qc 2 < qOf G ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G →
        ∀ A : Subgroup (MulAut V), IsA2 T A → rAV A ≤ 2 →
          A ≤ L ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4 ∧ ¬ IsQuadratic A) ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G →
        ∃ A : Subgroup (MulAut V), IsA2 T A ∧ commSeries A 3 = ⊥ ∧ rAV A = 2 ∧
          A ≤ L ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4 ∧ ¬ IsQuadratic A)

section
open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H


end

end CFSG.ASVolI
