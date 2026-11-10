module

public import CFSG.Quasithin.Background.HL3WrBlock
public import CFSG.Quasithin.Background.RonanH43One
public import CFSG.Quasithin.Background.RonanH43Two
public import CFSG.Quasithin.Background.RonanH49Orbit
public import CFSG.Quasithin.Background.RonanH49Wr
public import CFSG.Quasithin.Background.RonanH49Chief
public import CFSG.Quasithin.Background.RonanH49Y
public import CFSG.Quasithin.Background.RonanH49D
public import CFSG.Quasithin.Background.RonanH49Tr
public import CFSG.Quasithin.Background.RonanH49Irr
public import CFSG.Quasithin.Background.RonanH412Main
public import CFSG.Quasithin.Background.RonanH44Six
public import CFSG.Quasithin.Background.RonanH44TwoMain
public import CFSG.Quasithin.Background.RonanH44Num
public import CFSG.Quasithin.Background.RonanH44Five
public import CFSG.Quasithin.Background.RonanH45D
public import CFSG.Quasithin.Background.RonanH46One
public import CFSG.Quasithin.Background.RonanH46Three
public import CFSG.Quasithin.Background.RonanH46TwoB
public import CFSG.Quasithin.Background.RonanH46Chief
public import CFSG.Quasithin.Background.RonanH46ChiefTop
public import CFSG.Quasithin.Background.RonanH46Transv
public import CFSG.Quasithin.Background.RonanH46TransvFull
public import CFSG.Quasithin.Background.RonanH46OzZ
public import CFSG.Quasithin.Background.H47WMain
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.RonanH412Odd
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

section Pair

open CFSG.Quasithin.H.SL3Pair

abbrev PV : Type := PairMod (ZMod 2)

@[expose] def swapT : MulAut PV := MulEquiv.prodComm

@[expose] def b1 (i : Fin 3) : PV := (Multiplicative.ofAdd (Pi.single i 1), 1)

@[expose] def b2 (i : Fin 3) : PV := swapT (b1 i)

@[expose] def pairQ (x : PV) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd x.1 i * Multiplicative.toAdd x.2 i

@[expose] def pairPolar (x y : PV) : ZMod 2 := pairQ (x * y) + pairQ x + pairQ y

@[expose] def V1sub : Subgroup PV := (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).prod ⊥

@[expose] noncomputable def groupLT : Subgroup (MulAut PV) :=
  pairSL (ZMod 2) ⊔ Subgroup.zpowers swapT

end Pair

section Nine

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def slStab (S : Set (Fin 3 → K)) : Subgroup SL(3, K) :=
  (glStab S).comap SpecialLinearGroup.toGL

@[expose] def spW (K : Type) [Field K] : Set (Fin 3 → K) := {v | v 2 = 0}

@[expose] def spZ (K : Type) [Field K] : Set (Fin 3 → K) := {v | v 1 = 0 ∧ v 2 = 0}

@[expose] def tvSL (i j : Fin 3) (h : i ≠ j) (c : K) : SL(3, K) :=
  SpecialLinearGroup.transvection h c

@[expose] def QWsl (K : Type) [Field K] : Subgroup SL(3, K) :=
  Subgroup.closure {g | ∃ c : K, g = tvSL 0 2 (by decide) c ∨ g = tvSL 1 2 (by decide) c}

@[expose] def QZsl (K : Type) [Field K] : Subgroup SL(3, K) :=
  Subgroup.closure {g | ∃ c : K, g = tvSL 0 1 (by decide) c ∨ g = tvSL 0 2 (by decide) c}

@[expose] noncomputable def PWL (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (slStab (spW K)).map (rho hK)

@[expose] noncomputable def QWL (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (QWsl K).map (rho hK)

@[expose] noncomputable def PZL (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (slStab (spZ K)).map (rho hK)

@[expose] noncomputable def QZL (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (QZsl K).map (rho hK)

@[expose] noncomputable def sigmaAut (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    MulAut (HMod n K) :=
  fldAut (bar n)

@[expose] def IsFHyperplane (n : ℕ) (H : Subgroup (HMod n K)) : Prop :=
  (∀ (c : K) (X Y : HMod n K), bar n c = c → X ∈ H → mat Y = c • mat X → Y ∈ H) ∧ rkIdx H = n

@[expose] def hermWBlock (X : HMod n K) : Matrix (Fin 2) (Fin 2) K :=
  fun row col => mat X (Fin.castLE (by decide) row) (Fin.castLE (by decide) col)

@[expose] def HermWParabolicAction (hK : Nat.card K = (2 ^ n) ^ 2) : Prop :=
  ∃ action : ↥(slStab (spW K)) →* GL (Fin 2) K,
    Function.Surjective action ∧
    (∀ groupElement : ↥(slStab (spW K)), action groupElement = 1 ↔
      (groupElement : SL(3, K)) ∈ QWsl K) ∧
    (∀ groupElement : ↥(slStab (spW K)), ∀ row col : Fin 2,
        (action groupElement : Matrix (Fin 2) (Fin 2) K) row col =
          ((groupElement : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
            (Fin.castLE (by decide) row) (Fin.castLE (by decide) col)) ∧
    (∀ block : Matrix (Fin 2) (Fin 2) K,
      (block.map (bar n))ᵀ = block →
      ∃ vector ∈ fixV (QWL hK), hermWBlock vector = block) ∧
    (∀ (groupElement : ↥(slStab (spW K))) (vector : HMod n K),
      vector ∈ fixV (QWL hK) →
      rho hK (groupElement : SL(3, K)) vector ∈ fixV (QWL hK) ∧
      hermWBlock (rho hK (groupElement : SL(3, K)) vector) =
        (action groupElement : Matrix (Fin 2) (Fin 2) K) * hermWBlock vector *
          ((action groupElement : Matrix (Fin 2) (Fin 2) K).map (bar n))ᵀ ∧
      (hermWBlock (rho hK (groupElement : SL(3, K)) vector)).det =
        ((action groupElement : Matrix (Fin 2) (Fin 2) K).det *
          bar n ((action groupElement : Matrix (Fin 2) (Fin 2) K).det)) *
            (hermWBlock vector).det)

@[expose] def IsNineFixedField {F : Type} [Field F] (scalar : F →+* K) : Prop :=
  Nat.card F = 2 ^ n ∧
    ∀ coefficient : K, bar n coefficient = coefficient ↔
      ∃ fixedCoefficient : F, scalar fixedCoefficient = coefficient

@[expose] def NineOrthogonalBlock {F : Type} [Field F] (scalar : F →+* K)
    (anisotropicCoefficient : F) (hK : Nat.card K = (2 ^ n) ^ 2) : Prop :=
  ∃ coordinates : ↥(fixV (QWL hK)) ≃* Multiplicative (Fin 4 → F),
    (∀ (coefficient : F) (vector scaled : ↥(fixV (QWL hK))),
      mat (scaled : HMod n K) = scalar coefficient • mat (vector : HMod n K) →
      Multiplicative.toAdd (coordinates scaled) =
        coefficient • Multiplicative.toAdd (coordinates vector)) ∧
    (∀ vector : ↥(fixV (QWL hK)),
      (hermWBlock (vector : HMod n K)).det =
        scalar (orthMinus F anisotropicCoefficient (Multiplicative.toAdd (coordinates vector)))) ∧
    (∀ groupElement ∈ perfectCore (PWL hK),
      ∃ isometry ∈ omegaFour F (orthMinus F anisotropicCoefficient),
        ∀ vector image : ↥(fixV (QWL hK)),
          (image : HMod n K) = groupElement vector →
          coordinates image = isometry (coordinates vector)) ∧
    (∀ isometry ∈ omegaFour F (orthMinus F anisotropicCoefficient),
      ∃ groupElement ∈ perfectCore (PWL hK),
        ∀ vector image : ↥(fixV (QWL hK)),
          (image : HMod n K) = groupElement vector →
          coordinates image = isometry (coordinates vector))

@[expose] def NineFaithfulSection {F : Type} [Field F] (scalar : F →+* K)
    (group : Subgroup (MulAut (HMod n K)))
    (upper lower : Subgroup (HMod n K)) (dimension : ℕ) : Prop :=
  lower ≤ upper ∧
    (∀ groupElement ∈ group, ∀ vector ∈ upper, groupElement vector ∈ upper) ∧
    (∀ groupElement ∈ group, ∀ vector ∈ lower, groupElement vector ∈ lower) ∧
    (∀ coefficient : F, ∀ vector scaled : HMod n K,
      vector ∈ upper → mat scaled = scalar coefficient • mat vector → scaled ∈ upper) ∧
    (∀ coefficient : F, ∀ vector scaled : HMod n K,
      vector ∈ lower → mat scaled = scalar coefficient • mat vector → scaled ∈ lower) ∧
    ∃ quotientMap : ↥upper →* Multiplicative (Fin dimension → F),
      Function.Surjective quotientMap ∧
      (∀ vector : ↥upper, quotientMap vector = 1 ↔ (vector : HMod n K) ∈ lower) ∧
      (∀ (coefficient : F) (vector scaled : ↥upper),
        mat (scaled : HMod n K) = scalar coefficient • mat (vector : HMod n K) →
        Multiplicative.toAdd (quotientMap scaled) =
          coefficient • Multiplicative.toAdd (quotientMap vector)) ∧
      ∃ action : ↥group →* ((Fin dimension → F) ≃ₗ[F] (Fin dimension → F)),
        Function.Injective action ∧
        ∀ (groupElement : ↥group) (vector image : ↥upper),
          (image : HMod n K) = (groupElement : MulAut (HMod n K)) vector →
          Multiplicative.toAdd (quotientMap image) =
            action groupElement (Multiplicative.toAdd (quotientMap vector))

end Nine

section Wr

open CFSG.Quasithin.H.L3Wr

@[expose] def xw (i j : Fin 3) : WMod := Multiplicative.ofAdd (Matrix.single i j 1)

@[expose] def yw (i j : Fin 3) : WMod := xw i j * xw j i

@[expose] def dW : WMod := xw 0 0 * xw 1 1 * xw 2 2

@[expose] def fstCoords (m : ℕ) : Set (Fin 3 → ZMod 2) := {v | ∀ j : Fin 3, m ≤ (j : ℕ) → v j = 0}

@[expose] def parabSL (m : ℕ) : Subgroup ↥SL32 := (glStab (fstCoords m)).comap SL32.subtype

@[expose] def fixSL (m : ℕ) : Subgroup ↥SL32 := (glFix (fstCoords m)).comap SL32.subtype

@[expose] noncomputable def Lw1 : Subgroup (MulAut WMod) :=
  ((⊤ : Subgroup ↥SL32).prod ⊥).map rho

@[expose] noncomputable def Lw2 : Subgroup (MulAut WMod) :=
  ((⊥ : Subgroup ↥SL32).prod ⊤).map rho

@[expose] noncomputable def Lw0 : Subgroup (MulAut WMod) := rho.range

@[expose] noncomputable def Gw : Subgroup (MulAut WMod) := Lw0 ⊔ Subgroup.zpowers tau

@[expose] noncomputable def Gwm (m : ℕ) : Subgroup (MulAut WMod) :=
  ((parabSL m).prod (parabSL m)).map rho ⊔ Subgroup.zpowers tau

@[expose] noncomputable def Rw : Subgroup (MulAut WMod) :=
  ((fixSL 2).prod (fixSL 2)).map rho

@[expose] def flagSL : Subgroup ↥SL32 := parabSL 1 ⊓ parabSL 2

@[expose] noncomputable def Tw : Subgroup (MulAut WMod) :=
  (flagSL.prod flagSL).map rho ⊔ Subgroup.zpowers tau

@[expose] def V5w : Subgroup WMod :=
  Subgroup.closure {xw 0 0, xw 0 1, xw 0 2, xw 1 0, xw 2 0}

@[expose] def traceZeroW : Subgroup WMod :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)))

end Wr

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.L3Wr

@[expose] def H_4_1 : Prop :=
  (∀ g ∈ groupLT, ∀ x : PV, pairQ (g x) = pairQ x) ∧
  (∀ v w : Multiplicative (Fin 3 → ZMod 2),
    pairPolar (v, 1) (1, w) = ∑ i, Multiplicative.toAdd v i * Multiplicative.toAdd w i) ∧
  (∀ v : Multiplicative (Fin 3 → ZMod 2), pairQ (v, 1) = 0) ∧
  (∀ w : Multiplicative (Fin 3 → ZMod 2), pairQ (1, w) = 0) ∧
  (∀ i j : Fin 3, pairPolar (b1 i) (b2 j) = if i = j then 1 else 0)


section H42


end H42

@[expose] def H_4_2 : Prop :=
  (∀ v : PV, v ≠ 1 → (∃ g ∈ groupLT, g (b1 0) = v) ∨ (∃ g ∈ groupLT, g (b1 0 * b2 1) = v) ∨
      (∃ g ∈ groupLT, g (b1 0 * b2 0) = v)) ∧
  (¬ ∃ g ∈ groupLT, g (b1 0) = b1 0 * b2 1) ∧ (¬ ∃ g ∈ groupLT, g (b1 0) = b1 0 * b2 0) ∧
  (¬ ∃ g ∈ groupLT, g (b1 0 * b2 1) = b1 0 * b2 0) ∧
  (pairQ (b1 0) = 0 ∧ ¬ IsTwoCentralVec groupLT (b1 0)) ∧
  (pairQ (b1 0 * b2 1) = 0 ∧ IsTwoCentralVec groupLT (b1 0 * b2 1)) ∧
  pairQ (b1 0 * b2 0) = 1


@[expose] def H_4_3 : Prop :=
  ∀ M : Subgroup (MulAut PV), perfectCore M = pairSL (ZMod 2) → swapT ∈ M →
  ∀ A : Subgroup (MulAut PV), A ≤ M → IsElemAbelian2 A → Nat.card A = 4 →
    (¬ A ≤ pairSL (ZMod 2) → rk ↥(fixV A) = 2 ∧ rk ↥(xiSub A) = 5) ∧
    (A ≤ pairSL (ZMod 2) → ∃ g ∈ M,
      fixV (conjAut g A) = Subgroup.closure {b1 0, b2 1, b2 2} ∧ rk ↥(fixV (conjAut g A)) = 3 ∧
      xiSub (conjAut g A) = V1sub ⊔ fixV (conjAut g A) ∧ rk ↥(xiSub (conjAut g A)) = 5 ∧
      commOn (xiSub (conjAut g A)) (conjAut g A) = Subgroup.zpowers (b1 0))


section H44glue

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}


end H44glue

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 in
@[expose] def H_4_4 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
  (M : Subgroup (MulAut (HMod n K))), perfectCore M = img hK →
    (({X : Matrix (Fin 3) (Fin 3) K | ∀ g ∈ QWsl K, tw n (g : Matrix (Fin 3) (Fin 3) K) X = X} =
        {X | ∀ i j, (i = 2 ∨ j = 2) → X i j = 0}) ∧
      HermWParabolicAction hK ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ n ∧
        ∃ (scalar : F →+* K) (a : F), IsNineFixedField (n := n) scalar ∧
        (∀ t : F, t ^ 2 + t + a ≠ 0) ∧ NineOrthogonalBlock scalar a hK ∧
        InducesOn (perfectCore (PWL hK)) (fixV (QWL hK)) ⊥ (Multiplicative (Fin 4 → F))
          (omegaFour F (orthMinus F a))) ∧
    (∀ r ∈ img hK ⊓ Subgroup.centralizer ({sigmaAut n K} : Set (MulAut (HMod n K))),
      orderOf r = 2 → rk ↥(fixV (Subgroup.zpowers r)) = 5 * n ∧
      ∃ rh : SL(3, K), rho hK rh = r ∧ orderOf rh = 2 ∧
        ((M ⊓ centSub (fixV (Subgroup.zpowers r)) : Subgroup (MulAut (HMod n K))) :
            Set (MulAut (HMod n K))) =
          {x | (∃ (g : SL(3, K)) (c : K), (g : Matrix (Fin 3) (Fin 3) K) =
              1 + c • ((rh : Matrix (Fin 3) (Fin 3) K) - 1) ∧ rho hK g = x) ∧
            sigmaAut n K * x * (sigmaAut n K)⁻¹ = x}) ∧
    (∀ A : Subgroup (MulAut (HMod n K)), IsA2 M A →
      (3 * n ≤ rk ↥A ∨ (A ≤ img hK ∧ n < rk ↥A)) → 5 * n ≤ rkIdx (fixV A)) ∧
    (∀ A : Subgroup (MulAut (HMod n K)), IsA2 (img hK) A → rk ↥A = 4 * n →
      ¬ ∃ x ∈ M ⊓ Subgroup.normalizer (A : Set (MulAut (HMod n K))),
        orderOf x = 2 ^ (2 * n) - 1 ∧ rk ↥(fixV (A ⊔ Subgroup.zpowers x)) = 3 * n) ∧
    (∀ A : Subgroup (MulAut (HMod n K)), IsA2 M A → rk ↥A = 4 * n → rkIdx (fixV A) = 5 * n →
      ¬ ∃ x ∈ img hK, x ≠ 1 ∧ orderOf x = 2 ^ n - 1 ∧ ∀ v ∈ fixV A, x v = v) ∧
    (∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      rk ↥(fixV (Subgroup.zpowers i)) = 6 * n ∧
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i ∧
      (∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K)))) ≃* SL(3, F))) ∧
      rk ↥(commV (Subgroup.zpowers i)) = 3 * n ∧ rkIdx (fixV (Subgroup.zpowers i)) = 3 * n ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u ∈ commV (Subgroup.zpowers i), g u = u) → g = 1) ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u ∈ fixV (Subgroup.zpowers i), g u * u⁻¹ ∈ commV (Subgroup.zpowers i)) → g = 1) ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u : HMod n K, g u * u⁻¹ ∈ fixV (Subgroup.zpowers i)) → g = 1) ∧
      ∃ (F : Type) (_ : Field F) (scalar : F →+* K),
        IsNineFixedField (n := n) scalar ∧
        Nonempty (↥(img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K)))) ≃* SL(3, F)) ∧
        NineFaithfulSection scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))))
          (commV (Subgroup.zpowers i)) ⊥ 3 ∧
        NineFaithfulSection scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))))
          (fixV (Subgroup.zpowers i)) (commV (Subgroup.zpowers i)) 3 ∧
        NineFaithfulSection scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))))
          ⊤ (fixV (Subgroup.zpowers i)) 3) ∧
    ((Odd n → Nonempty (↥(img hK) ≃* PSL(3, K))) ∧ (Even n → Nonempty (↥(img hK) ≃* SL(3, K))))


open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 in
@[expose] def H_4_5 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
  (M : Subgroup (MulAut (HMod n K))), perfectCore M = img hK →
  ∀ T : Subgroup (MulAut (HMod n K)), IsSylowIn 2 T M →
    T ⊓ img hK ≤ (slStab (spZ K) ⊓ slStab (spW K)).map (rho hK) →
  ∀ A ∈ E3.aSet (2 * n + 1) T,
    A ≤ QWL hK ∧
    (3 * n < rk ↥A → IsFHyperplane n (E3.gammaCheck (3 * n) A)) ∧
    E3.aParam M = 3 * n


open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 in
@[expose] def H_4_6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
  (M : Subgroup (MulAut (HMod 1 K))), perfectCore M = img hK →
    (∀ y ∈ M, Odd (orderOf y) → rk ↥(fixV (Subgroup.zpowers y)) = 5 →
      Subgroup.zpowers y = M ⊓ centSub (fixV (Subgroup.zpowers y)) ∧ orderOf y = 3) ∧
    (InducesOn (perfectCore (PWL hK)) (fixV (QWL hK)) ⊥ (Multiplicative (Fin 4 → ZMod 2))
        (omegaFour (ZMod 2) (orthMinus (ZMod 2) 1)) ∧
      ∃ (K' : Type) (_ : Field K'), Nat.card K' = 4 ∧
        InducesOn (perfectCore (PWL hK)) (commOn ⊤ (perfectCore (PWL hK))) (fixV (QWL hK))
          (Multiplicative (Fin 2 → K')) (natSub 2 K' (CFSG.Open.StatedSL 2 K'))) ∧
    (M ⊓ centSub (fixV (QWL hK)) = QWL hK ∨
      ∃ D : Subgroup (MulAut (HMod 1 K)), Nonempty (↥D ≃* Multiplicative (ZMod 3)) ∧
        Nonempty (↥(img hK ⊔ D) ≃* (GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K))) ∧
        M ⊓ centSub (fixV (QWL hK)) = QWL hK ⊔ D) ∧
    (∃ V₂ : Subgroup (HMod 1 K),
      (IsChiefFactorUnder (actsOnModule (perfectCore (PZL hK))) ⊥ (fixV (QZL hK)) ∧
        rk ↥(fixV (QZL hK)) = 1 ∧
        IsChiefFactorUnder (actsOnModule (perfectCore (PZL hK))) (fixV (QZL hK)) V₂ ∧
        IsChiefFactorUnder (actsOnModule (perfectCore (PZL hK))) V₂ ⊤ ∧
        (∃ (K' : Type) (_ : Field K'), Nat.card K' = 4 ∧
          InducesOn (perfectCore (PZL hK)) V₂ (fixV (QZL hK)) (Multiplicative (Fin 2 → K'))
            (natSub 2 K' (CFSG.Open.StatedSL 2 K'))) ∧
        (∀ q ∈ QZL hK, ∀ x ∈ V₂, q x * x⁻¹ ∈ fixV (QZL hK)) ∧
        (∀ τ : MulAut ↥V₂, (∀ x : ↥V₂, ((τ x : ↥V₂) : HMod 1 K) * ((x : ↥V₂) : HMod 1 K)⁻¹ ∈
            fixV (QZL hK)) → ∃ q ∈ QZL hK, ∀ x : ↥V₂, q (x : HMod 1 K) = ((τ x : ↥V₂) : HMod 1 K)) ∧
        InducesOn (perfectCore (PZL hK)) ⊤ V₂ (Multiplicative (Fin 4 → ZMod 2))
          (omegaFour (ZMod 2) (orthMinus (ZMod 2) 1))) ∧
      V₂ ≤ commOn ⊤ (perfectCore (PWL hK)) ∧
      (∀ x : HMod 1 K, x ∈ V₂ ↔ ∀ q ∈ QZL hK, q x * x⁻¹ ∈ fixV (QZL hK)))


open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 in
@[expose] def H_4_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M : Subgroup (MulAut V)) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2),
    Nonempty (↥(CFSG.generalizedFitting ↥M) ≃* PSL(3, K)) →
    IsIrredOn ((CFSG.generalizedFitting ↥M).map M.subtype) ⊤ →
    ∀ t ∈ M, orderOf t = 2 →
      3 ≤ rk ↥(commV (Subgroup.zpowers t)) ∧
      (rk ↥(commV (Subgroup.zpowers t)) = 3 ↔
        ∃ e : V ≃* HMod 1 K,
          ((CFSG.generalizedFitting ↥M).map M.subtype).map (MulAut.congr e).toMonoidHom = img hK ∧
          ∃ l ∈ img hK, ∃ φ : K ≃+* K, φ ≠ 1 ∧ MulAut.congr e t = l * fldAut φ)

section H47

theorem as_H_4_7 : H_4_7 := by
  unfold H_4_7
  intro V _ _ hV M K _ _ _ hK hL hirr t htM ht2
  exact CFSG.Quasithin.H47W.H47_main V hV M K hK hL hirr t htM ht2

end H47

@[expose] def H_4_8 : Prop :=
  (conjAut tau Lw1 = Lw2 ∧ ∀ a : ↥SL32, tau * rho (a, 1) * tau⁻¹ = rho (1, a)) ∧
  Nonempty (↥Gw ≃* (↥SL32 ≀ᵣ Multiplicative (ZMod 2))) ∧
  (∀ m : ℕ, (m = 1 ∨ m = 2) → Tw ≤ Gwm m ∧ Gwm m ≤ Gw ∧ Gwm m ≠ Gw ∧
    ∀ H : Subgroup (MulAut WMod), Gwm m ≤ H → H ≤ Gw → H = Gwm m ∨ H = Gw) ∧
  IsSylowIn 2 Tw Gw ∧
  (commV (Subgroup.zpowers tau) = Subgroup.closure {yw 0 1, yw 0 2, yw 1 2} ∧
    rk ↥(commV (Subgroup.zpowers tau)) = 3 ∧
    fixV (Subgroup.zpowers tau) =
      commV (Subgroup.zpowers tau) ⊔ Subgroup.closure {xw 0 0, xw 1 1, xw 2 2} ∧
    commV (Subgroup.zpowers tau) ⊓ Subgroup.closure {xw 0 0, xw 1 1, xw 2 2} = ⊥)

@[expose] def H_4_9 : Prop :=
  ((∀ v : WMod, v ≠ 1 → (∃ g ∈ Lw0, g (xw 0 0) = v) ∨ (∃ g ∈ Lw0, g (yw 0 1) = v) ∨
      (∃ g ∈ Lw0, g dW = v)) ∧
    (¬ ∃ g ∈ Lw0, g (xw 0 0) = yw 0 1) ∧ (¬ ∃ g ∈ Lw0, g (xw 0 0) = dW) ∧
    (¬ ∃ g ∈ Lw0, g (yw 0 1) = dW)) ∧
  (Gw ⊓ centSub (Subgroup.zpowers (xw 0 0)) = Gwm 1 ∧
    Nonempty (↥(Gwm 1) ≃* (Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2))) ∧
    IsChiefFactorUnder (actsOnModule (Gwm 1)) (Subgroup.zpowers (xw 0 0)) V5w ∧
    IsChiefFactorUnder (actsOnModule (Gwm 1)) V5w ⊤) ∧
  (Gw ⊓ centSub (Subgroup.zpowers (yw 0 1)) ≤ Gwm 2 ∧
    (Gw ⊓ centSub (Subgroup.zpowers (yw 0 1))).relIndex (Gwm 2) = 6 ∧
    ∃ E : Subgroup (MulAut WMod), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      IsExtOf (Gw ⊓ centSub (Subgroup.zpowers (yw 0 1))) E
        (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∧
  (Nonempty (↥(Gw ⊓ centSub (Subgroup.zpowers dW)) ≃* MulAut ↥SL32) ∧
    commOn ⊤ (Gw ⊓ centSub (Subgroup.zpowers dW)) ⊔ Subgroup.zpowers dW = ⊤ ∧
    commOn ⊤ (Gw ⊓ centSub (Subgroup.zpowers dW)) ⊓ Subgroup.zpowers dW = ⊥ ∧
    commOn ⊤ (Gw ⊓ centSub (Subgroup.zpowers dW)) = traceZeroW ∧
    rk ↥(commOn ⊤ (Gw ⊓ centSub (Subgroup.zpowers dW))) = 8 ∧
    IsIrredOn (Gw ⊓ centSub (Subgroup.zpowers dW)) (commOn ⊤ (Gw ⊓ centSub (Subgroup.zpowers dW))))

@[expose] def H_4_10 : Prop :=
  ∃ a : ↥SL32,
    orderOf (rho (a, 1)) = 2 ∧
    (∀ v : Fin 3 → ZMod 2,
      (((a : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v ↔
        v ∈ fstCoords 2)) ∧
    (∀ v : Fin 3 → ZMod 2, v ∈ fstCoords 1 ↔
      ∃ w : Fin 3 → ZMod 2, v = ((a : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w - w) ∧
    ((∀ u : MulAut WMod, (u ∈ Lw1 ∨ u ∈ Lw2) → orderOf u = 2 → IsConjIn Gw (rho (a, 1)) u) ∧
      commV (Subgroup.zpowers (rho (a, 1))) = Subgroup.closure {xw 0 0, xw 0 1, xw 0 2}) ∧
    ((∀ u : MulAut WMod, u ∈ Lw0 → u ∉ Lw1 → u ∉ Lw2 → orderOf u = 2 →
        IsConjIn Gw (rho (a, 1) * (tau * rho (a, 1) * tau⁻¹)) u) ∧
      commV (Subgroup.zpowers (rho (a, 1) * (tau * rho (a, 1) * tau⁻¹))) =
        Subgroup.closure {xw 0 0, xw 0 1, xw 1 0, yw 0 2} ∧
      fixV (Subgroup.zpowers (rho (a, 1) * (tau * rho (a, 1) * tau⁻¹))) =
        commV (Subgroup.zpowers (rho (a, 1) * (tau * rho (a, 1) * tau⁻¹))) ⊔
          Subgroup.zpowers (xw 1 1)) ∧
    ((∀ u : MulAut WMod, u ∈ Gw → u ∉ Lw0 → orderOf u = 2 → IsConjIn Gw tau u) ∧
      rk ↥(commV (Subgroup.zpowers tau)) = 3 ∧ dW ∈ fixV (Subgroup.zpowers tau) ∧
      ¬ ∃ A : Subgroup (MulAut WMod), CFSG.Quasithin.H.IsFOneOffender Gw A ∧ tau ∈ A)

@[expose] def H_4_11 : Prop :=
  E3.aParam Gw = 2 ∧ (⨆ A ∈ E3.aSet 2 Tw, A) = Rw


section WrH48


end WrH48


section WrH410

open CFSG.Quasithin.H.L3Wr
open scoped Matrix


end WrH410


@[expose] def H_4_12 : Prop :=
  (∀ Y : Subgroup (MulAut WMod), Y ≤ Gw → Nat.card Y = 3 → NoncentralChiefCount (actsOnModule Y) ⊤ 3) ∧
  (∀ P : Subgroup (MulAut WMod), P ≤ Gwm 1 → P ≤ Lw0 → ¬ P ≤ Lw1 → ¬ P ≤ Lw2 → Nat.card P = 3 →
    NoncentralChiefCount (actsByConj P) (CFSG.Open.pCoreOf 2 (Gwm 1)) 2) ∧
  (∀ U : Subgroup WMod, rkIdx U < 6 → IsPGroup 2 ↥(Gw ⊓ centSub U))


end CFSG.ASVolI
