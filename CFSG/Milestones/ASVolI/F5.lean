module

public import CFSG.Quasithin.Background.SimsF5Asm7

public section

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

abbrev GL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)

abbrev V6 : Type := Fin 6 → ZMod 3

abbrev Sub6 : Type := Submodule (ZMod 3) V6

@[expose] def qV (v : V6) : ZMod 3 := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 - v 5 ^ 2

@[expose] def bil (u v : V6) : ZMod 3 := qV (u + v) - qV u - qV v

@[expose] def xvec (i : Fin 6) : V6 := Pi.single i 1

@[expose] def x1 : V6 := xvec 0
@[expose] def x2 : V6 := xvec 1
@[expose] def x3 : V6 := xvec 2
@[expose] def x4 : V6 := xvec 3
@[expose] def x5 : V6 := xvec 4
@[expose] def x6 : V6 := xvec 5

@[expose] def Iset : Finset (Fin 6) := {0, 1, 2, 3, 4}

@[expose] def commSp (g : GL6) : Sub6 :=
  LinearMap.range (Matrix.mulVecLin ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1))

@[expose] def fixSp (g : GL6) : Sub6 :=
  LinearMap.ker (Matrix.mulVecLin ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1))

@[expose] def IsNondegSub (W : Sub6) : Prop :=
  ∀ w ∈ W, (∀ w' ∈ W, bil w w' = 0) → w = 0

@[expose] def SignPlus (W : Sub6) : Prop :=
  IsNondegSub W ∧ Even (Module.finrank (ZMod 3) W) ∧
    ∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧ 2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W

@[expose] def SignMinus (W : Sub6) : Prop :=
  IsNondegSub W ∧ Even (Module.finrank (ZMod 3) W) ∧
    ¬ ∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧ 2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W

@[expose] def OVq : Subgroup GL6 := CFSG.MatrixModel.isometryCore qV

@[expose] def MDot : Subgroup GL6 := StatedOmega qV

@[expose] def eJd (J : Finset (Fin 6)) : Fin 6 → ZMod 3 := fun i => if i ∈ J then -1 else 1

theorem eJ_mat_sq (J : Finset (Fin 6)) :
    Matrix.diagonal (eJd J) * Matrix.diagonal (eJd J) = (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  unfold eJd
  split_ifs <;> decide

@[expose] def eJ (J : Finset (Fin 6)) : GL6 :=
  ⟨Matrix.diagonal (eJd J), Matrix.diagonal (eJd J), eJ_mat_sq J, eJ_mat_sq J⟩

@[expose] def fMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1]

theorem fMat_sq : fMat * fMat = 1 := by
  decide

@[expose] def fDot : GL6 := ⟨fMat, fMat, fMat_sq, fMat_sq⟩

@[expose] noncomputable def zDot : GL6 := eJ {0, 1, 2, 3}

@[expose] noncomputable def tDot : GL6 := eJ {0, 1}

@[expose] def spn (s : Set V6) : Sub6 := Submodule.span (ZMod 3) s

@[expose] def V2minus : Sub6 := spn {x1 - x2, x6}

@[expose] def V4minus : Sub6 := spn {x1 + x2, x3, x4, x5}

@[expose] def V4plus : Sub6 := spn {x1, x2, x3, x4}

@[expose] def V3plus : Sub6 := spn {x1, x2, x6}

@[expose] def Lambda : Set Sub6 := {S | ∃ i : Fin 6, S = spn {xvec i}}

@[expose] def M0Dot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 (spn {x6})

@[expose] def GDot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 x6

@[expose] def DDot : Subgroup GL6 := GDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)

@[expose] def CGDot12 : Subgroup GL6 := GDot ⊓ MulAction.stabilizer GL6 (x1 - x2)

@[expose] noncomputable def M1Dot : Subgroup GL6 := MDot ⊓ Subgroup.centralizer ({zDot} : Set GL6)

@[expose] def M2Dot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 Lambda

@[expose] noncomputable def Q2Dot : Subgroup GL6 :=
  Subgroup.closure {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J}

@[expose] noncomputable def Q1Dot : Subgroup GL6 := pCoreOf 2 M1Dot

@[expose] def SDot : Subgroup GL6 := pCoreOf 2 (M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}))

@[expose] def TDot : Subgroup GL6 := SDot ⊔ Subgroup.zpowers fDot

@[expose] def EDot (Mi : Subgroup GL6) : Subgroup GL6 := Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6)

@[expose] def ADot (Mi : Subgroup GL6) : Subgroup GL6 := pCoreOf 2 (EDot Mi)

@[expose] def IsEn (n : ℕ) (H : Type) [Group H] : Prop :=
  (∀ a b : H, a * b = b * a) ∧ (∀ a : H, a * a = 1) ∧ Nat.card H = 2 ^ n

@[expose] def Q8SqK : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.zpowers (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem Q8SqK_le_center : Q8SqK ≤ Subgroup.center (QuaternionGroup 2 × QuaternionGroup 2) := by
  rw [Q8SqK, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  rintro ⟨g1, g2⟩
  have h : ∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by decide
  exact Prod.ext (h g1) (h g2)

instance Q8SqK.normal : Q8SqK.Normal := Subgroup.normal_of_le_center Q8SqK_le_center

abbrev Q8Sq : Type := (QuaternionGroup 2 × QuaternionGroup 2) ⧸ Q8SqK

@[expose] def IsAutU42 (H : Type) [Group H] : Prop :=
  ∃ (G : Type) (_ : Group G), IsGenLie G GLKind.U4 2 1 ∧ Nonempty (H ≃* MulAut G)

@[expose] def qV5 (v : Fin 5 → ZMod 3) : ZMod 3 := ∑ i, v i ^ 2

@[expose] def qV4m (c : Fin 4 → ZMod 3) : ZMod 3 := -(c 0 ^ 2) + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2

@[expose] def bvec : Fin 4 → V6 := ![x1 + x2, x3, x4, x5]

@[expose] def bidx : Fin 4 → Fin 6 := ![0, 2, 3, 4]

@[expose] def blk4 (g : GL6) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)).mulVec (bvec j)) (bidx i)

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5

@[expose] def F_5_1 : Prop :=
  (IsL43 ↥MDot ∧
    ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card →
      eJ J ∈ OVq ∧ eJ J * eJ J = 1 ∧ commSp (eJ J) = spn {w | ∃ j ∈ J, w = xvec j} ∧
      fixSp (eJ J) = spn ({x6} ∪ {w | ∃ i ∈ Iset \ J, w = xvec i}) ∧
      ∀ g ∈ OVq, g * g = 1 → commSp g = spn {w | ∃ j ∈ J, w = xvec j} → g = eJ J) ∧
  (M0Dot = GDot ⊔ Subgroup.zpowers fDot ∧
    Nonempty (↥GDot ≃* ↥(StatedOmega qV5)) ∧ IsGenLie ↥GDot GLKind.U4 2 1 ∧
    (fDot ∈ MDot ∧ fDot * fDot = 1 ∧ fDot • x3 = x3 ∧ fDot • x4 = x4 ∧ fDot • x5 = x5 ∧
      fDot • x6 = -x6 ∧ fDot • x1 = x2) ∧
    ∀ g ∈ MDot, g * g = 1 → g • x3 = x3 → g • x4 = x4 → g • x5 = x5 → g • x6 = -x6 →
      g • x1 = x2 → g = fDot) ∧
  (Nonempty (↥M0Dot ≃* StatedProj (CFSG.MatrixModel.isometryCore qV5)) ∧ IsAutU42 ↥M0Dot) ∧
  (commSp fDot = V2minus ∧ Module.finrank (ZMod 3) V2minus = 2 ∧ SignMinus V2minus ∧
    fixSp fDot = V4minus ∧ Module.finrank (ZMod 3) V4minus = 4 ∧ SignMinus V4minus) ∧
  (DDot = CGDot12 ⊔ Subgroup.zpowers zDot ∧
    (∀ g ∈ CGDot12, ∀ h ∈ CGDot12, blk4 g = blk4 h → g = h) ∧
    (∀ B : Matrix (Fin 4) (Fin 4) (ZMod 3), (∃ g ∈ CGDot12, blk4 g = B) ↔
      ∃ u ∈ StatedOmega qV4m, (u : Matrix (Fin 4) (Fin 4) (ZMod 3)) = B) ∧
    (zDot ∈ GDot ∧ zDot * zDot = 1 ∧ commSp zDot = V4plus ∧ Module.finrank (ZMod 3) V4plus = 4 ∧
      SignPlus V4plus) ∧
    (∃ v ∈ V4minus, qV v ≠ 0 ∧ ∀ w ∈ V4minus, -(zDot • w) = w - (bil w v * (qV v)⁻¹) • v) ∧
    Nonempty (↥DDot ≃* Equiv.Perm (Fin 6)))


@[expose] def F_5_2 : Prop :=
  M1Dot = MDot ⊓ MulAction.stabilizer GL6 V4plus ∧
  (((Q2Dot : Set GL6) = {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J}) ∧
    IsEn 4 ↥Q2Dot ∧ Q2Dot ≤ M2Dot ∧ (Q2Dot.subgroupOf M2Dot).Normal ∧
    (∃ K : Subgroup GL6, K ≤ M2Dot ∧ K ⊓ Q2Dot = ⊥ ∧ Q2Dot ⊔ K = M2Dot ∧
      Nonempty (↥K ≃* Equiv.Perm (Fin 5))) ∧
    (Nonempty (↥Q1Dot ≃* Q8Sq) ∧
      ∃ K : Subgroup GL6, K ≤ M1Dot ∧ K ⊓ Q1Dot = ⊥ ∧ Q1Dot ⊔ K = M1Dot ∧
        Nonempty (↥K ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) ∧
  (IsAutU42 ↥M0Dot ∧ M1Dot ≤ M0Dot ∧ M2Dot ≤ M0Dot ∧ M1Dot ≠ M2Dot ∧
    TDot = SDot ⊔ Subgroup.zpowers fDot ∧
    IsSylowOf 2 TDot (M1Dot ⊓ M2Dot) ∧ IsSylowOf 2 TDot MDot ∧
    ∀ Q : Subgroup GL6,
      (TDot ≤ Q ∧ Q ≤ M0Dot ∧ Q ≠ M0Dot ∧ ∀ R' : Subgroup GL6, Q < R' → R' ≤ M0Dot → R' = M0Dot) ↔
        (Q = M1Dot ∨ Q = M2Dot))

section F52


end F52

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Abstract

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] def fOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) : M := bM β ε fb

@[expose] def TOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E) : Subgroup M := imB β ε Tb

@[expose] def M0Of (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M := MiOne β ε ⊔ MiTwo β ε

@[expose] def EOf (Mi : Subgroup M) (f : M) : Subgroup M := Mi ⊓ Subgroup.centralizer ({f} : Set M)

@[expose] def AOf (Mi : Subgroup M) (f : M) : Subgroup M := pCoreOf 2 (EOf Mi f)

@[expose] def QTwoOf (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))

@[expose] def IsTInv (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) (t : M) :
    Prop :=
  t ≠ 1 ∧ ⁅QTwoOf Gp β ε, Subgroup.zpowers (fOf β ε fb)⁆ = Subgroup.zpowers t

@[expose] def DOne (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) :
    Subgroup M :=
  (((cenIn (Gp ⊓ M₁) (fb : E)).subgroupOf M₁).map (f1 (c := β))).map (epsG β ε)

@[expose] def DTwo (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) :
    Subgroup M :=
  (((cenIn (Gp ⊓ M₂) (fb : E)).subgroupOf M₂).map (f2 (c := β))).map (epsG β ε)

end Abstract

@[expose] def IsTransvection {A : Type} [Group A] (τ : MulAut A) : Prop :=
  τ ≠ 1 ∧ Nat.card ↥(Subgroup.closure {x : A | ∃ a : A, x = τ a * a⁻¹}) = 2

@[expose] def U42Hermitian (K : Type) [Field K] (vectors other : Fin 4 → K) : K :=
  ∑ coordinate : Fin 4, vectors coordinate ^ 2 * other coordinate

@[expose] def U42ParabolicAt {E K : Type} [Group E] [Field K] (Gp parabolic : Subgroup E)
    (marking : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
    (space : Submodule K (Fin 4 → K)) : Prop :=
  parabolic ≤ Gp ∧ ∀ element : ↥Gp, (element : E) ∈ parabolic ↔
    ∃ matrix : ↥(StatedSU 4 2 K),
      marking element = (QuotientGroup.mk matrix : StatedProj (StatedSU 4 2 K)) ∧
      ∀ vector : Fin 4 → K,
        ((matrix : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec
          vector ∈ space ↔ vector ∈ space

@[expose] def U42MarkedGraphAmalgam {E : Type} [Group E]
    (Gp M₁ M₂ : Subgroup E) (actor : E) : Prop :=
  actor ∉ Gp ∧ actor * actor = 1 ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ (frobenius : K →+* K) (changeBasis : Matrix.GeneralLinearGroup (Fin 4) K),
        (∀ scalar : K, frobenius scalar = scalar ^ 2) ∧
        ((Matrix.transpose ((changeBasis : Matrix (Fin 4) (Fin 4) K).map frobenius)) *
          (changeBasis : Matrix (Fin 4) (Fin 4) K)) =
            Matrix.of (fun row column : Fin 4 =>
              if (row.val, column.val) = (0, 2) ∨ (row.val, column.val) = (1, 3) ∨
                (row.val, column.val) = (2, 0) ∨ (row.val, column.val) = (3, 1) then 1 else 0) ∧
        ∃ (marking : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
            (point plane : Submodule K (Fin 4 → K)),
          Module.finrank K point = 1 ∧ Module.finrank K plane = 2 ∧ point ≤ plane ∧
          (∀ vector ∈ plane, ∀ other ∈ plane, U42Hermitian K vector other = 0) ∧
          U42ParabolicAt Gp (Gp ⊓ M₁) marking point ∧
          U42ParabolicAt Gp (Gp ⊓ M₂) marking plane ∧
          ∀ element : ↥Gp, ∃ conjugate : ↥Gp,
            (conjugate : E) = actor * (element : E) * actor⁻¹ ∧
            ∀ matrix : ↥(StatedSU 4 2 K),
              marking element = (QuotientGroup.mk matrix : StatedProj (StatedSU 4 2 K)) →
                ∃ image : ↥(StatedSU 4 2 K),
                  marking conjugate = (QuotientGroup.mk image : StatedProj (StatedSU 4 2 K)) ∧
                  (image : Matrix.GeneralLinearGroup (Fin 4) K) =
                    changeBasis * (Matrix.GeneralLinearGroup.map frobenius changeBasis)⁻¹ *
                      Matrix.GeneralLinearGroup.map frobenius
                        (matrix : Matrix.GeneralLinearGroup (Fin 4) K) *
                          Matrix.GeneralLinearGroup.map frobenius changeBasis * changeBasis⁻¹

structure F5Amalgam {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) (actor : E) : Prop where
  finite : Finite E
  normal : Gp.Normal
  centralizer_trivial : Subgroup.centralizer (Gp : Set E) = ⊥
  gen : M₁ ⊔ M₂ = ⊤
  native : U42MarkedGraphAmalgam Gp M₁ M₂ actor
  split : ∀ element : E, ∃ inside ∈ Gp, ∃ localElement ∈ M₁ ⊓ M₂,
    element = inside * localElement
  dynkin : ∀ element : E,
    element ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) →
      element ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)

structure F5Completion {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (z : M) (actor : E) : Prop where
  amalgam : F5Amalgam Gp M₁ M₂ actor
  faithful : β.IsFaithful
  finite_M : Finite M
  inj : Function.Injective (epsG β ε)
  z_inv : z ≠ 1 ∧ z * z = 1
  z_mem : z ∈ ctr (oPPrime 2 (GiOne Gp β ε))
  ha : Subgroup.normalizer ((ctr (pCoreOf 2 (GiOne Gp β ε)) : Subgroup M) : Set M) =
      MiOne β ε ∧
    Subgroup.normalizer ((ctr (pCoreOf 2 (GiTwo Gp β ε)) : Subgroup M) : Set M) = MiTwo β ε
  hb : Subgroup.centralizer ({z} : Set M) ≤ MiOne β ε
  he : oTwoRes (⊤ : Subgroup M) = ⊤

structure HypF5 {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (z : M)
    (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) : Prop where
  f431 : F5Completion Gp M₁ M₂ β ε z (fb : E)
  Tb_syl : IsSylowOf 2 Tb (M₁ ⊓ M₂)
  fb_mem : (fb : E) ∈ Tb
  fb_syl : IsSylowOf 2
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
      (cenIn Gp (fb : E))
  not_i : ¬ IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
    (Subgroup.centralizer ({bM β ε fb} : Set M))

@[expose] def IsRSylow {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂))
    (R : Subgroup M) : Prop :=
  IsSylowOf 2 R (Subgroup.centralizer ({bM β ε fb} : Set M)) ∧
    imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M) ≤ R

structure IsMuIso {E : Type} [Group E] {M₁ M₂ : Subgroup E} (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁)
    (fb : ↥(M₁ ⊓ M₂)) : Prop where
  faithful : μ.IsFaithful
  img1 : μ.φ1.range.map M0Dot.subtype = M1Dot
  img2 : μ.φ2.range.map M0Dot.subtype = M2Dot
  img12 : μ.φ12.range.map M0Dot.subtype = M1Dot ⊓ M2Dot
  z_eq : ((μ.φ1 zb : ↥M0Dot) : GL6) = zDot
  f_eq : ((μ.φ12 fb : ↥M0Dot) : GL6) = fDot

@[expose] def IsMarkedMuIso {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁) (fb : ↥(M₁ ⊓ M₂)) (Tb : Subgroup E) : Prop :=
  IsMuIso μ zb fb ∧
    ((Tb.subgroupOf (M₁ ⊓ M₂)).map μ.φ12).map M0Dot.subtype = TDot

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def F_5_3 : Prop :=
  ((∀ Mi : Subgroup GL6, (Mi = M1Dot ∨ Mi = M2Dot) →
      Nonempty (↥(EDot Mi) ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) ∧
        IsEn 4 ↥(ADot Mi)) ∧
    (ADot M1Dot = Subgroup.zpowers fDot ⊔ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ ∧
      ADot M2Dot = Subgroup.zpowers fDot ⊔ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥) ∧
    (((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) : Set GL6) =
      {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) ∧
        g = eJ J}) ∧
    ({u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1} =
      {zDot} ∪ {u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1 ∧ u * u = 1 ∧
        commSp u ≤ V4plus ∧ Module.finrank (ZMod 3) (commSp u) = 2 ∧ SignMinus (commSp u)}) ∧
    ((∀ w : GL6, w ∈ MDot → w ≠ 1 → w * w = 1 →
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 4 ∧ SignPlus (commSp w))) ∧
        ((∃ g ∈ MDot, g * fDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 2 ∧ SignMinus (commSp w))) ∧
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ∨ (∃ g ∈ MDot, g * fDot * g⁻¹ = w))) ∧
      ¬ ∃ g ∈ MDot, g * zDot * g⁻¹ = fDot) ∧
    (⁅Q2Dot, Subgroup.zpowers fDot⁆ = Subgroup.zpowers tDot ∧ tDot ≠ 1)) ∧
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)),
    HypF5 Gp M₁ M₂ β ε z Tb fb →
    (∃ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z ∧ IsMarkedMuIso μ zb fb Tb) ∧
    (∀ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z → IsMarkedMuIso μ zb fb Tb →
      ∀ a : ↥(M₁ ⊓ M₂),
        (((∃ g ∈ MDot, g * zDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6)) ∧
            ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot) ↔
          (IsConj z (bM β ε a) ∧ bM β ε a ∈ TOf β ε Tb)) ∧
        (((∃ g ∈ MDot, g * fDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6)) ∧
            ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot) ↔
          (IsConj (fOf β ε fb) (bM β ε a) ∧ bM β ε a ∈ TOf β ε Tb))) ∧
    (∀ t : M, IsTInv Gp β ε fb t → IsConj z (fOf β ε fb * t * z)) ∧
    (({x : M | IsConj z x} ∩ (AOf (MiOne β ε) (fOf β ε fb) : Set M)).ncard = 5 ∧
      ({x : M | IsConj z x} ∩ (QTwoOf Gp β ε : Set M)).ncard = 5 ∧
      ({x : M | IsConj z x} ∩ (AOf (MiTwo β ε) (fOf β ε fb) : Set M)).ncard = 9)

section F53


end F53

@[expose] def F_5_4 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    ∀ t : M, IsTInv Gp β ε fb t →
      (AOf (MiOne β ε) (fOf β ε fb) =
          Subgroup.centralizer ((AOf (MiOne β ε) (fOf β ε fb) : Subgroup M) : Set M) ∧
        AOf (MiTwo β ε) (fOf β ε fb) =
          Subgroup.centralizer ((AOf (MiTwo β ε) (fOf β ε fb) : Subgroup M) : Set M)) ∧
      (Nonempty (↥R ≃* ↥(TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M))) ∧
        Nonempty (↥(TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M)) ≃*
          DihedralGroup 4 × DihedralGroup 4)) ∧
      (∀ Mi : Subgroup M, (Mi = MiOne β ε ∨ Mi = MiTwo β ε) →
        R ≤ Subgroup.normalizer (EOf Mi (fOf β ε fb) : Set M) ∧
        Nonempty (↥(EOf Mi (fOf β ε fb) ⊔ R) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4))) ∧
      ((∀ y : M, y ∈ TOf β ε Tb → y ∉ Subgroup.centralizer ({t} : Set M) →
          {A : Subgroup M | IsMaxElemAbelian (TOf β ε Tb) A} =
            {AOf (MiOne β ε) (fOf β ε fb), AOf (MiTwo β ε) (fOf β ε fb),
              cj y⁻¹ (AOf (MiTwo β ε) (fOf β ε fb)), QTwoOf Gp β ε}) ∧
        Nonempty (↥(Subgroup.normalizer (QTwoOf Gp β ε : Set M)) ⧸
          (QTwoOf Gp β ε).subgroupOf (Subgroup.normalizer (QTwoOf Gp β ε : Set M)) ≃*
            Equiv.Perm (Fin 5)) ∧
        Nonempty (↥(Subgroup.normalizer (AOf (MiOne β ε) (fOf β ε fb) : Set M)) ⧸
          (AOf (MiOne β ε) (fOf β ε fb)).subgroupOf
            (Subgroup.normalizer (AOf (MiOne β ε) (fOf β ε fb) : Set M)) ≃* Equiv.Perm (Fin 5)) ∧
        Nonempty (↥(Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)) ⧸
          (AOf (MiTwo β ε) (fOf β ε fb)).subgroupOf
            (Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)) ≃*
              Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      (∀ Mi : Subgroup M, (Mi = MiOne β ε ∨ Mi = MiTwo β ε) →
        ∃ τ ∈ autOn (⊤ : Subgroup M) (AOf Mi (fOf β ε fb)), IsTransvection τ)

section F54


end F54

@[expose] def F_5_5 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    (Nonempty (↥(DOne Gp β ε fb) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (↥(DTwo Gp β ε fb) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
    Nonempty (↥(DOne Gp β ε fb ⊔ DTwo Gp β ε fb) ≃* Equiv.Perm (Fin 6)) ∧
    Nonempty (↥(R ⊓ Subgroup.centralizer
      ((oTwoRes (DOne Gp β ε fb ⊔ DTwo Gp β ε fb) : Subgroup M) : Set M)) ≃*
        Multiplicative (ZMod 4)) ∧
    ((R : Set M) * ((DOne Gp β ε fb ⊔ DTwo Gp β ε fb : Subgroup M) : Set M) =
      ((Subgroup.centralizer ({fOf β ε fb} : Set M) : Subgroup M) : Set M)) ∧
    (Nonempty (↥(M0Of β ε) ≃* E) ∧ Nonempty (E ≃* ↥M0Dot) ∧ IsAutU42 ↥M0Dot)

section F55


end F55

@[expose] def F_5_6 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)),
    HypF5 Gp M₁ M₂ β ε z Tb fb →
    M0Of β ε ⊔ Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M) = ⊤

section F56


end F56

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem qV_smul_of_mem_isometryCore {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) :
    ∀ v : V6, qV (g • v) = qV v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => intro v; exact hx v
  | one => intro v; simp
  | mul x y _ _ hx hy => intro v; rw [mul_smul, hx, hy]
  | inv x _ hx =>
    intro v
    have := hx (x⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this.symm

theorem commutator_le_self' (H : Subgroup GL6) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem MDot_le_OVq : MDot ≤ OVq := commutator_le_self' _

theorem qV_smul_of_mem_MDot {g : GL6} (hg : g ∈ MDot) (v : V6) : qV (g • v) = qV v :=
  qV_smul_of_mem_isometryCore (MDot_le_OVq hg) v

@[expose] def PtsMinusSet : Set Sub6 := {S | ∃ v : V6, qV v = -1 ∧ S = spn {v}}

@[expose] def PtsMinus : SubMulAction ↥MDot Sub6 where
  carrier := PtsMinusSet
  smul_mem' := by
    rintro g S ⟨v, hv, rfl⟩
    refine ⟨(g : GL6) • v, ?_, ?_⟩
    · rw [qV_smul_of_mem_MDot g.2, hv]
    · change ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) • Submodule.span (ZMod 3) {v} =
        Submodule.span (ZMod 3) {((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) • v}
      rw [Submodule.smul_span, Set.smul_set_singleton]

abbrev PtX : Type := ↥PtsMinus

theorem qV_x6 : qV x6 = -1 := by
  decide

@[expose] def xDot : PtX := ⟨spn {x6}, x6, qV_x6, rfl⟩

theorem qV_x1_sub_x2 : qV (x1 - x2) = -1 := by
  decide

@[expose] def yDot : PtX := ⟨spn {x1 - x2}, x1 - x2, qV_x1_sub_x2, rfl⟩

@[expose] def DeltaDot : SimpleGraph PtX :=
  SimpleGraph.fromRel fun S S' => ∀ v ∈ S.1, ∀ w ∈ S'.1, bil v w = 0

@[expose] def DeltaDotH : Set PtX := {S | S.1 ≤ V3plus}

@[expose] def DeltaDotSub : DeltaDot.Subgraph := (⊤ : DeltaDot.Subgraph).induce DeltaDotH

@[expose] def HDot : Subgroup ↥MDot := (MDot ⊓ MulAction.stabilizer GL6 V3plus).subgroupOf MDot

section AbstractGraph

variable {M : Type} [Group M]

@[expose] def DeltaGraph (M0 R Tf : Subgroup M) : SimpleGraph (M ⧸ M0) :=
  SimpleGraph.fromRel fun u v => ∃ a b : M, (a : M ⧸ M0) = u ∧ (b : M ⧸ M0) = v ∧
    ∃ r ∈ R, r ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a⁻¹ * b = m₁ * r * m₂

end AbstractGraph

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section AbstractUS

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] def TfOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) : Subgroup M :=
  TOf β ε Tb ⊓ Subgroup.centralizer ({fOf β ε fb} : Set M)

@[expose] def HOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) : Subgroup M :=
  Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)

@[expose] def xOf (M0 : Subgroup M) : M ⧸ M0 := ((1 : M) : M ⧸ M0)

@[expose] def yOf (M0 : Subgroup M) (r : M) : M ⧸ M0 := (r : M ⧸ M0)

@[expose] def DeltaSub (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E)
    (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M) :
    (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb)).Subgraph :=
  (⊤ : (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb)).Subgraph).induce
    ((fun h : M => h • xOf (M0Of β ε)) '' (HOf β ε fb : Set M))

end AbstractUS

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5 CFSG.Quasithin.Asc94
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def F_5_7 : Prop :=
  (IsNondegSub V3plus ∧ Module.finrank (ZMod 3) V3plus = 3 ∧
    Matrix.det (Matrix.of fun i j : Fin 3 => bil (![x1, x2, x6] i) (![x1, x2, x6] j)) = 1 ∧
    DeltaDotH = {S : PtX | S.1 = spn {x6} ∨ S.1 = spn {x1 - x2} ∨ S.1 = spn {x1 + x2}} ∧
    MDot ⊓ MulAction.stabilizer GL6 V3plus =
      MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6)) ∧
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    ∀ r : M, r ∈ R → r ∉ TfOf β ε Tb fb →
      ∃ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁),
        ε (β.φ1 zb) = z ∧ IsMarkedMuIso μ zb fb Tb ∧
      ∃ σ : ↥M0Dot ≃* ↥(M0Of β ε),
        ((∀ a : ↥M₁, ((σ (μ.φ1 a) : ↥(M0Of β ε)) : M) = ε (β.φ1 a)) ∧
          (∀ a : ↥M₂, ((σ (μ.φ2 a) : ↥(M0Of β ε)) : M) = ε (β.φ2 a)) ∧
          (∀ a : ↥(M₁ ⊓ M₂), ((σ (μ.φ12 a) : ↥(M0Of β ε)) : M) = bM β ε a)) ∧
        ∃ ζ : ↥HDot ≃* ↥(HOf β ε fb),
          ((∀ (g : ↥HDot) (g0 : ↥M0Dot), ((g : ↥MDot) : GL6) = (g0 : GL6) →
              ((ζ g : ↥(HOf β ε fb)) : M) = ((σ g0 : ↥(M0Of β ε)) : M)) ∧
            ((MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX)).subgroupOf HDot).map
                ζ.toMonoidHom =
              (MulAction.stabilizer M
                ({xOf (M0Of β ε), yOf (M0Of β ε) r} : Set (M ⧸ M0Of β ε))).subgroupOf
                  (HOf β ε fb)) ∧
          ((FaithfulSMul M (M ⧸ M0Of β ε) ∧
            IsUniquenessSystem (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb))
              (HOf β ε fb) (DeltaSub β ε Tb fb R)
              (xOf (M0Of β ε)) (yOf (M0Of β ε) r)) ∧
            (FaithfulSMul ↥MDot PtX ∧ IsUniquenessSystem DeltaDot HDot DeltaDotSub xDot yDot) ∧
            ∃ β' : ↥(MulAction.stabilizer ↥MDot xDot) ≃* ↥(MulAction.stabilizer M (xOf (M0Of β ε))),
              (∀ (g : ↥(MulAction.stabilizer ↥MDot xDot)) (g0 : ↥M0Dot),
                ((g : ↥MDot) : GL6) = (g0 : GL6) →
                  ((β' g : ↥(MulAction.stabilizer M (xOf (M0Of β ε)))) : M) =
                    ((σ g0 : ↥(M0Of β ε)) : M)) ∧
              IsEquivalence HDot xDot yDot (HOf β ε fb) (xOf (M0Of β ε)) (yOf (M0Of β ε) r) β' ζ)

section F57


end F57

@[expose] def F_5_8 : Prop :=
  (DeltaDot.IsClique DeltaDotH ∧ DeltaDotH.ncard = 3) ∧
  (∀ θ : Set PtX, DeltaDot.IsClique θ → θ.ncard = 3 → ∃ g : ↥MDot, g • θ = DeltaDotH) ∧
  (DeltaDot.Connected ∧ Triangulable DeltaDot) ∧
  IsBase ↥MDot DeltaDot DeltaDotSub

namespace ChF5S

open CFSG.ASVolI.ChF5 Matrix
open scoped commutatorElement
open scoped Pointwise

private abbrev T5 := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

private def qT (t : T5) : ZMod 3 :=
  t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2.1 ^ 2 + t.2.2.2.2 ^ 2

private def dT (t s : T5) : ZMod 3 :=
  t.1 * s.1 + t.2.1 * s.2.1 + t.2.2.1 * s.2.2.1 + t.2.2.2.1 * s.2.2.2.1 + t.2.2.2.2 * s.2.2.2.2

private def neg5 (t : T5) : T5 := (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2.1, -t.2.2.2.2)

private def L3 : List (ZMod 3) := [0, 1, 2]

private def all5 : List T5 :=
  L3.flatMap fun a => L3.flatMap fun b => L3.flatMap fun c => L3.flatMap fun d =>
    L3.map fun e => (a, b, c, d, e)

private theorem mem_all5 (t : T5) : t ∈ all5 := by
  obtain ⟨a, b, c, d, e⟩ := t
  revert a b c d e
  decide


set_option maxRecDepth 100000 in
private theorem C2_bool : all5.all (fun y =>
    !(qT y == 0 && y != (0, 0, 0, 0, 0)) ||
      ((all5.filter (fun t => qT t == 2 && dT t y == 0)).all (fun a =>
        (all5.filter (fun t => qT t == 2 && dT t y == 0)).all (fun b =>
          !(dT a b != 0 && a != b && a != neg5 b) ||
            (all5.filter (fun t => qT t == 2 && dT t y == 0)).any (fun c =>
              dT c a == 0 && dT c b == 0))))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem C3_bool : all5.all (fun y => all5.all (fun z =>
    !(qT y == 0 && qT z == 0 && dT y z != 0) ||
      all5.any (fun t => qT t == 2 && dT t y == 0 && dT t z == 0))) = true := by
  decide +kernel


private theorem h2_5 (y : T5) (hy : qT y = 0) (hne : y ≠ (0, 0, 0, 0, 0)) (a b : T5)
    (ha : qT a = 2) (hay : dT a y = 0) (hb : qT b = 2) (hby : dT b y = 0)
    (hab : dT a b ≠ 0) (hne' : a ≠ b) (hneg : a ≠ neg5 b) :
    ∃ c : T5, qT c = 2 ∧ dT c y = 0 ∧ dT c a = 0 ∧ dT c b = 0 := by
  have h := List.all_eq_true.mp C2_bool y (mem_all5 y)
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exfalso
    simp [hy, hne] at h
  have hA := List.all_eq_true.mp h a (List.mem_filter.mpr ⟨mem_all5 a, by simp [ha, hay]⟩)
  have hB := List.all_eq_true.mp hA b (List.mem_filter.mpr ⟨mem_all5 b, by simp [hb, hby]⟩)
  rw [Bool.or_eq_true] at hB
  rcases hB with hB | hB
  · exfalso
    simp [hab, hne', hneg] at hB
  · rw [List.any_eq_true] at hB
    obtain ⟨c, hc, hc'⟩ := hB
    rw [List.mem_filter] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc hc'
    exact ⟨c, hc.2.1, hc.2.2, hc'.1, hc'.2⟩

private theorem h3_5 (y z : T5) (hy : qT y = 0) (hz : qT z = 0) (hyz : dT y z ≠ 0) :
    ∃ t : T5, qT t = 2 ∧ dT t y = 0 ∧ dT t z = 0 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp C3_bool y (mem_all5 y)) z (mem_all5 z)
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨t, _, ht⟩
  · exfalso
    simp [hy, hz, hyz] at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨t, ht.1.1, ht.1.2, ht.2⟩

open scoped commutatorElement
open scoped Pointwise


end ChF5S


end CFSG.ASVolI
