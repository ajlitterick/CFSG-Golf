module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Hyp18 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop where
  hyp125 : Hyp125 D V₀ V
  hp : p ∈ D.sig
  hL : L ∈ S17.calLp D p
  hX : conjClosure D.M L ∈ S17.calL0Star D p
  small : mSub V₀ ≤ 1

theorem mSub_le_one_iff {V₀ : Subgroup G} (hV₀ : IsElemAbelian 2 V₀) :
    mSub V₀ ≤ 1 ↔ Nat.card V₀ ≤ 2 := by
  have h2 : IsPGroup 2 V₀ := fun g => ⟨1, Subtype.ext (by simpa using hV₀.2 (g : G) g.2)⟩
  rw [card_eq_two_pow_mSub h2]
  constructor
  · intro h
    calc 2 ^ mSub V₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
      _ = 2 := by norm_num
  · intro h
    by_contra hc
    have h2' : 2 ≤ mSub V₀ := by omega
    have h4 : 4 ≤ 2 ^ mSub V₀ := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h2'
    omega

@[expose] def Concl18_1_2 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ n : ℕ, n < mBar D.M V₀ V hV → calO n D.M V₀ V = ∅

@[expose] def Concl18_1_3 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ (H S : Subgroup G) (i j n : ℕ), Fstar H = pCoreOf 2 H →
    CFSG.ABGLocalTools.IsSylowOf 2 S H → i + j = n → n < mBar D.M V₀ V hV →
      (InEGroup j ↥H →
        H = (H ⊓ normalizer ((F12.Wi i S V : Subgroup G) : Set G)) ⊔
          (H ⊓ centralizer ((F12.Ci n S V : Subgroup G) : Set G))) ∧
      (WeakClosure81.InFSq j H →
        ((F12.Wi i S V).subgroupOf H).Normal ∨
          ⁅(F12.Ci n S V : Subgroup G), S17.oUpperTwo H⁆ = ⊥)

structure Hyp1222 (D : Data G) (V₀ V : Subgroup G) (L : Subgroup G) (j : ℕ)
    (Δ : Set (Subgroup G)) : Prop where
  hyp125 : Hyp125 D V₀ V
  ne_bot : V₀ ≠ ⊥
  X_normal : ((conjClosure D.M L).subgroupOf D.M).Normal
  delta_le : ∀ H ∈ Δ, H ≤ D.M
  delta_T : ∀ H ∈ Δ, D.T ≤ H
  delta_unique : UniqueMax D.M (⨆ H ∈ Δ, H)
  either : XCond1218 D.M V₀ V hyp125.isElemAbelian j (conjClosure D.M L)


section Coords

variable {W : Type*} [CommGroup W]

@[expose] def NatCoordsSU4 (H : Subgroup (MulAut W)) (n : ℕ) (F : Type) [Field F]
    (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
    (ψ : W ≃* Multiplicative (Fin 4 → F)) : Prop :=
  ∀ (l : ↥H) (s : W), ψ ((l : MulAut W) s) = Multiplicative.ofAdd
    (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ s)))

@[expose] def NatCoordsOmegaMinusOn (H : Subgroup (MulAut W)) (W' : Subgroup W)
    (hW' : ∀ x ∈ H, ∀ s ∈ W', x s ∈ W') (F : Type) [Field F] (b c : F)
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) : Prop :=
  ∀ (l : ↥H) (s : W'), ψ ⟨(l : MulAut W) s.1, hW' l.1 l.2 s.1 s.2⟩ = Multiplicative.ofAdd
    (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
      (Multiplicative.toAdd (ψ s)))

@[expose] def NatCoordsOmegaPlus (H : Subgroup (MulAut W)) (F : Type) [Field F]
    (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
    (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)) : Prop :=
  ∀ (l : ↥H) (s : W), ψ ((l : MulAut W) s) = Multiplicative.ofAdd
    (((ε l : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec
      (Multiplicative.toAdd (ψ s)))

end Coords

@[expose] def tilOf (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (v : G) (hv : v ∈ V) :
    Vtil V₀ V hV :=
  mkTil V₀ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)

@[expose] def centVec {W : Type*} [Group W] (X : Subgroup (MulAut W)) (v : W) :
    Subgroup (MulAut W) where
  carrier := {x | x ∈ X ∧ x v = v}
  one_mem' := ⟨X.one_mem, rfl⟩
  mul_mem' := by
    rintro x y ⟨hxX, hx⟩ ⟨hyX, hy⟩
    exact ⟨X.mul_mem hxX hyX, by rw [MulAut.mul_apply, hy, hx]⟩
  inv_mem' := by
    rintro x ⟨hxX, hx⟩
    exact ⟨X.inv_mem hxX, by
      have h := congrArg (x⁻¹ : MulAut W) hx
      simpa [MulAut.mul_apply] using h.symm⟩

namespace centVec

variable {W : Type*} [Group W] {X : Subgroup (MulAut W)} {v : W}

theorem mem_centVec {x : MulAut W} : x ∈ centVec X v ↔ x ∈ X ∧ x v = v := by
  show x ∈ (centVec X v).carrier ↔ _
  rfl

theorem le (X : Subgroup (MulAut W)) (v : W) : centVec X v ≤ X := by
  intro x hx
  exact (mem_centVec.mp hx).1

theorem apply_eq {x : MulAut W} (hx : x ∈ centVec X v) : x v = v :=
  (mem_centVec.mp hx).2

end centVec


@[expose] def P18_6_2 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∃ f : ℕ,
    (IsSp4 (Bar2 (conjClosure D.M L)) f ∧
        NatSpn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f) ∨
      (IsG2 (Bar2 (conjClosure D.M L)) f ∧
        CFSG.Quasithin.G2Natural (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) f) ∨
      (IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
        NatSUn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f) ∨
      (IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 f ∧
        NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 6 f) ∨
      (IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
        NatOmegaPlus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f) ∨
      (Even f ∧ IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 (f / 2) ∧
        NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)))
          4 (f / 2)) ∨
      (IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f ∧
        CFSG.Quasithin.BinaryNaturalSL (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
          (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 2 f)

@[expose] def P18_6_3 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∃ f : ℕ,
    (IsSp4 (Bar2 (conjClosure D.M L)) f ∧
        SumOfNat (fun H U Z => NatSpn H U Z 4 f)
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2) ∨
      (IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 f ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 f)
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2) ∨
      (Even f ∧ IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 (f / 2) ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 (f / 2))
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2)

@[expose] def P18_6_4 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  (IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 2 ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2)
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 3) ∨
    (IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 2 ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2)
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 3)

@[expose] def P18_6_5 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (_h : Hyp18 D V₀ V p L) : Prop :=
  conjClosure D.M L ≠ L ∧
    ∀ x ∈ D.M, x ∉ normalizer (L : Set G) →
      ⁅⁅V, L⁆, CFSG.Quasithin.conjSubgroup L x⁆ = ⊥

@[expose] def P18_13_1 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∃ f : ℕ, IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
    NatSUn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 4 f

@[expose] def P18_13_2 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (s : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ 2 ∧ ∃ f : ℕ,
    IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 f ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 f)
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ s

@[expose] def P18_13_3 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∃ f : ℕ, IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
    NatOmegaPlus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 4 f

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
