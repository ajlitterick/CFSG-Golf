module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Milestones.ASVolI.I7
public import CFSG.Milestones.ASVolI.I8
public import CFSG.Milestones.ASVolI.J1
public import CFSG.Milestones.ASVolI.J2
public import CFSG.Milestones.ASVolI.J3
public import CFSG.Quasithin.Background.ASVolIRu.Bridge
public import CFSG.Quasithin.Background.ASVolIRu.StUnique
public import CFSG.Quasithin.Recognition.RuTypeJ11c
public import CFSG.Quasithin.Recognition.RuTypeJ42
public import CFSG.Quasithin.Recognition.RuTypeJ47j
public import CFSG.Quasithin.Recognition.RuTypeJ47l
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmFinal2
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuCert
public import CFSG.Quasithin.Vol2.TwoF4F48Cert
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.RuTypeJ45a
public import CFSG.Quasithin.Recognition.RuTypeQuasithin
public import CFSG.Quasithin.Recognition.CertTitsBridge
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J4

variable {G : Type} [Group G]

@[expose] def IsV2 (V T V2 : Subgroup G) : Prop :=
  V2 ≤ V ∧ Nat.card ↥V2 = 4 ∧ T ≤ Subgroup.normalizer (V2 : Set G)

@[expose] def L2Ru (L V2 : Subgroup G) : Subgroup G := twoResidual (L ⊓ Subgroup.normalizer (V2 : Set G))

@[expose] def G2Ru (L V2 T : Subgroup G) : Subgroup G := L2Ru L V2 ⊔ T

@[expose] def R2Ru (L V2 T : Subgroup G) : Subgroup G := pCoreOf 2 (L2Ru L V2 ⊔ T)


@[expose] def Q5Ru (T B5 : Subgroup G) : Subgroup G := ⁅QRu T, B5⁆

@[expose] def S2Ru (L V V2 T : Subgroup G) : Subgroup G := ⁅SRu L, R2Ru L V2 T⁆ ⊔ V

@[expose] def IsAChoice (L V T V2 B5 : Subgroup G) (a : G) : Prop :=
  (Q5Ru T B5 ⊔ S2Ru L V V2 T) ⊓ R2Ru L V2 T = Subgroup.zpowers a ⊔ S2Ru L V V2 T ∧
    a ∉ S2Ru L V V2 T ∧ a ^ 2 ∈ S2Ru L V V2 T ∧ ∀ t ∈ T, a⁻¹ * t⁻¹ * a * t ∈ S2Ru L V V2 T

@[expose] def ARu (L V V2 T : Subgroup G) (a : G) : Subgroup G :=
  conjClosure (Subgroup.zpowers a) (G2Ru L V2 T) ⊔ S2Ru L V V2 T

@[expose] def TFRu (L V V2 T : Subgroup G) (a : G) (B5 : Subgroup G) : Subgroup G :=
  ARu L V V2 T a ⊔ Q5Ru T B5

@[expose] def F1Ru (L V V2 T : Subgroup G) (a : G) (B5 : Subgroup G) : Subgroup G :=
  TFRu L V V2 T a B5 ⊔ B5

@[expose] def F2Ru (L V V2 T : Subgroup G) (a : G) (B5 X : Subgroup G) : Subgroup G :=
  TFRu L V V2 T a B5 ⊔ X

@[expose] def FRu (L V V2 T : Subgroup G) (a : G) (B5 X : Subgroup G) : Subgroup G :=
  F1Ru L V V2 T a B5 ⊔ F2Ru L V V2 T a B5 X


@[expose] def InvertsGroup (v : G) (B : Subgroup G) : Prop :=
  v ∈ Subgroup.normalizer (B : Set G) ∧ ∀ b ∈ B, v⁻¹ * b * v = b⁻¹

end J4


open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J4b

variable {G : Type} [Group G]


end J4b

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

section RuChoiceSec


open CFSG.Quasithin.RuType in
def RuChoice.V2pl {G : Type} [Group G] (M : RuDataM G) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruV M.L, (Multiplicative.toAdd (M.ψV ⟨x, hx⟩)) 2 = 0}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : ruV M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    simp [ha2, hb2]
  one_mem' := ⟨(ruV M.L).one_mem, by
    have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]
    rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨inv_mem ha, ?_⟩
    have : (⟨a⁻¹, inv_mem ha⟩ : ruV M.L) = (⟨a, ha⟩ : ruV M.L)⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    have h2 : ∀ x : ZMod 2, -x = x := by decide
    simp [ha2]

open CFSG.Quasithin.RuType in
theorem RuChoice.card_V2pl {G : Type} [Group G] (M : RuDataM G) :
    Nat.card (RuChoice.V2pl M) = 4 := by
  have e : (RuChoice.V2pl M) ≃ {y : Fin 3 → ZMod 2 // y 2 = 0} :=
    { toFun := fun x => ⟨Multiplicative.toAdd (M.ψV ⟨x.1, x.2.1⟩), x.2.2⟩
      invFun := fun y => ⟨(M.ψV.symm (Multiplicative.ofAdd y.1) : G),
        ⟨(M.ψV.symm (Multiplicative.ofAdd y.1)).2, by simpa using y.2⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.exists_T_of_P0 {G : Type} [Group G] (M : RuDataM G) {p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hp : p ∈ SL3.P0) :
    ∃ (t : G) (htL : t ∈ M.L), t ∈ (M.T : Subgroup G) ∧ M.θ ⟨t, htL⟩ = p := by
  rw [← M.hP0] at hp
  obtain ⟨t', ht', rfl⟩ := hp
  exact ⟨t'.1, t'.2, Subgroup.mem_subgroupOf.mp ht', rfl⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.p0p1 : ∀ y : Fin 3 → ZMod 2, y 2 = 1 →
    natAct3 (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![1, 0, 0] ∧
    natAct3 (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![0, 1, 0] := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.p0p1_mem :
    (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 ∧
    (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

theorem RuChoice.vec_cancel : ∀ y e : Fin 3 → ZMod 2, y + e + y = e := by
  decide +kernel

theorem RuChoice.decomp : ∀ y w : Fin 3 → ZMod 2, y 2 = 1 →
    ∃ a b c : Bool, w = (if a then ![1, 0, 0] else 0) + (if b then ![0, 1, 0] else 0) +
      (if c then y else 0) := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.V2_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) : V2 = RuChoice.V2pl M := by
  obtain ⟨hVle, hcard, hT⟩ := hV2
  have hle : V2 ≤ RuChoice.V2pl M := by
    intro x hx
    have hxV : x ∈ ruV M.L := hVle hx
    refine ⟨hxV, ?_⟩
    by_contra h2
    have hy2 : (Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2 = 1 := by
      rcases Quasithin.RuType.Sigma.zmod2_cases ((Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2) with h | h
      · exact absurd h h2
      · exact h
    set y := Multiplicative.toAdd (M.ψV ⟨x, hxV⟩) with hy
    have hconj : ∀ p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), p ∈ SL3.P0 → ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
        Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = natAct3 p y := by
      intro p hp
      obtain ⟨t, htL, htT, hθ⟩ := RuChoice.exists_T_of_P0 M hp
      have hz : t * x * t⁻¹ ∈ V2 := (Subgroup.mem_normalizer_iff.mp (hT htT) x).mp hx
      have hzV : t * x * t⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V htL hxV
      refine ⟨t * x * t⁻¹, hz, hzV, ?_⟩
      have := M.ψV_equiv ⟨t, htL⟩ ⟨x, hxV⟩ ⟨t * x * t⁻¹, hzV⟩ rfl
      rw [this, toAdd_ofAdd, hθ]
    obtain ⟨z0, hz0, hz0V, hz0e⟩ := hconj _ RuChoice.p0p1_mem.1
    obtain ⟨z1, hz1, hz1V, hz1e⟩ := hconj _ RuChoice.p0p1_mem.2
    rw [(RuChoice.p0p1 y hy2).1] at hz0e
    rw [(RuChoice.p0p1 y hy2).2] at hz1e
    let Y : Set (Fin 3 → ZMod 2) := {w | ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
      Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = w}
    have hY0 : (0 : Fin 3 → ZMod 2) ∈ Y := ⟨1, V2.one_mem, (ruV M.L).one_mem, by
      have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
      rw [this, map_one, toAdd_one]⟩
    have hYadd : ∀ w1 ∈ Y, ∀ w2 ∈ Y, w1 + w2 ∈ Y := by
      rintro _ ⟨a, ha, haV, rfl⟩ _ ⟨b, hb, hbV, rfl⟩
      refine ⟨a * b, V2.mul_mem ha hb, mul_mem haV hbV, ?_⟩
      have : (⟨a * b, mul_mem haV hbV⟩ : ruV M.L) = ⟨a, haV⟩ * ⟨b, hbV⟩ := rfl
      rw [this, map_mul, toAdd_mul]
    have hYy : y ∈ Y := ⟨x, hx, hxV, rfl⟩
    have hYe0 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z0, hz0, hz0V, hz0e⟩ _ hYy
      rwa [RuChoice.vec_cancel] at h
    have hYe1 : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z1, hz1, hz1V, hz1e⟩ _ hYy
      rwa [RuChoice.vec_cancel] at h
    have hVV2 : ruV M.L ≤ V2 := by
      intro v hv
      obtain ⟨a, b, c, hw⟩ := RuChoice.decomp y (Multiplicative.toAdd (M.ψV ⟨v, hv⟩)) hy2
      have hmem : Multiplicative.toAdd (M.ψV ⟨v, hv⟩) ∈ Y := by
        rw [hw]
        refine hYadd _ (hYadd _ ?_ _ ?_) _ ?_
        · split_ifs
          · exact hYe0
          · exact hY0
        · split_ifs
          · exact hYe1
          · exact hY0
        · split_ifs
          · exact hYy
          · exact hY0
      obtain ⟨z, hz, hzV, hze⟩ := hmem
      have : (⟨z, hzV⟩ : ruV M.L) = ⟨v, hv⟩ := M.ψV.injective (Multiplicative.toAdd.injective hze)
      have hzv : z = v := congrArg Subtype.val this
      rw [← hzv]
      exact hz
    have h8 : Nat.card (ruV M.L) = 8 := M.toRuData.card_V
    have h4 : Nat.card V2 = 4 := hcard
    have := Subgroup.card_le_of_le hVV2
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [RuChoice.card_V2pl, hcard])

open CFSG.Quasithin.RuType in
theorem RuChoice.conj_mem_V2pl {G : Type} [Group G] (M : RuDataM G) {g : G} (hgL : g ∈ M.L)
    (hθ : M.θ ⟨g, hgL⟩ ∈ SL3.Pl) {x : G} (hx : x ∈ RuChoice.V2pl M) :
    g * x * g⁻¹ ∈ RuChoice.V2pl M := by
  obtain ⟨hxV, hx2⟩ := hx
  have hgxV : g * x * g⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hgL hxV
  refine ⟨hgxV, ?_⟩
  have := M.ψV_equiv ⟨g, hgL⟩ ⟨x, hxV⟩ ⟨g * x * g⁻¹, hgxV⟩ rfl
  rw [this, toAdd_ofAdd]
  exact SL3.Pl_plane _ hθ _ hx2

open CFSG.Quasithin.RuType in
theorem RuChoice.L_inf_normalizer {G : Type} [Group G] (M : RuDataM G) :
    M.L ⊓ Subgroup.normalizer (RuChoice.V2pl M : Set G) = M.G2 := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgN⟩
    refine mem_pullL.mpr ⟨hgL, ?_⟩
    have hcol : ∀ e : Fin 3 → ZMod 2, e 2 = 0 → (natAct3 (M.θ ⟨g, hgL⟩) e) 2 = 0 := by
      intro e he
      set x : ruV M.L := M.ψV.symm (Multiplicative.ofAdd e) with hxdef
      have hxV2 : (x : G) ∈ RuChoice.V2pl M := ⟨x.2, by simpa [hxdef] using he⟩
      have hgx : g * x * g⁻¹ ∈ RuChoice.V2pl M :=
        (Subgroup.mem_normalizer_iff.mp hgN x).mp hxV2
      obtain ⟨hgxV, hgx2⟩ := hgx
      have := M.ψV_equiv ⟨g, hgL⟩ x ⟨g * x * g⁻¹, hgxV⟩ rfl
      rw [this, toAdd_ofAdd] at hgx2
      simpa [hxdef] using hgx2
    have h0 := hcol ![1, 0, 0] rfl
    have h1 := hcol ![0, 1, 0] rfl
    refine ⟨?_, ?_⟩
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1
  · intro hg
    obtain ⟨hgL, hθ⟩ := mem_pullL.mp hg
    refine ⟨hgL, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => RuChoice.conj_mem_V2pl M hgL hθ hx
    · intro hx
      have hθ' : M.θ ⟨g⁻¹, inv_mem hgL⟩ ∈ SL3.Pl := by
        have : M.θ ⟨g⁻¹, inv_mem hgL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact inv_mem hθ
      have := RuChoice.conj_mem_V2pl M (inv_mem hgL) hθ' hx
      simpa [mul_assoc] using this

theorem RuChoice.twoResidual_le {G : Type} [Group G] (X : Subgroup G) :
    ChIJK.twoResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem RuChoice.mem_twoResidual_of_odd {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {x : G} (hx : x ∈ X) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    x ∈ ChIJK.twoResidual X := by
  unfold ChIJK.twoResidual
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_sInf]
  rintro N ⟨hN, k, hk⟩
  have hcard : Nat.card (↥X ⧸ N) = 2 ^ k := by
    rw [← Subgroup.index_eq_card]
    exact hk
  have h1 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ (2 ^ k) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h2 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : X) ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this]
    rfl
  have hcop : Nat.Coprime n (2 ^ k) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hn
  have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rw [hcop, pow_one] at h3
  exact (QuotientGroup.eq_one_iff _).mp h3

@[expose] def RuChoice.a3mat : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.a3 :
    RuChoice.a3mat ∈ SL3.Pl ∧ RuChoice.a3mat ^ 3 = 1 ∧ RuChoice.a3mat ≠ 1 :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.exists_L2_lift3 {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ∈ SL3.Pl) (ha3 : a ^ 3 = 1) :
    ∃ (l : G) (hl : l ∈ M.L), l ∈ ChIJK.twoResidual M.G2 ∧ M.θ ⟨l, hl⟩ = a ∧ l ^ 3 = 1 := by
  obtain ⟨l, hθ, hl3⟩ := M.exists_lift ha3 (by norm_num)
  have hlG : (l : G) ∈ M.G2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact ha⟩
  exact ⟨l, l.2, RuChoice.mem_twoResidual_of_odd hlG (n := 3) (by decide) hl3, hθ, hl3⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.card_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
  rw [← M.toRuData.TL_eq, M.toRuData.card_TL]

open CFSG.Quasithin.RuType in
theorem RuChoice.L2_sup_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) = M.G2 := by
  have hle : ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) ≤ M.G2 :=
    sup_le (RuChoice.twoResidual_le _) M.T_le_G2
  obtain ⟨ha, ha3, ha1⟩ := RuChoice.a3
  obtain ⟨l, hl, hl2, hθ, hl3⟩ := RuChoice.exists_L2_lift3 M ha ha3
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hθ]
    exact map_one M.θ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  set K := ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) with hK
  have h3 : 3 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K (x := l) (Subgroup.mem_sup_left hl2)
    rwa [hord] at this
  have h2 : 2 ^ 14 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (le_sup_right : (M.T : Subgroup G) ≤ K)
    rwa [RuChoice.card_T] at this
  have h6 : 2 ^ 14 * 3 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hG : Nat.card M.G2 = 2 ^ 14 * 3 := by rw [M.card_G2]; norm_num
  have hKG : Nat.card K ∣ Nat.card M.G2 := Subgroup.card_dvd_of_le hle
  rw [hG] at hKG
  have heq : Nat.card K = 2 ^ 14 * 3 := Nat.dvd_antisymm hKG h6
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hG, heq])

open CFSG.Quasithin.RuType in
theorem RuChoice.inter_P0 : ∀ y ∈ SL3.Pl, (∀ p ∈ SL3.Pl, p⁻¹ * y * p ∈ SL3.P0) → y ∈ SL3.R2m := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.pCoreOf_G2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    pCoreOf 2 M.G2 = M.R2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    have hn : (CFSG.pCore 2 ↥M.G2).Normal := CFSG.pCore_normal
    have hTp : IsPGroup 2 ((M.T : Subgroup G).subgroupOf M.G2) :=
      (M.T.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe M.T_le_G2).symm
    have hidx : ¬ 2 ∣ ((M.T : Subgroup G).subgroupOf M.G2).index := by
      have h1 := Subgroup.card_mul_index ((M.T : Subgroup G).subgroupOf M.G2)
      rw [card_subgroupOf_of_le M.T_le_G2, RuChoice.card_T, M.card_G2] at h1
      have : ((M.T : Subgroup G).subgroupOf M.G2).index = 3 := by omega
      rw [this]
      norm_num
    let P : Sylow 2 ↥M.G2 := hTp.toSylow hidx
    have hle : CFSG.pCore 2 ↥M.G2 ≤ (P : Subgroup ↥M.G2) :=
      (CFSG.pCore_isPGroup (G := ↥M.G2) (p := 2)).le_sylow_of_normal P
    rintro x ⟨y, hy, rfl⟩
    have hyG : (y : G) ∈ M.G2 := y.2
    obtain ⟨hyL, -⟩ := mem_pullL.mp hyG
    refine mem_pullL.mpr ⟨hyL, ?_⟩
    apply RuChoice.inter_P0
    · exact (mem_pullL.mp hyG).2
    · intro p hp
      obtain ⟨⟨g, hgL⟩, rfl⟩ := M.θ_surj p
      have hgG : g ∈ M.G2 := mem_pullL.mpr ⟨hgL, hp⟩
      have hmem : (⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ ∈ CFSG.pCore 2 ↥M.G2 := by
        have := hn.conj_mem y hy (⟨g, hgG⟩ : ↥M.G2)⁻¹
        simpa using this
      have hP : ((⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ : ↥M.G2) ∈ (P : Subgroup ↥M.G2) := hle hmem
      have hPT : g⁻¹ * y * g ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp hP
      have := M.θ_mem_P0 hPT
      have e : (⟨g⁻¹ * y * g, M.toRuData.T_le_L hPT⟩ : M.L) =
          (⟨g, hgL⟩ : M.L)⁻¹ * ⟨y, hyL⟩ * ⟨g, hgL⟩ := rfl
      rw [e, map_mul, map_mul, map_inv] at this
      exact this
  ·
    have hRn : (M.R2.subgroupOf M.G2).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxL, hxR⟩ := mem_pullL.mp hx
      obtain ⟨hgL, hgP⟩ := mem_pullL.mp g.2
      show (g : G) * x * (g : G)⁻¹ ∈ M.R2
      refine mem_pullL.mpr ⟨mul_mem (mul_mem hgL hxL) (inv_mem hgL), ?_⟩
      have e : (⟨(g : G) * x * (g : G)⁻¹, mul_mem (mul_mem hgL hxL) (inv_mem hgL)⟩ : M.L) =
          ⟨g, hgL⟩ * ⟨(x : G), hxL⟩ * (⟨g, hgL⟩ : M.L)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact SL3.conj_mem_R2m _ hgP _ hxR
    have hRp : IsPGroup 2 (M.R2.subgroupOf M.G2) := by
      rw [IsPGroup.iff_card, card_subgroupOf_of_le M.R2_le_G2, M.card_R2]
      exact ⟨13, rfl⟩
    have hle : M.R2.subgroupOf M.G2 ≤ CFSG.pCore 2 ↥M.G2 := le_sSup ⟨hRn, hRp⟩
    have := Subgroup.map_mono (f := M.G2.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le M.R2_le_G2] at this
    exact this

open CFSG.Quasithin.RuType in
theorem RuChoice.L2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.L2Ru M.L V2 = ChIJK.twoResidual M.G2 := by
  rw [ChIJK.L2Ru, RuChoice.V2_eq M hV2, RuChoice.L_inf_normalizer]

open CFSG.Quasithin.RuType in
theorem RuChoice.G2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.G2Ru M.L V2 (M.T : Subgroup G) = M.G2 := by
  rw [ChIJK.G2Ru, RuChoice.L2Ru_eq M hV2, RuChoice.L2_sup_T]

open CFSG.Quasithin.RuType in
theorem RuChoice.R2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.R2Ru M.L V2 (M.T : Subgroup G) = M.R2 := by
  rw [ChIJK.R2Ru, RuChoice.L2Ru_eq M hV2, RuChoice.L2_sup_T, RuChoice.pCoreOf_G2]

open CFSG.Quasithin.RuType in
def RuChoice.chiAdd {G : Type} [Group G] (M : RuDataM G) (X : Subgroup G) :
    AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  carrier := {A | ∃ x ∈ X, ∃ hx : x ∈ ruS M.L, Multiplicative.toAdd (M.χ ⟨x, hx⟩) = A}
  zero_mem' := ⟨1, X.one_mem, (ruS M.L).one_mem, by
    have : (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, haS, rfl⟩ ⟨b, hb, hbS, rfl⟩
    refine ⟨a * b, X.mul_mem ha hb, mul_mem haS hbS, ?_⟩
    have : (⟨a * b, mul_mem haS hbS⟩ : ruS M.L) = ⟨a, haS⟩ * ⟨b, hbS⟩ := rfl
    rw [this, M.toAdd_χ_mul]
  neg_mem' := by
    rintro _ ⟨a, ha, haS, rfl⟩
    refine ⟨a⁻¹, X.inv_mem ha, inv_mem haS, ?_⟩
    have : (⟨a⁻¹, inv_mem haS⟩ : ruS M.L) = (⟨a, haS⟩ : ruS M.L)⁻¹ := rfl
    rw [this, M.toAdd_χ_inv]
    ext i j
    simp only [Matrix.neg_apply]
    have h2 : ∀ x : ZMod 2, x = -x := by decide
    exact h2 _

open CFSG.Quasithin.RuType in
theorem RuChoice.mem_of_chi {G : Type} [Group G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X) {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ RuChoice.chiAdd M X) : x ∈ X := by
  obtain ⟨y, hyX, hyS, hy⟩ := h
  have hk : (⟨y, hyS⟩ : ruS M.L)⁻¹ * ⟨x, hx⟩ ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Multiplicative.toAdd.injective hy]
    exact inv_mul_cancel _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact X.mul_mem hyX (hVX hk)

open CFSG.Quasithin.RuType in
theorem RuChoice.W_le_of_chi {G : Type} [Group G] [Finite G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X)
    (h : ∀ A, SL3.IsM2 A → IsTraceZero A → A ∈ RuChoice.chiAdd M X) : M.W ≤ X := by
  rintro x ⟨hx, hxM⟩
  exact RuChoice.mem_of_chi M hVX hx (h _ hxM (M.χ_trace _))

def RuChoice.inSpan :
    List (Matrix (Fin 3) (Fin 3) (ZMod 2)) → Matrix (Fin 3) (Fin 3) (ZMod 2) → Bool
  | [], A => decide (A = 0)
  | g :: gs, A => RuChoice.inSpan gs A || RuChoice.inSpan gs (A + g)

theorem RuChoice.mat_add_self : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g + g = 0 := by
  decide +kernel

theorem RuChoice.mem_of_inSpan (P : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∀ («gens» : List (Matrix (Fin 3) (Fin 3) (ZMod 2))), (∀ g ∈ «gens», g ∈ P) →
      ∀ A, RuChoice.inSpan «gens» A = true → A ∈ P := by
  intro «gens»
  induction «gens» with
  | nil =>
    intro _ A h
    simp only [RuChoice.inSpan, decide_eq_true_eq] at h
    rw [h]
    exact P.zero_mem
  | cons g gs ih =>
    intro hg A h
    simp only [RuChoice.inSpan, Bool.or_eq_true] at h
    have hgs : ∀ x ∈ gs, x ∈ P := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases h with h | h
    · exact ih hgs A h
    · have h1 := ih hgs (A + g) h
      have hgP := hg g List.mem_cons_self
      have : A = (A + g) + g := by
        rw [add_assoc, RuChoice.mat_add_self, add_zero]
      rw [this]
      exact P.add_mem h1 hgP

open CFSG.Quasithin.RuType in
theorem RuChoice.comm_mem_chiAdd {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {X : Subgroup G} (hX : ⁅ruS M.L, M.R2⁆ ≤ X) {r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hr : r ∈ SL3.R2m) {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    stAct r A + A ∈ RuChoice.chiAdd M X := by
  obtain ⟨l, hθ⟩ := M.θ_surj r
  have hlR : (l : G) ∈ M.R2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact hr⟩
  obtain ⟨s, hs⟩ := M.χ_surj A hA
  have hlS : (l : G) ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L l.2
  have ht : (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp hlS _).mp (inv_mem s.2)
  have hy : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L := by
    have : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ =
        (s : G) * ((l : G) * (s : G)⁻¹ * (l : G)⁻¹) := by group
    rw [this]
    exact mul_mem s.2 ht
  refine ⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹,
    hX (Subgroup.commutator_mem_commutator s.2 hlR), hy, ?_⟩
  have e : (⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹, hy⟩ : ruS M.L) =
      s * ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  rw [e, M.toAdd_χ_mul]
  have h1 : Multiplicative.toAdd (M.χ ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩) =
      stAct (M.θ l) (Multiplicative.toAdd (M.χ s⁻¹)) := M.χ_conj l s⁻¹
  rw [h1, M.toAdd_χ_inv, hs, toAdd_ofAdd, hθ, add_comm]

@[expose] def RuChoice.ra : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def RuChoice.rb : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def RuChoice.pairsR2 :
    List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [(RuChoice.ra, !![1, 0, 0; 0, 0, 0; 0, 0, 1]),
   (RuChoice.ra, !![1, 0, 0; 0, 0, 0; 0, 1, 1]),
   (RuChoice.ra, !![0, 0, 0; 0, 0, 0; 1, 0, 0]),
   (RuChoice.ra, !![0, 1, 0; 0, 0, 0; 0, 0, 0]),
   (RuChoice.rb, !![0, 0, 0; 0, 0, 0; 0, 1, 0]),
   (RuChoice.rb, !![0, 0, 0; 0, 1, 0; 1, 0, 1])]

@[expose] def RuChoice.gensR2 : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
   !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0; 0, 0, 1]]

open CFSG.Quasithin.RuType in
theorem RuChoice.gensR2_spec : ∀ g ∈ RuChoice.gensR2, ∃ p ∈ RuChoice.pairsR2,
    p.1 ∈ SL3.R2m ∧ IsTraceZero p.2 ∧ stAct p.1 p.2 + p.2 = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.span_M2 : ∀ A, SL3.IsM2 A → IsTraceZero A →
    RuChoice.inSpan RuChoice.gensR2 A = true := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.W_le_S2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    M.W ≤ ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L := by
  refine RuChoice.W_le_of_chi M le_sup_right fun A hA hAt => ?_
  refine RuChoice.mem_of_inSpan _ RuChoice.gensR2 ?_ A (RuChoice.span_M2 A hA hAt)
  intro g hg
  obtain ⟨p, -, hp1, hp2, rfl⟩ := RuChoice.gensR2_spec g hg
  exact RuChoice.comm_mem_chiAdd M le_sup_left hp1 hp2

open CFSG.Quasithin.RuType in
theorem RuChoice.comm_sup_V_eq_W {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L = M.W := by
  refine le_antisymm (sup_le ?_ ?_) (RuChoice.W_le_S2 M)
  · rw [Subgroup.commutator_le]
    intro s hs r hr
    have := M.W.inv_mem (M.comm_mem_W hr hs)
    have e : s * r * s⁻¹ * r⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ := by group
    show s * r * s⁻¹ * r⁻¹ ∈ M.W
    rw [e]
    exact this
  · exact fun v hv => M.U_le_W (M.V_le_U hv)

open CFSG.Quasithin.RuType in
theorem RuChoice.S2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.S2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W := by
  rw [ChIJK.S2Ru, RuChoice.R2Ru_eq M hV2]
  exact RuChoice.comm_sup_V_eq_W M

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.frame {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    G2Ru M.L V2 (M.T : Subgroup G) = M.G2 ∧ R2Ru M.L V2 (M.T : Subgroup G) = M.R2 ∧
      S2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W :=
  ⟨RuChoice.G2Ru_eq M hV2, RuChoice.R2Ru_eq M hV2, RuChoice.S2Ru_eq M hV2⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.sylow5_swap :
    ∀ w ∈ Sigma.SP0, w * w = 1 → w ≠ 1 → w.right = 1 →
    ∀ b₁ : SigmaL2F4, b₁ ^ 5 = 1 → b₁ ≠ 1 → w * b₁ * w⁻¹ = b₁⁻¹ →
    ∀ b₂ : SigmaL2F4, b₂ ^ 5 = 1 → b₂ ≠ 1 → w * b₂ * w⁻¹ = b₂⁻¹ →
    ∃ s ∈ Sigma.SP0, ∃ k : Fin 5, s * b₂ * s⁻¹ = b₁ ^ (k : ℕ) := by
  decide +kernel

open scoped Pointwise in
theorem RuChoice.sylow_mod {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {b c : G} (hb : orderOf b = 5) (hc : orderOf c = 5)
    (hbN : b ∈ Subgroup.normalizer (Q : Set G)) {k : ℕ} (hk : (b ^ k)⁻¹ * c ∈ Q) :
    ∃ q ∈ Q, Subgroup.zpowers b = Subgroup.zpowers (q * c * q⁻¹) := by
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbQ : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hbN
  set N : Subgroup G := Subgroup.zpowers b ⊔ Q with hN
  have hbN' : Subgroup.zpowers b ≤ N := le_sup_left
  have hQN : Q ≤ N := le_sup_right
  have hset : ((N : Subgroup G) : Set G) = (Subgroup.zpowers b : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbQ
  have hcN : c ∈ N := by
    have : c = b ^ k * ((b ^ k)⁻¹ * c) := by group
    rw [this]
    exact N.mul_mem (N.pow_mem (hbN' (Subgroup.mem_zpowers b)) k) (hQN hk)
  have hinf : Subgroup.zpowers b ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    have h1 : orderOf x ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard _ hx1
      rwa [Nat.card_zpowers, hb] at this
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hQ2)
    have h2 : orderOf x ∣ 2 ^ m := by
      have := Subgroup.orderOf_dvd_natCard _ hx2
      rwa [hm] at this
    have hd := Nat.dvd_gcd h1 h2
    have : Nat.gcd 5 (2 ^ m) = 1 := by
      apply Nat.Coprime.pow_right
      norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hQ2)
  have hcardN : Nat.card N = 5 * 2 ^ m := by
    have h := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hbQ
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hb, hm] at h
    exact h
  set P1 : Subgroup N := (Subgroup.zpowers b).subgroupOf N with hP1
  set P2 : Subgroup N := (Subgroup.zpowers c).subgroupOf N with hP2
  have hc' : Subgroup.zpowers c ≤ N := by
    rw [Subgroup.zpowers_le]
    exact hcN
  have hP1c : Nat.card P1 = 5 := by
    rw [hP1, CFSG.Quasithin.RuType.card_subgroupOf_of_le hbN', Nat.card_zpowers, hb]
  have hP2c : Nat.card P2 = 5 := by
    rw [hP2, CFSG.Quasithin.RuType.card_subgroupOf_of_le hc', Nat.card_zpowers, hc]
  have hidx1 : P1.index = 2 ^ m := by
    have h := Subgroup.card_mul_index P1
    rw [hP1c, hcardN] at h
    omega
  have hidx2 : P2.index = 2 ^ m := by
    have h := Subgroup.card_mul_index P2
    rw [hP2c, hcardN] at h
    omega
  have hnd : ¬ 5 ∣ 2 ^ m := by
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    omega
  let S1 : Sylow 5 N := (IsPGroup.of_card (n := 1) (by rw [hP1c]; norm_num)).toSylow
    (by rw [hidx1]; exact hnd)
  let S2 : Sylow 5 N := (IsPGroup.of_card (n := 1) (by rw [hP2c]; norm_num)).toSylow
    (by rw [hidx2]; exact hnd)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N S2 S1
  have hn' : (S1 : Subgroup N) = (S2 : Subgroup N).map (MulAut.conj n).toMonoidHom := by
    rw [← hn, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hnmem : (n : G) ∈ (Subgroup.zpowers b : Set G) * (Q : Set G) := by
    rw [← hset]
    exact n.2
  obtain ⟨y, hy, q, hq, hyq⟩ := Set.mem_mul.mp hnmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨q, hq, ?_⟩
  have hmapN : ∀ X : Subgroup N, X.map N.subtype = X.map N.subtype := fun _ => rfl
  have key : Subgroup.zpowers b = ((Subgroup.zpowers c).map (MulAut.conj (n : G)).toMonoidHom) := by
    ext x
    constructor
    · intro hx
      have hxN : x ∈ N := hbN' hx
      have : (⟨x, hxN⟩ : N) ∈ (S1 : Subgroup N) := by
        show (⟨x, hxN⟩ : N) ∈ P1
        exact hx
      rw [hn'] at this
      obtain ⟨z, hz, hzx⟩ := this
      have hz' : (z : G) ∈ Subgroup.zpowers c := hz
      refine ⟨z, hz', ?_⟩
      have := congrArg Subtype.val hzx
      simpa [MulAut.conj_apply] using this
    · rintro ⟨z, hz, rfl⟩
      have hzN : z ∈ N := hc' hz
      have : (⟨z, hzN⟩ : N) ∈ (S2 : Subgroup N) := by
        show (⟨z, hzN⟩ : N) ∈ P2
        exact hz
      have h2 : (MulAut.conj n) ⟨z, hzN⟩ ∈ (S1 : Subgroup N) := by
        rw [hn']
        exact ⟨⟨z, hzN⟩, this, rfl⟩
      have h3 : ((MulAut.conj n) ⟨z, hzN⟩ : N) ∈ P1 := h2
      have h4 : (((MulAut.conj n) ⟨z, hzN⟩ : N) : G) ∈ Subgroup.zpowers b := h3
      simpa [MulAut.conj_apply] using h4
  rw [show Subgroup.zpowers (q * c * q⁻¹) = (Subgroup.zpowers c).map (MulAut.conj q).toMonoidHom by
    rw [MonoidHom.map_zpowers]; rfl]
  have hmem : ∀ (A : Subgroup G) (g x : G),
      x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
    intro A g x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have key' : ∀ x : G, x ∈ Subgroup.zpowers b ↔ (b ^ i * q)⁻¹ * x * (b ^ i * q) ∈ Subgroup.zpowers c := by
    intro x
    rw [← hyq] at key
    rw [key, hmem]
  have hbi : ∀ x ∈ Subgroup.zpowers b, b ^ i * x * (b ^ i)⁻¹ ∈ Subgroup.zpowers b := fun x hx =>
    mul_mem (mul_mem (zpow_mem (Subgroup.mem_zpowers b) i) hx)
      (inv_mem (zpow_mem (Subgroup.mem_zpowers b) i))
  ext x
  rw [hmem]
  constructor
  · intro hx
    have h1 := (key' _).mp (hbi x hx)
    have e : (b ^ i * q)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * (b ^ i * q) = q⁻¹ * x * q := by group
    rwa [e] at h1
  · intro hx
    have e : (b ^ i * q)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * (b ^ i * q) = q⁻¹ * x * q := by group
    have h1 : b ^ i * x * (b ^ i)⁻¹ ∈ Subgroup.zpowers b := (key' _).mpr (by rw [e]; exact hx)
    have h2 : (b ^ i)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * b ^ i ∈ Subgroup.zpowers b :=
      mul_mem (mul_mem (inv_mem (zpow_mem (Subgroup.mem_zpowers b) i)) h1)
        (zpow_mem (Subgroup.mem_zpowers b) i)
    have e2 : (b ^ i)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * b ^ i = x := by group
    rwa [e2] at h2

open CFSG.Quasithin.RuType in
theorem RuChoice.ZRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.ZRu (M.T : Subgroup G) = ruZ M.T :=
  ChIJK.RuType.BridgeTwo.centerOf_eq _

open CFSG.Quasithin.RuType in
theorem RuChoice.HRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.HRu (M.T : Subgroup G) = ruH M.T :=
  congrArg (fun Z : Subgroup G => Subgroup.centralizer (Z : Set G)) (RuChoice.ZRu_eq M)

open CFSG.Quasithin.RuType in
theorem RuChoice.QRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.QRu (M.T : Subgroup G) = ruQ M.T :=
  congrArg (pCoreOf 2) (RuChoice.HRu_eq M)

open CFSG.Quasithin.RuType in
theorem RuChoice.URu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.URu (ruV M.L) (M.T : Subgroup G) = ruU M.L M.T :=
  (ChIJK.RuType.BridgeTwo.conjClosure_eq _ _).trans
    (congrArg (CFSG.Quasithin.conjClosure (ruV M.L)) (RuChoice.HRu_eq M))

open CFSG.Quasithin.RuType in
theorem RuChoice.conjugate_U_eq {G : Type} [Group G] (M : RuDataM G) (g : G) :
    CFSG.conjugate (ChIJK.URu (ruV M.L) (M.T : Subgroup G)) g = M.conjU g⁻¹ := by
  ext x
  rw [RuChoice.URu_eq, M.mem_conjU]
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

open CFSG.Quasithin.RuType in
theorem RuChoice.Ual_mul_mem_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) {v : G}
    (hv : v ∈ M.Ual) (hvQ : v ∉ ruQ M.T) : v * M.vel⁻¹ ∈ ruQ M.T := by
  have hidx : ((M.Ual ⊓ ruQ M.T).subgroupOf M.Ual).index = 2 := by
    have h := Subgroup.card_mul_index ((M.Ual ⊓ ruQ M.T).subgroupOf M.Ual)
    rw [card_subgroupOf_of_le inf_le_left, M.card_Ual_inf_Q, M.card_Ual] at h
    omega
  have h1 : (⟨v, hv⟩ : M.Ual) * (⟨M.vel, M.vel_mem_Ual⟩ : M.Ual)⁻¹ ∈
      (M.Ual ⊓ ruQ M.T).subgroupOf M.Ual := by
    refine (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false ?_ ?_)
    · intro h
      exact hvQ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
    · intro h
      have h' := inv_mem h
      rw [inv_inv] at h'
      exact M.vel_not_mem_Q (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h')).2
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2

open CFSG.Quasithin.RuType in
theorem RuChoice.B5_core {G : Type} [Group G] [Finite G] (M : RuDataM G) {v b : G}
    (hvU : v ∈ M.Ual) (hvQ : v ∉ ruQ M.T) (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hinv : v * b * v⁻¹ = b⁻¹) :
    ∃ s : G, s ∈ (M.T : Subgroup G) ∧
      Subgroup.zpowers b = Subgroup.zpowers (s * M.b5el * s⁻¹) := by
  have hvS : v ∈ ruS M.L := M.Ual_le_S hvU
  have hvH : v ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hvq := RuChoice.Ual_mul_mem_Q M hvU hvQ
  have hker : (⟨v, hvH⟩ : ruH M.T) * (⟨M.vel, M.vel_mem_H⟩ : ruH M.T)⁻¹ ∈ M.φ.ker := by
    rw [M.φ_ker, Subgroup.mem_subgroupOf]
    exact hvq
  have hφv : M.φ ⟨v, hvH⟩ = M.φ ⟨M.vel, M.vel_mem_H⟩ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    exact hker
  set w : SigmaL2F4 := M.φ ⟨M.vel, M.vel_mem_H⟩ with hw
  have hwSP0 : w ∈ Sigma.SP0 := by
    rw [← M.hSP0]
    exact ⟨⟨M.vel, M.vel_mem_H⟩, Subgroup.mem_subgroupOf.mpr M.vel_mem_T, rfl⟩
  have hw2 : w * w = 1 := by
    rw [hw, ← map_mul]
    have : (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) * ⟨M.vel, M.vel_mem_H⟩ = 1 :=
      Subtype.ext M.vel_mul_self
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply M.vel_not_mem_Q
    have : (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  have hwr : w.right = 1 := by
    obtain ⟨hk, hk1⟩ := M.mem_K_iff.mp M.vel_mem_K
    exact hk1
  have hb5H : M.b5el ∈ ruH M.T := M.b5el_mem_H
  have hbQ : ∀ (x : G) (hx : x ∈ ruH M.T), orderOf x = 5 → M.φ ⟨x, hx⟩ ≠ 1 := by
    intro x hx hx5 h
    have : (⟨x, hx⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    have h1 := Subgroup.orderOf_dvd_natCard _ this
    rw [hx5, M.toRuData.card_Q] at h1
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1
    omega
  have hord : ∀ (x : G) (hx : x ∈ ruH M.T), orderOf x = 5 → (M.φ ⟨x, hx⟩) ^ 5 = 1 := by
    intro x hx hx5
    rw [← map_pow]
    have : (⟨x, hx⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hx5]
      exact pow_orderOf_eq_one x)
    rw [this, map_one]
  have hb₁inv : w * M.φ ⟨b, hbH⟩ * w⁻¹ = (M.φ ⟨b, hbH⟩)⁻¹ := by
    have h := congrArg M.φ (show (⟨v, hvH⟩ : ruH M.T) * ⟨b, hbH⟩ * ⟨v, hvH⟩⁻¹ = ⟨b, hbH⟩⁻¹ from
      Subtype.ext hinv)
    rw [map_mul, map_mul, map_inv, map_inv, hφv] at h
    exact h
  have hb₂inv : w * M.φ ⟨M.b5el, hb5H⟩ * w⁻¹ = (M.φ ⟨M.b5el, hb5H⟩)⁻¹ := by
    have h := congrArg M.φ (show (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) * ⟨M.b5el, hb5H⟩ *
        ⟨M.vel, M.vel_mem_H⟩⁻¹ = ⟨M.b5el, hb5H⟩⁻¹ from Subtype.ext M.vel_inv_b5el)
    rw [map_mul, map_mul, map_inv, map_inv] at h
    exact h
  obtain ⟨s₀, hs₀, k, hk⟩ := RuChoice.sylow5_swap w hwSP0 hw2 hw1 hwr
    (M.φ ⟨b, hbH⟩) (hord b hbH hb5) (hbQ b hbH hb5) hb₁inv
    (M.φ ⟨M.b5el, hb5H⟩) (hord _ hb5H M.orderOf_b5el) (hbQ _ hb5H M.orderOf_b5el) hb₂inv
  have hs₀' := hs₀
  rw [← M.hSP0] at hs₀'
  obtain ⟨x₁, hx₁T, hx₁⟩ := hs₀'
  set s₁ : G := (x₁ : G) with hs₁
  have hs₁T : s₁ ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp hx₁T
  have hs₁H : s₁ ∈ ruH M.T := x₁.2
  set c : G := s₁ * M.b5el * s₁⁻¹ with hc
  have hcH : c ∈ ruH M.T := mul_mem (mul_mem hs₁H hb5H) (inv_mem hs₁H)
  have hcord : orderOf c = 5 := by
    rw [hc, CFSG.Quasithin.RuType.orderOf_conj_eq]
    exact M.orderOf_b5el
  have hφc : M.φ ⟨c, hcH⟩ = (M.φ ⟨b, hbH⟩) ^ (k : ℕ) := by
    rw [← hk, ← hx₁]
    have : (⟨c, hcH⟩ : ruH M.T) = x₁ * ⟨M.b5el, hb5H⟩ * x₁⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hker2 : ((⟨b, hbH⟩ : ruH M.T) ^ (k : ℕ))⁻¹ * ⟨c, hcH⟩ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hφc, inv_mul_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hker2
  have hker3 : (b ^ (k : ℕ))⁻¹ * c ∈ ruQ M.T := hker2
  have hQ2 : IsPGroup 2 (ruQ M.T) := IsPGroup.of_card M.toRuData.card_Q
  have hbN : b ∈ Subgroup.normalizer ((ruQ M.T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact M.conj_mem_Q hbH hq
    · intro hq
      have := M.conj_mem_Q (inv_mem hbH) hq
      simpa [mul_assoc] using this
  obtain ⟨q, hq, hzq⟩ := RuChoice.sylow_mod hQ2 hb5 hcord hbN hker3
  refine ⟨q * s₁, mul_mem (M.toRuDataN.Q_le_T hq) hs₁T, ?_⟩
  rw [hzq]
  congr 1
  simp only [hc]
  group

open CFSG.Quasithin.RuType in
theorem RuChoice.sylow5_gen {G : Type} [Group G] [Finite G] (M : RuDataM G) {B5 : Subgroup G}
    (hB5 : ChIJK.IsSylowIn 5 B5 (ChIJK.HRu (M.T : Subgroup G))) :
    ∃ b : G, b ∈ ruH M.T ∧ orderOf b = 5 ∧ B5 = Subgroup.zpowers b := by
  rw [RuChoice.HRu_eq] at hB5
  obtain ⟨hle, hp, hidx⟩ := hB5
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have h := Subgroup.card_mul_index (B5.subgroupOf (ruH M.T))
  rw [card_subgroupOf_of_le hle, hn, M.toRuData.card_H] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      apply hidx
      rw [pow_zero, one_mul] at h
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ 2 ^ 11 * 120 := by
        rw [← h]
        exact Dvd.dvd.mul_right ⟨5 ^ n, by ring⟩ _
      norm_num at h25
  subst hn1
  have hcard : Nat.card B5 = 5 := by rw [hn]; norm_num
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B5, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B5 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hord : orderOf b = 5 := by
    have h1 : orderOf b ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard B5 hbB
      rwa [hcard] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  refine ⟨b, hle hbB, hord, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
    (by rw [Nat.card_zpowers, hord, hcard])).symm

theorem RuChoice.zpowers_conj {G : Type} [Group G] {b x : G}
    (h : Subgroup.zpowers b = Subgroup.zpowers x) (t : G) :
    Subgroup.zpowers (t * b * t⁻¹) = Subgroup.zpowers (t * x * t⁻¹) := by
  have := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) h
  simpa [MonoidHom.map_zpowers, MulAut.conj_apply] using this

open CFSG.Quasithin.RuType in
theorem RuChoice.plane :
    ∀ l ∈ SL3.Pl, natAct3 l SL3.e0 ≠ SL3.e0 →
      ∃ p ∈ SL3.P0, natAct3 p⁻¹ ![0, 1, 0] = natAct3 l SL3.e0 := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.B5_proof {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {g : G} (hg : g ∈ L2Ru M.L V2) (hgH : g ∉ HRu (M.T : Subgroup G))
    {v : G} (hv : v ∈ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g)
    (hvQ : v ∉ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g ⊓ QRu (M.T : Subgroup G))
    {B5 : Subgroup G} (hB5 : IsSylowIn 5 B5 (HRu (M.T : Subgroup G))) (hinv : InvertsGroup v B5) :
    ∃ t : G, t ∈ (M.T : Subgroup G) ∧ B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t := by
  obtain ⟨b, hbH, hb5, rfl⟩ := RuChoice.sylow5_gen M hB5
  have hgG2 : g ∈ M.G2 := by
    rw [RuChoice.L2Ru_eq M hV2] at hg
    exact RuChoice.twoResidual_le _ hg
  obtain ⟨hgL, hgPl⟩ := mem_pullL.mp hgG2
  rw [RuChoice.HRu_eq] at hgH
  have hθ : M.θ ⟨g, hgL⟩ ∉ SL3.Stab0 := by
    intro h
    apply hgH
    have : g ∈ M.LT1 := mem_pullL.mpr ⟨hgL, h⟩
    rw [← M.L_inf_H] at this
    exact this.2
  have hlL : g⁻¹ ∈ M.L := inv_mem hgL
  have hθl : M.θ ⟨g⁻¹, hlL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hlPl : M.θ ⟨g⁻¹, hlL⟩ ∈ SL3.Pl := by
    rw [hθl]
    exact inv_mem hgPl
  have hlSt : natAct3 (M.θ ⟨g⁻¹, hlL⟩) SL3.e0 ≠ SL3.e0 := by
    intro h
    apply hθ
    have h1 : M.θ ⟨g⁻¹, hlL⟩ ∈ SL3.Stab0 := h
    rw [hθl] at h1
    have := SL3.Stab0.inv_mem h1
    rwa [inv_inv] at this
  obtain ⟨p, hp0, hpe⟩ := RuChoice.plane _ hlPl hlSt
  obtain ⟨t', ht'L, ht'T, hθt'⟩ := RuChoice.exists_T_of_P0 M hp0
  have ht'H : t' ∈ ruH M.T := M.toRuData.T_le_H ht'T
  have hl'L : t'⁻¹ * (M.gel : G) ∈ M.L := mul_mem (inv_mem ht'L) M.gel.2
  have hcu : M.conjU g⁻¹ = M.conjU (t'⁻¹ * (M.gel : G)) := by
    refine (M.conjU_eq_conjU_iff ⟨g⁻¹, hlL⟩ ⟨t'⁻¹ * (M.gel : G), hl'L⟩).mpr ?_
    have e : (⟨t'⁻¹ * (M.gel : G), hl'L⟩ : M.L) = (⟨t', ht'L⟩ : M.L)⁻¹ * M.gel := rfl
    rw [e, map_mul, map_inv, hθt', M.θ_gel, SL3.natAct3_mul, SL3.natAct3_gpl_e0, ← hpe]
  have hv' : v ∈ M.conjU g⁻¹ := by
    rw [← RuChoice.conjugate_U_eq]
    exact hv
  rw [hcu] at hv'
  have hv1 := M.mem_conjU.mp hv'
  have hvU : t' * v * t'⁻¹ ∈ M.Ual := by
    show t' * v * t'⁻¹ ∈ M.conjU (M.gel : G)
    rw [M.mem_conjU]
    have e : (M.gel : G)⁻¹ * (t' * v * t'⁻¹) * (M.gel : G) =
        (t'⁻¹ * (M.gel : G))⁻¹ * v * (t'⁻¹ * (M.gel : G)) := by group
    rw [e]
    exact hv1
  have hvQ' : v ∉ ruQ M.T := by
    intro h
    apply hvQ
    rw [RuChoice.QRu_eq]
    exact Subgroup.mem_inf.mpr ⟨hv, h⟩
  have hvQ'' : t' * v * t'⁻¹ ∉ ruQ M.T := by
    intro h
    apply hvQ'
    have := M.conj_mem_Q (inv_mem ht'H) h
    simpa [mul_assoc] using this
  have hvb : v * b * v⁻¹ = b⁻¹ := by
    have h1 := hinv.2 b (Subgroup.mem_zpowers b)
    have h2 : v⁻¹ * b⁻¹ * v = b := by
      have := congrArg (fun x => x⁻¹) h1
      simpa [mul_assoc] using this
    calc v * b * v⁻¹ = v * (v⁻¹ * b⁻¹ * v) * v⁻¹ := by rw [h2]
      _ = b⁻¹ := by group
  have hb'H : t' * b * t'⁻¹ ∈ ruH M.T := mul_mem (mul_mem ht'H hbH) (inv_mem ht'H)
  have hb'5 : orderOf (t' * b * t'⁻¹) = 5 := by
    rw [CFSG.Quasithin.RuType.orderOf_conj_eq]
    exact hb5
  have hinv' : (t' * v * t'⁻¹) * (t' * b * t'⁻¹) * (t' * v * t'⁻¹)⁻¹ = (t' * b * t'⁻¹)⁻¹ := by
    calc (t' * v * t'⁻¹) * (t' * b * t'⁻¹) * (t' * v * t'⁻¹)⁻¹ = t' * (v * b * v⁻¹) * t'⁻¹ := by
          group
      _ = t' * b⁻¹ * t'⁻¹ := by rw [hvb]
      _ = (t' * b * t'⁻¹)⁻¹ := by group
  obtain ⟨s, hsT, hz⟩ := RuChoice.B5_core M hvU hvQ'' hb'H hb'5 hinv'
  refine ⟨s⁻¹ * t', mul_mem (inv_mem hsT) ht'T, ?_⟩
  have h3 := RuChoice.zpowers_conj hz t'⁻¹
  have e1 : t'⁻¹ * (t' * b * t'⁻¹) * t'⁻¹⁻¹ = b := by group
  rw [e1] at h3
  rw [h3]
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.B5 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {g : G} (hg : g ∈ L2Ru M.L V2) (hgH : g ∉ HRu (M.T : Subgroup G))
    {v : G} (hv : v ∈ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g)
    (hvQ : v ∉ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g ⊓ QRu (M.T : Subgroup G))
    {B5 : Subgroup G} (hB5 : IsSylowIn 5 B5 (HRu (M.T : Subgroup G))) (hinv : InvertsGroup v B5) :
    ∃ t : G, t ∈ (M.T : Subgroup G) ∧ B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t :=
  RuChoice.B5_proof M hV2 hg hgH hv hvQ hB5 hinv

open CFSG.Quasithin.RuType in
open scoped commutatorElement in
theorem RuChoice.Q5_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {b : G}
    (hbH : b ∈ ruH M.T) :
    M.Q5 hbH = ⁅ruQ M.T, Subgroup.zpowers b⁆ ⊔ ruU M.L M.T := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, a', ha'⟩ := (M.mem_Q5 hbH).mp hx
    induction a' using QuotientGroup.induction_on with
    | H a =>
    have ha'' : M.dQ ⟨b, hbH⟩ (a : M.Qbar) = ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) := ha'
    rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      M.mk_eq_mk_iff] at ha''
    have hc : ((M.conjQ ⟨b, hbH⟩ a * a⁻¹ : ruQ M.T) : G) = b * a * b⁻¹ * (a : G)⁻¹ := rfl
    rw [hc] at ha''
    have e : x = (b * a * b⁻¹ * (a : G)⁻¹) * ((b * a * b⁻¹ * (a : G)⁻¹)⁻¹ * x) := by group
    rw [e]
    refine Subgroup.mul_mem_sup ?_ ha''
    have h1 : ⁅(a : G), b⁆ ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_zpowers b)
    have h2 := inv_mem h1
    have e2 : b * a * b⁻¹ * (a : G)⁻¹ = ⁅(a : G), b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact h2
  · refine sup_le ?_ (M.U_le_Q5 hbH)
    rw [Subgroup.commutator_le]
    intro q hq y hy
    have hyp : y ∈ Submonoid.powers b := (mem_powers_iff_mem_zpowers).mpr hy
    obtain ⟨j, rfl⟩ := hyp
    have hbj : b ^ j ∈ ruH M.T := pow_mem hbH j
    have hQ : ⁅q, b ^ j⁆ ∈ ruQ M.T := by
      have h1 := M.conj_mem_Q hbj (inv_mem hq)
      have e : ⁅q, b ^ j⁆ = q * (b ^ j * q⁻¹ * (b ^ j)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hq h1
    refine (M.mem_Q5 hbH).mpr ⟨hQ, ?_⟩
    have key : ((⟨⁅q, b ^ j⁆, hQ⟩ : ruQ M.T) : M.Qbar) =
        (M.dQ (⟨b, hbH⟩ ^ j) ((⟨q, hq⟩ : ruQ M.T) : M.Qbar))⁻¹ := by
      rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv]
      congr 1
      apply Subtype.ext
      show ⁅q, b ^ j⁆ = (((b ^ j : G) * q * (b ^ j : G)⁻¹) * q⁻¹)⁻¹
      simp only [commutatorElement_def]
      group
    rw [key]
    exact inv_mem (M.dQ_pow_range_le ⟨b, hbH⟩ j ⟨_, rfl⟩)

theorem RuChoice.map_conj_eq {G : Type} [Group G] (A : Subgroup G) (c : G)
    (h : ∀ x ∈ A, c * x * c⁻¹ ∈ A) (h' : ∀ x ∈ A, c⁻¹ * x * c ∈ A) :
    A.map (MulAut.conj c).toMonoidHom = A := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := h _ hx
    simpa [mul_assoc] using this
  · intro hx
    exact h' x hx

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.Q5_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) :
    Q5Ru (M.T : Subgroup G) B5 ⊔ URu (ruV M.L) (M.T : Subgroup G) =
      CFSG.conjugate (M.Q5 M.b5el_mem_H) t := by
  have htH : t ∈ ruH M.T := M.toRuData.T_le_H ht
  have hQ : (ruQ M.T).map (MulAut.conj t⁻¹).toMonoidHom = ruQ M.T :=
    RuChoice.map_conj_eq _ _ (fun x hx => M.conj_mem_Q (inv_mem htH) hx)
      (fun x hx => by simpa using M.conj_mem_Q htH hx)
  have hU : (ruU M.L M.T).map (MulAut.conj t⁻¹).toMonoidHom = ruU M.L M.T :=
    RuChoice.map_conj_eq _ _ (fun x hx => M.conj_mem_U (inv_mem htH) hx)
      (fun x hx => by simpa using M.conj_mem_U htH hx)
  rw [RuChoice.Q5_eq M M.b5el_mem_H]
  unfold Q5Ru CFSG.conjugate
  rw [hB, RuChoice.QRu_eq, RuChoice.URu_eq, Subgroup.map_sup, Subgroup.map_commutator,
    hQ, hU]
  unfold CFSG.conjugate
  rfl

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.Q5 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) :
    Q5Ru (M.T : Subgroup G) B5 ⊔ URu (ruV M.L) (M.T : Subgroup G) =
      CFSG.conjugate (M.Q5 M.b5el_mem_H) t :=
  RuChoice.Q5_proof M ht hB

theorem RuChoice.mem_normalizer {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := (MulAut.conj g).injective hyx
  rwa [← this]

theorem RuChoice.conjugate_sup {G : Type} [Group G] (A B : Subgroup G) (t : G) :
    CFSG.conjugate (A ⊔ B) t = CFSG.conjugate A t ⊔ CFSG.conjugate B t := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem RuChoice.conjugate_inf {G : Type} [Group G] (A B : Subgroup G) (t : G) :
    CFSG.conjugate (A ⊓ B) t = CFSG.conjugate A t ⊓ CFSG.conjugate B t := by
  unfold CFSG.conjugate
  exact Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective

theorem RuChoice.conjugate_zpowers {G : Type} [Group G] (x t : G) :
    CFSG.conjugate (Subgroup.zpowers x) t = Subgroup.zpowers (t⁻¹ * x * t) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem RuChoice.conjugate_eq_self {G : Type} [Group G] {A : Subgroup G} {t : G}
    (h : ∀ x ∈ A, t * x * t⁻¹ ∈ A) (h' : ∀ x ∈ A, t⁻¹ * x * t ∈ A) :
    CFSG.conjugate A t = A := by
  unfold CFSG.conjugate
  exact RuChoice.map_conj_eq A t⁻¹ (fun x hx => by simpa using h' x hx)
    (fun x hx => by simpa using h x hx)

theorem RuChoice.mem_conjugate {G : Type} [Group G] {A : Subgroup G} {t x : G} :
    x ∈ CFSG.conjugate A t ↔ t * x * t⁻¹ ∈ A := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

open scoped Pointwise in
open CFSG.Quasithin.RuType in
theorem RuChoice.Q5W_inf_R2
    {G : Type} [Group G] [Finite G] (M : CFSG.Quasithin.RuType.RuDataM G) :
    (M.Q5 M.b5el_mem_H ⊔ M.W) ⊓ M.R2 = Subgroup.zpowers M.ael ⊔ M.W := by
  apply le_antisymm
  · rintro x ⟨hx1, hxR⟩
    have hQT : M.Q5 M.b5el_mem_H ≤ (M.T : Subgroup G) :=
      (M.Q5_le_Q _).trans M.toRuDataN.Q_le_T
    have hnorm : M.Q5 M.b5el_mem_H ≤ Subgroup.normalizer (M.W : Set G) := fun p hp =>
      RuChoice.mem_normalizer fun w hw => M.conj_mem_W (M.T_le_G2 (hQT hp)) hw
    have hset : ((M.Q5 M.b5el_mem_H ⊔ M.W : Subgroup G) : Set G) =
        ((M.Q5 M.b5el_mem_H : Subgroup G) : Set G) * ((M.W : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
    have hx1' : x ∈ ((M.Q5 M.b5el_mem_H : Subgroup G) : Set G) * ((M.W : Subgroup G) : Set G) := by
      rw [← hset]
      exact hx1
    obtain ⟨p, hp, w, hw, rfl⟩ := Set.mem_mul.mp hx1'
    have hpL := M.Q5_le_L _ hp
    have hwS : w ∈ ruS M.L := M.W_le_S hw
    have hwL : w ∈ M.L := M.toRuData.S_le_L hwS
    have hwθ : M.θ ⟨w, hwL⟩ = 1 := (M.mem_S_iff_θ hwL).mp hwS
    have hθR0 : M.θ ⟨p, hpL⟩ ∈ SL3.R0 := by
      rw [← M.θQ_eq]
      exact ⟨⟨p, hpL⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q _ hp), rfl⟩
    have hxL : p * w ∈ M.L := mul_mem hpL hwL
    have hθx : M.θ ⟨p * w, hxL⟩ = M.θ ⟨p, hpL⟩ := by
      have : (⟨p * w, hxL⟩ : M.L) = ⟨p, hpL⟩ * ⟨w, hwL⟩ := rfl
      rw [this, map_mul, hwθ, mul_one]
    have hθR2 : M.θ ⟨p, hpL⟩ ∈ SL3.R2m := by
      rw [← hθx]
      exact (mem_pullL.mp hxR).2
    have key : ∀ c ∈ M.Q5 M.b5el_mem_H, ∀ hc : c ∈ M.L, M.θ ⟨c, hc⟩ = M.θ ⟨p, hpL⟩ →
        c⁻¹ * p ∈ M.W := by
      intro c hc hcL hθc
      refine M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hc) hp, ?_⟩)
      rw [M.mem_S_iff_θ (mul_mem (inv_mem hcL) hpL)]
      have e : (⟨c⁻¹ * p, mul_mem (inv_mem hcL) hpL⟩ : M.L) = (⟨c, hcL⟩ : M.L)⁻¹ * ⟨p, hpL⟩ := rfl
      rw [e, map_mul, map_inv, hθc, inv_mul_cancel]
    rcases CFSG.Quasithin.RuType.SL3.R0_elems _ hθR0 with h | h | h | h
    ·
      have hpS : p ∈ ruS M.L := (M.mem_S_iff_θ hpL).mpr h
      have hpW : p ∈ M.W := M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr ⟨hp, hpS⟩)
      exact Subgroup.mem_sup_right (mul_mem hpW hw)
    ·
      have h1 := key M.ael M.ael_mem_Q5 M.ael_mem_L (by rw [M.θ_ael, h])
      have e : p * w = M.ael * ((M.ael⁻¹ * p) * w) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (mul_mem h1 hw)
    · exfalso
      rw [h] at hθR2
      exact CFSG.Quasithin.RuType.SL3.rr_not_mem_R2m hθR2
    · exfalso
      rw [h] at hθR2
      have hz : CFSG.Quasithin.RuType.SL3.zP0 ∈ CFSG.Quasithin.RuType.SL3.R2m :=
        CFSG.Quasithin.RuType.SL3.zP0_mem_R2m
      have := mul_mem hθR2 (inv_mem hz)
      rw [mul_inv_cancel_right] at this
      exact CFSG.Quasithin.RuType.SL3.rr_not_mem_R2m this
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left M.ael_mem_Q5, M.ael_mem_R2⟩
    · exact le_inf le_sup_right (M.W_le_S.trans M.S_le_R2)

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.A_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a = M.Agrp := by
  obtain ⟨hG2, hR2, hS2⟩ := RuChoice.frame M hV2
  have htG : t ∈ M.G2 := M.T_le_G2 ht
  have htiG : t⁻¹ ∈ M.G2 := inv_mem htG
  have hWfix : ∀ g ∈ M.G2, CFSG.conjugate M.W g = M.W := fun g hg =>
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_W hg hx)
      (fun x hx => by simpa using M.conj_mem_W (inv_mem hg) hx)
  have hR2fix : CFSG.conjugate M.R2 t = M.R2 :=
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_R2 htG hx)
      (fun x hx => by simpa using M.conj_mem_R2 htiG hx)
  have hQ5 := RuChoice.Q5 M ht hB
  rw [RuChoice.URu_eq] at hQ5
  have hQW : Q5Ru (M.T : Subgroup G) B5 ⊔ M.W =
      CFSG.conjugate (M.Q5 M.b5el_mem_H ⊔ M.W) t := by
    rw [RuChoice.conjugate_sup, hWfix t htG, ← hQ5, sup_assoc,
      sup_eq_right.mpr M.U_le_W]
  set c : G := t⁻¹ * M.ael * t with hc
  have hIn : (Q5Ru (M.T : Subgroup G) B5 ⊔ M.W) ⊓ M.R2 = Subgroup.zpowers c ⊔ M.W := by
    rw [hQW]
    conv_lhs => rw [← hR2fix]
    rw [← RuChoice.conjugate_inf, RuChoice.Q5W_inf_R2, RuChoice.conjugate_sup,
      hWfix t htG, RuChoice.conjugate_zpowers]
  obtain ⟨ha1, -, -, -⟩ := ha
  rw [hS2, hR2] at ha1
  have hac : Subgroup.zpowers a ⊔ M.W = Subgroup.zpowers c ⊔ M.W := ha1.symm.trans hIn
  have hcA : c ∈ M.Agrp := by
    have := M.conj_mem_Agrp htiG M.ael_mem_Agrp
    simpa [hc] using this
  have haA : a ∈ M.Agrp := by
    have h1 : a ∈ Subgroup.zpowers a ⊔ M.W := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    rw [hac] at h1
    exact (sup_le (Subgroup.zpowers_le.mpr hcA) M.W_le_Agrp) h1
  unfold ARu
  rw [hG2, hS2]
  apply le_antisymm
  · refine sup_le ?_ M.W_le_Agrp
    unfold conjClosure
    refine iSup₂_le fun y hy => ?_
    intro z hz
    rw [RuChoice.mem_conjugate] at hz
    have h1 : y * z * y⁻¹ ∈ M.Agrp := (Subgroup.zpowers_le.mpr haA) hz
    have := M.conj_mem_Agrp (inv_mem hy) h1
    simpa [mul_assoc] using this
  · set Z : Subgroup G := conjClosure (Subgroup.zpowers a) M.G2 ⊔ M.W with hZ
    have hWZ : M.W ≤ Z := le_sup_right
    have hconjZ : ∀ g ∈ M.G2, g * M.ael * g⁻¹ ∈ Z := by
      intro g hg
      have hy : (g * t)⁻¹ ∈ M.G2 := inv_mem (mul_mem hg htG)
      have hmem : g * M.ael * g⁻¹ ∈ CFSG.conjugate (Subgroup.zpowers a ⊔ M.W) (g * t)⁻¹ := by
        rw [RuChoice.mem_conjugate, hac]
        refine Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩)
        simp only [hc, zpow_one]
        group
      rw [RuChoice.conjugate_sup, hWfix _ hy] at hmem
      have hle : CFSG.conjugate (Subgroup.zpowers a) (g * t)⁻¹ ≤
          conjClosure (Subgroup.zpowers a) M.G2 :=
        le_iSup₂ (f := fun y (_ : y ∈ M.G2) => CFSG.conjugate (Subgroup.zpowers a) y)
          (g * t)⁻¹ hy
      exact (sup_le_sup_right hle _) hmem
    have c0 : M.cak 0 ∈ Z := by
      rw [M.cak_zero]
      simpa using hconjZ 1 (one_mem _)
    have c1 : M.cak 1 ∈ Z := by
      have := hconjZ (M.xel : G) M.xel_mem_G2
      simpa [CFSG.Quasithin.RuType.RuDataM.cak] using this
    intro x hx
    obtain ⟨-, h | h | h | h⟩ := M.mem_Agrp_iff.mp hx
    · exact hWZ h
    · have e : x = M.cak 0 * ((M.cak 0)⁻¹ * x) := by group
      rw [e]
      exact mul_mem c0 (hWZ h)
    · have e : x = M.cak 1 * ((M.cak 1)⁻¹ * x) := by group
      rw [e]
      exact mul_mem c1 (hWZ h)
    · have e : x = (M.cak 0 * M.cak 1) * ((M.cak 0 * M.cak 1)⁻¹ * x) := by group
      rw [e]
      exact mul_mem (mul_mem c0 c1) (hWZ h)

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.TF_F1_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 t := by
  have hA := RuChoice.A_proof M hV2 ht hB ha
  have htG : t ∈ M.G2 := M.T_le_G2 ht
  have htiG : t⁻¹ ∈ M.G2 := inv_mem htG
  have hQ5 := RuChoice.Q5 M ht hB
  rw [RuChoice.URu_eq] at hQ5
  have hAfix : CFSG.conjugate M.Agrp t = M.Agrp :=
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_Agrp htG hx)
      (fun x hx => by simpa using M.conj_mem_Agrp htiG hx)
  have hUA : ruU M.L M.T ≤ M.Agrp := M.U_le_W.trans M.W_le_Agrp
  have hTF : TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t := by
    unfold TFRu
    rw [hA]
    show M.Agrp ⊔ Q5Ru (M.T : Subgroup G) B5 = CFSG.conjugate (M.Agrp ⊔ M.Q5 M.b5el_mem_H) t
    rw [RuChoice.conjugate_sup, hAfix, ← hQ5]
    exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
      (sup_le le_sup_left (sup_le le_sup_right (hUA.trans le_sup_left)))
  refine ⟨hTF, ?_⟩
  unfold F1Ru
  rw [hTF, hB, ← RuChoice.conjugate_sup]
  congr 1
  show M.Agrp ⊔ M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el =
    M.Agrp ⊔ (M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el)
  rw [sup_assoc]

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.A {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a = M.Agrp :=
  RuChoice.A_proof M hV2 ht hB ha

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.TF_F1 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 t :=
  RuChoice.TF_F1_proof M hV2 ht hB ha

theorem RuChoice.fx_mem_conjugate {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_apply]

theorem RuChoice.fx_conjugate_conjugate {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext y
  rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate]
  have : g * (h * y * h⁻¹) * g⁻¹ = (g * h) * y * (g * h)⁻¹ := by group
  rw [this]

theorem RuChoice.fx_conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    CFSG.conjugate A 1 = A := by
  ext y
  rw [RuChoice.fx_mem_conjugate]
  simp

theorem RuChoice.fx_card_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem RuChoice.fx_conjugate_le {G : Type*} [Group G] {A N : Subgroup G} {g : G} (hA : A ≤ N)
    (hg : g ∈ N) : CFSG.conjugate A g ≤ N := by
  intro y hy
  rw [RuChoice.fx_mem_conjugate] at hy
  have h1 := N.mul_mem (N.mul_mem (N.inv_mem hg) (hA hy)) hg
  simpa [mul_assoc] using h1

theorem RuChoice.fx_conjugate_mono {G : Type*} [Group G] {A B : Subgroup G} (g : G)
    (h : A ≤ B) : CFSG.conjugate A g ≤ CFSG.conjugate B g := by
  intro y hy
  rw [RuChoice.fx_mem_conjugate] at hy ⊢
  exact h hy

theorem RuChoice.fx_normalizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.normalizer (A : Set G)) g := by
  ext y
  rw [RuChoice.fx_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g⁻¹ * a * g)
    rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate] at this
    have e : g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ := by group
    simpa [e, mul_assoc] using this
  · intro h a
    rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate]
    have := h (g * a * g⁻¹)
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem RuChoice.fx_conjugate_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem RuChoice.fx_conjugate_eq_self {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : CFSG.conjugate A g = A := by
  ext y
  rw [RuChoice.fx_mem_conjugate]
  exact (Subgroup.mem_normalizer_iff.mp hg y).symm

theorem RuChoice.fx_conjugate_zpowers {G : Type*} [Group G] (x g : G) :
    CFSG.conjugate (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem RuChoice.fx_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (h1 : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (h2 : ∀ y ∈ K, g⁻¹ * y * g ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    simpa [mul_assoc] using this

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_G2_factor {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {g : G} (hg : g ∈ M.G2) :
    ∃ t ∈ (M.T : Subgroup G), ∃ x ∈ Subgroup.zpowers M.x2el, g = t * x := by
  classical
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hX0 : Nat.card (Subgroup.zpowers M.x2el) = 3 := by
    rw [Nat.card_zpowers, M.orderOf_x2el]
  have hinf : ∀ y : G, y ∈ (M.T : Subgroup G) → y ∈ Subgroup.zpowers M.x2el → y = 1 := by
    intro y hyT hyX
    have h1 : orderOf y ∣ 2 ^ 14 := by
      have := Subgroup.orderOf_dvd_natCard _ hyT
      rwa [hT] at this
    have h2 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard _ hyX
      rwa [hX0] at this
    have hd := Nat.dvd_gcd h1 h2
    have : Nat.gcd (2 ^ 14) 3 = 1 := by norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hXG : Subgroup.zpowers M.x2el ≤ M.G2 := (Subgroup.zpowers_le).mpr M.x2el_mem_G2
  let f : ↥(M.T : Subgroup G) × ↥(Subgroup.zpowers M.x2el) → ↥M.G2 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (M.T_le_G2 p.1.2) (hXG p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨t, ht⟩, ⟨x, hx⟩⟩ ⟨⟨t', ht'⟩, ⟨x', hx'⟩⟩ h
    have h' : t * x = t' * x' := congrArg Subtype.val h
    have h1 : t'⁻¹ * t = x' * x⁻¹ := by
      have : t'⁻¹ * (t * x) * x⁻¹ = t'⁻¹ * (t' * x') * x⁻¹ := by rw [h']
      simpa [mul_assoc] using this
    have hA : t'⁻¹ * t ∈ (M.T : Subgroup G) := mul_mem (inv_mem ht') ht
    have hB : x' * x⁻¹ ∈ Subgroup.zpowers M.x2el := mul_mem hx' (inv_mem hx)
    have h2 : t'⁻¹ * t = 1 := hinf _ hA (h1 ▸ hB)
    have h3 : t = t' := by
      have := congrArg (fun y => t' * y) h2
      simpa using this
    subst h3
    have h4 : x = x' := mul_left_cancel h'
    subst h4
    rfl
  have hcard : Nat.card ↥M.G2 ≤ Nat.card (↥(M.T : Subgroup G) × ↥(Subgroup.zpowers M.x2el)) := by
    rw [Nat.card_prod, hT, hX0, M.card_G2]
    norm_num
  obtain ⟨⟨t, x⟩, h⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨g, hg⟩
  exact ⟨t, t.2, x, x.2, (congrArg Subtype.val h).symm⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_exists_conj {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {X : Subgroup G} (hX : CFSG.ASVolI.ChIJK.IsSylowIn 3 X M.G2) :
    ∃ s ∈ (M.T : Subgroup G), X = CFSG.conjugate (Subgroup.zpowers M.x2el) s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXG, hXp, hidx⟩ := hX
  have hG2 : Nat.card M.G2 = 2 ^ 14 * 3 := by rw [M.card_G2]; norm_num
  have hXcard : Nat.card X = 3 := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    have h := Subgroup.index_mul_card (X.subgroupOf M.G2)
    rw [card_subgroupOf_of_le hXG, hn, hG2] at h
    have hn1 : n = 1 := by
      rcases n with _ | _ | n
      · exfalso
        rw [pow_zero, mul_one] at h
        apply hidx
        rw [h]
        norm_num
      · rfl
      · exfalso
        have h9 : 9 ∣ (X.subgroupOf M.G2).index * 3 ^ (n + 2) :=
          Dvd.dvd.mul_left (by
            rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
            exact pow_dvd_pow 3 (by omega)) _
        rw [h] at h9
        norm_num at h9
    rw [hn1, pow_one] at hn
    exact hn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard])
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have hXz : Subgroup.zpowers (y : G) = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2) (by
      rw [hXcard, Nat.card_zpowers, hy3])
  have hK : ¬ 3 ^ 2 ∣ Nat.card M.G2 := by
    rw [hG2]
    norm_num
  obtain ⟨g, hgG, hyg⟩ := exists_conj_zpowers hK M.x2el_mem_G2 (hXG y.2) M.orderOf_x2el hy3
  have hz3 : (g * M.x2el * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, M.x2el_pow_three]
    group
  have hz1 : g * M.x2el * g⁻¹ ≠ 1 := by
    intro h1
    have : M.x2el = 1 := by
      calc M.x2el = g⁻¹ * (g * M.x2el * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h3 := M.orderOf_x2el
    rw [this, orderOf_one] at h3
    norm_num at h3
  have hz : orderOf (g * M.x2el * g⁻¹) = 3 := orderOf_eq_prime hz3 hz1
  have hXeq : X = Subgroup.zpowers (g * M.x2el * g⁻¹) := by
    rw [← hXz]
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyg) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hz, hy3]
  obtain ⟨t, htT, x', hx', rfl⟩ := RuChoice.fx_G2_factor M hgG
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  refine ⟨t⁻¹, inv_mem htT, ?_⟩
  rw [RuChoice.fx_conjugate_zpowers, hXeq]
  congr 1
  group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_comm_isM2 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {l σ : G} (hl : l ∈ M.L) (hσS : σ ∈ ruS M.L)
    (hW : σ * l * σ⁻¹ * l⁻¹ ∈ M.W) :
    SL3.IsM2 (stAct (M.θ ⟨l, hl⟩) (Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) +
      Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) := by
  have hlσ : l * σ⁻¹ * l⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hl) σ⁻¹).mp (inv_mem hσS)
  obtain ⟨hcS, hM2⟩ := hW
  have hsplit : (⟨σ * l * σ⁻¹ * l⁻¹, hcS⟩ : ruS M.L) =
      (⟨σ, hσS⟩ : ruS M.L) * ⟨l * σ⁻¹ * l⁻¹, hlσ⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hχ : Multiplicative.toAdd (M.χ ⟨l * σ⁻¹ * l⁻¹, hlσ⟩) =
      stAct (M.θ ⟨l, hl⟩) (Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) := by
    have h := M.χ_conj ⟨l, hl⟩ ⟨σ⁻¹, inv_mem hσS⟩
    have h2 : Multiplicative.toAdd (M.χ ⟨σ⁻¹, inv_mem hσS⟩) =
        Multiplicative.toAdd (M.χ ⟨σ, hσS⟩) := M.toAdd_χ_inv ⟨σ, hσS⟩
    rw [h2] at h
    exact h
  rw [hsplit, M.toAdd_χ_mul, hχ] at hM2
  rw [add_comm]
  exact hM2

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_mem_W_of_normalizes {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {σ : G} (hσS : σ ∈ ruS M.L)
    (hσN : σ ∈ Subgroup.normalizer (M.XA : Set G)) : σ ∈ M.W := by
  have hxL : M.x2el ∈ M.L := M.x2el_mem_L
  have hxXA : M.x2el ∈ M.XA := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have h1 : σ * M.x2el * σ⁻¹ ∈ M.XA := (Subgroup.mem_normalizer_iff.mp hσN _).mp hxXA
  have hc : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ M.XA := mul_mem h1 (inv_mem hxXA)
  have hxσ : M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hxL) σ⁻¹).mp (inv_mem hσS)
  have hcS : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ ruS M.L := by
    have e : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ = σ * (M.x2el * σ⁻¹ * M.x2el⁻¹) := by group
    rw [e]
    exact mul_mem hσS hxσ
  have hcW : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ M.W := by
    rw [← M.F2_inf_S]
    refine ⟨?_, hcS⟩
    rw [M.F2_eq]
    exact Subgroup.mem_sup_right hc
  have h := RuChoice.fx_comm_isM2 M hxL hσS hcW
  rw [M.θ_x2el] at h
  exact ⟨hσS, SL3.x0_fpf_M2 _ (M.χ_trace _) h⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_inf_normalizer_XA {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) = M.TF := by
  set N := (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) with hN
  have hTFN : M.TF ≤ N := le_inf M.TF_le_T M.TF_le_normalizer_XA
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hR2A : M.R2 ⊓ N ≤ M.Agrp := by
    rintro r ⟨hrR, hrN⟩
    obtain ⟨hrL, hrP⟩ := mem_pullL.mp hrR
    obtain ⟨y, hyA, hyL, hθ⟩ := M.exists_Agrp_θ hrP
    have hσL : y⁻¹ * r ∈ M.L := mul_mem (inv_mem hyL) hrL
    have hσS : y⁻¹ * r ∈ ruS M.L := by
      rw [M.mem_S_iff_θ hσL]
      have e : (⟨y⁻¹ * r, hσL⟩ : M.L) = (⟨y, hyL⟩ : M.L)⁻¹ * ⟨r, hrL⟩ := rfl
      rw [e, map_mul, map_inv, hθ, inv_mul_cancel]
    have hyN : y ∈ Subgroup.normalizer (M.XA : Set G) :=
      Subgroup.le_normalizer (M.Agrp_le_XA hyA)
    have hσN : y⁻¹ * r ∈ Subgroup.normalizer (M.XA : Set G) :=
      mul_mem (inv_mem hyN) (Subgroup.mem_inf.mp hrN).2
    have hσW := RuChoice.fx_mem_W_of_normalizes M hσS hσN
    have e : r = y * (y⁻¹ * r) := by group
    rw [e]
    exact mul_mem hyA (M.W_le_Agrp hσW)
  have hc1 : Nat.card ↥(M.R2 ⊓ N) ≤ 2 ^ 11 := by
    have := Subgroup.card_le_of_le hR2A
    rwa [M.card_Agrp] at this
  have hNT : N ≤ (M.T : Subgroup G) := inf_le_left
  have hrel : M.R2.relIndex N ≤ 2 := by
    have h2 : M.R2.relIndex (M.T : Subgroup G) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := M.R2) (K := (M.T : Subgroup G))
      rw [inf_eq_left.mpr M.R2_le_T, M.card_R2, hT] at h
      have h' : M.R2.relIndex (M.T : Subgroup G) * 2 ^ 13 = 2 * 2 ^ 13 := by
        rw [h]
        norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
    have h1 : M.R2.relIndex N ≤ M.R2.relIndex (M.T : Subgroup G) :=
      Subgroup.relIndex_le_of_le_right hNT (by rw [h2]; norm_num)
    omega
  have hmul := Subgroup.relIndex_mul_card (H := M.R2) (K := N)
  have hcN : Nat.card N ≤ 2 ^ 12 := by
    rw [← hmul]
    calc M.R2.relIndex N * Nat.card ↥(M.R2 ⊓ N) ≤ 2 * 2 ^ 11 := Nat.mul_le_mul hrel hc1
      _ = 2 ^ 12 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTFN (by rw [M.card_TF]; exact hcN)).symm

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_F1_inf_T {G : Type} [Group G] [Finite G]
    (M : RuDataM G) : M.F1 ⊓ (M.T : Subgroup G) = M.TF := by
  have hTF : M.TF ≤ M.F1 ⊓ (M.T : Subgroup G) := le_inf M.TF_le_F1 M.TF_le_T
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  obtain ⟨k, -, hcard⟩ := RuDataN.exists_card_eq_two_pow
    (inf_le_right : M.F1 ⊓ (M.T : Subgroup G) ≤ (M.T : Subgroup G)) hT
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : M.F1 ⊓ (M.T : Subgroup G) ≤ M.F1)
  rw [hcard, M.card_F1] at hdvd
  have hk12 : k ≤ 12 := RuDataN.le_of_two_pow_dvd hdvd (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hTF (by
    rw [hcard, M.card_TF]
    exact Nat.pow_le_pow_right (by norm_num) hk12)).symm

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_Q_le_normalizer_F1 {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : ruQ M.T ≤ Subgroup.normalizer (M.F1 : Set G) := by
  intro q hq
  exact RuChoice.fx_mem_normalizer (fun y hy => M.Q_conj_mem_F1 hq hy)
    (fun y hy => by simpa using M.Q_conj_mem_F1 (inv_mem hq) hy)

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_Q_le_normalizer_TF {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : ruQ M.T ≤ Subgroup.normalizer (M.TF : Set G) := by
  intro q hq
  have hqT : q ∈ (M.T : Subgroup G) := M.Q_le_T hq
  have key : ∀ g : G, g ∈ ruQ M.T → ∀ y ∈ M.TF, g * y * g⁻¹ ∈ M.TF := by
    intro g hg y hy
    have hgT : g ∈ (M.T : Subgroup G) := M.Q_le_T hg
    have hyT : y ∈ (M.T : Subgroup G) := M.TF_le_T hy
    rw [← RuChoice.fx_F1_inf_T M]
    exact ⟨M.Q_conj_mem_F1 hg (M.TF_le_F1 hy),
      (M.T : Subgroup G).mul_mem ((M.T : Subgroup G).mul_mem hgT hyT)
        ((M.T : Subgroup G).inv_mem hgT)⟩
  exact RuChoice.fx_mem_normalizer (key q hq) (fun y hy => by simpa using key q⁻¹ (inv_mem hq) y hy)

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_card_Q_sup_TF {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : Nat.card ↥(ruQ M.T ⊔ M.TF) = 2 ^ 13 := by
  have h := card_sup_mul_inf_of_normalizes (RuChoice.fx_Q_le_normalizer_TF M)
  rw [inf_comm, M.TF_inf_Q, M.card_Y, M.toRuData.card_Q, M.card_TF] at h
  have h' : Nat.card ↥(ruQ M.T ⊔ M.TF) * 2 ^ 10 = 2 ^ 13 * 2 ^ 10 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_exists_not_normalizes {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    ∃ σ ∈ (M.T : Subgroup G), σ ∉ Subgroup.normalizer (M.TF : Set G) := by
  let A0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 0, 0; 1, 0, 0]
  have hA0 : IsTraceZero A0 := by decide
  have hA0M : ¬ SL3.IsM2 (stAct SL3.rr A0 + A0) := by decide
  obtain ⟨σ', hσ'⟩ := M.χ_surj A0 hA0
  refine ⟨(σ' : G), M.toRuData.S_le_T σ'.2, fun hσN => hA0M ?_⟩
  have hql : M.qel ∈ M.L := M.qel_mem_L
  have hq : M.qel ∈ M.TF := M.qel_mem_TF
  have h1 : (σ' : G) * M.qel * (σ' : G)⁻¹ ∈ M.TF := (Subgroup.mem_normalizer_iff.mp hσN _).mp hq
  have hc : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ M.TF := mul_mem h1 (inv_mem hq)
  have hlσ : M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hql) _).mp (inv_mem σ'.2)
  have hcS : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ ruS M.L := by
    have e : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ =
        (σ' : G) * (M.qel * (σ' : G)⁻¹ * M.qel⁻¹) := by group
    rw [e]
    exact mul_mem σ'.2 hlσ
  have hcW : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ M.W := by
    rw [← M.F2_inf_S]
    exact ⟨M.TF_le_F2 hc, hcS⟩
  have h := RuChoice.fx_comm_isM2 M hql σ'.2 hcW
  rw [M.θ_qel] at h
  have hA : Multiplicative.toAdd (M.χ ⟨(σ' : G), σ'.2⟩) = A0 := by
    have := congrArg Multiplicative.toAdd hσ'
    simpa using this
  rw [hA] at h
  exact h

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_normalizer_TF_le {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {n : G} (hnT : n ∈ (M.T : Subgroup G))
    (hn : n ∈ Subgroup.normalizer (M.TF : Set G)) : n ∈ Subgroup.normalizer (M.F1 : Set G) := by
  set N' := (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.TF : Set G) with hN'
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hle : ruQ M.T ⊔ M.TF ≤ N' :=
    sup_le (le_inf M.Q_le_T (RuChoice.fx_Q_le_normalizer_TF M))
      (le_inf M.TF_le_T Subgroup.le_normalizer)
  have hcard : Nat.card N' ≤ 2 ^ 13 := by
    obtain ⟨σ, hσT, hσ⟩ := RuChoice.fx_exists_not_normalizes M
    have hNT : N' ≤ (M.T : Subgroup G) := inf_le_left
    have hne : N'.relIndex (M.T : Subgroup G) ≠ 1 := by
      intro h1
      exact hσ (Subgroup.mem_inf.mp ((Subgroup.relIndex_eq_one.mp h1) hσT)).2
    have hmul := Subgroup.relIndex_mul_card (H := N') (K := (M.T : Subgroup G))
    rw [inf_eq_left.mpr hNT, hT] at hmul
    have hpos : 0 < N'.relIndex (M.T : Subgroup G) :=
      Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hmul; norm_num at hmul)
    have h2 : 2 ≤ N'.relIndex (M.T : Subgroup G) := by omega
    have h3 : 2 * Nat.card N' ≤ 2 ^ 14 := by
      calc 2 * Nat.card N' ≤ N'.relIndex (M.T : Subgroup G) * Nat.card N' :=
            Nat.mul_le_mul_right _ h2
        _ = 2 ^ 14 := hmul
    omega
  have heq : ruQ M.T ⊔ M.TF = N' :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [RuChoice.fx_card_Q_sup_TF M]; exact hcard)
  have hnN' : n ∈ N' := Subgroup.mem_inf.mpr ⟨hnT, hn⟩
  rw [← heq] at hnN'
  have hle2 : ruQ M.T ⊔ M.TF ≤ Subgroup.normalizer (M.F1 : Set G) :=
    sup_le (RuChoice.fx_Q_le_normalizer_F1 M) (M.TF_le_F1.trans Subgroup.le_normalizer)
  exact hle2 hnN'

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_core {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {X : Subgroup G} {t₀ : G} (ht₀ : t₀ ∈ (M.T : Subgroup G))
    (hX : CFSG.ASVolI.ChIJK.IsSylowIn 3 X M.G2)
    (hN : CFSG.conjugate M.TF t₀ ≤ Subgroup.normalizer ((X ⊔ M.Agrp : Subgroup G) : Set G)) :
    ∃ s ∈ (M.T : Subgroup G), X = CFSG.conjugate (Subgroup.zpowers M.x2el) s ∧
      CFSG.conjugate M.TF s = CFSG.conjugate M.TF t₀ ∧
      CFSG.conjugate M.F1 s = CFSG.conjugate M.F1 t₀ := by
  obtain ⟨s, hsT, hXs⟩ := RuChoice.fx_exists_conj M hX
  have hAs : CFSG.conjugate M.Agrp s = M.Agrp :=
    RuChoice.fx_conjugate_eq_self (M.G2_le_normalizer_Agrp (M.T_le_G2 hsT))
  have hXA : X ⊔ M.Agrp = CFSG.conjugate M.XA s := by
    rw [hXs, RuChoice.fx_conjugate_sup, hAs]
  rw [hXA, RuChoice.fx_normalizer_conjugate] at hN
  have h1 := RuChoice.fx_conjugate_mono s⁻¹ hN
  rw [RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_conjugate, mul_inv_cancel,
    RuChoice.fx_conjugate_one] at h1
  have hw : t₀ * s⁻¹ ∈ (M.T : Subgroup G) := mul_mem ht₀ (inv_mem hsT)
  have h2 : CFSG.conjugate M.TF (t₀ * s⁻¹) ≤
      (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) :=
    le_inf (RuChoice.fx_conjugate_le M.TF_le_T hw) h1
  rw [RuChoice.fx_inf_normalizer_XA] at h2
  have h3 : CFSG.conjugate M.TF (t₀ * s⁻¹) = M.TF :=
    Subgroup.eq_of_le_of_card_ge h2 (RuChoice.fx_card_conjugate _ _).ge
  have hwN : t₀ * s⁻¹ ∈ Subgroup.normalizer (M.TF : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← RuChoice.fx_mem_conjugate, h3]
  have hwF1 : t₀ * s⁻¹ ∈ Subgroup.normalizer (M.F1 : Set G) :=
    RuChoice.fx_normalizer_TF_le M hw hwN
  have hs : s = (t₀ * s⁻¹)⁻¹ * t₀ := by group
  refine ⟨s, hsT, hXs, ?_, ?_⟩
  · rw [hs, ← RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_eq_self (inv_mem hwN)]
  · rw [hs, ← RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_eq_self (inv_mem hwF1)]

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.F {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 X : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t)
    (hX : IsSylowIn 3 X (G2Ru M.L V2 (M.T : Subgroup G))) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a)
    (hQ : Q5Ru (M.T : Subgroup G) B5 ≤
      Subgroup.normalizer ((X ⊔ ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a : Subgroup G) : Set G)) :
    ∃ y : G, y ∈ (M.T : Subgroup G) ∧
      TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF y ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 y ∧
      F2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate M.F2 y ∧
      FRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate (M.F1 ⊔ M.F2) y := by
  obtain ⟨hG2, -, -⟩ := RuChoice.frame M hV2
  have hAeq := RuChoice.A M hV2 ht hB ha
  obtain ⟨hTF, hF1⟩ := RuChoice.TF_F1 M hV2 ht hB ha
  have hX' : IsSylowIn 3 X M.G2 := by
    rw [← hG2]
    exact hX
  have hN : CFSG.conjugate M.TF t ≤ Subgroup.normalizer ((X ⊔ M.Agrp : Subgroup G) : Set G) := by
    rw [← hTF, ← hAeq]
    exact sup_le (le_sup_right.trans Subgroup.le_normalizer) hQ
  obtain ⟨s, hsT, hXs, hTFs, hF1s⟩ := RuChoice.fx_core M ht hX' hN
  have hTFeq : TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF s := by
    rw [hTF, hTFs]
  have hF1eq : F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 s := by
    rw [hF1, hF1s]
  have hF2eq : F2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate M.F2 s := by
    unfold F2Ru
    rw [hTFeq, hXs, ← RuChoice.fx_conjugate_sup]
  refine ⟨s, hsT, hTFeq, hF1eq, hF2eq, ?_⟩
  unfold FRu
  rw [hF1eq, hF2eq, ← RuChoice.fx_conjugate_sup]


end RuChoiceSec


section BurnsideJ7_fold


open CFSG.Quasithin.RuType in
@[expose] def burnsideJ7_E (s x : SigmaL2F4) : Prop :=
  x ≠ 1 ∧ x ^ 5 = 1 ∧ s * x * s⁻¹ = x⁻¹

open CFSG.Quasithin.RuType in
instance burnsideJ7_E_decidable (s : SigmaL2F4) : DecidablePred (burnsideJ7_E s) := fun x =>
  inferInstanceAs (Decidable (x ≠ 1 ∧ x ^ 5 = 1 ∧ s * x * s⁻¹ = x⁻¹))


end BurnsideJ7_fold

section


end


section


end


section BurnsideJ8b


section MLevel


end MLevel

section TFixes


end TFixes

section J45Lemmas


section


end

section J45M


end J45M

section J45Main


end J45Main

end J45Lemmas

end BurnsideJ8b

section


end


section


end


section


end


section BurnsideJ9b


section


end

end BurnsideJ9b

section


end

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups


section BurnsideJ48

section BurnsideJ48Basic


end BurnsideJ48Basic

section BurnsideJ48LS


end BurnsideJ48LS

section BurnsideJ48Final


end BurnsideJ48Final

end BurnsideJ48

section


end


end CFSG.ASVolI
