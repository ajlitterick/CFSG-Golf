module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Monster.Code.LatticeCount
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.H132Irr

public section

open scoped Pointwise

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

abbrev S24 : Type := Equiv.Perm (Fin 24)

abbrev PM24 : Type := G6.PermMod 24

open scoped Classical in
@[expose] noncomputable def eY (Y : Finset (Fin 24)) : PM24 :=
  Multiplicative.ofAdd fun i => if i ∈ Y then 1 else 0

@[expose] def dot24 (u v : PM24) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd u i * Multiplicative.toAdd v i

@[expose] noncomputable def wt24 (v : PM24) : ℕ := Nat.card {i : Fin 24 // Multiplicative.toAdd v i ≠ 0}

abbrev Cocode24 : Type := PM24 ⧸ golayC

abbrev ComplementQuotient24 : Type := PM24 ⧸ Subgroup.zpowers (G6.allOnes 24)

@[expose] noncomputable def cocodeWt24 (coset : Cocode24) : ℕ :=
  sInf {weight : ℕ | ∃ representative : PM24,
    (QuotientGroup.mk representative : Cocode24) = coset ∧ wt24 representative = weight}

@[expose] def HasComplementWeight24 (coset : ComplementQuotient24) (weight : ℕ) : Prop :=
  ∃ representative : PM24,
    (QuotientGroup.mk representative : ComplementQuotient24) = coset ∧
      wt24 representative = weight


theorem sq24 (x : PM24) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change Multiplicative.toAdd x i + Multiplicative.toAdd x i = 0
  generalize Multiplicative.toAdd x i = y
  revert y
  decide


theorem h13_zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem mem_golayC_iff' (x : PM24) : x ∈ golayC ↔ Multiplicative.toAdd x ∈ CFSG.Monster.Code.C :=
  Iff.rfl

theorem toAdd_eY (Y : Finset (Fin 24)) (i : Fin 24) :
    Multiplicative.toAdd (eY Y) i = if i ∈ Y then 1 else 0 := by
  by_cases h : i ∈ Y <;> simp [eY, h]

theorem eY_empty : eY (∅ : Finset (Fin 24)) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [toAdd_eY]


theorem dot24_comm (x y : PM24) : dot24 x y = dot24 y x := by
  unfold dot24
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot24_mul_left (x y z : PM24) : dot24 (x * y) z = dot24 x z + dot24 y z := by
  unfold dot24
  simp only [toAdd_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot24_eY (c : PM24) (S : Finset (Fin 24)) :
    dot24 c (eY S) = ∑ k ∈ S, Multiplicative.toAdd c k := by
  unfold dot24
  simp only [toAdd_eY, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

theorem sum_toAdd_eY (Y : Finset (Fin 24)) :
    ∑ k, Multiplicative.toAdd (eY Y) k = (Y.card : ZMod 2) := by
  simp only [toAdd_eY]
  rw [Finset.sum_boole]
  congr 1
  congr 1
  ext k
  simp


theorem hammingNorm_le_of_support (x : Fin 24 → ZMod 2) (S : Finset (Fin 24))
    (h : ∀ i, x i ≠ 0 → i ∈ S) : hammingNorm x ≤ S.card := by
  unfold hammingNorm
  exact Finset.card_le_card fun i hi => h i (Finset.mem_filter.1 hi).2

theorem eY_mem_golayC_iff (S : Finset (Fin 24)) (hS : S.card < 8) :
    eY S ∈ golayC ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hne0 : Multiplicative.toAdd (eY S) ≠ 0 := by
      intro h0
      apply hne
      ext i
      have h1 := congrFun h0 i
      by_cases hi : i ∈ S
      · simp [toAdd_eY, hi] at h1
      · simp [hi]
    have h8 := CFSG.Monster.Code.eight_le_wt ((mem_golayC_iff' _).1 h) hne0
    have hle := hammingNorm_le_of_support (Multiplicative.toAdd (eY S)) S (fun i hi => by
      by_contra hiS
      apply hi
      simp [toAdd_eY, hiS])
    omega
  · rintro rfl
    rw [eY_empty]
    exact Subgroup.one_mem _

theorem eY_mul_eY_mem_golayC_iff (S T : Finset (Fin 24)) (hST : S.card + T.card < 8) :
    eY S * eY T ∈ golayC ↔ S = T := by
  constructor
  · intro h
    by_contra hne
    have hne0 : Multiplicative.toAdd (eY S * eY T) ≠ 0 := by
      intro h0
      apply hne
      ext i
      have h1 := congrFun h0 i
      simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Pi.zero_apply] at h1
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT] at h1 ⊢
    have h8 := CFSG.Monster.Code.eight_le_wt ((mem_golayC_iff' _).1 h) hne0
    have hle := hammingNorm_le_of_support (Multiplicative.toAdd (eY S * eY T)) (S ∪ T) (fun i hi => by
      by_contra hiST
      apply hi
      simp only [Finset.mem_union, not_or] at hiST
      simp [toAdd_eY, hiST.1, hiST.2])
    have hu := Finset.card_union_le S T
    omega
  · rintro rfl
    rw [sq24]
    exact Subgroup.one_mem _

theorem permAct_eY (σ : Equiv.Perm (Fin 24)) (S : Finset (Fin 24)) :
    G6.permAct 24 σ (eY S) = eY (S.map σ.toEmbedding) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [G6.permAct_apply, toAdd_eY, Finset.mem_map_equiv, Equiv.Perm.inv_def]

theorem smul_finset_eq_map (g : Equiv.Perm (Fin 24)) (S : Finset (Fin 24)) :
    g • S = S.map g.toEmbedding := by
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_map_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩


@[expose] def M24g : Subgroup S24 := AutPerm

@[expose] def M23g (a : Fin 24) : Subgroup S24 := M24g ⊓ MulAction.stabilizer S24 a

@[expose] def M22g (a b : Fin 24) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 a ⊓ MulAction.stabilizer S24 b

@[expose] def M2ab (a b : Fin 24) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24))

@[expose] def IsOctad (O : Finset (Fin 24)) : Prop := O.card = 8 ∧ eY O ∈ golayC

@[expose] def IsTrio (Tr : Finset (Finset (Fin 24))) : Prop :=
  Tr.card = 3 ∧ (∀ O ∈ Tr, IsOctad O) ∧
    (∀ O ∈ Tr, ∀ O' ∈ Tr, O ≠ O' → Disjoint O O') ∧ Tr.biUnion id = Finset.univ

@[expose] def IsSextet (S : Finset (Finset (Fin 24))) : Prop :=
  S.card = 6 ∧ (∀ B ∈ S, B.card = 4) ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → Disjoint B B') ∧
    S.biUnion id = Finset.univ ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → IsOctad (B ∪ B'))

@[expose] noncomputable def mathModel (isCode : Bool) (d : ℕ) (a b : Fin 24) (Γ : Subgroup S24) :
    FFModel :=
  FFModel.golaySec Γ
    (if isCode then (if d = 22 then golayC ⊓ pairKer a b else golayC) else G6.coreMod 24)
    (if isCode then Subgroup.zpowers (G6.allOnes 24)
      else (if d = 22 then golayC ⊔ Subgroup.zpowers (pairVec a b) else golayC))

@[expose] noncomputable def IsMathModule {V : Type*} [CommGroup V] (isCode : Bool) (d : ℕ)
    (a b : Fin 24) (Γ : Subgroup S24) (ρ : ↥Γ →* MulAut V) : Prop :=
  ∃ β, RealizesBy (mathModel isCode d a b Γ) ρ.range ⊤ ⊥ ρ.rangeRestrict β

@[expose] def rImg {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (A : Subgroup S24) : Subgroup (MulAut V) :=
  (A.subgroupOf Γ).map ρ

@[expose] def Ld (d : ℕ) (a b : Fin 24) : Subgroup S24 :=
  if d = 24 then M24g else if d = 23 then M23g a else M22g a b

@[expose] def AutLd (d : ℕ) (a b : Fin 24) : Subgroup S24 :=
  if d = 22 then M2ab a b else Ld d a b

@[expose] def IsAbsIrredMod {V : Type*} [CommGroup V] (M : Subgroup (MulAut V)) : Prop :=
  IsIrredOn M ⊤ ∧ ∀ θ : V →* V, (∀ g ∈ M, ∀ v, θ (g v) = g (θ v)) → θ = 1 ∨ θ = MonoidHom.id V

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu


theorem mem_M23g_iff (a : Fin 24) (g : Equiv.Perm (Fin 24)) :
    g ∈ M23g a ↔ g ∈ M24g ∧ g a = a := by
  simp [M23g, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]


@[expose] def H_13_1_partial : Prop :=
  ((∀ g ∈ M24g, ∀ u v : PM24, dot24 (G6.permAct 24 g u) (G6.permAct 24 g v) = dot24 u v) ∧
    (∀ u : PM24, u ≠ 1 → ∃ v : PM24, dot24 u v ≠ 0) ∧
    (∀ v : PM24, v ∈ G6.coreMod 24 ↔ dot24 v (G6.allOnes 24) = 0) ∧
    golayC ≤ G6.coreMod 24 ∧ G6.allOnes 24 ∈ golayC) ∧
  ((∀ u ∈ golayC, ∀ v ∈ golayC, dot24 u v = 0) ∧
    (∀ w : PM24, (∀ c ∈ golayC, dot24 w c = 0) → w ∈ golayC)) ∧
  (rk ↥golayC = 12 ∧ rk ↥(⊤ : Subgroup PM24) - rk ↥golayC = 12 ∧
    rk ↥(G6.coreMod 24) - rk ↥golayC = 11 ∧ rk ↥golayC - rk ↥(Subgroup.zpowers (G6.allOnes 24)) = 11) ∧
  ((∀ c ∈ golayC, c ∉ Subgroup.zpowers (G6.allOnes 24) → ∃ w ∈ G6.coreMod 24, dot24 c w ≠ 0) ∧
    (∀ w ∈ G6.coreMod 24, w ∉ golayC → ∃ c ∈ golayC, dot24 c w ≠ 0)) ∧
  ∀ a b : Fin 24, a ≠ b →
    ((∀ g ∈ M24g, (G6.permAct 24 g (eY {a}) = eY {a} ↔ g a = a) ∧
        (G6.permAct 24 g (eY {a}) * (eY {a})⁻¹ ∈ golayC ↔ g a = a)) ∧
      Nonempty (↥(M23g a) ≃* ↥CFSG.Blueprint.NativeSporadic.M23) ∧
      (∀ g ∈ M24g,
        ((G6.permAct 24 g (eY {a}) = eY {a} ∧ G6.permAct 24 g (eY {b}) = eY {b}) ↔ g ∈ M22g a b) ∧
        ((G6.permAct 24 g (eY {a}) * (eY {a})⁻¹ ∈ golayC ∧
            G6.permAct 24 g (eY {b}) * (eY {b})⁻¹ ∈ golayC) ↔ g ∈ M22g a b)) ∧
      Nonempty (↥(M22g a b) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧
      (∀ g ∈ M24g, (G6.permAct 24 g (eY {a, b}) = eY {a, b} ↔ g ∈ M2ab a b) ∧
        (G6.permAct 24 g (eY {a, b}) * (eY {a, b})⁻¹ ∈ golayC ↔ g ∈ M2ab a b)) ∧
      Nonempty (↥(M2ab a b) ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
    (pairVec a b ∈ G6.coreMod 24 ∧ rk ↥(G6.coreMod 24) - rk ↥(golayC ⊔ Subgroup.zpowers (pairVec a b)) = 10 ∧
      rk ↥(golayC ⊓ pairKer a b) - rk ↥(Subgroup.zpowers (G6.allOnes 24)) = 10 ∧
      (∀ c ∈ golayC ⊓ pairKer a b, c ∉ Subgroup.zpowers (G6.allOnes 24) →
        ∃ w ∈ G6.coreMod 24, dot24 c w ≠ 0) ∧
      (∀ w ∈ G6.coreMod 24, w ∉ golayC ⊔ Subgroup.zpowers (pairVec a b) →
        ∃ c ∈ golayC ⊓ pairKer a b, dot24 c w ≠ 0))

@[expose] def H_13_1 : Prop :=
  H_13_1_partial ∧
  golayC = Subgroup.closure {vector : PM24 |
    ∃ octad : Finset (Fin 24), IsOctad octad ∧ eY octad = vector} ∧
  (∀ support : Finset (Fin 24), wt24 (eY support) = support.card) ∧
  (∀ coset : Cocode24,
    (∃ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset ∧
        wt24 representative = cocodeWt24 coset) ∧
    (∀ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset →
        cocodeWt24 coset ≤ wt24 representative)) ∧
  (∀ representative : PM24, ∀ weight : ℕ,
    HasComplementWeight24 (QuotientGroup.mk representative) weight ↔
      weight = wt24 representative ∨
        weight = wt24 (representative * G6.allOnes 24)) ∧
  (∀ representative : PM24,
    wt24 (representative * G6.allOnes 24) = 24 - wt24 representative) ∧
  (∀ a b : Fin 24, a ≠ b → pairVec a b = eY {a, b}) ∧
  (∀ a b : Fin 24, ∀ representative : PM24,
    representative ∈ pairKer a b ↔ dot24 representative (pairVec a b) = 0)


@[expose] noncomputable def conjOn22 (g : ↥mog22plus) : ↥mog22 ≃* ↥mog22 where
  toFun h := ⟨(g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹,
    mog22_normal_in_plus g.2 h.2⟩
  invFun h := ⟨(g : Equiv.Perm (Fin 24))⁻¹ * h * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹,
    mog22_normal_in_plus (mog22plus.inv_mem g.2) h.2⟩
  left_inv h := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24))⁻¹ * ((g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹)
      * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹ = h
    group)
  right_inv h := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24)) * ((g : Equiv.Perm (Fin 24))⁻¹ * h * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹)
      * (g : Equiv.Perm (Fin 24))⁻¹ = h
    group)
  map_mul' x y := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24)) * ((x : Equiv.Perm (Fin 24)) * (y : Equiv.Perm (Fin 24)))
      * (g : Equiv.Perm (Fin 24))⁻¹ = ((g : Equiv.Perm (Fin 24)) * (x : Equiv.Perm (Fin 24))
      * (g : Equiv.Perm (Fin 24))⁻¹) * ((g : Equiv.Perm (Fin 24)) * (y : Equiv.Perm (Fin 24))
      * (g : Equiv.Perm (Fin 24))⁻¹)
    group)

theorem conjOn22_mul (g k : ↥mog22plus) : conjOn22 (g * k) = conjOn22 g * conjOn22 k := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  show ((g * k : ↥mog22plus) : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) *
      ((g * k : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ =
    (g : Equiv.Perm (Fin 24)) * ((k : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) *
      (k : Equiv.Perm (Fin 24))⁻¹) * (g : Equiv.Perm (Fin 24))⁻¹
  rw [Subgroup.coe_mul]
  group

theorem conjOn22_one : conjOn22 (1 : ↥mog22plus) = 1 := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  show (1 : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) * (1 : Equiv.Perm (Fin 24))⁻¹ = h
  group

@[expose] noncomputable def conjHom22 : ↥mog22plus →* MulAut ↥mog22 where
  toFun g := conjOn22 g
  map_one' := conjOn22_one
  map_mul' g k := conjOn22_mul g k

section H13Cert

theorem conjHom22_injective : Function.Injective conjHom22 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hconj : ∀ h : ↥mog22, (g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹ = h := by
    intro h
    have e : conjOn22 g = 1 := hg
    have h1 : conjOn22 g h = h := by
      rw [e]
      rfl
    exact congrArg Subtype.val h1
  have hcent : rho10 mog22plus le_rfl g ∈
      Subgroup.centralizer ((rho10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (MonoidHom.mem_range).1 hy with ⟨x, rfl⟩
    have hcomm : ((⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ : ↥mog22plus)) * g =
        g * ⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ := by
      apply Subtype.ext
      show (x : Equiv.Perm (Fin 24)) * (g : Equiv.Perm (Fin 24)) =
        (g : Equiv.Perm (Fin 24)) * (x : Equiv.Perm (Fin 24))
      have := hconj x
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hx : rho10 mog22 mog22_le_mog22plus x =
        rho10 mog22plus le_rfl ⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ := rfl
    rw [hx, ← map_mul, ← map_mul, hcomm]
  rw [centralizer_rho10_mog22, Subgroup.mem_bot] at hcent
  exact rho10_mog22plus_injective (by rw [hcent, map_one])

theorem conjHom22_bijective : Function.Bijective conjHom22 := by
  haveI : Finite (MulAut ↥mog22) := finite_mulAut ↥mog22
  apply Function.Injective.bijective_of_nat_card_le conjHom22_injective
  have h1 := CFSG.Sporadic.Schreier.m22_mulAut_card
  rw [CFSG.Sporadic.Schreier.m22_card] at h1
  rw [card_mulAut_congr mog22EquivM22, card_mog22plus]
  omega


end H13Cert

@[expose] def H_13_2 : Prop :=
  ∀ (isCode : Bool) (d : ℕ), (d = 22 ∨ d = 23 ∨ d = 24) → ∀ a b : Fin 24, a ≠ b →
  ∀ (V : Type) [CommGroup V] (ρ : ↥(Ld d a b) →* MulAut V),
    IsMathModule isCode d a b (Ld d a b) ρ →
      Nat.card V = 2 ^ (if d = 22 then 10 else 11) ∧ IsAbsIrredMod ρ.range


section H13Two


end H13Two

end CFSG.ASVolI
