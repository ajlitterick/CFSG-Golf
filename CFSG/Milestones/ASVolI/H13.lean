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


@[expose] def IsOctad (O : Finset (Fin 24)) : Prop := O.card = 8 ∧ eY O ∈ golayC

@[expose] def IsTrio (Tr : Finset (Finset (Fin 24))) : Prop :=
  Tr.card = 3 ∧ (∀ O ∈ Tr, IsOctad O) ∧
    (∀ O ∈ Tr, ∀ O' ∈ Tr, O ≠ O' → Disjoint O O') ∧ Tr.biUnion id = Finset.univ

@[expose] def IsSextet (S : Finset (Finset (Fin 24))) : Prop :=
  S.card = 6 ∧ (∀ B ∈ S, B.card = 4) ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → Disjoint B B') ∧
    S.biUnion id = Finset.univ ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → IsOctad (B ∪ B'))


end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu


theorem mem_M23g_iff (a : Fin 24) (g : Equiv.Perm (Fin 24)) :
    g ∈ M23g a ↔ g ∈ M24g ∧ g a = a := by
  simp [M23g, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]


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


section H13Two


end H13Two

end CFSG.ASVolI
