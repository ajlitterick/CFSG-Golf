module

public import CFSG.YGroups.Y443.CentralWord
public import CFSG.YGroups.Y443.EvenPresentation
public import CFSG.YGroups.Y433.Q343

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443ArmLength monsterY443Rels
  MonsterY443Derived)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] noncomputable def y443Gen (c : ℕ) : MonsterY443 := PresentedGroup.of (y443GenOfLetter c)

theorem y443EquivOpen_yGen_eq {c : ℕ} (hc : c < 12) :
    y443EquivOpen (yGen 4 4 3 c) = y443Gen c :=
  y443EquivOpen_yGen hc

theorem y443Gen_letterOfGen (s : MonsterY443Gen) :
    y443Gen (y443LetterOfGen s) = PresentedGroup.of s := by
  rw [y443Gen, y443GenOfLetter_letterOfGen]

theorem y443Gen_mul_self (c : ℕ) : y443Gen c * y443Gen c = 1 :=
  Y443.gen_mul_self _

@[expose] noncomputable def y443Z : MonsterY443 :=
  (y443Gen 0 * y443Gen 9 * y443Gen 10 * y443Gen 11 * y443Gen 1 * y443Gen 2 * y443Gen 5) ^ 9

@[expose] noncomputable def y443F0 : MonsterY443 :=
  (y443Gen 0 * y443Gen 1 * y443Gen 2 * y443Gen 3 * y443Gen 5 * y443Gen 6 * y443Gen 9) ^ 9


theorem y443EquivOpen_zY : y443EquivOpen Y443.zY = y443Z := by
  simp only [Y443.zY, map_pow, map_mul, Nat.ofNat_pos, y443EquivOpen_yGen, Nat.reduceLT,
    Nat.lt_add_one, Nat.one_lt_ofNat, y443Z, y443Gen]

theorem y443EquivOpen_fY : y443EquivOpen Y443.fY = y443F0 := by
  simp only [Y443.fY, map_pow, map_mul, Nat.ofNat_pos, y443EquivOpen_yGen, Nat.one_lt_ofNat,
    Nat.reduceLT, y443F0, y443Gen]


theorem y443Z_mul_self :
    y443Z * y443Z = 1 := by
  rw [← y443EquivOpen_zY, ← map_mul, Y443.zY_mul_self, map_one]


theorem y443Z_central :
    y443Z ∈ Subgroup.center MonsterY443 := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := y443EquivOpen.surjective g
  rw [← y443EquivOpen_zY, ← map_mul, ← map_mul,
    Subgroup.mem_center_iff.1 Y443.zY_central g]

theorem y443Z_comm
    (g : MonsterY443) : g * y443Z = y443Z * g :=
  Subgroup.mem_center_iff.1 y443Z_central g

theorem y443Parity_Z : y443Parity y443Z = Multiplicative.ofAdd 1 := by
  simp only [y443Z, map_pow, map_mul, y443Gen, y443Parity_of]
  decide


theorem y443F0_mul_self :
    y443F0 * y443F0 = 1 := by
  rw [← y443EquivOpen_fY, ← map_mul, Y443.fY_mul_self, map_one]


theorem y443Gen_comm_F0
    {c : ℕ} (hc : c < 12) (hc4 : c ≠ 4) :
    y443Gen c * y443F0 = y443F0 * y443Gen c := by
  rw [← y443EquivOpen_fY, ← y443EquivOpen_yGen_eq hc, ← map_mul, ← map_mul,
    Y443.fY_comm hc hc4]

theorem y443Parity_F0 : y443Parity y443F0 = Multiplicative.ofAdd 1 := by
  simp only [y443F0, map_pow, map_mul, y443Gen, y443Parity_of]
  decide

@[expose] def y443E1 : MonsterY443Gen := some ⟨0, ⟨3, by decide⟩⟩

@[expose] def y443D1 : MonsterY443Gen := some ⟨0, ⟨2, by decide⟩⟩

theorem y443LetterOfGen_E1 : y443LetterOfGen y443E1 = 4 := rfl

theorem y443LetterOfGen_D1 : y443LetterOfGen y443D1 = 3 := rfl

theorem y443LetterOfGen_eq_four_iff {s : MonsterY443Gen} : y443LetterOfGen s = 4 ↔ s = y443E1 := by
  constructor
  · intro h
    have := y443GenOfLetter_letterOfGen s
    rw [h] at this
    exact this.symm
  · rintro rfl
    rfl


@[expose] noncomputable def y443ZHom :
    Multiplicative (ZMod 2) →* MonsterY443 :=
  Y443.z2Hom y443Z y443Z_mul_self

@[simp] theorem y443ZHom_one :
    y443ZHom 1 = 1 := map_one _

@[simp] theorem y443ZHom_ofAdd_one :
    y443ZHom (Multiplicative.ofAdd 1) = y443Z :=
  Y443.z2Hom_ofAdd_one _ _

theorem y443ZHom_comm
    (a : Multiplicative (ZMod 2)) (g : MonsterY443) :
    g * y443ZHom a = y443ZHom a * g := by
  rcases Y443.z2_cases a with rfl | rfl
  · rw [y443ZHom_one, mul_one, one_mul]
  · rw [y443ZHom_ofAdd_one]
    exact y443Z_comm g

theorem y443Parity_ZHom
    (a : Multiplicative (ZMod 2)) : y443Parity (y443ZHom a) = a := by
  rcases Y443.z2_cases a with rfl | rfl
  · rw [y443ZHom_one, map_one]
  · rw [y443ZHom_ofAdd_one, y443Parity_Z]

@[expose] noncomputable def y443PiP :
    MonsterY443 →* MonsterY443 where
  toFun p := p * y443ZHom (y443Parity p)
  map_one' := by
    simp only [map_one, mul_one]
  map_mul' p q := by
    simp only [map_mul]
    calc p * q * (y443ZHom (y443Parity p) * y443ZHom (y443Parity q))
        = p * (q * y443ZHom (y443Parity p)) * y443ZHom (y443Parity q) := by
          simp only [mul_assoc]
      _ = p * (y443ZHom (y443Parity p) * q) * y443ZHom (y443Parity q) := by
          rw [y443ZHom_comm (y443Parity p) q]
      _ = p * y443ZHom (y443Parity p) * (q * y443ZHom (y443Parity q)) := by
          simp only [mul_assoc]

theorem y443PiP_mem
    (p : MonsterY443) : y443PiP p ∈ MonsterY443Derived := by
  rw [y443_mem_derived_iff]
  show y443Parity (p * y443ZHom (y443Parity p)) = 1
  rw [map_mul, y443Parity_ZHom]
  exact Y443.z2_mul_self' _

@[expose] noncomputable def y443Pi :
    MonsterY443 →* MonsterY443Derived :=
  y443PiP.codRestrict MonsterY443Derived y443PiP_mem

theorem y443Pi_coe_apply
    (p : MonsterY443) :
    (y443Pi p : MonsterY443) = p * y443ZHom (y443Parity p) := rfl

theorem y443_of_mul_Z_mem (s : MonsterY443Gen) :
    (PresentedGroup.of s : MonsterY443) * y443Z ∈ MonsterY443Derived := by
  rw [y443_mem_derived_iff, map_mul, y443Parity_of, y443Parity_Z]
  exact Y443.z2_mul_self' _

@[expose] noncomputable def y443T (s : MonsterY443Gen) : MonsterY443Derived :=
  ⟨PresentedGroup.of s * y443Z, y443_of_mul_Z_mem s⟩

@[simp] theorem y443T_coe (s : MonsterY443Gen) :
    (y443T s : MonsterY443) = PresentedGroup.of s * y443Z := rfl

theorem y443Pi_of
    (s : MonsterY443Gen) : y443Pi (PresentedGroup.of s) = y443T s := by
  refine Subtype.ext ?_
  rw [y443Pi_coe_apply, y443Parity_of, y443ZHom_ofAdd_one]
  rfl

theorem y443Pi_coe
    (m : MonsterY443Derived) : y443Pi (m : MonsterY443) = m := by
  refine Subtype.ext ?_
  rw [y443Pi_coe_apply, y443_mem_derived_iff.1 m.2, y443ZHom_one, mul_one]

theorem y443Pi_surjective :
    Function.Surjective y443Pi := fun m => ⟨m, y443Pi_coe m⟩

theorem y443Pi_Z :
    y443Pi y443Z = 1 := by
  refine Subtype.ext ?_
  rw [y443Pi_coe_apply, y443Parity_Z, y443ZHom_ofAdd_one]
  exact y443Z_mul_self


theorem y443T_mul_self
    (s : MonsterY443Gen) : y443T s * y443T s = 1 := by
  refine Subtype.ext ?_
  show (PresentedGroup.of s * y443Z) * (PresentedGroup.of s * y443Z) = 1
  rw [Y443.mul_z_mul_z y443Z_comm y443Z_mul_self]
  exact Y443.gen_mul_self s

theorem y443T_mul_coe
    (s r : MonsterY443Gen) :
    ((y443T s * y443T r : MonsterY443Derived) : MonsterY443) =
      PresentedGroup.of s * PresentedGroup.of r :=
  Y443.mul_z_mul_z y443Z_comm y443Z_mul_self _ _

@[expose] noncomputable def y443X : MonsterY443Derived := y443T y443E1

@[expose] noncomputable def y443Y : MonsterY443Derived := y443T y443D1

@[expose] noncomputable def y443H : Subgroup MonsterY443Derived :=
  Subgroup.closure (y443T '' {s | s ≠ y443E1})

@[expose] noncomputable def y443K : Subgroup MonsterY443Derived :=
  Subgroup.closure (y443T '' {s | s ≠ y443E1 ∧ s ≠ y443D1})

theorem y443T_mem_H {s : MonsterY443Gen} (hs : s ≠ y443E1) : y443T s ∈ y443H :=
  Subgroup.subset_closure ⟨s, hs, rfl⟩

theorem y443T_mem_K {s : MonsterY443Gen} (hs : s ≠ y443E1) (hs' : s ≠ y443D1) :
    y443T s ∈ y443K :=
  Subgroup.subset_closure ⟨s, ⟨hs, hs'⟩, rfl⟩

theorem y443Adj_E1 {s : MonsterY443Gen} (h : MonsterY443Adj y443E1 s) : s = y443D1 := by
  rcases s with _ | ⟨i, ⟨j, hj⟩⟩
  · exact absurd h (by simp only [MonsterY443Adj, y443E1, Fin.isValue, OfNat.ofNat_ne_zero,
      not_false_eq_true])
  · obtain ⟨hi, hj'⟩ := h
    subst hi
    have hj4 : j < 4 := hj
    have hj2 : j = 2 := by
      rcases hj' with h | h
      · exact absurd h (by simp only; omega)
      · simp only at h
        omega
    subst hj2
    rfl

theorem y443T_comm_X
    {s : MonsterY443Gen} (hs : s ≠ y443E1) (hs' : s ≠ y443D1) :
    y443T s * y443X = y443X * y443T s := by
  refine Subtype.ext ?_
  have h1 := y443T_mul_coe s y443E1
  have h2 := y443T_mul_coe y443E1 s
  have hc : Commute (PresentedGroup.of s : MonsterY443) (PresentedGroup.of y443E1) :=
    Y443.gen_commute_of_nonadj hs fun h => hs' (y443Adj_E1 (Y443.adj_symm h))
  show ((y443T s * y443T y443E1 : MonsterY443Derived) : MonsterY443) =
    ((y443T y443E1 * y443T s : MonsterY443Derived) : MonsterY443)
  rw [h1, h2]
  exact hc.eq

theorem y443X_mul_self :
    y443X * y443X = 1 := y443T_mul_self _

theorem y443Y_mul_self :
    y443Y * y443Y = 1 := y443T_mul_self _

theorem y443Y_mem_H : y443Y ∈ y443H :=
  y443T_mem_H (by decide)

theorem y443_xy_cube :
    (y443X * y443Y) ^ 3 = 1 := by
  refine Subtype.ext ?_
  show (((y443T y443E1 * y443T y443D1 : MonsterY443Derived)) : MonsterY443) ^ 3 = 1
  rw [y443T_mul_coe]
  exact Y443.gen_pair_adj (s := y443E1) (t := y443D1) ⟨rfl, Or.inr rfl⟩

theorem y443K_le :

    y443K ≤ y443H ⊓ y443H.map (MulAut.conj y443X).toMonoidHom := by
  rw [y443K, Subgroup.closure_le]
  rintro _ ⟨s, ⟨hs, hs'⟩, rfl⟩
  refine ⟨y443T_mem_H hs, Subgroup.mem_map.2 ⟨y443T s, y443T_mem_H hs, ?_⟩⟩
  have hc := y443T_comm_X hs hs'
  show y443X * y443T s * y443X⁻¹ = y443T s
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

theorem y443K_le_H_and_conj
    {k : MonsterY443Derived} (hk : k ∈ y443K) :
    k ∈ y443H ∧ y443X * k * y443X ∈ y443H := by
  obtain ⟨h1, h2⟩ := y443K_le hk
  refine ⟨h1, ?_⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 h2
  have hxinv : y443X⁻¹ = y443X := inv_eq_of_mul_eq_one_right y443X_mul_self
  show y443X * (y443X * h * y443X⁻¹) * y443X ∈ y443H
  rw [hxinv, ← mul_assoc, ← mul_assoc, y443X_mul_self, one_mul, mul_assoc, y443X_mul_self,
    mul_one]
  exact hh

theorem y443_closure_range_T :
    Subgroup.closure (Set.range y443T) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨p, rfl⟩ := y443Pi_surjective m
  have hp : p ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : MonsterY443Gen → MonsterY443)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  have h := Subgroup.mem_map_of_mem y443Pi hp
  rw [MonoidHom.map_closure, ← Set.range_comp] at h
  have e : (y443Pi ∘ (PresentedGroup.of : MonsterY443Gen → MonsterY443)) = y443T :=
    funext y443Pi_of
  rwa [e] at h


@[expose] noncomputable def y443Tl (c : ℕ) : MonsterY443Derived := y443T (y443GenOfLetter c)

theorem y443Pi_gen
    (c : ℕ) : y443Pi (y443Gen c) = y443Tl c := y443Pi_of _

theorem y443Tl_mul_self
    (c : ℕ) : y443Tl c * y443Tl c = 1 := y443T_mul_self _


theorem y443Tl_pair_pow
    {s t : ℕ} (hst : s < t) (ht : t < 12) :
    (y443Tl s * y443Tl t) ^ pairExp 4 4 3 s t = 1 := by
  have h := Y443.yGen_pair_pow (p := 4) (q := 4) (r := 3) hst (show t < ngen 4 4 3 from ht)
  have h1 := congrArg (fun w => y443Pi (y443EquivOpen w)) h
  simp only [map_pow, map_mul, map_one, y443EquivOpen_yGen_eq (show s < 12 by omega),
    y443EquivOpen_yGen_eq ht, y443Pi_gen] at h1
  exact h1


theorem y443Tl_extra :
    (y443Tl 0 * y443Tl 9 * y443Tl 10 * y443Tl 11 * y443Tl 1 * y443Tl 2 * y443Tl 5) ^ 9 = 1 := by
  have h := y443Pi_Z
  simpa only [y443Z, map_pow, map_mul, y443Pi_gen] using h


theorem y443_F0_mul_Z_mem : y443F0 * y443Z ∈ MonsterY443Derived := by
  rw [y443_mem_derived_iff, map_mul, y443Parity_F0, y443Parity_Z]
  exact Y443.z2_mul_self' _

@[expose] noncomputable def y443C : MonsterY443Derived := ⟨y443F0 * y443Z, y443_F0_mul_Z_mem⟩

@[simp] theorem y443C_coe : (y443C : MonsterY443) = y443F0 * y443Z := rfl

theorem y443Pi_F0 :
    y443Pi y443F0 = y443C := by
  refine Subtype.ext ?_
  rw [y443Pi_coe_apply, y443Parity_F0, y443ZHom_ofAdd_one]
  rfl

theorem y443Tl_mem_H {k : ℕ} (hk : k < 12) (hk4 : k ≠ 4) : y443Tl k ∈ y443H := by
  refine y443T_mem_H fun h => hk4 ?_
  have := congrArg y443LetterOfGen h
  rw [y443LetterOfGen_genOfLetter k hk, y443LetterOfGen_E1] at this
  exact this

theorem y443C_mem_H :
    y443C ∈ y443H := by
  have e : y443C = (y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 *
      y443Tl 9) ^ 9 := by
    rw [← y443Pi_F0, y443F0]
    simp only [map_pow, map_mul, y443Pi_gen]
  rw [e]
  refine Subgroup.pow_mem _ ?_ 9
  refine y443H.mul_mem (y443H.mul_mem (y443H.mul_mem (y443H.mul_mem (y443H.mul_mem
    (y443H.mul_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;>
    exact y443Tl_mem_H (by norm_num) (by norm_num)

theorem y443C_mul_self :
    y443C * y443C = 1 := by
  rw [← y443Pi_F0, ← map_mul, y443F0_mul_self, map_one]

theorem y443C_comm_T
    {s : MonsterY443Gen} (hs : s ≠ y443E1) :
    y443T s * y443C = y443C * y443T s := by
  have hc : (PresentedGroup.of s : MonsterY443) * y443F0 = y443F0 * PresentedGroup.of s := by
    rw [← y443Gen_letterOfGen s]
    exact y443Gen_comm_F0 (y443LetterOfGen_lt s) fun h => hs (y443LetterOfGen_eq_four_iff.1 h)
  rw [← y443Pi_F0, ← y443Pi_of, ← map_mul, ← map_mul, hc]

theorem y443C_comm_H
    {h : MonsterY443Derived} (hh : h ∈ y443H) : h * y443C = y443C * h := by
  have hle : y443H ≤ Subgroup.centralizer {y443C} := by
    rw [y443H, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (y443C_comm_T hs)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)


theorem y443_terminal_central_map
    {G : Type*} [Group G] (f : MonsterY443Derived →* G) :
    (∃ hc : f y443C ∈ y443H.map f,
      (⟨f y443C, hc⟩ : y443H.map f) ∈ Subgroup.center (y443H.map f)) ∧
      f y443C * f y443C = 1 := by
  refine ⟨⟨Subgroup.mem_map_of_mem f y443C_mem_H, ?_⟩, by rw [← map_mul, y443C_mul_self, map_one]⟩
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, h, hh, rfl⟩
  refine Subtype.ext ?_
  show f h * f y443C = f y443C * f h
  rw [← map_mul, ← map_mul, y443C_comm_H hh]

@[expose] noncomputable def y443TlHom :
    YGroup 4 4 3 →* MonsterY443Derived :=
  y443Pi.comp (y443EquivOpen : YGroup 4 4 3 →* MonsterY443)

theorem y443TlHom_yGen
    {c : ℕ} (hc : c < 12) : y443TlHom (yGen 4 4 3 c) = y443Tl c := by
  show y443Pi (y443EquivOpen (yGen 4 4 3 c)) = y443Tl c
  rw [y443EquivOpen_yGen_eq hc, y443Pi_gen]

theorem y443Tl_relators :
    ∀ w ∈ yRels 4 4 3, evalWord y443Tl w = 1 := by
  intro w hw
  have h1 := Relabel.map_evalWord y443TlHom (yGen 4 4 3) w
  rw [evalWord_yGen_of_mem hw, map_one] at h1
  calc evalWord y443Tl w = evalWord (fun c => y443TlHom (yGen 4 4 3 c)) w :=
        evalWord_congr fun c hc =>
          (y443TlHom_yGen (show c < 12 from lt_ngen_of_mem_yRels hw c hc)).symm
    _ = 1 := h1.symm

theorem shiftAt_three_delE1 {c : ℕ} (hc : c ≠ 4) : shiftAt 3 (delE1 c) = c := by
  unfold shiftAt delE1
  split_ifs <;> omega

theorem evalWord_map_letters {G : Type*} [Group G] (g : ℕ → G) (m : ℕ → ℕ) (w : List ℕ) :
    evalWord g (w.map m) = evalWord (fun c => g (m c)) w := by
  unfold evalWord
  rw [List.map_map]
  rfl

theorem y443Tl_Q343_relators :
    ∀ w ∈ yRels 3 4 3, evalWord (fun c => y443Tl (shiftAt 3 c)) w = 1 := by
  intro w hw
  rw [yRels_343_eq] at hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  obtain ⟨hw1, h4⟩ := List.mem_filter.1 hw'
  have h4' : 4 ∉ w' := of_decide_eq_true h4
  rw [evalWord_map_letters]
  rw [← y443Tl_relators w' hw1]
  exact evalWord_congr fun c hc => by
    rw [shiftAt_three_delE1 (fun h => h4' (h ▸ hc))]

theorem y443Tl_Q343_extra :
    evalWord (fun c => y443Tl (shiftAt 3 c)) [0, 8, 9, 10, 1, 2, 4] ^ 9 = 1 := by
  have h := y443Tl_extra
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc, shiftAt] at h ⊢
  exact h

@[expose] noncomputable def y443Q343Hom :
    Q343 →* MonsterY443Derived :=
  Q343.lift (fun c => y443Tl (shiftAt 3 c)) y443Tl_Q343_relators y443Tl_Q343_extra

theorem y443Q343Hom_π
    {c : ℕ} (hc : c < 11) :
    y443Q343Hom (Q343.π (yGen 3 4 3 c)) = y443Tl (shiftAt 3 c) :=
  Q343.lift_π _ _ _ hc

theorem y443Q343Hom_range :
    y443Q343Hom.range = y443H := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := Q343.π_surjective q
    have hu : u ∈ Subgroup.closure (yGen 3 4 3 '' Set.Iio (ngen 3 4 3)) := by
      rw [closure_yGen]
      trivial
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      have hc' : c < 11 := hc
      rw [y443Q343Hom_π hc']
      refine y443Tl_mem_H (by unfold shiftAt; split_ifs <;> omega) ?_
      unfold shiftAt
      split_ifs <;> omega
    | one => rw [map_one, map_one]; exact y443H.one_mem
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact y443H.mul_mem hx hy
    | inv x _ hx => rw [map_inv, map_inv]; exact y443H.inv_mem hx
  · rw [y443H, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨Q343.π (yGen 3 4 3 (delE1 (y443LetterOfGen s))), ?_⟩
    have hl : y443LetterOfGen s < 12 := y443LetterOfGen_lt s
    have hl4 : y443LetterOfGen s ≠ 4 := fun h => hs (y443LetterOfGen_eq_four_iff.1 h)
    have hc : delE1 (y443LetterOfGen s) < 11 := by unfold delE1; split_ifs <;> omega
    show y443Q343Hom (Q343.π (yGen 3 4 3 (delE1 (y443LetterOfGen s)))) = y443T s
    rw [y443Q343Hom_π hc, shiftAt_three_delE1 hl4, y443Tl, y443GenOfLetter_letterOfGen]


end CFSG.YGroups
