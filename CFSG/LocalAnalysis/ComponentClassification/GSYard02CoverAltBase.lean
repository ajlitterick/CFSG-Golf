
module

public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
public import Certificates.Data.CFSGNative.GSYard02Spin
public import CFSG.Sporadic.Schreier.J4SSylowBase

@[expose] public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup

@[expose] def treeAux {G : Type*} [Mul G] [One G] (gs : List G) : List G → List (ℕ × ℕ) → List G
  | acc, [] => acc
  | acc, (p, g) :: tr => treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr

@[expose] def treeTab {G : Type*} [Mul G] [One G] (gs : List G) (tr : List (ℕ × ℕ)) : List G :=
  treeAux gs [1] tr

private theorem getD_mem_of {α : Type*} [One α] {P : α → Prop} (h1 : P 1) :
    ∀ (l : List α) (n : ℕ), (∀ y ∈ l, P y) → P (l.getD n 1)
  | [], _, _ => h1
  | x :: _, 0, h => by
    rw [List.getD_cons_zero]
    exact h x (List.mem_cons.mpr (Or.inl rfl))
  | _ :: xs, n + 1, h => by
    rw [List.getD_cons_succ]
    exact getD_mem_of h1 xs n fun y hy => h y (List.mem_cons.mpr (Or.inr hy))

private theorem treeAux_mem_of_mem {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    ∀ (acc : List G) (y : G), y ∈ acc → y ∈ treeAux gs acc tr := by
  induction tr with
  | nil => intro acc y hy; exact hy
  | cons pg tr ih =>
    intro acc y hy
    obtain ⟨p, g⟩ := pg
    show y ∈ treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr
    exact ih _ y (List.mem_append.mpr (Or.inl hy))

private theorem treeAux_mem_closure {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    ∀ (acc : List G), (∀ y ∈ acc, y ∈ Subgroup.closure {g | g ∈ gs}) →
      ∀ y ∈ treeAux gs acc tr, y ∈ Subgroup.closure {g | g ∈ gs} := by
  induction tr with
  | nil => intro acc h y hy; exact h y hy
  | cons pg tr ih =>
    intro acc h
    obtain ⟨p, g⟩ := pg
    show ∀ y ∈ treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr,
      y ∈ Subgroup.closure {g | g ∈ gs}
    apply ih
    intro y hy
    rcases List.mem_append.mp hy with hy' | hy'
    · exact h y hy'
    · rw [List.mem_singleton.mp hy']
      have hgen : ∀ z ∈ gs, z ∈ Subgroup.closure {g | g ∈ gs} := fun z hz =>
        Subgroup.subset_closure (show z ∈ {g | g ∈ gs} from hz)
      exact mul_mem
        (getD_mem_of (P := fun z => z ∈ Subgroup.closure {g | g ∈ gs}) (one_mem _) gs g hgen)
        (getD_mem_of (P := fun z => z ∈ Subgroup.closure {g | g ∈ gs}) (one_mem _) acc p h)

private theorem one_mem_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    (1 : G) ∈ treeTab gs tr :=
  treeAux_mem_of_mem gs tr [1] 1 (List.mem_singleton.mpr rfl)

private theorem closure_le_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) (x : G)
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) : x ∈ treeTab gs tr := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact one_mem_treeTab gs tr
  | mul_left g hg y _ ih => exact hcl y ih g hg
  | inv_mul_cancel g hg y _ ih => exact hcl y ih g⁻¹ (hinv g hg)

theorem mem_closure_iff_mem_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs) (hnd : (treeTab gs tr).Nodup)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ x ∈ treeTab gs tr :=
  ⟨closure_le_treeTab gs tr hinv hcl x, fun hx =>
    treeAux_mem_closure gs tr [1] (fun y hy => by
      rw [List.mem_singleton.mp hy]
      exact one_mem _) x hx⟩

theorem card_closure_eq_length_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs) (hnd : (treeTab gs tr).Nodup)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = (treeTab gs tr).length := by
  classical
  have hset : ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G) =
      ↑(treeTab gs tr).toFinset := by
    ext y
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_setOf_eq]
    exact mem_closure_iff_mem_treeTab gs tr hinv hnd hcl y
  have h1 : Nat.card (Subgroup.closure {g | g ∈ gs}) =
      ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

private def pairTree : List (ℕ × ℕ) := [(0, 0), (0, 1), (2, 0)]

theorem isKleinFour_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsKleinFour (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) = 4 := by
  have hA : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hB : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have hba : b * a = a * b := hab.symm
  have hab1 : a * b ≠ 1 := fun h => hne (mul_left_cancel (h.trans ha.symm)).symm
  have h1a : (1 : G) ≠ a := fun h => ha1 h.symm
  have h1b : (1 : G) ≠ b := fun h => hb1 h.symm
  have h1ab : (1 : G) ≠ a * b := fun h => hab1 h.symm
  have haab : a ≠ a * b := fun h => hb1 (mul_left_cancel ((mul_one a).trans h)).symm
  have hbab : b ≠ a * b := fun h => ha1 (mul_right_cancel ((one_mul b).trans h)).symm
  have hinv : ∀ g ∈ [a, b], g⁻¹ ∈ [a, b] := by
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · rw [h, inv_eq_of_mul_eq_one_right ha]
      simp
    · rw [List.mem_singleton.mp h, inv_eq_of_mul_eq_one_right hb]
      simp
  have hL : treeTab [a, b] pairTree = [1, a, b, a * b] := by
    simp [pairTree, treeTab, treeAux]
  have hnd : (treeTab [a, b] pairTree).Nodup := by
    rw [hL]
    simp [h1a, h1b, h1ab, ha1, hb1, hne, hne.symm, hab1, haab, hbab]
  have hcl : ∀ x ∈ treeTab [a, b] pairTree, ∀ g ∈ [a, b],
      g * x ∈ treeTab [a, b] pairTree := by
    rw [hL]
    intro x hx g hg
    simp at hx hg
    rcases hx with h | h | h | h <;> rcases hg with h' | h' <;> rw [h, h'] <;>
      simp [hA, hB, hba, ha, hb]
  have hset : ({g | g ∈ [a, b]} : Set G) = {a, b} := by
    ext g
    simp
  have hcardT := card_closure_eq_length_treeTab [a, b] pairTree hinv hnd hcl
  rw [hset, hL] at hcardT
  have h4 : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := hcardT.trans (by simp)
  have hmem : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x hx
    rw [← hset] at hx
    have hx' := (mem_closure_iff_mem_treeTab [a, b] pairTree hinv hnd hcl x).mp hx
    rw [hL] at hx'
    simpa using hx'
  have h2 : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 2 = 1 := by
    intro x hx
    rcases hmem x hx with h | h | h | h
    · rw [h]
      exact one_pow 2
    · rw [h, sq]
      exact ha
    · rw [h, sq]
      exact hb
    · rw [h, sq, mul_assoc, hB]
      exact ha
  exact ⟨FooteLit.isKleinFour_of_card_eq_four h4 h2, h4⟩

theorem exists_pair_of_isKleinFour {G : Type*} [Group G] (Y : Subgroup G) (hY : IsKleinFour Y) :
    ∃ a b : G, a ∈ Y ∧ b ∈ Y ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      Y = Subgroup.closure {a, b} := by
  have hY2 : ∀ x ∈ Y, x ^ 2 = 1 := fun x hx => FooteLit.sq_eq_one_of_isKleinFour hY hx
  have hsq : ∀ x ∈ Y, x * x = 1 := fun x hx => by
    have h := hY2 x hx
    rwa [sq] at h
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
    FooteLit.commute_of_sq_eq_one hY2 hx hy
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY.card_four]; norm_num)
  have hYcard : (Y : Set G).ncard = 4 :=
    (Nat.card_coe_set_eq (Y : Set G)).symm.trans hY.card_four
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ Y, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Y : Set G) ⊆ ({1} : Set G) := fun x hx =>
      Set.mem_singleton_iff.mpr (hcon x hx)
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton, hYcard] at h1
    omega
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ Y, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Y : Set G) ⊆ ({1, a} : Set G) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [Set.mem_insert_iff]
        exact Or.inl hx1
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (hcon x hx hx1)
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair (show (1 : G) ≠ a from fun h => ha1 h.symm), hYcard] at h1
    omega
  have hbb : b * b = 1 := hsq b hb
  have hab : a * b = b * a := hcomm a ha b hb
  have hne : a ≠ b := fun h => hba h.symm
  have hcl := (isKleinFour_closure_pair (hsq a ha) hbb hab ha1 hb1 hne).2
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact ha
    · rw [Set.mem_singleton_iff.mp h]
      exact hb
  have hEq : Subgroup.closure ({a, b} : Set G) = Y :=
    Subgroup.eq_of_le_of_card_ge hle (hY.card_four.trans hcl.symm).le
  exact ⟨a, b, ha, hb, hsq a ha, hbb, hab, ha1, hb1, hne, hEq.symm⟩


end CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.Alternating.Multipliers.Spin
open SpinNative (Wd Q4 invW wordsOK)
open CFSG.Alternating.Multipliers CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup
open scoped commutatorElement

section Model

variable {m : ℕ}

theorem exists_negE (hm : 2 ≤ m) : ∃ x : E (m + 2), ((x : H (m + 2)) : monomial (m + 2)) = negOne := by
  set p₀ : Fin (m + 2) := ⟨0, by omega⟩
  set p₁ : Fin (m + 2) := ⟨1, by omega⟩
  set p₂ : Fin (m + 2) := ⟨2, by omega⟩
  set p₃ : Fin (m + 2) := ⟨3, by omega⟩
  have h01 : p₀ ≠ p₁ := by simp [p₀, p₁]
  have h02 : p₀ ≠ p₂ := by simp [p₀, p₂, Fin.ext_iff]
  have h03 : p₀ ≠ p₃ := by simp [p₀, p₃, Fin.ext_iff]
  have h12 : p₁ ≠ p₂ := by simp [p₁, p₂, Fin.ext_iff]
  have h13 : p₁ ≠ p₃ := by simp [p₁, p₃, Fin.ext_iff]
  have h23 : p₂ ≠ p₃ := by simp [p₂, p₃, Fin.ext_iff]
  set x : H (m + 2) := ⟨dd h01 h23, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set y : H (m + 2) := ⟨dd h02 h13, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  exact ⟨⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩,
    commutator_dd h01 h02 h03 h12 h13 h23⟩

@[expose] noncomputable def negE (hm : 2 ≤ m) : E (m + 2) := (exists_negE (m := m) hm).choose

theorem coe_negE (hm : 2 ≤ m) :
    ((negE hm : H (m + 2)) : monomial (m + 2)) = negOne :=
  (exists_negE (m := m) hm).choose_spec

theorem psi_negE (hm : 2 ≤ m) : psi (negE hm) = 1 := by
  apply Subtype.ext
  change perm ((negE hm : H (m + 2)) : monomial (m + 2)) = 1
  rw [coe_negE, perm_negOne]

theorem negE_ne_one (hm : 2 ≤ m) : negE hm ≠ 1 := by
  intro h
  have := coe_negE (m := m) hm
  rw [h] at this
  exact negOne_ne_one (by rw [← this]; rfl)

end Model

section Model2

variable {m : ℕ}

theorem card_ker_psi_le (hm : 6 ≤ m) :
    Finite (psi (m := m)).ker ∧ Nat.card (psi (m := m)).ker ≤ 2 := by
  have hK : (psi (m := m)).ker ≤ center (E (m + 2)) := ker_psi_le_center
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have hperf : Group.IsPerfect (E (m + 2)) := E_isPerfect (by omega)
  have hAperf : Group.IsPerfect (alternatingGroup (Fin (m + 2))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  haveI : Finite (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier hAperf
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift (psi (m := m)) hψ hK
  have hcardM : Nat.card (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_hopfMultiplier_alternatingGroup (by omega)
  let g : RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2))) →
      (psi (m := m)).ker := fun x =>
    ⟨RankThree.PerfectCover.hopfLift (psi (m := m)) hψ hK x.1, by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ x.2⟩
  have hg : Function.Surjective g := by
    intro y
    have hy : (y : E (m + 2)) ∈ (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))).map
        (RankThree.PerfectCover.hopfLift (psi (m := m)) hψ hK) := by
      rw [hmap]; exact y.2
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  haveI : Finite (psi (m := m)).ker := Finite.of_surjective g hg
  refine ⟨inferInstance, ?_⟩
  have := Nat.card_le_card_of_surjective g hg
  omega

theorem card_ker_psi (hm : 6 ≤ m) : Nat.card (psi (m := m)).ker = 2 := by
  obtain ⟨hfin, hle⟩ := card_ker_psi_le hm
  haveI := hfin
  have hne : (psi (m := m)).ker ≠ ⊥ := by
    intro h
    have hmem : negE (m := m) (by omega) ∈ (psi (m := m)).ker := by
      rw [MonoidHom.mem_ker]; exact psi_negE _
    rw [h, Subgroup.mem_bot] at hmem
    exact negE_ne_one _ hmem
  have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  omega

theorem negOne_mul_negOne : (negOne : monomial (m + 2)) * negOne = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [negOne]

theorem negE_sq (hm : 2 ≤ m) : negE (m := m) hm * negE (m := m) hm = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  rw [coe_negE]
  exact negOne_mul_negOne

theorem ker_psi_eq (hm : 6 ≤ m) (x : E (m + 2)) (hx : psi x = 1) :
    x = 1 ∨ x = negE (m := m) (by omega) := by
  obtain ⟨hfin, _⟩ := card_ker_psi_le hm
  haveI := hfin
  set g := negE (m := m) (by omega) with hg
  have hle : Subgroup.closure {g} ≤ (psi (m := m)).ker := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact MonoidHom.mem_ker.mpr (psi_negE _)
  have hgsq : g ^ 2 = 1 := by rw [sq]; exact negE_sq _
  have hgne : g ≠ 1 := negE_ne_one _
  have hord : orderOf g = 2 := orderOf_eq_prime hgsq hgne
  have hcl : Nat.card (Subgroup.closure {g}) = 2 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, hord]
  have hkeq : (psi (m := m)).ker = Subgroup.closure {g} := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    exact le_of_eq (by rw [card_ker_psi hm, hcl])
  have hxmem : x ∈ Subgroup.closure {g} := by rw [← hkeq]; exact MonoidHom.mem_ker.mpr hx
  obtain ⟨k, hk⟩ := Subgroup.mem_closure_singleton.mp hxmem
  rw [← hk]
  have hmod : g ^ k = g ^ (k % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf g k, hord]; simp
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [hmod, h0, zpow_zero]
  · right; rw [hmod, h1, zpow_one]

end Model2

section Model3

variable {m : ℕ}

theorem center_E_eq (hm : 6 ≤ m) : center (E (m + 2)) = (psi (m := m)).ker := by
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
    have hc : psi z ∈ center (alternatingGroup (Fin (m + 2))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hψ g
      have h := congrArg psi ((Subgroup.mem_center_iff.mp hz) y)
      simp only [map_mul] at h
      exact h
    rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
    simpa using hc
  · exact ker_psi_le_center

theorem finite_E (hm : 6 ≤ m) : Finite (E (m + 2)) := by
  obtain ⟨hfin, _⟩ := card_ker_psi_le hm
  haveI := hfin
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have e := QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) hψ
  haveI : Finite (E (m + 2) ⧸ (psi (m := m)).ker) := Finite.of_equiv _ e.toEquiv.symm
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := (psi (m := m)).ker)).symm

theorem alternatingGroup_nonabelian {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin n)).mp this
  simp at h
  omega

noncomputable def quotCenter_iso (hm : 6 ≤ m) :
    E (m + 2) ⧸ center (E (m + 2)) ≃* alternatingGroup (Fin (m + 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (center_E_eq hm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) (psi_surjective (by omega)))

theorem isQuasisimple_E (hm : 6 ≤ m) : IsQuasisimple (E (m + 2)) := by
  refine ⟨E_isPerfect (m := m) (by omega), ?_⟩
  have hA : IsSimpleGroup (alternatingGroup (Fin (m + 2))) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  haveI := hA
  obtain ⟨a₀, b₀, hab₀⟩ := alternatingGroup_nonabelian (n := m + 2) (by omega)
  haveI : Nontrivial (alternatingGroup (Fin (m + 2))) :=
    ⟨⟨a₀, b₀, fun h => hab₀ (by rw [h])⟩⟩
  have e := quotCenter_iso hm
  haveI : Nontrivial (E (m + 2) ⧸ center (E (m + 2))) := e.toEquiv.nontrivial
  refine ⟨IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  exact ⟨e.symm a₀, e.symm b₀, fun h => hab₀ (by have := congrArg e h; simpa using this)⟩

theorem card_center_E (hm : 6 ≤ m) : Nat.card (center (E (m + 2))) = 2 := by
  rw [center_E_eq hm]
  exact card_ker_psi hm

theorem card_E (hm : 6 ≤ m) : Nat.card (E (m + 2)) = (m + 2).factorial := by
  haveI := finite_E hm
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have e := QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) hψ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (psi (m := m)).ker,
    Nat.card_congr e.toEquiv, card_ker_psi hm]
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (m + 2))
  have h3 : Nat.card (Equiv.Perm (Fin (m + 2))) = (m + 2).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  omega

theorem quotCenter_E (hm : 6 ≤ m) :
    Nonempty (E (m + 2) ⧸ center (E (m + 2)) ≃* alternatingGroup (Fin (m + 2))) :=
  ⟨quotCenter_iso hm⟩

end Model3

namespace SpinM

@[expose] def Mdd {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (q : Q4) :
    Matrix (Fin N) (Fin N) ℚ :=
  if q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2 then 1
  else (1 / 2 : ℚ) • ((Γ q.1 - Γ q.2.1) * (Γ q.2.2.1 - Γ q.2.2.2))

@[expose] def Mw {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (w : Wd) :
    Matrix (Fin N) (Fin N) ℚ :=
  (w.map (Mdd Γ)).prod

@[expose] def Mcomm {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (p : Wd × Wd) :
    Matrix (Fin N) (Fin N) ℚ :=
  Mw Γ p.1 * Mw Γ p.2 * Mw Γ (invW p.1) * Mw Γ (invW p.2)

@[expose] def gensM {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (ps : List (Wd × Wd)) :
    List (Matrix (Fin N) (Fin N) ℚ) :=
  ps.map (Mcomm Γ) ++ ps.map fun p => Mcomm Γ (p.2, p.1)

end SpinM

section Bridge

open SpinNative (Mat ent ofF oneM zeroM addM subM smulM mulM prodM gensM closedB
  pairsS10 treeS10)

variable {N : ℕ}


end Bridge

section Clifford

variable {N : ℕ}

@[expose] def GammaRel (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, Γ i * Γ j + Γ j * Γ i = if i = j then (2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) else 0


@[expose] def gammaLin (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (n : ℕ) :
    (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin N) (Fin N) ℚ where
  toFun x := ∑ i : Fin n, x i • Γ i.val
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem sumSq_apply' (n : ℕ) (x : Fin n → ℚ) : sumSq n x = ∑ i, x i * x i := by
  simp [sumSq, QuadraticMap.weightedSumSquares_apply]

theorem gammaLin_mul_self {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n)
    (x : Fin n → ℚ) :
    gammaLin Γ n x * gammaLin Γ n x = algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ) (∑ i : Fin n, x i * x i) := by
  have hrel : ∀ i j : Fin n, Γ i.val * Γ j.val + Γ j.val * Γ i.val =
      if i = j then (2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) else 0 := by
    intro i j
    have := h i.val i.isLt j.val j.isLt
    simpa [Fin.val_inj] using this
  set S := ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • (Γ i.val * Γ j.val) with hSdef
  set T := ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • (Γ j.val * Γ i.val) with hTdef
  have hAA : gammaLin Γ n x * gammaLin Γ n x = S := by
    simp only [gammaLin, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum, hSdef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hsym : S = T := by
    rw [hSdef, hTdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (x j) (x i)]
  have hST : S + T = (∑ i : Fin n, x i * x i) • ((2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ)) := by
    rw [hSdef, hTdef, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j : Fin n, (x i * x j) • (Γ i.val * Γ j.val) + (x i * x j) • (Γ j.val * Γ i.val) =
        if i = j then (x i * x i) • ((2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ)) else 0 := by
      intro j
      rw [← smul_add, hrel i j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq]
    simp
  have hsum2 : (2 : ℚ) • S = (2 : ℚ) • algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ) (∑ i : Fin n, x i * x i) := by
    rw [(two_smul ℚ S).trans (congrArg (S + ·) hsym), hST, Algebra.algebraMap_eq_smul_one, smul_comm]
  rw [hAA]
  exact smul_right_injective (Matrix (Fin N) (Fin N) ℚ) two_ne_zero hsum2

@[expose] def cliffHom {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n) →ₐ[ℚ] Matrix (Fin N) (Fin N) ℚ :=
  CliffordAlgebra.lift (CFSG.Alternating.Multipliers.Spin.sumSq n)
    ⟨gammaLin Γ n, fun x => by rw [sumSq_apply']; exact gammaLin_mul_self h x⟩

theorem cliffHom_v {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) (i : Fin n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.v n i) = Γ i.val := by
  unfold cliffHom CFSG.Alternating.Multipliers.Spin.v
  rw [CliffordAlgebra.lift_ι_apply]
  simp [gammaLin, Pi.single_apply]

theorem cliffHom_algebraMap {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) (c : ℚ) :
    cliffHom h (algebraMap ℚ (CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n)) c) =
      c • (1 : Matrix (Fin N) (Fin N) ℚ) := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

end Clifford

section Rep

variable {N : ℕ}

@[expose] def thetaH {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    H n →* (Matrix (Fin N) (Fin N) ℚ)ˣ :=
  (Units.map (cliffHom h).toMonoidHom).comp ((monomial n).subtype.comp (H n).subtype)

@[expose] def thetaE {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    E n →* (Matrix (Fin N) (Fin N) ℚ)ˣ :=
  (thetaH h).comp (E n).subtype

end Rep

section Injective

variable {N : ℕ} {m : ℕ}


end Injective

section Words

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

abbrev ValidQ (n : ℕ) (q : Q4) : Prop :=
  q.1 < n ∧ q.2.1 < n ∧ q.2.2.1 < n ∧ q.2.2.2 < n ∧ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2

instance (n : ℕ) (q : Q4) : Decidable (ValidQ n q) := by
  unfold ValidQ; infer_instance

@[expose] def ddH (n : ℕ) (q : Q4) : H n :=
  if h : ValidQ n q then
    have hab : (⟨q.1, h.1⟩ : Fin n) ≠ ⟨q.2.1, h.2.1⟩ := fun e => h.2.2.2.2.1 (congrArg Fin.val e)
    have hcd : (⟨q.2.2.1, h.2.2.1⟩ : Fin n) ≠ ⟨q.2.2.2, h.2.2.2.1⟩ :=
      fun e => h.2.2.2.2.2 (congrArg Fin.val e)
    ⟨dd hab hcd, subset_closure ⟨_, _, _, _, hab, hcd, rfl⟩⟩
  else 1

@[expose] def wordH (n : ℕ) (X : Wd) : H n := (X.map (ddH n)).prod

@[expose] def liftE (n : ℕ) (X Y : Wd) : E n :=
  ⟨⁅wordH n X, wordH n Y⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩

@[expose] def gensE (n : ℕ) (ps : List (Wd × Wd)) : List (E n) :=
  ps.map (fun p => liftE n p.1 p.2) ++ ps.map (fun p => liftE n p.2 p.1)

@[expose] def thetaM (h : GammaRel Γ n) : E n →* Matrix (Fin N) (Fin N) ℚ :=
  (Units.coeHom (Matrix (Fin N) (Fin N) ℚ)).comp (thetaE h)


theorem cliffHom_r' (h : GammaRel Γ n) (a b : Fin n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.r a b) = Γ a.val - Γ b.val := by
  unfold CFSG.Alternating.Multipliers.Spin.r
  rw [map_sub, cliffHom_v, cliffHom_v]

theorem cliffHom_half (h : GammaRel Γ n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.half : CliffordAlgebra
      (CFSG.Alternating.Multipliers.Spin.sumSq n)) = (1 / 2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) := by
  unfold CFSG.Alternating.Multipliers.Spin.half
  exact cliffHom_algebraMap h _

theorem thetaH_ddH (h : GammaRel Γ n) (q : Q4) (hq : ValidQ n q) :
    ((thetaH h (ddH n q) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) = Mdd Γ q := by
  have hdd : ((thetaH h (ddH n q) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) =
      cliffHom h (CFSG.Alternating.Multipliers.Spin.half *
        CFSG.Alternating.Multipliers.Spin.r (⟨q.1, hq.1⟩ : Fin n) ⟨q.2.1, hq.2.1⟩ *
        CFSG.Alternating.Multipliers.Spin.r (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ⟨q.2.2.2, hq.2.2.2.1⟩) := by
    unfold ddH
    rw [dif_pos hq]
    rfl
  have hne : ¬ (q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2) := fun h => h.elim hq.2.2.2.2.1 hq.2.2.2.2.2
  have hMdd : SpinM.Mdd Γ q = (1 / 2 : ℚ) • ((Γ q.1 - Γ q.2.1) * (Γ q.2.2.1 - Γ q.2.2.2)) := by
    unfold SpinM.Mdd
    rw [if_neg hne]
  rw [hMdd, hdd, map_mul, map_mul, cliffHom_half, cliffHom_r', cliffHom_r']
  simp only [smul_mul_assoc, one_mul]

end Words

section Words2

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

theorem validQ_swap {q : Q4} (hq : ValidQ n q) : ValidQ n (q.2.2.1, q.2.2.2, q.1, q.2.1) :=
  ⟨hq.2.2.1, hq.2.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.2, hq.2.2.2.2.1⟩

theorem half_dd_dd_swap {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    (CFSG.Alternating.Multipliers.Spin.half * CFSG.Alternating.Multipliers.Spin.r a b *
      CFSG.Alternating.Multipliers.Spin.r c d) *
    (CFSG.Alternating.Multipliers.Spin.half * CFSG.Alternating.Multipliers.Spin.r c d *
      CFSG.Alternating.Multipliers.Spin.r a b) = (1 : CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n)) := by
  open CFSG.Alternating.Multipliers.Spin in
  have hA : r a b * r a b = 2 := r_mul_self hab
  have hB : r c d * r c d = 2 := r_mul_self hcd
  have h2c : r a b * (2 * r a b) = 2 * (r a b * r a b) := by
    rw [← mul_assoc, (Commute.ofNat_right (r a b) 2).eq, mul_assoc]
  have hhh : (half : Cl n) * half = algebraMap ℚ (Cl n) (1 / 4) := by
    rw [half, ← map_mul]; norm_num
  calc (half * r a b * r c d) * (half * r c d * r a b)
      = half * (r a b * (r c d * (half * (r c d * r a b)))) := by simp only [mul_assoc]
    _ = half * (r a b * (r c d * ((r c d * r a b) * half))) := by rw [half_comm (r c d * r a b)]
    _ = half * ((r a b * (r c d * (r c d * r a b))) * half) := by simp only [mul_assoc]
    _ = half * (half * (r a b * (r c d * (r c d * r a b)))) := by
          rw [half_comm (r a b * (r c d * (r c d * r a b)))]
    _ = (half * half) * (r a b * (r c d * (r c d * r a b))) := by rw [mul_assoc]
    _ = (half * half) * (r a b * ((r c d * r c d) * r a b)) := by simp only [mul_assoc]
    _ = (half * half) * (r a b * (2 * r a b)) := by rw [hB]
    _ = (half * half) * (2 * (r a b * r a b)) := by rw [h2c]
    _ = (half * half) * 4 := by rw [hA]; norm_num
    _ = algebraMap ℚ (Cl n) (1 / 4) * 4 := by rw [hhh]
    _ = 1 := by
          rw [← map_ofNat (algebraMap ℚ (Cl n)) 4, ← map_mul]; norm_num

theorem ddH_swap (q : Q4) (hq : ValidQ n q) :
    ddH n (q.2.2.1, q.2.2.2, q.1, q.2.1) = (ddH n q)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  have hq' : ValidQ n (q.2.2.1, q.2.2.2, q.1, q.2.1) := validQ_swap hq
  unfold ddH
  rw [dif_pos hq, dif_pos hq']
  have hab : (⟨q.1, hq.1⟩ : Fin n) ≠ ⟨q.2.1, hq.2.1⟩ := fun e => hq.2.2.2.2.1 (congrArg Fin.val e)
  have hcd : (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ≠ ⟨q.2.2.2, hq.2.2.2.1⟩ :=
    fun e => hq.2.2.2.2.2 (congrArg Fin.val e)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [CFSG.Alternating.Multipliers.Spin.coe_dd] using half_dd_dd_swap hab hcd

theorem invW_cons (q : Q4) (X : Wd) : invW (q :: X) = invW X ++ [(q.2.2.1, q.2.2.2, q.1, q.2.1)] := by
  simp [invW, List.reverse_cons]

theorem wordH_invW (X : Wd) (hX : ∀ q ∈ X, ValidQ n q) : wordH n (invW X) = (wordH n X)⁻¹ := by
  induction X with
  | nil => simp [invW, wordH]
  | cons q X ih =>
    have hq : ValidQ n q := hX q List.mem_cons_self
    have ih' := ih (fun q' hq' => hX q' (List.mem_cons_of_mem _ hq'))
    have hw : wordH n (q :: X) = ddH n q * wordH n X := by simp [wordH]
    have hinv : wordH n (invW (q :: X)) =
        wordH n (invW X) * ddH n (q.2.2.1, q.2.2.2, q.1, q.2.1) := by
      rw [invW_cons]; simp [wordH]
    rw [hinv, ih', ddH_swap q hq, hw, mul_inv_rev]

theorem thetaH_wordH (h : GammaRel Γ n) (X : Wd) (hX : ∀ q ∈ X, ValidQ n q) :
    ((thetaH h (wordH n X) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) = Mw Γ X := by
  induction X with
  | nil => simp [wordH, Mw, thetaH]
  | cons q X ih =>
    have hq : ValidQ n q := hX q List.mem_cons_self
    have ih' := ih (fun q' hq' => hX q' (List.mem_cons_of_mem _ hq'))
    simp only [wordH, List.map_cons, List.prod_cons, Mw] at ih' ⊢
    rw [map_mul, Units.val_mul, thetaH_ddH h q hq]
    rw [ih']

theorem thetaE_liftE (h : GammaRel Γ n) (X Y : Wd) (hX : ∀ q ∈ X, ValidQ n q)
    (hY : ∀ q ∈ Y, ValidQ n q) :
    ((thetaE h (liftE n X Y) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) =
      Mcomm Γ (X, Y) := by
  have hc : thetaE h (liftE n X Y) =
      ⁅thetaH h (wordH n X), thetaH h (wordH n Y)⁆ := by
    rw [thetaE, MonoidHom.comp_apply]
    show thetaH h ⁅wordH n X, wordH n Y⁆ = _
    rw [map_commutatorElement]
  have hX' : ∀ q ∈ invW X, ValidQ n q := by
    intro q hq
    simp only [invW, List.mem_map, List.mem_reverse] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact validQ_swap (hX q' hq')
  have hY' : ∀ q ∈ invW Y, ValidQ n q := by
    intro q hq
    simp only [invW, List.mem_map, List.mem_reverse] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact validQ_swap (hY q' hq')
  rw [hc, commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  have e1 : ((thetaH h (wordH n X))⁻¹ : (Matrix (Fin N) (Fin N) ℚ)ˣ) = thetaH h (wordH n (invW X)) := by
    rw [wordH_invW X hX, map_inv]
  have e2 : ((thetaH h (wordH n Y))⁻¹ : (Matrix (Fin N) (Fin N) ℚ)ˣ) = thetaH h (wordH n (invW Y)) := by
    rw [wordH_invW Y hY, map_inv]
  rw [e1, e2, thetaH_wordH h X hX, thetaH_wordH h Y hY, thetaH_wordH h _ hX', thetaH_wordH h _ hY']
  rfl

end Words2

section Transfer

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

theorem thetaM_liftE (h : GammaRel Γ n) (X Y : Wd) (hX : ∀ q ∈ X, ValidQ n q)
    (hY : ∀ q ∈ Y, ValidQ n q) : thetaM h (liftE n X Y) = Mcomm Γ (X, Y) := by
  unfold thetaM
  rw [MonoidHom.comp_apply, Units.coeHom_apply]
  exact thetaE_liftE h X Y hX hY

theorem liftE_inv (X Y : Wd) : (liftE n X Y)⁻¹ = liftE n Y X := by
  apply Subtype.ext
  change ⁅wordH n X, wordH n Y⁆⁻¹ = ⁅wordH n Y, wordH n X⁆
  rw [commutatorElement_inv]


end Transfer

section Checks

open SpinNative


end Checks

section Normal

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ}


end Normal

section NormalCase

variable {N : ℕ}


end NormalCase

section KleinCase

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ}

theorem commute_closure_of_gens {G : Type*} [Group G] (S T : Set G)
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have hs : ∀ s ∈ S, ∀ y ∈ Subgroup.closure T, s * y = y * s := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact h s hs t ht
    | one => simp
    | mul y₁ y₂ _ _ ih₁ ih₂ => rw [← mul_assoc, ih₁, mul_assoc, ih₂, mul_assoc]
    | inv y₁ _ ih => exact ((show Commute s y₁ from ih).inv_right).eq
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem s hs' => exact hs s hs' y hy
  | one => simp
  | mul x₁ x₂ _ _ ih₁ ih₂ => rw [mul_assoc, ih₂, ← mul_assoc, ih₁, mul_assoc]
  | inv x₁ _ ih => exact ((show Commute x₁ y from ih).inv_left).eq

theorem le_centralizer_closure {G : Type*} [Group G] (S T : Set G)
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_closure_of_gens S T h x hx y hy).symm


end KleinCase


theorem le_centralizer_pair {G : Type} [Group G] {a b c d : G}
    (h1 : a * c = c * a) (h2 : a * d = d * a) (h3 : b * c = c * b) (h4 : b * d = d * b) :
    Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
  refine le_centralizer_closure _ _ ?_
  intro s hs t ht
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem reflTransGen_chain {G : Type} [Group G] (L : ℕ) (K : ℕ → Subgroup G) (par : ℕ → ℕ)
    (hedge : ∀ idx, idx < L → idx ≠ 0 → par idx < idx ∧ CommFourAdj G (K idx) (K (par idx))) :
    ∀ idx, idx < L → Relation.ReflTransGen (CommFourAdj G) (K idx) (K 0) := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | _ idx ih =>
    intro hidx
    by_cases h0 : idx = 0
    · subst h0
      exact Relation.ReflTransGen.refl
    · obtain ⟨hpar, hadj⟩ := hedge idx hidx h0
      exact Relation.ReflTransGen.head hadj (ih (par idx) hpar (lt_trans hpar hidx))

section KleinMain2

variable {N : ℕ}


end KleinMain2

section Final

theorem card_center_of_cover {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hz : center Q ≠ ⊥) (h2 : IsPGroup 2 (center Q)) {n : ℕ} (hn : 5 ≤ n)
    (eQ : Q ⧸ center Q ≃* alternatingGroup (Fin n)) : Nat.card (center Q) = 2 := by
  haveI : Group.IsPerfect Q := hQ.1
  let η : Q →* alternatingGroup (Fin n) := eQ.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hη : Function.Surjective η := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Q := by
    ext x
    simp only [η, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, map_eq_one_iff _ eQ.injective, QuotientGroup.eq_one_iff]
  have hle := alternating_perfect_central_two_kernel_order_at_most_two hn η hη
    (by rw [hker]) (by rw [hker]; exact h2)
  rw [hker] at hle
  have hgt : 1 < Nat.card (center Q) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hz
  omega

theorem card_griess_alt {n : ℕ} (hn : 8 ≤ n) :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin n))) = 2 := by
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess (alternatingGroup (Fin n))).toEquiv]
  exact card_hopfMultiplier_alternatingGroup hn

theorem card_sylow_of_card_two {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 2)
    (P : Sylow 2 G) : Nat.card P = 2 := by
  have h1 := P.card_mul_index
  have h2 : ¬ 2 ∣ P.index := P.not_dvd_index
  rw [hG] at h1
  have hi : P.index ∣ 2 := Dvd.intro_left _ h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with h3 | h3
  · rw [h3, mul_one] at h1; exact h1
  · exact (h2 (by omega)).elim

end Final

section Main

theorem sylowFourJoined_of_cover {Q : Type} [Group Q] [Finite Q] (hquasi : IsQuasisimple Q)
    (hz : center Q ≠ ⊥) (h2 : IsPGroup 2 (center Q)) {m : ℕ} (hm : 6 ≤ m)
    (eQ : Q ⧸ center Q ≃* alternatingGroup (Fin (m + 2)))
    (hSyl : SylowFourJoined (E (m + 2))) : SylowFourJoined Q := by
  have hzQ : Nat.card (center Q) = 2 := card_center_of_cover hquasi hz h2 (by omega) eQ
  have hGr : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_griess_alt (by omega)
  haveI : Finite (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hGr]; norm_num)
  haveI := finite_E hm
  obtain ⟨e⟩ := (RankThree.PerfectCover.hopf_central_cover_consequences
    (alternatingGroup (Fin (m + 2)))).2 (fun S => card_sylow_of_card_two hGr S) Q (E (m + 2))
    hquasi (isQuasisimple_E hm) hzQ (card_center_E hm) ⟨eQ⟩ (quotCenter_E hm)
  exact SylowFourJoined.of_mulEquiv e.symm hSyl


end Main

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
