
module

public import Certificates.Kernel.J4Count.FixCEEltBase

public import Certificates.Kernel.J4Count.FixCEChecks
public import Certificates.Kernel.J4Count.SuborbBase1
public import Certificates.Kernel.J4Q.QT2AC
public import Certificates.Kernel.J4Q.C4025
public import CFSG.Certificates.Kernel.J4FixCESound
public import Certificates.Kernel.J4Count.StarsBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.E1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.Quasithin.J4M2 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KS.SporSch.C11 MulAction CertificateChecks.KernelJ4Q
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply)
open CFSG.Sporadic.J4Schreier (app11)


theorem PR_gE_q {n : ℕ} (hn : n < 12) : PR (gE n) (getN one QAs n) := by
  have h := qR_enc hn
  refine PR_of h ?_
  rw [gE, genWord, if_pos hn, Mx_el5 matFacts]
  rfl

theorem PR_gE_a : PR (gE 12) YA := by
  refine PR_of ya_enc ?_
  rw [gE, genWord, if_neg (by norm_num), if_pos rfl, Mx_el5 matFacts]

theorem PR_gE_b : PR (gE 13) YB := by
  refine PR_of yb_enc ?_
  rw [gE, genWord, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, Mx_el5 matFacts]

theorem Mx_el5_pow (w : List ℤ) (e : ℕ) : Mx (el5 (powWord w e)) = rowsMatrix (powRows (wR w) e) := by
  rw [el5_powWord, map_pow, Mx_el5 matFacts, rowsMatrix_powRows]

theorem PR_gE_5 : PR (gE 14) YP5 := by
  refine PR_of y5_enc ?_
  rw [gE, genWord, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl, Mx_el5_pow]
  rfl

theorem PR_gE_7 : PR (gE 15) YP7 := by
  refine PR_of y7_enc ?_
  rw [gE, genWord, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_pos rfl, Mx_el5_pow]
  rfl

theorem PR_gE_11 : PR (gE 16) YP11 := by
  refine PR_of y11_enc ?_
  rw [gE, genWord, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, Mx_el5_pow]
  rfl

theorem PR_uJ {j : ℕ} (hj : j < 11) : PR (uJ j) (getN one UL j) := by
  have h := uTab_enc j hj
  refine PR_of ⟨h.1, h.2.trans ?_⟩ (Mx_uJ matFacts hj)
  interval_cases j <;> rfl

theorem PR_eta (m : ℕ) : PR (eta uJ 11 m) (etaK c rm one UL m) :=
  PR_of (eta_enc m) (Mx_eta matFacts 11 le_rfl m)

theorem PR_kJ {i : ℕ} (hi : i < 4) : PR (kJ i) (getN one mkKMs i) := by
  have h := kRows_enc hi
  rw [← kTab_get hi] at h
  exact PR_of h (Mx_kJ matFacts hi)

theorem PR_gE {n : ℕ} (hn : n < 32) : PR (gE n) (getN one GL32 n) := by
  rcases Nat.lt_or_ge n 12 with h | h
  · have e : getN one GL32 n = getN one QAs n := by interval_cases n <;> rfl
    rw [e]
    exact PR_gE_q h
  rcases Nat.lt_or_ge n 17 with h' | h'
  · interval_cases n
    · exact PR_gE_a
    · exact PR_gE_b
    · exact PR_gE_5
    · exact PR_gE_7
    · exact PR_gE_11
  rcases Nat.lt_or_ge n 28 with h'' | h''
  · obtain ⟨j, rfl⟩ : ∃ j, n = 17 + j := ⟨n - 17, by omega⟩
    have hj : j < 11 := by omega
    have e : getN one GL32 (17 + j) = getN one UL j := by
      interval_cases j <;> rfl
    rw [e, gE_u hj]
    exact PR_uJ hj
  · obtain ⟨i, rfl⟩ : ∃ i, n = 28 + i := ⟨n - 28, by omega⟩
    have hi : i < 4 := by omega
    have e : getN one GL32 (28 + i) = getN one mkKMs i := by
      interval_cases i <;> rfl
    rw [e, gE_k hi]
    exact PR_kJ hi

theorem PR_prod : ∀ (w : List ℕ), (∀ n ∈ w, n < 32) → ∀ (g : J) (x : ℕ), PR g x →
    PR (w.foldl (fun acc n => acc * gE n) g) (prodK c rm one GL32 w x)
  | [], _, _, _, h => h
  | n :: w, hw, g, x, h => by
    rw [List.foldl_cons]
    have h1 := PR_mul h (PR_gE (hw n List.mem_cons_self))
    change PR _ (CFSG.KC.Enum.strictN (mulJ c rm x (getN one GL32 n)) (prodK c rm one GL32 w))
    rw [CFSG.KC.J4FixC.sN]
    exact PR_prod w (fun m hm => hw m (List.mem_cons_of_mem _ hm)) _ _ h1

theorem PR_gw {w : List ℕ} (hw : ∀ n ∈ w, n < 32) : PR (gw w) (prodK c rm one GL32 w one) :=
  PR_prod w hw 1 one PR_one

theorem PR_cE : PR cE CMD := by
  have ha := PR_gE_a
  have hb := PR_gE_b
  have e : cE = gE 12 * gE 13 * gE 12 * gE 12 * gE 13 * gE 13 := by
    rw [cE, commutatorElement_def, inv_eq_sq ha a3, inv_eq_sq hb b3]
    group
  rw [e, ← Nat.eq_of_beq_eq_true cm_ok]
  exact PR_mul (PR_mul (PR_mul (PR_mul (PR_mul ha hb) ha) ha) hb) hb

theorem cE_smul_v : cE • CFSG.Sporadic.J4Schreier.v = CFSG.Sporadic.J4Schreier.v :=
  fix_of_PR PR_cE rootBits_lt (Nat.eq_of_beq_eq_true root_fix)

theorem cE_pow_three' : cE ^ 3 = 1 := PR_eq_of_beq (PR_pow PR_cE 3) PR_one c3

section H

end H

section E

theorem cE_conj_uJ {j : ℕ} (hj : j < 11) : cE * uJ j * cE⁻¹ = eta uJ 11 CC[j]! := by
  have h := CFSG.KS.allN_spec cols_ok j hj
  have e := PR_eq_of_beq (PR_mul PR_cE (PR_uJ hj)) (PR_mul (PR_eta (colK PC j)) PR_cE) h
  rw [CC_get hj, e, mul_inv_cancel_right]

theorem cE_conj_eta (a : ℕ) : cE * eta uJ 11 a * cE⁻¹ = eta uJ 11 (app11 CC a) := by
  have hf : ∀ x y, eta uJ 11 (x ^^^ y) = eta uJ 11 x * eta uJ 11 y :=
    fun x y => eta_xor (elem_uJ matFacts) le_rfl x y
  rw [← CFSG.Sporadic.J4Schreier.prod_bits_eq (eta uJ 11) hf CC a, eta_ofFn]
  have h := map_list_prod (MulAut.conj cE)
    (List.ofFn fun j : Fin 11 => if a.testBit j then uJ j else 1)
  rw [MulAut.conj_apply, List.map_ofFn] at h
  rw [h]
  refine congrArg List.prod (List.ofFn_inj.2 (funext fun j => ?_))
  simp only [Function.comp_apply]
  split_ifs
  · rw [MulAut.conj_apply]
    exact cE_conj_uJ j.isLt
  · exact map_one _

theorem card_cent_E : Nat.card ↥(Eg uJ 11 ⊓ Subgroup.centralizer ({cE} : Set J)) = 32 := by
  classical
  have hM := matFacts
  have hlt : ∀ a, app11 CC a < 2 ^ 11 := fun a => by
    rw [CC, app_eq]
    exact CFSG.KC.J4FixC.appK_lt' _ _
  have hmem : ∀ a, a < 2048 →
      (eta uJ 11 a ∈ Subgroup.centralizer ({cE} : Set J) ↔ app11 CC a = a) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have e : cE * eta uJ 11 a * cE⁻¹ = eta uJ 11 a := by rw [← h1, mul_inv_cancel_right]
      rw [cE_conj_eta] at e
      exact eta_inj hM _ (hlt a) _ (by omega) e
    · intro h
      have e := cE_conj_eta a
      rw [h] at e
      calc eta uJ 11 a * cE = cE * eta uJ 11 a * cE⁻¹ * cE := by rw [e]
        _ = cE * eta uJ 11 a := by group
  let f : {a // a ∈ (Finset.range 2048).filter fun a => app11 CC a = a} →
      ↥(Eg uJ 11 ⊓ Subgroup.centralizer ({cE} : Set J)) := fun a =>
    ⟨eta uJ 11 a.1, eta_mem_Eg 11 le_rfl _,
      (hmem a.1 (Finset.mem_range.1 (Finset.mem_filter.1 a.2).1)).2 (Finset.mem_filter.1 a.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' := Subtype.ext_iff.1 h
      dsimp only [f] at h'
      exact Subtype.ext (eta_inj hM _ (by simpa using (Finset.mem_filter.1 ha).1) _
        (by simpa using (Finset.mem_filter.1 hb).1) h')
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (Subgroup.mem_inf.1 hn).1
      exact ⟨⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, (hmem a ha).1 (Subgroup.mem_inf.1 hn).2⟩⟩,
        rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]
  have h := fix_sound cnt_ok
  rw [← CC, CFSG.Sporadic.J4Schreier.fixCount] at h
  exact h


end E

section Final

end Final

end CertificateChecks.KernelJ4Count.FixCE

end
