module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.FixSet

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false


private theorem pr2_commutes_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Commutes (Subgroup.closure S) (Subgroup.closure T) := by
  have h1 : ∀ s ∈ S, Subgroup.closure T ≤ Subgroup.centralizer {s} := by
    intro s hs
    rw [Subgroup.closure_le]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (h s hs t ht).symm
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 s hs hy)
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hx)) y hy).symm


private theorem pr2_closureG_eq_top : closureG = ⊤ := by
  obtain ⟨hTW, hTstab, -, -, -, -, -, horb, -⟩ := classPkg0Y
  have hlet : ∀ l < 16, letE l ∈ closureG := by
    intro l hl
    unfold letE closureG
    split_ifs with h
    · exact Subgroup.subset_closure ⟨l, h, rfl⟩
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l - 8, by simp only [Set.mem_setOf_eq]; omega, rfl⟩)
  have hT : closureY wT ≤ closureG := by
    rw [closureY, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hok := wordYOK_of_sub wT_sub w hw
    unfold wordYOK at hok
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact hlet l (by simpa using List.all_eq_true.1 hok l hl)
  refine OmGen.eq_top_of_orbit_eq (negSetY t0Y) le_rfl ?_ horb
  rw [← hTstab, ← hTW]
  exact hT

private theorem pr2_phi_mem_Yg (g : HY) : phi g ∈ Om2Facts.Yg := by
  have hws : ∀ w ∈ (List.range 8).map (fun i => [i]), wordYOK w = true := by decide
  have hle : closureG ≤ closureY ((List.range 8).map fun i => [i]) := by
    rw [closureG, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 8 := hk
    have e : wordE [k] = genE k := by simp [wordE, letE, hk']
    rw [SetLike.mem_coe, ← e]
    exact wordE_mem_closureY (List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩)
  have hg : g ∈ closureY ((List.range 8).map fun i => [i]) :=
    hle (by rw [pr2_closureG_eq_top]; exact Subgroup.mem_top g)
  exact (mem_closureY_iff hws).1 hg

private theorem pr2_key {g u : HY} (hu : u = g * t0Y * g⁻¹) (hmem : u ∈ closureY wCR) :
    ∃ x : HY, x * t0Y * x⁻¹ = u ∧
      (x * i0Y * x⁻¹ * i0Y = i0Y * (x * i0Y * x⁻¹) →
        x * i0Y * x⁻¹ * j0Y = j0Y * (x * i0Y * x⁻¹) →
        x * j0Y * x⁻¹ * i0Y = i0Y * (x * j0Y * x⁻¹) →
        x * j0Y * x⁻¹ * j0Y = j0Y * (x * j0Y * x⁻¹) →
        u = t0Y ∨ ∃ k < 3, u = t0Y * cK k) := by
  refine ⟨g, hu.symm, fun _ _ _ _ => ?_⟩
  have hsq : u * u = 1 := by
    rw [hu]
    calc g * t0Y * g⁻¹ * (g * t0Y * g⁻¹) = g * (t0Y * t0Y) * g⁻¹ := by group
      _ = 1 := by rw [t0Y_mul_self, mul_one, mul_inv_cancel]
  have h := Certificates.certificate197003.2.2.2.2.2.1 (phi u)
    ((mem_closureY_iff (wordYOK_of_sub wCR_sub)).1 hmem) (by rw [← map_mul, hsq, map_one])
    ⟨phi g, pr2_phi_mem_Yg g, by rw [hu, map_mul, map_mul, map_inv, phi_t0Y]⟩
  simp only [Om2Facts.Zt4, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · exact Or.inl (phi_injective (h.trans phi_t0Y.symm))
  · exact Or.inr ⟨0, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩
  · exact Or.inr ⟨1, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩
  · exact Or.inr ⟨2, by norm_num, phi_injective (by rw [h, map_mul, phi_t0Y, phi_cK (by norm_num)])⟩

private theorem pr2_conjSub_of_mem_closure {g : HY} (hg : g ∈ closureY wT) :
    conjSub g R0Y = R0Y := by
  rw [closureY] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact conjSub_R0Y_of_mem hw
  | one => exact conjSub_one R0Y
  | mul a b _ _ ha hb => rw [conjSub_mul, hb, ha]
  | inv a _ ha =>
    calc conjSub a⁻¹ R0Y = conjSub a⁻¹ (conjSub a R0Y) := by rw [ha]
      _ = R0Y := conjSub_inv_conjSub a R0Y

theorem normalizer_R0Y (hR : IsUniqueInvolution R0Y t0Y) (g : HY) :
    conjSub g R0Y = R0Y ↔ g ∈ T0Y := by
  constructor
  · intro h
    have h1 := hR.conj_eq h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t0Y = g * t0Y * g⁻¹ * g := by group
      _ = t0Y * g := by rw [h1]
  · intro hg
    exact pr2_conjSub_of_mem_closure (by rw [classPkg0Y.1]; exact hg)

private theorem pr2_i0_mem : i0Y ∈ R0Y :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem pr2_j0_mem : j0Y ∈ R0Y :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem pr2_eq_iff (hR : IsUniqueInvolution R0Y t0Y) {a b : HY} :
    conjSub a R0Y = conjSub b R0Y ↔ a * t0Y * a⁻¹ = b * t0Y * b⁻¹ := by
  constructor
  · intro h
    have h1 : conjSub (b⁻¹ * a) R0Y = R0Y := by
      rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h3 := hR.conj_eq h1
    calc a * t0Y * a⁻¹ = b * ((b⁻¹ * a) * t0Y * (b⁻¹ * a)⁻¹) * b⁻¹ := by group
      _ = b * t0Y * b⁻¹ := by rw [h3]
  · intro h
    have h1 : b⁻¹ * a ∈ T0Y := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc b⁻¹ * a * t0Y = b⁻¹ * (a * t0Y * a⁻¹) * a := by group
        _ = b⁻¹ * (b * t0Y * b⁻¹) * a := by rw [h]
        _ = t0Y * (b⁻¹ * a) := by group
    have h2 := (normalizer_R0Y hR _).2 h1
    calc conjSub a R0Y = conjSub b (conjSub (b⁻¹ * a) R0Y) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = conjSub b R0Y := by rw [h2]

private theorem pr2_commutes_fuse0 {m : ℕ} (hm : m < 3) :
    Commutes R0Y (conjSub (fuse0 m) R0Y) := by
  have hlen : m < wFuse0.length := by simpa [wFuse0] using hm
  have hmem : wFuse0.getD m [] ∈ wFuse0 := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  have hok : ∀ w ∈ allWordsY, wordYOK w = true := fun w hw => (wordsCheckY_spec hw).1
  have hc : ∀ a ∈ [wI0, wJ0], ∀ b ∈ [wI0, wJ0],
      fuse0 m * wordE a * (fuse0 m)⁻¹ * wordE b = wordE b * (fuse0 m * wordE a * (fuse0 m)⁻¹) := by
    intro a ha b hb
    have hab : ∀ v ∈ [wI0, wJ0], v ∈ allWordsY := by simp [allWordsY]
    have e := (Certificates.certificate197003.2.2.2.2.2.2 _ hmem a ha b hb).eq
    apply phi_injective
    simp only [map_mul, map_inv]
    rw [phi_wordE (hok _ (hab a ha)), phi_wordE (hok _ (hab b hb)),
      phi_wordE (hok _ (wFuse0_sub _ hmem))]
    exact e
  have e1 := hc wI0 (by simp) wI0 (by simp)
  have e2 := hc wI0 (by simp) wJ0 (by simp)
  have e3 := hc wJ0 (by simp) wI0 (by simp)
  have e4 := hc wJ0 (by simp) wJ0 (by simp)
  rw [conjSub, R0Y, MonoidHom.map_closure]
  apply pr2_commutes_closure
  intro s hs t ht
  obtain ⟨y, hy, rfl⟩ := ht
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hs with rfl | rfl <;> rcases hy with rfl | rfl
  · exact e1.symm
  · exact e3.symm
  · exact e2.symm
  · exact e4.symm

private noncomputable def pr2_f : ℕ → HY
  | 0 => 1
  | k + 1 => fuse0 k

private noncomputable def pr2_w : ℕ → HY
  | 0 => 1
  | k + 1 => cK k

private theorem pr2_f_conj {k : ℕ} (hk : k < 4) : pr2_f k * t0Y * (pr2_f k)⁻¹ = t0Y * pr2_w k := by
  cases k with
  | zero => simp [pr2_f, pr2_w]
  | succ k =>
    simp only [pr2_f, pr2_w]
    exact fuse0_conj (by omega)

private theorem pr2_w_comm (k : ℕ) (x : HY) : x * pr2_w k = pr2_w k * x := by
  cases k with
  | zero => simp [pr2_w]
  | succ k => exact cK_comm k x

private theorem pr2_w_inj {a b : ℕ} (ha : a < 4) (hb : b < 4) (h : pr2_w a = pr2_w b) :
    a = b := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ b => exact absurd h.symm (cK_ne_one (by omega))
  | succ a =>
    cases b with
    | zero => exact absurd h (cK_ne_one (by omega))
    | succ b => exact congrArg Nat.succ (cK_inj (by omega) (by omega) h)

private theorem pr2_prod (a b : ℕ) :
    (t0Y * pr2_w a) * (t0Y * pr2_w b) = pr2_w a * pr2_w b := by
  calc (t0Y * pr2_w a) * (t0Y * pr2_w b) = t0Y * (pr2_w a * t0Y) * pr2_w b := by
        simp only [mul_assoc]
    _ = t0Y * (t0Y * pr2_w a) * pr2_w b := by rw [← pr2_w_comm a t0Y]
    _ = (t0Y * t0Y) * pr2_w a * pr2_w b := by simp only [mul_assoc]
    _ = pr2_w a * pr2_w b := by rw [t0Y_mul_self, one_mul]

private theorem pr2_prod_central (a b : ℕ) (x : HY) :
    x * (pr2_w a * pr2_w b) = (pr2_w a * pr2_w b) * x := by
  calc x * (pr2_w a * pr2_w b) = (x * pr2_w a) * pr2_w b := by rw [mul_assoc]
    _ = (pr2_w a * x) * pr2_w b := by rw [pr2_w_comm a x]
    _ = pr2_w a * (x * pr2_w b) := by rw [mul_assoc]
    _ = pr2_w a * (pr2_w b * x) := by rw [pr2_w_comm b x]
    _ = (pr2_w a * pr2_w b) * x := by rw [mul_assoc]

private theorem pr2_commNbrs (hR : IsUniqueInvolution R0Y t0Y) :
    Twin1711.commNbrs (⊤ : Subgroup HY) R0Y =
      (fun k => conjSub (pr2_f k) R0Y) '' {k | k < 4} := by
  ext J
  constructor
  · rintro ⟨⟨g, -, hgJ⟩, hcase⟩
    subst hgJ
    rcases hcase with h | h
    · exact ⟨0, by norm_num, by simp [pr2_f, h]⟩
    · have hu : g * t0Y * g⁻¹ ∈ conjSub g R0Y := conj_mem_conjSub hR.mem
      have hcI : i0Y * (g * t0Y * g⁻¹) = (g * t0Y * g⁻¹) * i0Y := h _ pr2_i0_mem _ hu
      have hcJ : j0Y * (g * t0Y * g⁻¹) = (g * t0Y * g⁻¹) * j0Y := h _ pr2_j0_mem _ hu
      obtain ⟨x, hx, hmain⟩ := pr2_key (g := g) rfl
        (mem_closureY_wCR_of_comm hcI.symm hcJ.symm)
      have hxg : conjSub x R0Y = conjSub g R0Y := (pr2_eq_iff hR).2 hx
      have hxi : x * i0Y * x⁻¹ ∈ conjSub g R0Y := hxg ▸ conj_mem_conjSub pr2_i0_mem
      have hxj : x * j0Y * x⁻¹ ∈ conjSub g R0Y := hxg ▸ conj_mem_conjSub pr2_j0_mem
      rcases hmain (h _ pr2_i0_mem _ hxi).symm (h _ pr2_j0_mem _ hxi).symm
          (h _ pr2_i0_mem _ hxj).symm (h _ pr2_j0_mem _ hxj).symm with h0 | ⟨k, hk, hk'⟩
      · refine ⟨0, by norm_num, ?_⟩
        show conjSub 1 R0Y = conjSub g R0Y
        rw [pr2_eq_iff hR]
        simpa using h0.symm
      · refine ⟨k + 1, show k + 1 < 4 by omega, ?_⟩
        show conjSub (fuse0 k) R0Y = conjSub g R0Y
        rw [pr2_eq_iff hR, fuse0_conj hk]
        exact hk'.symm
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := hk
    refine ⟨⟨pr2_f k, Subgroup.mem_top _, rfl⟩, ?_⟩
    cases k with
    | zero => exact Or.inl (by simp [pr2_f])
    | succ m => exact Or.inr (pr2_commutes_fuse0 (by omega))

theorem pairing_R0Y (hR : IsUniqueInvolution R0Y t0Y) :
    (Twin1711.commNbrs (⊤ : Subgroup HY) R0Y).ncard = 4 ∧
      ∀ J ∈ Twin1711.commNbrs (⊤ : Subgroup HY) R0Y, ∀ J' ∈ Twin1711.commNbrs (⊤ : Subgroup HY) R0Y,
        J ≠ J' → ∀ u u' : HY, IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ (⊤ : Subgroup HY), x * (u * u') = (u * u') * x := by
  refine ⟨?_, ?_⟩
  · have hinj : Set.InjOn (fun k => conjSub (pr2_f k) R0Y) {k | k < 4} := by
      intro a ha b hb h
      have := (pr2_eq_iff hR).1 h
      rw [pr2_f_conj ha, pr2_f_conj hb] at this
      exact pr2_w_inj ha hb (mul_left_cancel this)
    rw [pr2_commNbrs hR, hinj.ncard_image]
    exact Set.ncard_Iio_nat 4
  · rintro J hJ J' hJ' hne u u' hu hu'
    rw [pr2_commNbrs hR] at hJ hJ'
    obtain ⟨a, ha, rfl⟩ := hJ
    obtain ⟨b, hb, rfl⟩ := hJ'
    have hua : u = t0Y * pr2_w a := (hu.eq (hR.conj (pr2_f a))).trans (pr2_f_conj ha)
    have hub : u' = t0Y * pr2_w b := (hu'.eq (hR.conj (pr2_f b))).trans (pr2_f_conj hb)
    have hab : a ≠ b := fun h => hne (by rw [h])
    refine ⟨?_, fun x _ => ?_⟩
    · rw [hua, hub]
      intro h
      exact hab (pr2_w_inj ha hb (mul_left_cancel h))
    · rw [hua, hub, pr2_prod]
      exact pr2_prod_central a b x

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
