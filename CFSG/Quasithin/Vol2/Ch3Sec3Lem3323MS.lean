module

public import CFSG.Quasithin.Background.S1567V4
public import CFSG.Quasithin.Background.C134L32Corr
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace MS3323

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem le_centralizer_vPlus (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLZ : L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    L ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  have hVZ : vPlus L T ≤ quasithinOmegaOneCenter T := by
    show conjClosure (quasithinOmegaOneCenter T) (conjClosure L T) ≤ _
    rw [show conjClosure L T = L from Hyp331.mPlus_eq_of_le hTL]
    unfold conjClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, z, hz, rfl⟩
    have hzl : l * z = z * l := (Subgroup.mem_centralizer_iff.mp (hLZ hl) z hz).symm
    rw [hzl, mul_inv_cancel_right]
    exact hz
  exact hLZ.trans (Subgroup.centralizer_le hVZ)

theorem false_of_le_center
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hZ : omegaOneCenterOf T ≤ centerOf (L ⊔ T)) : False := by
  apply h.not_L_le_centralizer h38 h39
  refine le_centralizer_vPlus hTL fun l hl => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hZ hz).2 l (Subgroup.mem_sup_left hl)).symm

omit [Finite G] in
theorem inf_centralizer_eq (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G) =
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T := by
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  rw [omegaOneCenterOf_eq]
  apply le_antisymm
  · rintro x ⟨hx, hxZ⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp hx
    have hlZ : l ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      have := Subgroup.mul_mem _ hxZ (Subgroup.inv_mem _ (hTZ ht))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hl, hlZ⟩ ht
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hTZ)

theorem lt_sup
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T < L ⊔ T := by
  set N := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hN
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_inf (hTL ht) (Subgroup.le_normalizer (hTZ ht))
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  refine lt_of_le_of_ne (sup_le_sup_right inf_le_left T) fun heq => ?_
  apply h.not_L_le_centralizer h38 h39
  refine le_centralizer_vPlus hTL ?_
  rw [← CFSG.Quasithin.C2Nine.oTwoUpper_eq_of_perfect h.toSetup331.perfect]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxL, hxo⟩
  have hxH : x ∈ N ⊔ T := heq ▸ Subgroup.mem_sup_left hxL
  obtain ⟨n, hn, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).mp hxH
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hstep : ∀ m : ℕ, ∃ n' ∈ N, (n * t) ^ m = n' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (t ^ m * n * (t ^ m)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTN (T.pow_mem ht m)) n).mp hn
      · rw [pow_succ, e]
        group
  obtain ⟨n', hn', e⟩ := hstep (2 ^ a)
  rw [ha', mul_one] at e
  have hxN : n * t ∈ N := Lem3328.mem_of_pow_odd hxo (by rw [pow_orderOf_eq_one]; exact N.one_mem)
    (e ▸ hn')
  exact hxN.2

theorem not_two_dvd_relIndex (h : Hyp331 G T M L D) :
    ¬ 2 ∣ (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T).relIndex (L ⊔ T) :=
  fun h2 => h.toSetup331.isSylowTwoOf.2.2
    (h2.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_right))


end MS3323

end CFSG.Quasithin.H13
