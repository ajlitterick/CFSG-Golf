module

public import CFSG.Monster.B.CTIB.Census
public import CFSG.Monster.B.TwoA.Amalgam.CoFiber

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam

theorem rs0_eq :
    rs 0 = xs := by
  show hs 0 * qS 4194304 = xs
  rw [show hs 0 = 1 from rfl, one_mul, show (4194304 : ℕ) = 2 ^ 22 by norm_num, qS_two_pow_22]

theorem rs1_eq :
    rs 1 = qS 1 := by
  show hs 0 * qS 1 = qS 1
  rw [show hs 0 = 1 from rfl, one_mul]

theorem rs2_eq :
    rs 2 = qS 3 := by
  show hs 0 * qS 3 = qS 3
  rw [show hs 0 = 1 from rfl, one_mul]

theorem rs3_eq :
    rs 3 = qS 7 := by
  show hs 0 * qS 7 = qS 7
  rw [show hs 0 = 1 from rfl, one_mul]

theorem census_valid_one : censusValid 1 = true := by decide

theorem psiS_qS_ne_zero
    {r : ℕ} (hr : censusValid r = true) : psiS (qS r) ≠ 0 :=
  vecW_ne_zero hr

theorem qS_ne_one
    {r : ℕ} (hr : censusValid r = true) : qS r ≠ 1 := fun h => by
  apply psiS_qS_ne_zero hr
  rw [h, psiS_one]

theorem xs_ne_one : xs ≠ 1 := fun h => xbar_ne_one (op_injective h)

theorem mem_censusRecs {r : ℕ × ℕ} (hr : r ∈ censusRecs) :
    r = (1, 2300) ∨ r = (3, 46575) ∨ r = (7, 2049300) ∨ r = (17, 1619200) ∨ r = (19, 476928) := by
  simpa [censusRecs] using hr

theorem census_ncard
    (r : ℕ × ℕ) (hr : r ∈ censusRecs) : (jOrbit (qS r.1)).ncard = r.2 :=
  (census_facts hr).2.1

theorem ncard_jOrbit_one :
    (jOrbit (qS 1)).ncard = 2300 := census_ncard (1, 2300) (by decide)
theorem ncard_jOrbit_three :
    (jOrbit (qS 3)).ncard = 46575 := census_ncard (3, 46575) (by decide)
theorem ncard_jOrbit_seven :
    (jOrbit (qS 7)).ncard = 2049300 :=
  census_ncard (7, 2049300) (by decide)
theorem ncard_jOrbit_17 :
    (jOrbit (qS 17)).ncard = 1619200 :=
  census_ncard (17, 1619200) (by decide)
theorem ncard_jOrbit_19 :
    (jOrbit (qS 19)).ncard = 476928 :=
  census_ncard (19, 476928) (by decide)

theorem census_cover'
    {w : WS} (hw : w ≠ 0) :
    w ∈ jOrbit (qS 1) ∨ w ∈ jOrbit (qS 3) ∨ w ∈ jOrbit (qS 7) ∨ w ∈ jOrbit (qS 17) ∨
      w ∈ jOrbit (qS 19) := by
  obtain ⟨r, hr, hw⟩ := census_cover hw
  rcases mem_censusRecs hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl hw))
  · exact .inr (.inr (.inr (.inl hw)))
  · exact .inr (.inr (.inr (.inr hw)))


theorem sq_one_of_mem
    {y : Sbp} (hy : y ∈ Qs)
    (h : psiS y ∈ jOrbit (qS 1) ∪ jOrbit (qS 3) ∪ jOrbit (qS 7)) : y * y = 1 := by
  rcases h with (h | h) | h
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inl rfl)]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inr (.inl rfl))]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_one (.inr (.inr rfl))]

theorem sq_x_of_mem
    {y : Sbp} (hy : y ∈ Qs) (h : psiS y ∈ jOrbit (qS 17) ∪ jOrbit (qS 19)) :
    y * y = xs := by
  rcases h with h | h
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_x (.inl rfl)]
  · rw [sq_eq_of_mem_jOrbit hy (qS_mem _) h, sq_qS_x (.inr rfl)]

theorem ncard_jClass_qS
    {r : ℕ} (hr : censusValid r = true) :
    (jClass (qS r)).ncard = 2 * (jOrbit (qS r)).ncard := by
  rw [jClass_eq_fiber (qS_mem r) (psiS_qS_ne_zero hr), ncard_fiber]

theorem mem_jClass_of
    {t : Sbp} {r : ℕ} (hr : censusValid r = true) (ht : t ∈ Qs)
    (h : psiS t ∈ jOrbit (qS r)) : t ∈ jClass (qS r) := by
  rw [jClass_eq_fiber (qS_mem r) (psiS_qS_ne_zero hr)]
  exact ⟨ht, h⟩

theorem invs_eq :
    {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} =
    jClass (rs 0) ∪ jClass (rs 1) ∪ jClass (rs 2) ∪ jClass (rs 3) := by
  rw [rs0_eq, rs1_eq, rs2_eq, rs3_eq]
  ext t
  constructor
  · rintro ⟨ht, hsq, hne⟩
    by_cases h0 : psiS t = 0
    · rcases eq_of_psiS_eq ht Qs.one_mem (h0.trans psiS_one.symm) with h | h
      · exact absurd h hne
      · rw [mul_one] at h
        subst h
        exact .inl (.inl (.inl (mem_jClass_self xs)))
    · rcases census_cover' h0 with h | h | h | h | h
      · exact .inl (.inl (.inr (mem_jClass_of (by decide) ht h)))
      · exact .inl (.inr (mem_jClass_of (by decide) ht h))
      · exact .inr (mem_jClass_of (by decide) ht h)
      · exact absurd (hsq.symm.trans (sq_x_of_mem ht (.inl h))) xs_ne_one.symm
      · exact absurd (hsq.symm.trans (sq_x_of_mem ht (.inr h))) xs_ne_one.symm
  · have key : ∀ z, z ∈ Qs → z * z = 1 → z ≠ 1 → ∀ t ∈ jClass z, t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1 := by
      rintro z hz hsq hne _ ⟨g, hg, rfl⟩
      refine ⟨conj_mem_Qs hg hz, ?_, fun h => hne ?_⟩
      · calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
          _ = 1 := by rw [hsq]; group
      · calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
    rintro (((h | h) | h) | h)
    · exact key xs xs_mem xs_mul_self xs_ne_one t h
    · exact key _ (qS_mem 1) (sq_qS_one (.inl rfl)) (qS_ne_one (by decide)) t h
    · exact key _ (qS_mem 3) (sq_qS_one (.inr (.inl rfl))) (qS_ne_one (by decide)) t h
    · exact key _ (qS_mem 7) (sq_qS_one (.inr (.inr rfl))) (qS_ne_one (by decide)) t h

theorem ncard_jClass_rs0 :
    (jClass (rs 0)).ncard = 1 := by
  rw [rs0_eq, jClass_xs, Set.ncard_singleton]

theorem ncard_jClass_rs1 :
    (jClass (rs 1)).ncard = 4600 := by
  rw [rs1_eq, ncard_jClass_qS (by decide), ncard_jOrbit_one]

theorem ncard_jClass_rs2 :
    (jClass (rs 2)).ncard = 93150 := by
  rw [rs2_eq, ncard_jClass_qS (by decide), ncard_jOrbit_three]

theorem ncard_jClass_rs3 :
    (jClass (rs 3)).ncard = 4098600 := by
  rw [rs3_eq, ncard_jClass_qS (by decide), ncard_jOrbit_seven]


@[expose] noncomputable def labelS : Sbp := op ((ehatEquiv.symm cE : Ebar) : Cbar)

theorem labelS_mem : labelS ∈ Qs := (ehatEquiv.symm cE).2

theorem iotaD_labelS : iotaD labelS.unop = cQ := by
  show iotaD ((ehatEquiv.symm cE : Ebar) : Cbar) = cQ
  rw [← coe_ehatEquiv, MulEquiv.apply_symm_apply]
  rfl

theorem wv_psiS_labelS :
    wvEquiv hv0 (psiS labelS) = Unitary.sigmaW := by
  rw [psiS_of_mem labelS_mem, ← native_Co2_coset_fiber_data.2.2.2.1,
    ← MulEquiv.apply_symm_apply ehatEquiv cE, psiW_ehatEquiv]
  rfl

theorem image_range_wvEquiv {a b : L2} (h : a = b) (x : Wv a) :
    wvEquiv h '' (Set.range fun k : Kstab a => wAct a k x) =
      Set.range fun k : Kstab b => wAct b k (wvEquiv h x) := by
  subst h
  ext w
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (wvEquiv_wAct rfl k x).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, wvEquiv_wAct rfl k x⟩

theorem ncard_jOrbit_labelS :
    (jOrbit labelS).ncard = 2300 := by
  have himg : wvEquiv hv0 '' jOrbit labelS = Unitary.OmegaW := by
    rw [jOrbit_eq_range labelS_mem, image_range_wvEquiv, wv_psiS_labelS,
      native_Co2_coset_fiber_data.2.2.2.2.1]
    rfl
  rw [← Set.ncard_image_of_injective _ (wvEquiv hv0).injective, himg,
    native_Co2_coset_fiber_data.2.2.2.2.2.1]

theorem psiS_labelS_ne_zero :
    psiS labelS ≠ 0 := by
  intro h0
  have hsub : jOrbit labelS ⊆ {0} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [psiS_conj hg labelS_mem, h0, map_zero]
    rfl
  have := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
  rw [ncard_jOrbit_labelS, Set.ncard_singleton] at this
  omega

theorem labelS_mem_jClass :
    labelS ∈ jClass (qS 1) := by
  have h1 : psiS labelS ∈ jOrbit (qS 1) := by
    rcases census_cover' psiS_labelS_ne_zero with h | h | h | h | h
    · exact h
    all_goals
      have e := congrArg Set.ncard (jOrbit_eq_of_mem (qS_mem _) labelS_mem h)
      rw [ncard_jOrbit_labelS] at e
      first
        | rw [ncard_jOrbit_three] at e | rw [ncard_jOrbit_seven] at e
        | rw [ncard_jOrbit_17] at e | rw [ncard_jOrbit_19] at e
      omega
  exact mem_jClass_of (by decide) labelS_mem h1


theorem range_clabel :
    Set.range clabel = {d | ∃ g : Shat, d = (g : Dfull)⁻¹ * cQ * g} := by
  ext d
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := cvOf_surjective v
    exact ⟨g, clabel_cvOf g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨cvOf g, clabel_cvOf g⟩


end CFSG.Monster.B.CTIB
