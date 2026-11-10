module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggZetaP_pow_self {p m : ℕ} (hpm : p ∣ m) : ggZetaP p m ^ p = 1 := by
  unfold ggZetaP
  rw [← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hpm, ZMod.natCast_self]
  rfl

theorem ggZetaP_orderOf {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m) :
    orderOf (ggZetaP p m) = p := by
  have := Fact.mk hp
  refine orderOf_eq_prime (ggZetaP_pow_self hpm) ?_
  unfold ggZetaP
  rw [Ne, ofAdd_eq_one, ZMod.natCast_eq_zero_iff]
  intro h
  have h1 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpm) hp.pos
  have h2 : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hp.one_lt
  exact absurd (Nat.le_of_dvd h1 h) (not_le.mpr h2)

theorem ggZetaP_exists_pow {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m)
    (u : Multiplicative (ZMod m)) (hu : u ^ p = 1) : ∃ j : ℕ, u = ggZetaP p m ^ j := by
  have : NeZero m := ⟨hm⟩
  set v := Multiplicative.toAdd u with hvdef
  have hv : ((p * v.val : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hvdef, ← toAdd_pow, hu]
    rfl
  rw [ZMod.natCast_eq_zero_iff] at hv
  obtain ⟨q, hq⟩ := hpm
  have hmq : m / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp.pos]
  generalize hval : v.val = t at hv
  rw [hq] at hv
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left hp.pos hv
  refine ⟨j, ?_⟩
  unfold ggZetaP
  rw [hmq, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, mul_comm (j : ℕ), ← hj, ← hval,
    ZMod.natCast_zmod_val]
  rfl

theorem ggTor_alpha_one {m : ℕ} {L' : Type} [Group L'] (T : Subgroup (MulAut L'))
    (f : MulAut L' → Multiplicative (ZMod m)) (h : ∀ x ∈ T, ∀ y ∈ T, f (x * y) = f x * f y) :
    f 1 = 1 := by
  have := h 1 T.one_mem 1 T.one_mem
  rw [mul_one] at this
  simpa using this

def ggTorAlphaHom {m : ℕ} {L' : Type} [Group L'] (T : Subgroup (MulAut L'))
    (f : MulAut L' → Multiplicative (ZMod m)) (h : ∀ x ∈ T, ∀ y ∈ T, f (x * y) = f x * f y) :
    ↥T →* Multiplicative (ZMod m) :=
  MonoidHom.mk' (fun x => f x) (fun x y => h x x.2 y y.2)

theorem ggTor_alpha_pow {m : ℕ} {L' : Type} [Group L'] (T : Subgroup (MulAut L'))
    (f : MulAut L' → Multiplicative (ZMod m)) (h : ∀ x ∈ T, ∀ y ∈ T, f (x * y) = f x * f y)
    (x : MulAut L') (hx : x ∈ T) (n : ℕ) : f (x ^ n) = f x ^ n := by
  have := map_pow (ggTorAlphaHom T f h) ⟨x, hx⟩ n
  exact this


theorem ggZetaP_pow_mod {p m : ℕ} (hpm : p ∣ m) (n : ℕ) :
    ggZetaP p m ^ (n % p) = ggZetaP p m ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, ggZetaP_pow_self hpm, one_pow,
    mul_one]

theorem ggTor_pow_m {m : ℕ} (ζ : Multiplicative (ZMod m)) : ζ ^ m = 1 := by
  rw [← ofAdd_toAdd ζ, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

theorem ggTor_zpow_sum {G : Type} [CommGroup G] (g : G) {ι : Type} (s : Finset ι) (e : ι → ℤ) :
    ∏ k ∈ s, g ^ e k = g ^ (∑ k ∈ s, e k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

def ggTorPsi (p m : ℕ) [NeZero p] (hpm : p ∣ m) :
    Multiplicative (ZMod p) →* Multiplicative (ZMod m) where
  toFun y := ggZetaP p m ^ (Multiplicative.toAdd y).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ggZetaP_pow_mod hpm, pow_add]

theorem ggTorPsi_apply {p m : ℕ} [NeZero p] (hpm : p ∣ m) (y : Multiplicative (ZMod p)) :
    ggTorPsi p m hpm y = ggZetaP p m ^ (Multiplicative.toAdd y).val := rfl

theorem ggTor_iSup_comm {L' : Type} [Group L'] {N m : ℕ}
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    ∀ x ∈ ⨆ k, (cor k).range, ∀ y ∈ ⨆ k, (cor k).range, Commute x y := by
  have h1 : ∀ x ∈ ⨆ k, (cor k).range, ∀ k ζ, Commute x (cor k ζ) := by
    intro x hx
    refine Subgroup.iSup_induction _ hx (C := fun x => ∀ k ζ, Commute x (cor k ζ)) ?_ ?_ ?_
    · rintro i _ ⟨ζ, rfl⟩ k ξ
      exact hcomm i k ζ ξ
    · exact fun _ _ => Commute.one_left _
    · exact fun x y hx hy k ξ => (hx k ξ).mul_left (hy k ξ)
  intro x hx y hy
  refine Subgroup.iSup_induction _ hy (C := fun y => Commute x y) ?_ ?_ ?_
  · rintro i _ ⟨ζ, rfl⟩
    exact h1 x hx i ζ
  · exact Commute.one_right _
  · exact fun y z hy hz => hy.mul_right hz

theorem ggTor_iSup_pow {L' : Type} [Group L'] {N m : ℕ}
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    ∀ x ∈ ⨆ k, (cor k).range, x ^ m = 1 := by
  intro x hx
  suffices x ∈ ⨆ k, (cor k).range ∧ x ^ m = 1 from this.2
  refine Subgroup.iSup_induction _ hx (C := fun x => x ∈ ⨆ k, (cor k).range ∧ x ^ m = 1)
    ?_ ?_ ?_
  · rintro i _ ⟨ζ, rfl⟩
    exact ⟨Subgroup.mem_iSup_of_mem i ⟨ζ, rfl⟩, by rw [← map_pow, ggTor_pow_m, map_one]⟩
  · exact ⟨Subgroup.one_mem _, one_pow _⟩
  · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    rw [(ggTor_iSup_comm cor hcomm x hx y hy).mul_pow, hx', hy', one_mul]

theorem ggTor_multiset_noncommProd {α : Type} [Monoid α] (s : Multiset α) (l : List α)
    (h : s = l) (comm) : s.noncommProd comm = l.prod := by
  subst h
  exact Multiset.noncommProd_coe _ _

noncomputable def ggTorE {p m N : ℕ} [NeZero p] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    (Fin N → Multiplicative (ZMod p)) →* L' :=
  MonoidHom.noncommPiCoprod (fun k => (cor k).comp (ggTorPsi p m hpm))
    (fun i j _ _x _y => hcomm i j _ _)

theorem ggTorE_apply {p m N : ℕ} [NeZero p] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (f : Fin N → Multiplicative (ZMod p)) :
    ggTorE hpm cor hcomm f = (List.ofFn fun k => cor k (ggTorPsi p m hpm (f k))).prod := by
  change Finset.univ.noncommProd (fun i => ((cor i).comp (ggTorPsi p m hpm)) (f i))
    (fun i _ j _ _ => hcomm i j _ _) = _
  unfold Finset.noncommProd
  exact ggTor_multiset_noncommProd (α := L') _ _ (Fin.univ_val_map _) _

theorem ggTorE_mulSingle {p m N : ℕ} [NeZero p] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (k : Fin N) (y : Multiplicative (ZMod p)) :
    ggTorE hpm cor hcomm (Pi.mulSingle k y) = cor k (ggTorPsi p m hpm y) :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem ggTorE_mem {p m N : ℕ} [NeZero p] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (f : Fin N → Multiplicative (ZMod p)) :
    ggTorE hpm cor hcomm f ∈ ⨆ k, (cor k).range := by
  rw [ggTorE_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem ggTorE_mem_closure {p m N : ℕ} [NeZero p] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) (f : Fin N → Multiplicative (ZMod p)) :
    ggTorE hpm cor hcomm f ∈ Subgroup.closure (Set.range fun k => cor k (ggZetaP p m)) := by
  rw [ggTorE_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  rw [ggTorPsi_apply, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self k)) _

theorem ggTor_closure_le_range {p m N : ℕ} [Fact p.Prime] (hpm : p ∣ m) {L' : Type} [Group L']
    (cor : Fin N → Multiplicative (ZMod m) →* L')
    (hcomm : ∀ j k ζ ξ, Commute (cor j ζ) (cor k ξ)) :
    Subgroup.closure (Set.range fun k => cor k (ggZetaP p m)) ≤
      (ggTorE hpm cor hcomm).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨Pi.mulSingle k (Multiplicative.ofAdd 1), ?_⟩
  rw [ggTorE_mulSingle, ggTorPsi_apply, toAdd_ofAdd, ZMod.val_one, pow_one]

theorem ggTor_ker {p m N : ℕ} {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hm0 : m ≠ 0) (hpm : p ∣ m)
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ))
    (f : Fin N → Multiplicative (ZMod p))
    (hf : haveI : NeZero p := ⟨hp.ne_zero⟩; MulAut.conj (ggTorE hpm w.cor hcomm f) = 1) :
    ∀ j, ∑ k, (C j k : ZMod p) * Multiplicative.toAdd (f k) = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨-, -, hcorT, hαmul, -, -, -, hpair, -⟩ := hw
  intro j
  have hmem : ∀ g, MulAut.conj (ggTorE hpm w.cor hcomm g) ∈ w.T := by
    intro g
    have h1 : ⨆ k, (w.cor k).range ≤ w.T.comap (MulAut.conj : L' →* MulAut L') :=
      iSup_le fun k => by
        rintro _ ⟨ζ, rfl⟩
        exact hcorT k ζ
    exact h1 (ggTorE_mem hpm w.cor hcomm g)
  let β : (Fin N → Multiplicative (ZMod p)) →* Multiplicative (ZMod m) :=
    (ggTorAlphaHom w.T (w.α j) (hαmul j)).comp
      (((MulAut.conj : L' →* MulAut L').comp (ggTorE hpm w.cor hcomm)).codRestrict w.T hmem)
  have hβ : ∀ g, β g = w.α j (MulAut.conj (ggTorE hpm w.cor hcomm g)) := fun g => rfl
  have hβs : ∀ k y, β (Pi.mulSingle k y) =
      ggZetaP p m ^ ((Multiplicative.toAdd y).val * C j k) := by
    intro k y
    rw [hβ, ggTorE_mulSingle, hpair, ggTorPsi_apply, ← zpow_natCast, ← zpow_mul]
  have h1 : β f = 1 := by
    rw [hβ, hf]
    exact ggTor_alpha_one w.T (w.α j) (hαmul j)
  rw [← Finset.univ_prod_mulSingle f, map_prod] at h1
  simp only [hβs] at h1
  rw [ggTor_zpow_sum, ← orderOf_dvd_iff_zpow_eq_one, ggZetaP_orderOf hp hm0 hpm,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  simpa [ZMod.natCast_zmod_val, mul_comm] using h1

theorem GGTorusTorWit.weylElt {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (w : GGTorusTorWit m N L' A)
    (hw : w.Holds C M) (hA : IsElemAbelian p A) (k : Fin N) :
    GGTorusWeylElt p A (w.n k) := by
  obtain ⟨-, hAT, -, hαmul, -, -, hfix, -, -, hWelt, -⟩ := hw
  intro a ha
  have haT := hAT ha
  rw [hWelt k a haT]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [inv_pow, ← map_pow, ← ggTor_alpha_pow w.T (w.α k) (hαmul k) a haT, hA.2 a ha,
      ggTor_alpha_one w.T (w.α k) (hαmul k), map_one, inv_one]
  · rw [map_inv, hfix a' (hAT ha')]


theorem GGTorusTorWit.mem_cor_of_conj_mem {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Odd m)
    (hpm : p ∣ m) (w : GGTorusTorWit m N L' A) (hw : w.Holds C M) (b : L')
    (hb : b ^ p = 1) (hbA : MulAut.conj b ∈ A) : b ∈ ⨆ k, (w.cor k).range := by
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -, -, -, hinner, hoddZ, ⟨-, -, htor⟩, -⟩ := hw
  obtain ⟨t, ht, hbt⟩ := hinner _ hbA ⟨b, rfl⟩
  have hz : t⁻¹ * b ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut L' => φ g) hbt
    simp only [MulAut.conj_apply] at h
    calc g * (t⁻¹ * b) = t⁻¹ * (t * g * t⁻¹) * b := by group
    _ = t⁻¹ * (b * g * b⁻¹) * b := by rw [h]
    _ = t⁻¹ * b * g := by group
  have htm : t ^ m = 1 := ggTor_iSup_pow w.cor hcomm t ht
  have hcomm_tz : Commute t (t⁻¹ * b) := Subgroup.mem_center_iff.mp hz t
  have hb' : t * (t⁻¹ * b) = b := by group
  have hbm : b ^ m = 1 := by
    obtain ⟨c, rfl⟩ := hpm
    rw [pow_mul, hb, one_pow]
  have hzm : (t⁻¹ * b) ^ m = 1 := by
    have h := hcomm_tz.mul_pow m
    rw [hb', hbm, htm, one_mul] at h
    exact h.symm
  have hzpm : (t⁻¹ * b) ^ (p * m) = 1 := by rw [mul_comm, pow_mul, hzm, one_pow]
  have hodd : Odd (orderOf (t⁻¹ * b)) :=
    Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hp.odd_of_ne_two hp2, hm⟩) (orderOf_dvd_of_pow_eq_one hzpm)
  rw [← hb']
  exact Subgroup.mul_mem _ ht (htor _ (hoddZ _ hz hodd) hzm)


theorem GGTorusTorWit.pairing {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hm : Odd m) (hpm : p ∣ m)
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M) (hA : IsElemAbelian p A) :
    ∃ αb : Fin N → ↥A → ZMod p,
      (∀ k (a : ↥A), w.α k a = ggZetaP p m ^ (αb k a).val) ∧
      (∀ i j (hj : MulAut.conj (w.cor j (ggZetaP p m)) ∈ A), αb i ⟨_, hj⟩ = (C i j : ZMod p)) ∧
      (∀ k (a : ↥A), ((ggConjAut A (w.hn k) a : ↥A) : MulAut L') =
        a * (MulAut.conj (w.cor k (ggZetaP p m)) ^ (αb k a).val)⁻¹) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨-, hAT, -, hαmul, -, -, -, hpair, hWaut, -⟩ := hw
  let αb : Fin N → ↥A → ZMod p := fun k a =>
    if h : ∃ j : ℕ, w.α k a = ggZetaP p m ^ j then (h.choose : ZMod p) else 0
  have hroot : ∀ k (a : ↥A), w.α k a = ggZetaP p m ^ (αb k a).val := by
    intro k a
    have hex : ∃ j : ℕ, w.α k a = ggZetaP p m ^ j :=
      ggZetaP_exists_pow hp hm0 hpm _
        (by rw [← ggTor_alpha_pow _ _ (hαmul k) _ (hAT a.2), hA.2 _ a.2,
          ggTor_alpha_one _ _ (hαmul k)])
    simp only [αb, dif_pos hex]
    rw [ZMod.val_natCast, ggZetaP_pow_mod hpm]
    exact hex.choose_spec
  refine ⟨αb, hroot, fun i j hj => ?_, fun k a => ?_⟩
  · have h1 : w.α i (MulAut.conj (w.cor j (ggZetaP p m))) =
        ggZetaP p m ^ (αb i ⟨_, hj⟩).val := hroot i ⟨_, hj⟩
    rw [hpair i j, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ggZetaP_orderOf hp hm0 hpm,
      ← ZMod.intCast_eq_intCast_iff] at h1
    rw [h1, Int.cast_natCast, ZMod.natCast_zmod_val]
  · rw [ggConjAut_apply, hWaut k a (hAT a.2), hroot k a, map_pow, map_pow]

theorem GGTorusTorWit.coroot_indep_of_ker_zero {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hm : Odd m)
    (hpm : p ∣ m) (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hC0 : ∀ c : Fin N → ZMod p, (∀ j, ∑ k, (C j k : ZMod p) * c k = 0) → c = 0) :
    ∀ c : Fin N → ZMod p, (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 →
      c = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro c hc
  have hcomm := hw.2.2.2.2.2.1
  have hE : ggTorE hpm w.cor hcomm (fun k => Multiplicative.ofAdd (c k)) = 1 := by
    rw [ggTorE_apply]
    exact hc
  exact hC0 c (ggTor_ker hp hm.pos.ne' hpm w hw hcomm (fun k => Multiplicative.ofAdd (c k))
    (by rw [hE, map_one]))


theorem GGTorusTorWit.coroot_indep_of_center {p m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp : p.Prime) (hm : Odd m)
    (hpm : p ∣ m) (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hC1 : ∀ c d : Fin N → ZMod p, (∀ j, ∑ k, (C j k : ZMod p) * c k = 0) →
      (∀ j, ∑ k, (C j k : ZMod p) * d k = 0) → c ≠ 0 → ∃ l : ZMod p, d = l • c)
    (x : L') (hxZ : x ∈ Subgroup.center L') (hxo : orderOf x = p)
    (hxs : x ∈ Subgroup.closure (Set.range fun k => w.cor k (ggZetaP p m))) :
    ∀ c : Fin N → ZMod p, (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 →
      c = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro c hc
  have hcomm := hw.2.2.2.2.2.1
  have hE : ggTorE hpm w.cor hcomm (fun k => Multiplicative.ofAdd (c k)) = 1 := by
    rw [ggTorE_apply]
    exact hc
  have hcK := ggTor_ker hp hm.pos.ne' hpm w hw hcomm (fun k => Multiplicative.ofAdd (c k))
    (by rw [hE, map_one])
  by_contra hc0
  obtain ⟨f₀, hf₀⟩ := ggTor_closure_le_range hpm w.cor hcomm hxs
  have hconj : MulAut.conj x = 1 := by
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hxZ g,
      mul_inv_cancel_right]
  have hd := ggTor_ker hp hm.pos.ne' hpm w hw hcomm f₀ (by rw [hf₀, hconj])
  obtain ⟨l, hl⟩ := hC1 c (fun k => Multiplicative.toAdd (f₀ k)) hcK hd hc0
  have hf : f₀ = (fun k => Multiplicative.ofAdd (c k)) ^ l.val := by
    funext k
    have h1 := congrFun hl k
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [Pi.pow_apply, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, ← h1, ofAdd_toAdd]
  rw [hf, map_pow, hE, one_pow] at hf₀
  rw [← hf₀, orderOf_one] at hxo
  exact hp.one_lt.ne hxo


theorem GGTorusTorWit.weylOfType {m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hM : GGIsWeylMatrix M) (hMC : GGIntCartan M C) :
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
        ∀ k, (e (M.simple k) : MulAut ↥A) = ggConjAut A (w.hn k) :=
  ⟨hM, hMC, hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end CFSG.StandardType
