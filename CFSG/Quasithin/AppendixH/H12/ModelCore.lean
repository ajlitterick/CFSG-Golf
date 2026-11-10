module

public import CFSG.Quasithin.AppendixH.H12.GLAction
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.Quasithin.H.Mathieu.H12Pf (glMul toAdd_glMul)
open CFSG.ASVolI.ChH (IsIntDirect cenIn ptStab)

abbrev G0 : Subgroup Γ12 := H12Cert.G

abbrev T0 : Subgroup Γ12 := H12Cert.T0

@[expose] def dc (c : ℕ) : Vec12 := Multiplicative.ofAdd (vecN 12 c)

@[expose] def cd (v : Vec12) : ℕ := codeN (Multiplicative.toAdd v)

theorem cd_lt (v : Vec12) : cd v < 4096 := codeN_lt _

theorem cd_dc {c : ℕ} (hc : c < 4096) : cd (dc c) = c := codeN_vecN hc

theorem dc_cd (v : Vec12) : dc (cd v) = v := by
  simp only [dc, cd]
  rw [vecN_codeN]
  exact ofAdd_toAdd v

theorem dc_inj {c d : ℕ} (hc : c < 4096) (hd : d < 4096) (h : dc c = dc d) : c = d := by
  exact vecN_inj hc hd (by simpa only [dc, toAdd_ofAdd] using congrArg Multiplicative.toAdd h)

theorem dc_zero : dc 0 = 1 := by
  rw [dc, vecN_zero]
  rfl

theorem dc_xor (a b : ℕ) : dc (a ^^^ b) = dc a * dc b := by
  rw [dc, vecN_xor, dc, dc]
  rfl

theorem glHom_dc (g : Γ12) (c : ℕ) :
    glHom g (dc c) = dc (mvN (colsN (g : Matrix (Fin 12) (Fin 12) (ZMod 2))) c) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_glHom]
  simp only [dc, toAdd_ofAdd]
  rw [mulVec_vecN]


@[expose] def gmv (g : Γ12) (c : ℕ) : ℕ := mvN (colsN (g : Matrix (Fin 12) (Fin 12) (ZMod 2))) c

theorem gmv_lt (g : Γ12) (c : ℕ) : gmv g c < 4096 := by
  rw [gmv]
  simpa using mvN_lt (validN_colsN (n := 12) _).2 c

theorem gmv_one {c : ℕ} (hc : c < 4096) : gmv 1 c = c := by
  rw [gmv, Units.val_one, colsN_one]
  have h := mulVec_vecN (n := 12) (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) c
  rw [Matrix.one_mulVec, colsN_one] at h
  exact vecN_inj (mvN_lt (n := 12) validN_oneN.2 c) hc h.symm

theorem gmv_mul (g h : Γ12) (c : ℕ) : gmv (g * h) c = gmv g (gmv h c) := by
  simp only [gmv, Units.val_mul, colsN_mul, mvN_mulN]

theorem gmv_xor (g : Γ12) (a b : ℕ) : gmv g (a ^^^ b) = gmv g a ^^^ gmv g b := by
  simp only [gmv, mvN_xor]


private theorem gmv_gU (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

theorem closed_of_gen {S : ℕ → Prop} (h : ∀ i < 2, ∀ c, S c → S (mvN (gG.getD i one12) c)) {g : Γ12}
    (hg : g ∈ G0) {c : ℕ} (hc : S c) : S (gmv g c) := by
  have hgen : ∀ i < 2, ∀ c, S c → S (gmv (gU i) c) := by
    intro i hi c hc
    simpa only [gmv_gU] using h i hi c hc
  have h1 : ∀ c, S c → S (gmv 1 c) := by
    intro c hc
    have hpow : ∀ m : ℕ, S c → S (gmv ((gU 0) ^ (m + 1)) c) := by
      intro m
      induction m with
      | zero =>
        intro hc
        rw [pow_one]
        exact hgen 0 (by norm_num) c hc
      | succ m ih =>
        intro hc
        rw [pow_succ', gmv_mul]
        exact hgen 0 (by norm_num) _ (ih hc)
    have hfin : IsOfFinOrder (gU 0) := isOfFinOrder_of_finite _
    have hk : (gU 0) ^ (orderOf (gU 0) - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [← hk]
    exact hpow (orderOf (gU 0) - 1) hc
  refine G_induction (p := fun x => ∀ c, S c → S (gmv x c)) h1 ?_ hg c hc
  intro i hi y hy c hc
  rw [gmv_mul]
  exact hgen i hi _ (hy c hc)

@[expose] def smulSub (g : Γ12) (P : Subgroup Vec12) : Subgroup Vec12 := P.map (glHom g).toMonoidHom

theorem smulSub_one (P : Subgroup Vec12) : smulSub 1 P = P := by
  rw [smulSub, map_one]
  exact Subgroup.map_id P

theorem smulSub_mul (g h : Γ12) (P : Subgroup Vec12) :
    smulSub (g * h) P = smulSub g (smulSub h P) := by
  rw [smulSub, smulSub, smulSub, map_mul, Subgroup.map_map]
  congr 1


theorem mem_ptStab_iff (X : Subgroup Γ12) (P : Subgroup Vec12) (g : Γ12) :
    g ∈ ptStab glHom X P ↔ g ∈ X ∧ smulSub g P = P := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨h1, StabLat.mem_stabSub_iff_map.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨h1, StabLat.mem_stabSub_iff_map.mpr h2⟩

theorem mem_cenIn_iff (X : Subgroup Γ12) (W : Subgroup Vec12) (g : Γ12) :
    g ∈ cenIn glHom X W ↔ g ∈ X ∧ ∀ u ∈ W, glHom g u = u := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨h1, mem_centSub.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨h1, mem_centSub.mpr h2⟩

@[expose] def spanSub (b : List ℕ) : Subgroup Vec12 := Subgroup.closure {x | ∃ c ∈ b, x = dc c}

private def snStep (S : List ℕ) (v : ℕ) : List ℕ :=
  if S.contains v then S else S ++ S.map (· ^^^ v)

private theorem snStep_contains {S : List ℕ} {v : ℕ} (h : v ∈ S) : S.contains v = true :=
  List.contains_iff_mem.mpr h

private theorem snStep_not_contains {S : List ℕ} {v : ℕ} (h : v ∉ S) : S.contains v = false := by
  cases hc : S.contains v with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) h

private theorem spanN_foldl_nd (vs : List ℕ) (S : List ℕ) (hSn : S.Nodup)
    (hSxor : ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S) (hS0 : 0 ∈ S) :
    (vs.foldl snStep S).Nodup ∧
      (∀ a ∈ vs.foldl snStep S, ∀ b ∈ vs.foldl snStep S, a ^^^ b ∈ vs.foldl snStep S) ∧
      0 ∈ vs.foldl snStep S ∧ (∀ v ∈ vs, v ∈ vs.foldl snStep S) ∧
      (∀ a ∈ S, a ∈ vs.foldl snStep S) := by
  induction vs generalizing S with
  | nil => exact ⟨hSn, hSxor, hS0, by simp, fun a ha => ha⟩
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih S hSn hSxor hS0
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h5 w hv
        · exact h4 w hw
      · intro a ha; exact h5 a ha
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      have hS1n : (S ++ S.map (· ^^^ v)).Nodup := by
        rw [List.nodup_append]
        refine ⟨hSn, hSn.map (fun a b h => Nat.xor_left_inj.mp h), ?_⟩
        intro a ha b hb hab
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        exact hv (by
          have h2 : v = a ^^^ c := by
            rw [hab]
            simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self, Nat.xor_zero]
          rw [h2]; exact hSxor a ha c hc)
      have hS1xor : ∀ a ∈ S ++ S.map (· ^^^ v), ∀ b ∈ S ++ S.map (· ^^^ v),
          a ^^^ b ∈ S ++ S.map (· ^^^ v) := by
        intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append.mpr (Or.inl (hSxor a ha b hb))
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
            exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
              ⟨a ^^^ c, hSxor a ha c hc, by simp [Nat.xor_assoc]⟩))
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
              ⟨c ^^^ b, hSxor c hc b hb, by simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]⟩))
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
            exact List.mem_append.mpr (Or.inl (by
              simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self, Nat.xor_zero]
                using hSxor c hc d hd))
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        ih (S ++ S.map (· ^^^ v)) hS1n hS1xor (List.mem_append.mpr (Or.inl hS0))
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hw
        · have hvS1 : v ∈ S ++ S.map (· ^^^ v) :=
            List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨0, hS0, by simp⟩))
          rw [hwv]
          exact h5 v hvS1
        · exact h4 w hw
      · intro a ha
        exact h5 a (List.mem_append.mpr (Or.inl ha))

private theorem spanN_foldl_lt (vs : List ℕ) (S : List ℕ)
    (hSlt : ∀ a ∈ S, a < 2 ^ 12) (hvs : ∀ v ∈ vs, v < 2 ^ 12) :
    ∀ a ∈ vs.foldl snStep S, a < 2 ^ 12 := by
  induction vs generalizing S with
  | nil => simpa using hSlt
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      exact ih S hSlt (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      refine ih (S ++ S.map (· ^^^ v)) ?_ (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hSlt a ha
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact Nat.xor_lt_two_pow (hSlt c hc) (hvs v List.mem_cons_self)

private theorem spanN_eq_foldl (b : List ℕ) : spanN b = b.foldl snStep [0] := rfl

private theorem spanN_nd_parts (b : List ℕ) :
    (spanN b).Nodup ∧ (∀ a ∈ spanN b, ∀ c ∈ spanN b, a ^^^ c ∈ spanN b) ∧
      0 ∈ spanN b ∧ (∀ v ∈ b, v ∈ spanN b) := by
  have h := spanN_foldl_nd b [0] (by simp)
    (by
      intro a ha c hc
      simp only [List.mem_singleton] at ha hc
      subst ha; subst hc
      simp)
    (by simp)
  simpa only [spanN_eq_foldl] using ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem spanN_xor {b : List ℕ} {a c : ℕ} (ha : a ∈ spanN b) (hc : c ∈ spanN b) :
    a ^^^ c ∈ spanN b :=
  (spanN_nd_parts b).2.1 a ha c hc

private theorem zero_mem_spanN (b : List ℕ) : 0 ∈ spanN b :=
  (spanN_nd_parts b).2.2.1

private theorem self_mem_spanN (b : List ℕ) : ∀ c ∈ b, c ∈ spanN b :=
  (spanN_nd_parts b).2.2.2

private theorem dc_mem_foldl (T : Subgroup Vec12) (vs S : List ℕ)
    (hS : ∀ a ∈ S, dc a ∈ T) (hvs : ∀ v ∈ vs, dc v ∈ T) :
    ∀ a ∈ vs.foldl snStep S, dc a ∈ T := by
  induction vs generalizing S with
  | nil => simpa using hS
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      exact ih S hS (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      refine ih (S ++ S.map (· ^^^ v)) ?_ (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hS a ha
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        rw [dc_xor]
        exact T.mul_mem (hS c hc) (hvs v List.mem_cons_self)

private theorem cd_mul (u v : Vec12) : cd (u * v) = cd u ^^^ cd v := by
  conv_lhs => rw [← dc_cd u, ← dc_cd v, ← dc_xor]
  rw [cd_dc (Nat.xor_lt_two_pow (n := 12) (cd_lt u) (cd_lt v))]

private theorem inv_eq_self_vec12 (x : Vec12) : x⁻¹ = x := by
  rw [← dc_cd x]
  apply inv_eq_of_mul_eq_one_right
  show dc (cd x) * dc (cd x) = 1
  rw [← dc_xor, Nat.xor_self, dc_zero]

theorem spanN_nodup (b : List ℕ) : (spanN b).Nodup :=
  (spanN_nd_parts b).1

theorem spanN_lt {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) : ∀ c ∈ spanN b, c < 4096 := by
  have h := spanN_foldl_lt b [0] (by intro a ha; simp only [List.mem_singleton] at ha; subst ha; norm_num)
    (fun v hv => hb v hv)
  intro c hc
  rw [spanN_eq_foldl] at hc
  simpa using h c hc

theorem mem_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) (v : Vec12) :
    v ∈ spanSub b ↔ cd v ∈ spanN b := by
  constructor
  · intro hv
    let K : Subgroup Vec12 :=
      { carrier := {v | cd v ∈ spanN b}
        one_mem' := by
          change cd (1 : Vec12) ∈ spanN b
          rw [show (1 : Vec12) = dc 0 from dc_zero.symm, cd_dc (by norm_num)]
          exact zero_mem_spanN b
        mul_mem' := by
          intro x y hx hy
          change cd (x * y) ∈ spanN b
          change cd x ∈ spanN b at hx
          change cd y ∈ spanN b at hy
          rw [cd_mul]
          exact spanN_xor hx hy
        inv_mem' := by
          intro x hx
          change cd x⁻¹ ∈ spanN b
          change cd x ∈ spanN b at hx
          simpa only [inv_eq_self_vec12 x] using hx }
    have hle : spanSub b ≤ K := by
      rw [spanSub, Subgroup.closure_le]
      rintro x ⟨c, hc, rfl⟩
      change cd (dc c) ∈ spanN b
      rw [cd_dc (hb c hc)]
      exact self_mem_spanN b c hc
    exact hle hv
  · intro hv
    have h := dc_mem_foldl (spanSub b) b [0]
      (by
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        rw [dc_zero]
        exact Subgroup.one_mem _)
      (fun c hc => Subgroup.subset_closure ⟨c, hc, rfl⟩)
    have := h (cd v) (by simpa only [spanN_eq_foldl] using hv)
    rwa [dc_cd] at this

theorem dc_mem_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) {c : ℕ} (hc : c < 4096) :
    dc c ∈ spanSub b ↔ c ∈ spanN b := by
  rw [mem_spanSub_iff hb, cd_dc hc]

theorem card_spanSub {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) :
    Nat.card (spanSub b) = (spanN b).length := by
  classical
  have hnd := spanN_nodup b
  have memF : ∀ a : ℕ, a ∈ (spanN b).toFinset ↔ a ∈ spanN b := fun a => List.mem_toFinset
  let e : spanSub b ≃ (spanN b).toFinset :=
    { toFun := fun v => ⟨cd v.1, (memF _).mpr ((mem_spanSub_iff hb v.1).mp v.2)⟩
      invFun := fun x => ⟨dc x.1, (mem_spanSub_iff hb (dc x.1)).mpr (by
        rw [cd_dc (spanN_lt hb x.1 ((memF _).mp x.2))]
        exact (memF _).mp x.2)⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change dc (cd v.1) = v.1
        rw [dc_cd]
      right_inv := by
        intro x
        apply Subtype.ext
        change cd (dc x.1) = x.1
        rw [cd_dc (spanN_lt hb x.1 ((memF _).mp x.2))] }
  calc Nat.card (spanSub b) = Nat.card (spanN b).toFinset := Nat.card_congr e
    _ = (spanN b).length := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem smulSub_spanSub (g : Γ12) (b : List ℕ) :
    smulSub g (spanSub b) = spanSub (b.map (gmv g)) := by
  rw [smulSub, spanSub, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨gmv g c, List.mem_map.mpr ⟨c, hc, rfl⟩, glHom_dc g c⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact ⟨dc d, ⟨d, hd, rfl⟩, glHom_dc g d⟩

theorem spanSub_eq_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanSub b = spanSub b' ↔ ∀ c < 4096, c ∈ spanN b ↔ c ∈ spanN b' := by
  constructor
  · intro h c hc
    rw [← dc_mem_spanSub_iff hb hc, h, dc_mem_spanSub_iff hb' hc]
  · intro h
    apply le_antisymm
    · intro v hv
      rw [mem_spanSub_iff hb] at hv
      rw [mem_spanSub_iff hb']
      exact (h (cd v) (cd_lt v)).mp hv
    · intro v hv
      rw [mem_spanSub_iff hb'] at hv
      rw [mem_spanSub_iff hb]
      exact (h (cd v) (cd_lt v)).mpr hv

theorem spanSub_le_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanSub b ≤ spanSub b' ↔ ∀ c ∈ b, c ∈ spanN b' := by
  constructor
  · intro hle c hc
    rw [← dc_mem_spanSub_iff hb' (hb c hc)]
    exact hle (Subgroup.subset_closure ⟨c, hc, rfl⟩)
  · intro h
    rw [spanSub, Subgroup.closure_le]
    rintro x ⟨c, hc, rfl⟩
    exact (dc_mem_spanSub_iff hb' (hb c hc)).mpr (h c hc)

@[expose] def ptSub (c : ℕ) : Subgroup Vec12 := spanSub [c, mvN z12 c]

@[expose] def lineOf (c : ℕ) : List ℕ := [c, mvN z12 c, mvN z12 (mvN z12 c)]

theorem z12_lt (c : ℕ) : mvN z12 c < 4096 := by
  simpa using mvN_lt (n := 12) validN_z12.2 c

theorem lineOf_lt {c : ℕ} (hc : c < 4096) : ∀ x ∈ lineOf c, x < 4096 := by
  intro x hx
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hc
  · exact z12_lt c
  · exact z12_lt _

theorem omega_sq {c : ℕ} (hc : c < 4096) : mvN z12 (mvN z12 c) = c ^^^ mvN z12 c := by
  have h : (List.range 4096).all (fun c => mvN z12 (mvN z12 c) == c ^^^ mvN z12 c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

theorem omega_cube {c : ℕ} (hc : c < 4096) : mvN z12 (mvN z12 (mvN z12 c)) = c := by
  have h : (List.range 4096).all (fun c => mvN z12 (mvN z12 (mvN z12 c)) == c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this


private theorem ptSub_hb {c : ℕ} (hc : c < 4096) : ∀ x ∈ [c, mvN z12 c], x < 4096 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hc
  · exact z12_lt c

theorem spanN_ptSub {c : ℕ} (hc : c < 4096) :
    ∀ x, x ∈ spanN [c, mvN z12 c] ↔ x = 0 ∨ x ∈ lineOf c := by
  have h : (List.range 4096).all (fun c => spanN [c, mvN z12 c] ==
      (if c == 0 then [0] else [0, c, mvN z12 c, mvN z12 (mvN z12 c)])) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  have hspan : spanN [c, mvN z12 c] =
      (if c == 0 then [0] else [0, c, mvN z12 c, mvN z12 (mvN z12 c)]) := by
    simpa using hc'
  rw [hspan]
  intro x
  by_cases hc0 : c = 0
  · subst hc0
    simp [lineOf, mvN_zero]
  · have hc0' : (c == 0) = false := by
      cases h : c == 0 with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) hc0
    simp only [hc0', Bool.false_eq_true, if_false, lineOf, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc]


theorem card_ptSub {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) : Nat.card (ptSub c) = 4 := by
  rw [ptSub, card_spanSub (ptSub_hb hc)]
  have h : (List.range 4096).all (fun c => (spanN [c, mvN z12 c]).length == 4 || c == 0) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  have hc0' : (c == 0) = false := by
    cases h : c == 0 with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp h) (ne_of_gt hc0)
  rw [hc0', Bool.or_false] at hc'
  simpa using hc'

private theorem card_ptSub_zero : Nat.card (ptSub 0) = 1 := by
  have hb : ∀ x ∈ [0, mvN z12 0], x < 4096 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · norm_num
    · rw [mvN_zero]; norm_num
  rw [ptSub, card_spanSub hb]
  decide +kernel

private theorem mem_lineOf_omega {c x : ℕ} (hc : c < 4096) :
    x ∈ lineOf (mvN z12 c) ↔ x ∈ lineOf c := by
  have h3 := omega_cube hc
  rw [show lineOf (mvN z12 c) = [mvN z12 c, mvN z12 (mvN z12 c), c] from by
    simp only [lineOf, h3]]
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mem_lineOf_omega2 {c x : ℕ} (hc : c < 4096) :
    x ∈ lineOf (mvN z12 (mvN z12 c)) ↔ x ∈ lineOf c := by
  have h3 := omega_cube hc
  have h4 : mvN z12 (mvN z12 (mvN z12 (mvN z12 c))) = mvN z12 c := congrArg (mvN z12) h3
  rw [show lineOf (mvN z12 (mvN z12 c)) = [mvN z12 (mvN z12 c), c, mvN z12 c] from by
    simp only [lineOf, h3, h4]]
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem ptSub_eq_iff {c d : ℕ} (hc0 : 0 < c) (hc : c < 4096) (hd : d < 4096) :
    ptSub c = ptSub d ↔ d ∈ lineOf c := by
  constructor
  · intro h
    have hs : spanSub [c, mvN z12 c] = spanSub [d, mvN z12 d] := by
      simpa only [ptSub] using h
    have hm := (spanSub_eq_iff (ptSub_hb hc) (ptSub_hb hd)).mp hs d hd
    have hdself : d ∈ spanN [d, mvN z12 d] := self_mem_spanN _ d (List.mem_cons_self)
    have hdc : d ∈ spanN [c, mvN z12 c] := hm.mpr hdself
    rw [spanN_ptSub hc] at hdc
    rcases hdc with hd0 | hlin
    · exfalso
      have h4 := card_ptSub hc0 hc
      rw [h, hd0, card_ptSub_zero] at h4
      omega
    · exact hlin
  · intro hd
    apply (spanSub_eq_iff (ptSub_hb hc) (ptSub_hb (lineOf_lt hc d hd))).mpr
    intro x _
    rw [spanN_ptSub hc, spanN_ptSub (lineOf_lt hc d hd)]
    have hperm : x ∈ lineOf d ↔ x ∈ lineOf c := by
      simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact Iff.rfl
      · exact mem_lineOf_omega hc
      · exact mem_lineOf_omega2 hc
    rw [hperm]

theorem ptSub_eq_of_mem {c d : ℕ} (hc0 : 0 < c) (hc : c < 4096) (hd : d ∈ lineOf c) :
    ptSub c = ptSub d :=
  (ptSub_eq_iff hc0 hc (lineOf_lt hc d hd)).mpr hd

theorem gmv_omega {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    gmv g (mvN z12 c) = mvN z12 (gmv g c) := by
  have hz : ∀ x, gmv zU x = mvN z12 x := fun x => by
    rw [gmv, zU_val, colsN_decN validN_z12]
  rw [← hz c, ← gmv_mul, zU_comm hg, gmv_mul, hz (gmv g c)]

theorem smulSub_ptSub {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    smulSub g (ptSub c) = ptSub (gmv g c) := by
  show smulSub g (spanSub [c, mvN z12 c]) = spanSub [gmv g c, mvN z12 (gmv g c)]
  rw [smulSub_spanSub]
  simp only [List.map_cons, List.map_nil, gmv_omega hg hc]

@[expose] def vecStab (c : ℕ) : Subgroup Γ12 := cenIn glHom G0 (spanSub [c])

theorem mem_vecStab_iff {c : ℕ} (hc : c < 4096) (g : Γ12) :
    g ∈ vecStab c ↔ g ∈ G0 ∧ gmv g c = c := by
  rw [vecStab, mem_cenIn_iff]
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    have h1 := hfix (dc c) (Subgroup.subset_closure ⟨c, List.mem_singleton_self c, rfl⟩)
    rw [glHom_dc] at h1
    exact dc_inj (gmv_lt g c) hc h1
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, ?_⟩
    let K : Subgroup Vec12 :=
      { carrier := {u | glHom g u = u}
        one_mem' := by change glHom g 1 = 1; simp
        mul_mem' := by intro a b ha hb; change glHom g (a * b) = a * b; rw [map_mul, ha, hb]
        inv_mem' := by intro a ha; change glHom g a⁻¹ = a⁻¹; rw [inv_eq_self_vec12 a]; exact ha }
    have hle : spanSub [c] ≤ K := by
      rw [spanSub, Subgroup.closure_le]
      rintro x ⟨d, hd, rfl⟩
      simp only [List.mem_singleton] at hd
      subst d
      have hz : glHom g (dc c) = dc c := by rw [glHom_dc]; exact congrArg dc hgc
      exact hz
    intro u hu
    exact hle hu

theorem vecStab_le_G0 (c : ℕ) : vecStab c ≤ G0 := inf_le_left


end CFSG.Quasithin.AppendixH.H12.Model
