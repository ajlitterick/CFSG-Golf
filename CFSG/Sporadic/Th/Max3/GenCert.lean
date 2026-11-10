module

public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Sporadic.Th.Max3.MaxGen

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th

open Native

theorem orderOf_eq_of_isConj {G : Type*} [Group G] {u v : G} (h : IsConj u v) :
    orderOf u = orderOf v := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

section Tables

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem Rep.treeTable (hn : n < 2 ^ 32) {gens : ℕ → Table} {gensG : ℕ → G}
    (hgens : ∀ s, Rep n (gens s) (gensG s)) (pl : Table) (k : ℕ) :
    Rep n (treeTable n pl gens k) (treeElt pl gensG k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [Native.treeTable.eq_def, treeElt.eq_def]
    split_ifs with hk
    · exact Rep.compT (hgens _) (ih _ hk.2)
    · exact Rep.idT hn

@[expose] noncomputable def schreierElt (pts pl pos T₁ T₂ : Table) (g₁ g₂ : G) (k l : ℕ) : G :=
  (treeElt pl (lettersG g₁ g₂) (ap pos (ap (letters T₁ T₂ l) (ap pts k))))⁻¹ *
    lettersG g₁ g₂ l * treeElt pl (lettersG g₁ g₂) k

theorem Rep.schreierTable (hn : n < 2 ^ 32) {T₁ T₂ : Table} {g₁ g₂ : G} (h₁ : Rep n T₁ g₁)
    (h₂ : Rep n T₂ g₂) (pts pl pos : Table) (k l : ℕ)
    (hok : (schreierTable n pts pl pos T₁ T₂ k l).2 = true) :
    Rep n (schreierTable n pts pl pos T₁ T₂ k l).1 (schreierElt pts pl pos T₁ T₂ g₁ g₂ k l) := by
  have hl : ∀ s, Rep n (Native.letters T₁ T₂ s) (lettersG g₁ g₂ s) := Rep.letters h₁ h₂
  unfold Native.schreierTable at hok ⊢
  dsimp only at hok ⊢
  unfold schreierElt
  rw [mul_assoc]
  exact Rep.compT (Rep.inv_of_invOK (Rep.treeTable hn hl pl _) hok)
    (Rep.compT (hl l) (Rep.treeTable hn hl pl k))

end Tables


section Chain

variable {G : Type*} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]

omit [Finite G] in
theorem closure_le_stabilizer {s₁ s₂ : G} {p : Fin n} (h₁ : s₁ • p = p) (h₂ : s₂ • p = p) :
    Subgroup.closure ({s₁, s₂} : Set G) ≤ MulAction.stabilizer G p := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact h₁
  · exact h₂

theorem card_orbit_mul_le {K S : Subgroup G} (hSK : S ≤ K) {p : Fin n}
    (hS : S ≤ MulAction.stabilizer G p) :
    Nat.card (MulAction.orbit K p) * Nat.card S ≤ Nat.card K := by
  have e := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K p)
  rw [Nat.card_prod] at e
  rw [← e]
  refine Nat.mul_le_mul_left _ ?_
  have hle : S.subgroupOf K ≤ MulAction.stabilizer K p := by
    intro g hg
    have := hS (Subgroup.mem_subgroupOf.1 hg)
    exact this
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
  exact Subgroup.card_le_of_le hle

theorem card_orbit_le (K : Subgroup G) (p : Fin n) :
    Nat.card (MulAction.orbit K p) ≤ Nat.card K := by
  have e := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K p)
  rw [Nat.card_prod] at e
  rw [← e]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem card_closure_ge {g₁ g₂ s₁ s₂ t₁ t₂ : G} {m₀ m₁ m₂ r₀ r₁ r₂ : ℕ}
    {p₀ p₁ p₂ l₀ l₁ l₂ : ℕ → ℕ} {q₀ q₁ q₂ : Table}
    (h0 : TreeData n g₁ g₂ m₀ r₀ p₀ l₀ q₀) (h1 : TreeData n s₁ s₂ m₁ r₁ p₁ l₁ q₁)
    (h2 : TreeData n t₁ t₂ m₂ r₂ p₂ l₂ q₂)
    (hs₁ : s₁ ∈ Subgroup.closure ({g₁, g₂} : Set G))
    (hs₂ : s₂ ∈ Subgroup.closure ({g₁, g₂} : Set G))
    (ht₁ : t₁ ∈ Subgroup.closure ({s₁, s₂} : Set G))
    (ht₂ : t₂ ∈ Subgroup.closure ({s₁, s₂} : Set G))
    (hfs₁ : s₁ • (⟨r₀, h0.r_lt⟩ : Fin n) = ⟨r₀, h0.r_lt⟩)
    (hfs₂ : s₂ • (⟨r₀, h0.r_lt⟩ : Fin n) = ⟨r₀, h0.r_lt⟩)
    (hft₁ : t₁ • (⟨r₁, h1.r_lt⟩ : Fin n) = ⟨r₁, h1.r_lt⟩)
    (hft₂ : t₂ • (⟨r₁, h1.r_lt⟩ : Fin n) = ⟨r₁, h1.r_lt⟩) :
    m₀ * m₁ * m₂ ≤ Nat.card (Subgroup.closure ({g₁, g₂} : Set G)) := by
  set K := Subgroup.closure ({g₁, g₂} : Set G)
  set S := Subgroup.closure ({s₁, s₂} : Set G)
  set T := Subgroup.closure ({t₁, t₂} : Set G)
  have hSK : S ≤ K := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hs₁
    · exact hs₂
  have hTS : T ≤ S := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ht₁
    · exact ht₂
  have e0 := h0.card_orbit
  have e1 := h1.card_orbit
  have e2 := h2.card_orbit
  have k0 := card_orbit_mul_le hSK (closure_le_stabilizer hfs₁ hfs₂)
  have k1 := card_orbit_mul_le hTS (closure_le_stabilizer hft₁ hft₂)
  have k2 := card_orbit_le T (⟨r₂, h2.r_lt⟩ : Fin n)
  rw [e0] at k0
  rw [e1] at k1
  rw [e2] at k2
  calc m₀ * m₁ * m₂ ≤ m₀ * (m₁ * Nat.card T) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ k2)
    _ ≤ m₀ * Nat.card S := Nat.mul_le_mul_left _ k1
    _ ≤ Nat.card K := k0

end Chain

section Schreier

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem schreierElt_mem (K : Subgroup G) (pts pl pos T₁ T₂ : Table) {g₁ g₂ : G} (h₁ : g₁ ∈ K)
    (h₂ : g₂ ∈ K) (k l : ℕ) : schreierElt pts pl pos T₁ T₂ g₁ g₂ k l ∈ K := by
  unfold schreierElt
  have hl := lettersG_mem K h₁ h₂
  exact K.mul_mem (K.mul_mem (K.inv_mem (treeElt_mem K pl hl _)) (hl l)) (treeElt_mem K pl hl _)

theorem schreierElt_fix {T₁ T₂ : Table} {g₁ g₂ : G} (h₁ : Rep n T₁ g₁) (h₂ : Rep n T₂ g₂)
    {m r : ℕ} {pts pl pos : Table} (hT : TreeData n g₁ g₂ m r (ap pts) (ap pos) pl) {k : ℕ}
    (hk : k < m) (l : ℕ) : idx n (schreierElt pts pl pos T₁ T₂ g₁ g₂ k l) r = r := by
  have hl : Rep n (letters T₁ T₂ l) (lettersG g₁ g₂ l) := Rep.letters h₁ h₂ l
  have hpk : ap pts k < n := hT.pts_lt k hk
  have hc : ap pos (idx n (lettersG g₁ g₂ l) (ap pts k)) < m ∧
      ap pts (ap pos (idx n (lettersG g₁ g₂ l) (ap pts k))) =
        idx n (lettersG g₁ g₂ l) (ap pts k) := by
    unfold lettersG
    split_ifs
    · exact hT.c1 k hk
    · exact hT.c2 k hk
  have hj : ap pos (ap (letters T₁ T₂ l) (ap pts k)) = ap pos (idx n (lettersG g₁ g₂ l) (ap pts k)) :=
    by rw [hl _ hpk]
  unfold schreierElt
  rw [hj, idx_mul, idx_mul, hT.elt k hk]
  set j := ap pos (idx n (lettersG g₁ g₂ l) (ap pts k))
  rw [← hc.2, ← hT.elt _ hc.1, idx_inv_idx]

theorem smul_fix_of_idx {g : G} {r : ℕ} (hr : r < n) (h : idx n g r = r) :
    g • (⟨r, hr⟩ : Fin n) = ⟨r, hr⟩ :=
  smul_eq_of_idx g _ _ h

end Schreier

@[expose] def genCheck (n : ℕ) (X Y C Ci : Table) (a₁ a₂ a₃ b₁ b₂ b₃ e₁ e₂ : ℕ × ℕ) : Bool :=
  let g1 := compT n X (compT n Ci (compT n X C))
  let g2 := compT n Y (compT n Ci (compT n Y C))
  let t0 := localBFS n 0 g1 g2
  (t0.1.size == n && treeOK n n 0 t0.1 t0.2.1 (ap t0.2.2) g1 g2) &&
  (let A1 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 a₁.1 a₁.2
   let A2 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 a₂.1 a₂.2
   let A3 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 a₃.1 a₃.2
   (A1.2 && A2.2 && A3.2) &&
   (let s1 := compT n A1.1 (compT n A2.1 A3.1)
    let B1 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 b₁.1 b₁.2
    let B2 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 b₂.1 b₂.2
    let B3 := schreierTable n t0.1 t0.2.1 t0.2.2 g1 g2 b₃.1 b₃.2
    (B1.2 && B2.2 && B3.2) &&
    (let s2 := compT n B1.1 (compT n B2.1 B3.1)
     let t1 := localBFS n 1 s1 s2
     (t1.1.size == 11741184 && treeOK n 11741184 1 t1.1 t1.2.1 (ap t1.2.2) s1 s2) &&
     (let E1 := schreierTable n t1.1 t1.2.1 t1.2.2 s1 s2 e₁.1 e₁.2
      let E2 := schreierTable n t1.1 t1.2.1 t1.2.2 s1 s2 e₂.1 e₂.2
      (E1.2 && E2.2) &&
      (let t2 := smallBFS 2 54 E1.1 E2.1
       t2.1.size == 54 && treeOK n 54 2 t2.1 t2.2 (findPt t2.1) E1.1 E2.1)))))

theorem genCheck_sound
    {c₀ : ℕ} (hC : CertFacts c₀) {X Y C Ci : Table} {x y c : J}
    (hX : Rep nX X x) (hY : Rep nX Y y) (hc : Rep nX C c) (hci : Rep nX Ci c⁻¹)
    {a₁ a₂ a₃ b₁ b₂ b₃ e₁ e₂ : ℕ × ℕ}
    (ha : a₁.1 < nX ∧ a₂.1 < nX ∧ a₃.1 < nX ∧ b₁.1 < nX ∧ b₂.1 < nX ∧ b₃.1 < nX)
    (he : e₁.1 < 11741184 ∧ e₂.1 < 11741184)
    (h : genCheck nX X Y C Ci a₁ a₂ a₃ b₁ b₂ b₃ e₁ e₂ = true) :
    Subgroup.closure ({x * (c⁻¹ * (x * c)), y * (c⁻¹ * (y * c))} : Set J) = ⊤ := by
  have hn : nX < 2 ^ 32 := by rw [hC.count]; norm_num
  unfold genCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h0⟩, ⟨⟨hA1, hA2⟩, hA3⟩, ⟨⟨hB1, hB2⟩, hB3⟩, ⟨-, h1⟩, ⟨hE1, hE2⟩, -, h2⟩ := h
  set g₁ : J := x * (c⁻¹ * (x * c)) with hg₁
  set g₂ : J := y * (c⁻¹ * (y * c)) with hg₂
  have hg1 : Rep nX (compT nX X (compT nX Ci (compT nX X C))) g₁ :=
    Rep.compT hX (Rep.compT hci (Rep.compT hX hc))
  have hg2 : Rep nX (compT nX Y (compT nX Ci (compT nX Y C))) g₂ :=
    Rep.compT hY (Rep.compT hci (Rep.compT hY hc))
  set G1 := compT nX X (compT nX Ci (compT nX X C))
  set G2 := compT nX Y (compT nX Ci (compT nX Y C))
  set t0 := localBFS nX 0 G1 G2
  have T0 := TreeData.of_treeOK hg1 hg2 h0
  set K := Subgroup.closure ({g₁, g₂} : Set J)
  have hg₁K : g₁ ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hg₂K : g₂ ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set Sx := fun p : ℕ × ℕ => schreierElt t0.1 t0.2.1 t0.2.2 G1 G2 g₁ g₂ p.1 p.2
  have rS : ∀ p : ℕ × ℕ, (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 p.1 p.2).2 = true →
      Rep nX (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 p.1 p.2).1 (Sx p) :=
    fun p hp => Rep.schreierTable hn hg1 hg2 _ _ _ _ _ hp
  have mS : ∀ p : ℕ × ℕ, Sx p ∈ K := fun p => schreierElt_mem K _ _ _ _ _ hg₁K hg₂K _ _
  have fS : ∀ p : ℕ × ℕ, p.1 < nX → idx nX (Sx p) 0 = 0 :=
    fun p hp => schreierElt_fix hg1 hg2 T0 hp _
  set s₁ := Sx a₁ * (Sx a₂ * Sx a₃)
  set s₂ := Sx b₁ * (Sx b₂ * Sx b₃)
  have hs1 := Rep.compT (rS a₁ hA1) (Rep.compT (rS a₂ hA2) (rS a₃ hA3))
  have hs2 := Rep.compT (rS b₁ hB1) (Rep.compT (rS b₂ hB2) (rS b₃ hB3))
  have T1 := TreeData.of_treeOK hs1 hs2 h1
  have hs₁K : s₁ ∈ K := K.mul_mem (mS _) (K.mul_mem (mS _) (mS _))
  have hs₂K : s₂ ∈ K := K.mul_mem (mS _) (K.mul_mem (mS _) (mS _))
  have fs₁ : idx nX s₁ 0 = 0 := by
    rw [idx_mul, idx_mul, fS a₃ ha.2.2.1, fS a₂ ha.2.1, fS a₁ ha.1]
  have fs₂ : idx nX s₂ 0 = 0 := by
    rw [idx_mul, idx_mul, fS b₃ ha.2.2.2.2.2, fS b₂ ha.2.2.2.2.1, fS b₁ ha.2.2.2.1]
  set S := Subgroup.closure ({s₁, s₂} : Set J)
  have hs₁S : s₁ ∈ S := Subgroup.subset_closure (Set.mem_insert _ _)
  have hs₂S : s₂ ∈ S := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set S1 := compT nX (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 a₁.1 a₁.2).1
    (compT nX (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 a₂.1 a₂.2).1
      (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 a₃.1 a₃.2).1)
  set S2 := compT nX (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 b₁.1 b₁.2).1
    (compT nX (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 b₂.1 b₂.2).1
      (schreierTable nX t0.1 t0.2.1 t0.2.2 G1 G2 b₃.1 b₃.2).1)
  set t1 := localBFS nX 1 S1 S2
  set Ex := fun p : ℕ × ℕ => schreierElt t1.1 t1.2.1 t1.2.2 S1 S2 s₁ s₂ p.1 p.2
  have hE1' := Rep.schreierTable hn hs1 hs2 _ _ _ _ _ hE1
  have hE2' := Rep.schreierTable hn hs1 hs2 _ _ _ _ _ hE2
  have T2 := TreeData.of_treeOK hE1' hE2' h2
  have ht₁ : Ex e₁ ∈ S := schreierElt_mem S _ _ _ _ _ hs₁S hs₂S _ _
  have ht₂ : Ex e₂ ∈ S := schreierElt_mem S _ _ _ _ _ hs₁S hs₂S _ _
  have ft₁ : idx nX (Ex e₁) 1 = 1 := schreierElt_fix hs1 hs2 T1 he.1 _
  have ft₂ : idx nX (Ex e₂) 1 = 1 := schreierElt_fix hs1 hs2 T1 he.2 _
  have hb := card_closure_ge T0 T1 T2 hs₁K hs₂K ht₁ ht₂ (smul_fix_of_idx _ fs₁)
    (smul_fix_of_idx _ fs₂) (smul_fix_of_idx _ ft₁) (smul_fix_of_idx _ ft₂)
  rw [hC.count] at hb
  apply Subgroup.eq_top_of_le_card
  rw [Max3.natCard_J]
  exact le_trans (by norm_num) hb

end CFSG.Sporadic.Th
