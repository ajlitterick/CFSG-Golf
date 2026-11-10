module

public import CFSG.Timmesfeld.LocalTwoSubgroups.Omega

public section


namespace CFSG.Timmesfeld.LocalTwoSubgroups


open Subgroup


namespace FrobeniusFixedSpaceBounds


@[to_additive]
theorem card_sup_mul_card_inf {G : Type*} [Group G] (H N : Subgroup G)
    (h : ∀ b ∈ H, ∀ n ∈ N, b * n * b⁻¹ ∈ N) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) = Nat.card H * Nat.card N := by
  have hLE : H ≤ normalizer N := fun b hb => by
    rw [mem_normalizer_iff]; intro n; constructor
    · intro hn; exact h b hb n hn
    · intro hn
      have := h b⁻¹ (inv_mem hb) _ hn
      simpa [mul_assoc] using this
  have h1 : N.relIndex (H ⊔ N) = N.relIndex H := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    unfold relIndex index
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE).toEquiv.symm
  have e1 := relIndex_mul_card (H := N) (K := H ⊔ N)
  have e2 := relIndex_mul_card (H := N) (K := H)
  rw [inf_of_le_left (le_sup_right : N ≤ H ⊔ N)] at e1
  rw [h1] at e1
  rw [inf_comm]
  rw [← e1, ← e2]
  ring


section

variable {F V : Type} [Group F] [AddCommGroup V] [DistribMulAction F V]


def fixSub (B : Subgroup F) : AddSubgroup V where
  carrier := {v | ∀ a ∈ B, a • v = v}
  zero_mem' := by intro a _; simp
  add_mem' := by
    intro x y hx hy a ha
    simp [smul_add, hx a ha, hy a ha]
  neg_mem' := by
    intro x hx a ha
    simp [smul_neg, hx a ha]


theorem fixSub_anti {B B' : Subgroup F} (h : B ≤ B') : fixSub (V := V) B' ≤ fixSub B :=
  fun _ hv a ha => hv a (h ha)


theorem fixSub_sup (B B' : Subgroup F) :
    fixSub (V := V) B ⊓ fixSub B' ≤ fixSub (B ⊔ B') := by
  intro v hv
  have hle : B ⊔ B' ≤ MulAction.stabilizer F v :=
    sup_le (fun a ha => hv.1 a ha) (fun a ha => hv.2 a ha)
  exact fun a ha => hle ha


noncomputable def val (V : Type) [AddCommGroup V] [DistribMulAction F V] (B : Subgroup F) : ℕ :=
  Nat.card B * Nat.card (fixSub (V := V) B)


def cj (k : F) (B : Subgroup F) : Subgroup F := B.map (MulAut.conj k).toMonoidHom


theorem mem_cj {k : F} {B : Subgroup F} {y : F} : y ∈ cj k B ↔ ∃ x ∈ B, k * x * k⁻¹ = y := by
  simp [cj, mem_map]


theorem cj_cj (k k' : F) (B : Subgroup F) : cj k (cj k' B) = cj (k * k') B := by
  ext y
  simp only [mem_cj]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by group⟩


theorem cj_sup (k : F) (B C : Subgroup F) : cj k (B ⊔ C) = cj k B ⊔ cj k C := map_sup _ _ _


theorem card_cj [Finite F] (k : F) (B : Subgroup F) : Nat.card (cj k B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj k).injective


theorem card_fixSub_cj (k : F) (B : Subgroup F) :
    Nat.card (fixSub (V := V) (cj k B)) = Nat.card (fixSub (V := V) B) := by
  refine Nat.card_congr ((MulAction.toPerm k : Equiv.Perm V).subtypeEquiv ?_).symm
  intro v
  show (∀ a ∈ B, a • v = v) ↔ (∀ a ∈ cj k B, a • (k • v) = k • v)
  constructor
  · intro h a ha
    obtain ⟨x, hx, rfl⟩ := mem_cj.1 ha
    have : k * x * k⁻¹ * k = k * x := by group
    rw [← mul_smul, this, mul_smul, h x hx]
  · intro h a ha
    have := h (k * a * k⁻¹) (mem_cj.2 ⟨a, ha, rfl⟩)
    have e : k * a * k⁻¹ * k = k * a := by group
    rw [← mul_smul, e, mul_smul] at this
    exact MulAction.injective k this


end


theorem core {F V : Type} [Group F] [Finite F] [AddCommGroup V] [Finite V] [DistribMulAction F V]
    {L K : Subgroup F} (hLnormal : L.Normal) (hLcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hreg : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ K, k * x * k⁻¹ = y)
    {A0 : Subgroup F} (hA0L : A0 ≤ L) (hA0 : A0 ≠ ⊥) (hA : Nat.card V ≤ val V A0) :
    Nat.card V ≤ val V L := by
  classical
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have cjL : ∀ (k : F) (B : Subgroup F), B ≤ L → cj k B ≤ L := by
    intro k B hB y hy
    obtain ⟨x, hx, rfl⟩ := mem_cj.1 hy
    exact hLnormal.conj_mem x (hB hx) k
  have Lsup : ∀ B C : Subgroup F, B ≤ L → C ≤ L →
      Nat.card (B ⊔ C : Subgroup F) * Nat.card (B ⊓ C : Subgroup F) = Nat.card B * Nat.card C := by
    intro B C hB hC
    apply card_sup_mul_card_inf
    intro b hb n hn
    rw [hLcomm b (hB hb) n (hC hn), mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  have Vsup : ∀ X Y : AddSubgroup V, Nat.card X * Nat.card Y ≤ Nat.card (X ⊓ Y : AddSubgroup V) * Nat.card V := by
    intro X Y
    rw [← card_sup_add_card_inf X Y (fun b _ n hn => by simpa using hn), mul_comm]
    exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_card_addGroup _)
  set S : Set (Subgroup F) := {B | B ≤ L ∧ B ≠ ⊥} with hS
  obtain ⟨A1, hA1S, hA1max⟩ := Set.exists_max_image S (val V) (Set.toFinite S) ⟨A0, hA0L, hA0⟩
  obtain ⟨A, ⟨hAS, hAval⟩, hAmin⟩ := Set.exists_min_image
    {B | B ∈ S ∧ val V B = val V A1} (fun B => Nat.card B) (Set.toFinite _) ⟨A1, hA1S, rfl⟩
  obtain ⟨hAL, hA1⟩ := hAS
  have hmax : ∀ B : Subgroup F, B ≤ L → B ≠ ⊥ → val V B ≤ val V A :=
    fun B h1 h2 => hAval ▸ hA1max B ⟨h1, h2⟩
  have hmin : ∀ B : Subgroup F, B ≤ L → B ≠ ⊥ → val V B = val V A → Nat.card A ≤ Nat.card B :=
    fun B h1 h2 h3 => hAmin B ⟨⟨h1, h2⟩, h3.trans hAval⟩
  have hPA : Nat.card V ≤ val V A := hA.trans (hmax A0 hA0L hA0)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcpos : 0 < Nat.card (fixSub (V := V) A) := Nat.card_pos
  have hTI : ∀ k ∈ K, A ⊓ cj k A = ⊥ ∨ A ⊓ cj k A = A := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨hD1, hD2⟩ := hcon
    have hA2L : cj k A ≤ L := cjL k A hAL
    have hcardA2 : Nat.card (cj k A) = Nat.card A := card_cj k A
    have hcA2 : Nat.card (fixSub (V := V) (cj k A)) = Nat.card (fixSub (V := V) A) :=
      card_fixSub_cj k A
    have hDL : A ⊓ cj k A ≤ L := inf_le_left.trans hAL
    have hdA : Nat.card (A ⊓ cj k A : Subgroup F) < Nat.card A := by
      by_contra h
      push Not at h
      exact hD2 (Subgroup.eq_of_le_of_card_ge inf_le_left h)
    have hvD : val V (A ⊓ cj k A) < val V A :=
      lt_of_le_of_ne (hmax _ hDL hD1) (fun h => by have := hmin _ hDL hD1 h; omega)
    have hfix_le : fixSub (V := V) A ⊔ fixSub (cj k A) ≤ fixSub (A ⊓ cj k A) :=
      sup_le (fixSub_anti inf_le_left) (fixSub_anti inf_le_right)
    have hs1 := card_sup_add_card_inf (fixSub (V := V) A) (fixSub (cj k A))
      (fun b _ n hn => by simpa using hn)
    have hs2 : Nat.card (fixSub (V := V) A ⊔ fixSub (cj k A) : AddSubgroup V) ≤
        Nat.card (fixSub (V := V) (A ⊓ cj k A)) := AddSubgroup.card_le_of_le hfix_le
    have hsA : Nat.card (A ⊔ cj k A : Subgroup F) * Nat.card (A ⊓ cj k A : Subgroup F) =
        Nat.card A * Nat.card A := by
      rw [Lsup A _ hAL hA2L, hcardA2]
    have hSne : A ⊔ cj k A ≠ ⊥ := fun h => hA1 (le_bot_iff.1 (h ▸ le_sup_left))
    have hv2 := hmax _ (sup_le hAL hA2L) hSne
    have hfix2 : fixSub (V := V) A ⊓ fixSub (cj k A) ≤ fixSub (A ⊔ cj k A) := fixSub_sup _ _
    have he : Nat.card (fixSub (V := V) A ⊓ fixSub (cj k A) : AddSubgroup V) ≤
        Nat.card (fixSub (V := V) (A ⊔ cj k A)) := AddSubgroup.card_le_of_le hfix2
    unfold val at hvD hv2
    rw [hcA2] at hs1
    generalize Nat.card A = a at *
    generalize Nat.card (A ⊓ cj k A : Subgroup F) = d at *
    generalize Nat.card (A ⊔ cj k A : Subgroup F) = s at *
    generalize Nat.card (fixSub (V := V) A) = c at *
    generalize Nat.card (fixSub (V := V) (A ⊓ cj k A)) = cD at *
    generalize Nat.card (fixSub (V := V) (A ⊔ cj k A)) = cS at *
    generalize Nat.card (fixSub (V := V) A ⊓ fixSub (cj k A) : AddSubgroup V) = e at *
    generalize Nat.card (fixSub (V := V) A ⊔ fixSub (cj k A) : AddSubgroup V) = u at *
    have hepos : 0 < e := by
      by_contra h0
      have : e = 0 := by omega
      subst this
      simp at hs1
      omega
    have hdpos : 0 < d := by
      by_contra h0
      have : d = 0 := by omega
      subst this
      simp at hsA
      omega
    have h1 : c * c ≤ e * cD := by
      calc c * c = u * e := hs1.symm
        _ ≤ cD * e := Nat.mul_le_mul_right _ hs2
        _ = e * cD := by ring
    have h2 : d * c < e * a := by
      have h3 : d * c * c < e * a * c := by
        calc d * c * c = d * (c * c) := by ring
          _ ≤ d * (e * cD) := Nat.mul_le_mul_left _ h1
          _ = e * (d * cD) := by ring
          _ < e * (a * c) := Nat.mul_lt_mul_of_pos_left hvD hepos
          _ = e * a * c := by ring
      exact Nat.lt_of_mul_lt_mul_right h3
    have h4 : a * e ≤ c * d := by
      have h5 : a * a * e ≤ a * c * d := by
        calc a * a * e = s * d * e := by rw [hsA]
          _ = s * e * d := by ring
          _ ≤ s * cS * d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)
          _ ≤ a * c * d := Nat.mul_le_mul_right _ hv2
      have : a * (a * e) ≤ a * (c * d) := by
        calc a * (a * e) = a * a * e := by ring
          _ ≤ a * c * d := h5
          _ = a * (c * d) := by ring
      exact Nat.le_of_mul_le_mul_left this hApos
    nlinarith
  have hTI' : ∀ k ∈ K, ∀ x ∈ A, x ≠ 1 → k * x * k⁻¹ ∈ A → cj k A = A := by
    intro k hk x hx hx1 hkx
    have hmem : k * x * k⁻¹ ∈ A ⊓ cj k A := ⟨hkx, mem_cj.2 ⟨x, hx, rfl⟩⟩
    rcases hTI k hk with h | h
    · rw [h, mem_bot] at hmem
      exact absurd (by simpa using hmem) hx1
    · have hle : A ≤ cj k A := h.symm.le.trans inf_le_right
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])).symm
  have hT : ∀ B : Subgroup F, (∀ k ∈ K, cj k A = A → cj k B ≤ B) →
      ∀ k0 ∈ K, B ⊓ cj k0 A ≠ ⊥ → cj k0 A ≤ B := by
    intro B hB k0 hk0 hne
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hx1 : (x : F) ≠ 1 := fun h => hx (Subtype.ext h)
    have hxB : (x : F) ∈ B := x.2.1
    have hxA' : (x : F) ∈ cj k0 A := x.2.2
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact one_mem _
    have hxL : (x : F) ∈ L := cjL k0 A hAL hxA'
    have hyL : y ∈ L := cjL k0 A hAL hy
    obtain ⟨k', hk', hk'xy⟩ := hreg x hxL hx1 y hyL hy1
    obtain ⟨x0, hx0, hx0e⟩ := mem_cj.1 hxA'
    obtain ⟨y0, hy0, hy0e⟩ := mem_cj.1 hy
    have hc : k0 * k' = k' * k0 := hKcomm k0 hk0 k' hk'
    have e : k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = k' * (k0 * x0 * k0⁻¹) * k'⁻¹ := by
      calc k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = (k0 * k') * x0 * (k0 * k')⁻¹ := by group
        _ = (k' * k0) * x0 * (k' * k0)⁻¹ := by rw [hc]
        _ = _ := by group
    have key : k' * x0 * k'⁻¹ = y0 := by
      have h1 : k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = k0 * y0 * k0⁻¹ := by
        rw [e, hx0e, hk'xy, hy0e]
      have := congrArg (fun z => k0⁻¹ * z * k0) h1
      simpa [mul_assoc] using this
    have hx01 : x0 ≠ 1 := by
      intro h; apply hx1; rw [← hx0e, h]; group
    have hconj : cj k' A = A := hTI' k' hk' x0 hx0 hx01 (key ▸ hy0)
    have := hB k' hk' hconj
    have hy' : y ∈ cj k' B := mem_cj.2 ⟨x, hxB, hk'xy⟩
    exact this hy'
  set T : Set (Subgroup F) := {B | B ≤ L ∧ B ≠ ⊥ ∧ (∀ k ∈ K, cj k A = A → cj k B ≤ B) ∧
      Nat.card V ≤ val V B} with hTdef
  have hAT : A ∈ T := by
    refine ⟨hAL, hA1, ?_, hPA⟩
    intro k _ hk
    rw [hk]
  obtain ⟨B, ⟨hBL, hB1, hBinv, hPB⟩, hBmax⟩ := Set.exists_max_image T (fun B => Nat.card B)
    (Set.toFinite _) ⟨A, hAT⟩
  by_cases hBL' : B = L
  · rw [← hBL']; exact hPB
  exfalso
  obtain ⟨x, hxL, hxB⟩ : ∃ x ∈ L, x ∉ B := by
    by_contra h
    push Not at h
    exact hBL' (le_antisymm hBL h)
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ one_mem _)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have ha1 : (a : F) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨k, hk, hkax⟩ := hreg a (hAL a.2) ha1 x hxL hx1
  have hxA' : x ∈ cj k A := mem_cj.2 ⟨a, a.2, hkax⟩
  have hBA' : B ⊓ cj k A = ⊥ := by
    by_contra hne
    exact hxB (hT B hBinv k hk hne hxA')
  have hA'L : cj k A ≤ L := cjL k A hAL
  have hA'ne : cj k A ≠ ⊥ := fun h => hx1 (by simpa [h] using hxA')
  have hA'inv : ∀ k1 ∈ K, cj k1 A = A → cj k1 (cj k A) ≤ cj k A := by
    intro k1 hk1 hk1A
    apply le_of_eq
    rw [cj_cj, hKcomm k1 hk1 k hk, ← cj_cj, hk1A]
  have hcardA' : Nat.card (cj k A) = Nat.card A := card_cj k A
  have hcfA' : Nat.card (fixSub (V := V) (cj k A)) = Nat.card (fixSub (V := V) A) :=
    card_fixSub_cj k A
  have hsB := Lsup B (cj k A) hBL hA'L
  rw [hBA', Subgroup.card_bot, mul_one] at hsB
  have hfs := Vsup (fixSub (V := V) B) (fixSub (cj k A))
  have hfs2 : fixSub (V := V) B ⊓ fixSub (cj k A) ≤ fixSub (B ⊔ cj k A) := fixSub_sup _ _
  have he := AddSubgroup.card_le_of_le hfs2
  have hmemT : B ⊔ cj k A ∈ T := by
    refine ⟨sup_le hBL hA'L, fun h => hB1 (le_bot_iff.1 (h ▸ le_sup_left)), ?_, ?_⟩
    · intro k1 hk1 hk1A
      rw [cj_sup]
      exact sup_le_sup (hBinv k1 hk1 hk1A) (hA'inv k1 hk1 hk1A)
    · have hvA' : Nat.card V ≤ Nat.card (cj k A) * Nat.card (fixSub (V := V) (cj k A)) := by
        rw [hcardA', hcfA']; exact hPA
      unfold val at hPB ⊢
      rw [hsB]
      generalize Nat.card B = b at *
      generalize Nat.card (cj k A) = a' at *
      generalize Nat.card (fixSub (V := V) B) = fb at *
      generalize Nat.card (fixSub (V := V) (cj k A)) = fa at *
      generalize Nat.card (fixSub (V := V) (B ⊔ cj k A)) = fS at *
      generalize Nat.card (fixSub (V := V) B ⊓ fixSub (cj k A) : AddSubgroup V) = e at *
      generalize Nat.card V = v at *
      have h1 : v * v ≤ (b * a' * e) * v := by
        calc v * v ≤ (b * fb) * (a' * fa) := Nat.mul_le_mul hPB hvA'
          _ = b * a' * (fb * fa) := by ring
          _ ≤ b * a' * (e * v) := Nat.mul_le_mul_left _ hfs
          _ = (b * a' * e) * v := by ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hVpos
      calc v ≤ b * a' * e := h2
        _ ≤ b * a' * fS := Nat.mul_le_mul_left _ he
        _ = b * a' * fS := rfl
  have hlt := hBmax _ hmemT
  have hA2 : 1 < Nat.card (cj k A) := by
    rw [hcardA']; exact (Subgroup.one_lt_card_iff_ne_bot A).2 hA1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  rw [hsB] at hlt
  nlinarith


end FrobeniusFixedSpaceBounds


end CFSG.Timmesfeld.LocalTwoSubgroups

public section


namespace CFSG.Timmesfeld.LocalTwoSubgroups


section FaithfulAbelianActionBounds


open Representation


end FaithfulAbelianActionBounds


section RegularNonzeroActions


open Representation


end RegularNonzeroActions


end CFSG.Timmesfeld.LocalTwoSubgroups
