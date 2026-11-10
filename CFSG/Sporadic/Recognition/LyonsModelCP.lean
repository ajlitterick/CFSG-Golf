module

public import CFSG.Sporadic.Recognition.LyonsModelArr
public import CFSG.Sporadic.Recognition.LyonsModelCount
public import CFSG.Sporadic.Recognition.LyonsModelCP3Fact

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier Equiv
  Subgroup


section Sets

variable {D : Cp3Data}


def fam (D : Cp3Data) : Set (Set (Fin deg)) := {S | ∃ i < 15400, S = setOfArr D.sets[i]!}


end Sets

abbrev UYperm : Subgroup (Perm (Fin deg)) := closure (Set.range fun j : Fin 4 => uG j.val)


theorem UYperm_le_B0 : UYperm ≤ B0 := by
  refine (closure_le B0).2 ?_
  rintro _ ⟨j, rfl⟩
  exact uG_mem_B0 j.val

theorem gcG_mem_B0 : gcG ∈ B0 := by
  rw [gcG_def]
  exact wG_mem B0 gens0 2 gens0_mem _ (decodeWord_mem _)

section Orbit

variable {D : Cp3Data}


end Orbit

theorem fix_conj (g y : Perm (Fin deg)) :
    {i | (g * y * g⁻¹) i = i} = g '' {i | y i = i} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
  constructor
  · intro hi
    refine ⟨g⁻¹ i, ?_, by simp⟩
    have h2 := congrArg (⇑(g⁻¹ : Perm (Fin deg))) hi
    simpa using h2
  · rintro ⟨j, hj, rfl⟩
    simp [hj]


theorem conj_y0G_of_mem_normalizer (h : tabCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) {n : Perm (Fin deg)}
    (hn : n ∈ normalizer (zpowers y0G : Set (Perm (Fin deg)))) :
    n * y0G * n⁻¹ = y0G ∨ n * y0G * n⁻¹ = y0G⁻¹ := by
  obtain ⟨-, h3, h1, -⟩ := cp1_facts h hs hc1
  have hfin : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  have hmem := (mem_normalizer_zpowers_iff_of_isOfFinOrder hfin).1 hn
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rcases zpow_cases h3 k with e | e | e
  · exfalso
    apply h1
    have : n * y0G * n⁻¹ = 1 := by rw [← hk, e]
    have h2 : y0G = n⁻¹ * (n * y0G * n⁻¹) * n := by group
    rw [h2, this]
    group
  · left; rw [← hk, e]
  · right
    rw [← hk, e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h3

theorem cp3_perm (hv : Cp3Fact) (hB : Nat.card B0 = 5388768000)
    (hN : Nat.card ↥(B0 ⊓ normalizer (zpowers y0G : Set (Perm (Fin deg)))) = 349920)
    {g w : Perm (Fin deg)} (hg : g ∈ B0) (hw : w = g * y0G * g⁻¹) (hcomm : w * y0G = y0G * w)
    (hne1 : w ≠ y0G) (hne2 : w ≠ y0G⁻¹) :
    ∃ u ∈ UYperm, u * w * u⁻¹ = w0G ∨ u * w * u⁻¹ = w0G⁻¹ :=
  hv hB hN g hg w hw hcomm hne1 hne2

theorem mem_zpowers_B0_iff {a : B0} {x : B0} {a' x' : Perm (Fin deg)}
    (ha : (a : Perm (Fin deg)) = a') (hx : (x : Perm (Fin deg)) = x') :
    x ∈ zpowers a ↔ x' ∈ zpowers a' := by
  subst ha hx
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem mem_Y0_iff (h : tabCheck = true) (hs : structCheck = true) (hc1 : cp1Check = true)
    {b : B0} :
    b ∈ Y0 ↔ (b : Perm (Fin deg)) ∈ normalizer (zpowers y0G : Set (Perm (Fin deg))) := by
  obtain ⟨-, h3, -⟩ := cp1_facts h hs hc1
  have hf1 : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  have hf2 : IsOfFinOrder yB := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_yB]
    exact h3
  rw [mem_normalizer_zpowers_iff_of_isOfFinOrder hf1,
    mem_normalizer_zpowers_iff_of_isOfFinOrder hf2,
    mem_zpowers_B0_iff (a := yB) (x := b * yB * b⁻¹) rfl rfl]
  rfl

theorem UYperm_le_normalizer (h : tabCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) (hi : invCheck = true) :
    UYperm ≤ normalizer (zpowers y0G : Set (Perm (Fin deg))) := by
  obtain ⟨-, h3, -⟩ := cp1_facts h hs hc1
  have hf1 : IsOfFinOrder y0G := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3⟩
  obtain ⟨-, -, -, hu⟩ := invCheck_spec h hs hi
  refine (closure_le _).2 ?_
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_normalizer_zpowers_iff_of_isOfFinOrder hf1]
  show uG j.val * y0G * (uG j.val)⁻¹ ∈ zpowers y0G
  rw [mul_assoc]
  rcases hu j.val j.isLt with e | e
  · rw [e]; exact mem_zpowers _
  · rw [e]; exact inv_mem (mem_zpowers _)

theorem UY_le_Y0 (h : tabCheck = true) (hs : structCheck = true) (hc1 : cp1Check = true)
    (hi : invCheck = true) : UY ≤ Y0 := by
  intro b hb
  rw [mem_Y0_iff h hs hc1]
  exact UYperm_le_normalizer h hs hc1 hi hb

section


theorem cp3_model (h : tabCheck = true) (hc : coverCheck = true) (hs : structCheck = true)
    (hc1 : cp1Check = true) (hv : Cp3Fact) {g w : B0} (hw : w = g * yB * g⁻¹)
    (hy : w * yB = yB * w) (hne1 : w ≠ yB) (hne2 : w ≠ yB⁻¹)
    (hN : Nat.card ↥(normalizer (zpowers yB : Set B0)) = 349920) :
    ∃ u ∈ UY, u * w * u⁻¹ = wB ∨ u * w * u⁻¹ = wB⁻¹ := by
  have hN' : Nat.card ↥(B0 ⊓ normalizer (zpowers y0G : Set (Perm (Fin deg)))) = 349920 := by
    rw [← hN]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, (mem_Y0_iff h hs hc1).2 x.2.2⟩
        invFun := fun b => ⟨b.1.1, b.1.2, (mem_Y0_iff h hs hc1).1 b.2⟩
        left_inv := fun x => rfl
        right_inv := fun b => rfl }
  have hw' : (w : Perm (Fin deg)) = (g : Perm (Fin deg)) * y0G * (g : Perm (Fin deg))⁻¹ := by
    rw [hw]; rfl
  have hy' : (w : Perm (Fin deg)) * y0G = y0G * (w : Perm (Fin deg)) := by
    have := congrArg Subtype.val hy
    exact this
  have hne1' : (w : Perm (Fin deg)) ≠ y0G := fun e => hne1 (Subtype.ext e)
  have hne2' : (w : Perm (Fin deg)) ≠ y0G⁻¹ := fun e => hne2 (Subtype.ext e)
  obtain ⟨u, hu, hue⟩ := cp3_perm hv (card_B0 h hc hs) hN' g.2 hw' hy' hne1' hne2'
  refine ⟨⟨u, UYperm_le_B0 hu⟩, hu, ?_⟩
  rcases hue with e | e
  · left; exact Subtype.ext e
  · right; exact Subtype.ext e

end

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
