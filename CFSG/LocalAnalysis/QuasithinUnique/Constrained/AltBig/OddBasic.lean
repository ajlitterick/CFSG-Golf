module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Basic

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]

theorem even_card_of_closed_odd (p : OddInv α) (S : Set α) (hS : ∀ x ∈ S, p.μ x ∈ S)
    (hω : p.ω ∉ S) : Even (Nat.card S) := by
  classical
  have hiff : ∀ x, p.μ x ∈ S ↔ x ∈ S := fun x =>
    ⟨fun hx => by simpa [p.inv] using hS _ hx, hS x⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Perm S, ∀ x : S, ((σ x : S) : α) = p.μ x :=
    ⟨Equiv.Perm.subtypePerm (p := fun x => x ∈ S) p.μ hiff, fun x => rfl⟩
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσ, p.inv]
  have hfix : ∀ x : S, σ x ≠ x := by
    intro x hx
    have hxω : (x : α) ≠ p.ω := fun h => hω (by rw [← h]; exact x.2)
    apply p.fpf x.1 hxω
    have h := congrArg Subtype.val hx
    rw [hσ] at h
    exact h
  have hsupp : σ.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Equiv.Perm.mem_support]
    exact hfix x
  have h2 := Equiv.Perm.two_dvd_card_support hσ2
  rw [hsupp, Finset.card_univ] at h2
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.mpr h2


private theorem ao4_exists_z (p : OddInv α) (h7 : 7 ≤ Fintype.card α) (x b : α) :
    ∃ z, z ≠ p.ω ∧ z ≠ x ∧ z ≠ p.μ x ∧ z ≠ b ∧ z ≠ p.μ b := by
  have hcard : ({p.ω, x, p.μ x, b, p.μ b} : Finset α).card < Fintype.card α :=
    lt_of_le_of_lt Finset.card_le_five (by omega)
  obtain ⟨z, hz⟩ := th3_exists_not_mem hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  exact ⟨z, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩

theorem block_closed_odd (p : OddInv α) (h7 : 7 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {B : Set α} (hBl : MulAction.IsBlock (↥Y) B)
    (h2 : ∃ a ∈ B, ∃ b ∈ B, a ≠ b) : ∀ x ∈ B, x ≠ p.ω → p.μ x ∈ B := by
  intro x hx hxω
  by_contra hnot
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ B, b ≠ x := by
    obtain ⟨a, ha, c, hc, hac⟩ := h2
    by_cases hax : a = x
    · exact ⟨c, hc, fun hcx => hac (hax.trans hcx.symm)⟩
    · exact ⟨a, ha, hax⟩
  have hbμ : b ≠ p.μ x := fun h => hnot (by rw [← h]; exact hb)
  obtain ⟨z, hzω, hzx, hzμx, hzb, hzμb⟩ := ao4_exists_z p h7 x b
  have hσY : swap x (p.μ x) * swap z (p.μ z) ∈ Y := hB x z hxω hzω hzx hzμx
  have hbμz : b ≠ p.μ z := fun h => hzμb (by rw [h, p.inv])
  have hxμz : x ≠ p.μ z := fun h => hzμx (by rw [h, p.inv])
  have hσb : (swap x (p.μ x) * swap z (p.μ z)) b = b := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hzb) hbμz,
      swap_apply_of_ne_of_ne hbx hbμ]
  have hσx : (swap x (p.μ x) * swap z (p.μ z)) x = p.μ x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hzx) hxμz, swap_apply_left]
  have hσbB : (swap x (p.μ x) * swap z (p.μ z)) b ∈ B := by
    rw [hσb]
    exact hb
  have hx' := altBigBlockFact hBl hσY hb hσbB x hx
  rw [hσx] at hx'
  exact hnot hx'

theorem preprimitive_odd (p : OddInv α) (h7 : 7 ≤ Fintype.card α) (hodd : Odd (Fintype.card α))
    {Y : Subgroup (Perm α)} (hB : p.Contained Y) (htr : MulAction.IsPretransitive (↥Y) α) :
    MulAction.IsPreprimitive (↥Y) α := by
  refine { toIsPretransitive := htr, isTrivialBlock_of_isBlock := ?_ }
  intro B hBl
  unfold MulAction.IsTrivialBlock
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  right
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
    by_contra hcon
    exact hne (Set.eq_univ_of_forall fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Y) z p.ω
  have hωB' : p.ω ∉ g • B := by
    intro h
    obtain ⟨y, hy, hgy⟩ := Set.mem_smul_set.mp h
    have hyz : y = z := (smul_left_cancel_iff g).mp (hgy.trans hg.symm)
    exact hz (by rw [← hyz]; exact hy)
  have hnt : ∃ a ∈ B, ∃ b ∈ B, a ≠ b := Set.not_subsingleton_iff.mp hs
  obtain ⟨a, ha, c, hc, hac⟩ := hnt
  have hblk : MulAction.IsBlock (↥Y) (g • B) := hBl.translate g
  have h2' : ∃ a' ∈ g • B, ∃ b' ∈ g • B, a' ≠ b' :=
    ⟨g • a, Set.smul_mem_smul_set ha, g • c, Set.smul_mem_smul_set hc,
      fun h => hac ((smul_left_cancel_iff g).mp h)⟩
  have hclos : ∀ w ∈ g • B, p.μ w ∈ g • B := fun w hw =>
    block_closed_odd p h7 hB hblk h2' w hw (fun hwω => hωB' (by rw [← hwω]; exact hw))
  have heven : Even (Nat.card ↥(g • B)) := even_card_of_closed_odd p (g • B) hclos hωB'
  have hne' : (g • B).Nonempty := ⟨g • a, Set.smul_mem_smul_set ha⟩
  have hdvd : (g • B).ncard ∣ Nat.card α := hblk.ncard_dvd_card hne'
  have hodd' : Odd (Nat.card α) := by
    rw [Nat.card_eq_fintype_card]
    exact hodd
  have hoddB : Odd (g • B).ncard := Odd.of_dvd_nat hodd' hdvd
  have hcard : Nat.card ↥(g • B) = (g • B).ncard := Nat.card_coe_set_eq (g • B)
  obtain ⟨k, hk⟩ := heven
  obtain ⟨j, hj⟩ := hoddB
  omega

private theorem ao5_core {G : Type*} [Group G] {A B R V : G}
    (hRA : R * A = A * R) (hRB : R * B = B * R) (hRV : R * V = V * R)
    (hVA : V * A = A * V) (hVB : V * B = B * V) (hR2 : R * R = 1) (hV2 : V * V = 1) :
    A * R * (B * V) * (A * R) * (B * V) = A * B * (A * B) := by
  have hX : A * R * (B * V) = A * B * (R * V) := by
    calc A * R * (B * V) = A * (R * B) * V := by simp only [mul_assoc]
      _ = A * (B * R) * V := by rw [hRB]
      _ = A * B * (R * V) := by simp only [mul_assoc]
  have hY : R * V * (A * B) = A * B * (R * V) := by
    calc R * V * (A * B) = R * (V * A) * B := by simp only [mul_assoc]
      _ = R * (A * V) * B := by rw [hVA]
      _ = R * A * (V * B) := by simp only [mul_assoc]
      _ = A * R * (V * B) := by rw [hRA]
      _ = A * R * (B * V) := by rw [hVB]
      _ = A * B * (R * V) := hX
  have hsq : R * V * (R * V) = 1 := by
    calc R * V * (R * V) = R * (V * R) * V := by simp only [mul_assoc]
      _ = R * (R * V) * V := by rw [hRV]
      _ = R * R * (V * V) := by simp only [mul_assoc]
      _ = 1 := by rw [hR2, hV2, mul_one]
  calc A * R * (B * V) * (A * R) * (B * V)
      = (A * R * (B * V)) * (A * R * (B * V)) := by simp only [mul_assoc]
    _ = (A * B * (R * V)) * (A * B * (R * V)) := by rw [hX]
    _ = (A * B) * (R * V * (A * B)) * (R * V) := by simp only [mul_assoc]
    _ = (A * B) * (A * B * (R * V)) * (R * V) := by rw [hY]
    _ = (A * B) * (A * B) * (R * V * (R * V)) := by simp only [mul_assoc]
    _ = A * B * (A * B) := by rw [hsq, mul_one]

theorem three_cycle_odd (p : OddInv α) (h9 : 9 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {n : Perm α} (hn : n ∈ Y) (hnω : n p.ω ≠ p.ω) :
    ∃ g ∈ Y, g.IsThreeCycle := by
  have hB2 : ∀ u v : α, u ≠ p.ω → v ≠ p.ω → v ≠ u → v ≠ p.μ u →
      swap u (p.μ u) * swap v (p.μ v) ∈ Y := hB
  have hmu : ∀ u v : α, p.μ u = v → u = p.μ v := by
    intro u v h
    subst h
    exact (p.inv u).symm
  have hμinj : ∀ u v : α, p.μ u = p.μ v → u = v := fun u v h =>
    (p.inv u).symm.trans ((congrArg p.μ h).trans (p.inv v))
  have hinv : ∀ u v : α, n u = v → u = n⁻¹ v := by
    intro u v h
    subst h
    simp
  obtain ⟨x, hx⟩ : ∃ x : α, x = n p.ω := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : α, x' = p.μ x := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : α, a = n⁻¹ x' := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : α, w = n (p.μ a) := ⟨_, rfl⟩
  have hxω : x ≠ p.ω := fun h => hnω (by rw [← hx]; exact h)
  have hx'x : x' ≠ x := by
    rw [hx']
    exact p.fpf x hxω
  have hna : n a = x' := by
    rw [ha]
    simp
  have hμx' : p.μ x' = x := by
    rw [hx']
    exact p.inv x
  have haω : a ≠ p.ω := by
    intro h
    apply hx'x
    rw [← hna, h]
    exact hx.symm
  have hμa : p.μ a ≠ a := p.fpf a haω
  have hwx' : w ≠ x' := fun h => hμa (n.injective (hw.symm.trans (h.trans hna.symm)))
  have hwx : w ≠ x := fun h =>
    haω ((p.mu_eq_omega_iff).1 (n.injective (hw.symm.trans (h.trans hx))))
  obtain ⟨r, hr⟩ := th3_exists_not_mem (S := ({p.ω, x, x', w, p.μ w} : Finset α)) (by
    have h5 : ({p.ω, x, x', w, p.μ w} : Finset α).card ≤ 5 := Finset.card_le_five
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hrω, hrx, hrx', hrw, hrμw⟩ := hr
  have hμrx : p.μ r ≠ x := fun h => hrx' ((hmu r x h).trans hx'.symm)
  have hμrx' : p.μ r ≠ x' := fun h => hrx ((hmu r x' h).trans hμx')
  have hμrw : p.μ r ≠ w := fun h => hrμw (hmu r w h)
  have hδ₁ : swap x x' * swap r (p.μ r) ∈ Y := by
    have h := hB2 x r hxω hrω hrx (by rw [← hx']; exact hrx')
    rw [← hx'] at h
    exact h
  obtain ⟨b, hb⟩ := th3_exists_not_mem
    (S := ({p.ω, a, p.μ a, n⁻¹ r, n⁻¹ (p.μ r), p.μ (n⁻¹ r), p.μ (n⁻¹ (p.μ r))} : Finset α))
    (by
      have h6 : ({a, p.μ a, n⁻¹ r, n⁻¹ (p.μ r), p.μ (n⁻¹ r), p.μ (n⁻¹ (p.μ r))} :
          Finset α).card ≤ 6 := Finset.card_le_six
      have h7 := Finset.card_insert_le p.ω
        ({a, p.μ a, n⁻¹ r, n⁻¹ (p.μ r), p.μ (n⁻¹ r), p.μ (n⁻¹ (p.μ r))} : Finset α)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨hbω, hba, hbμa, hbnr, hbnμr, hbμnr, hbμnμr⟩ := hb
  have hbnr' : n b ≠ r := fun h => hbnr (hinv b r h)
  have hbnμr' : n b ≠ p.μ r := fun h => hbnμr (hinv b (p.μ r) h)
  have hbμnr' : n (p.μ b) ≠ r := fun h => hbμnr (hmu b _ (hinv (p.μ b) r h))
  have hbμnμr' : n (p.μ b) ≠ p.μ r := fun h => hbμnμr (hmu b _ (hinv (p.μ b) (p.μ r) h))
  have hv1x : n b ≠ x := fun h => hbω (n.injective (h.trans hx))
  have hv1x' : n b ≠ x' := fun h => hba (n.injective (h.trans hna.symm))
  have hv1w : n b ≠ w := fun h => hbμa (n.injective (h.trans hw))
  have hv2x : n (p.μ b) ≠ x :=
    fun h => hbω ((p.mu_eq_omega_iff).1 (n.injective (h.trans hx)))
  have hv2x' : n (p.μ b) ≠ x' := fun h => hbμa (hmu b a (n.injective (h.trans hna.symm)))
  have hv2w : n (p.μ b) ≠ w := fun h => hba (hμinj b a (n.injective (h.trans hw)))
  have hconj : n * (swap a (p.μ a) * swap b (p.μ b)) * n⁻¹
      = swap (n a) (n (p.μ a)) * swap (n b) (n (p.μ b)) := by
    rw [Equiv.swap_apply_apply n a (p.μ a), Equiv.swap_apply_apply n b (p.μ b)]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hδ₂ : swap x' w * swap (n b) (n (p.μ b)) ∈ Y := by
    have h := Y.mul_mem (Y.mul_mem hn (hB2 a b haω hbω hba hbμa)) (Y.inv_mem hn)
    rw [hconj, hna, ← hw] at h
    exact h
  have hRA : swap r (p.μ r) * swap x x' = swap x x' * swap r (p.μ r) :=
    th3_swap_commute hrx hrx' hμrx hμrx'
  have hRB : swap r (p.μ r) * swap x' w = swap x' w * swap r (p.μ r) :=
    th3_swap_commute hrx' hrw hμrx' hμrw
  have hRV : swap r (p.μ r) * swap (n b) (n (p.μ b))
      = swap (n b) (n (p.μ b)) * swap r (p.μ r) :=
    th3_swap_commute hbnr'.symm hbμnr'.symm hbnμr'.symm hbμnμr'.symm
  have hVA : swap (n b) (n (p.μ b)) * swap x x' = swap x x' * swap (n b) (n (p.μ b)) :=
    th3_swap_commute hv1x hv1x' hv2x hv2x'
  have hVB : swap (n b) (n (p.μ b)) * swap x' w = swap x' w * swap (n b) (n (p.μ b)) :=
    th3_swap_commute hv1x' hv1w hv2x' hv2w
  have hc : (swap x x' * swap x' w).IsThreeCycle := by
    rw [Equiv.swap_comm x x']
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hx'x hwx'.symm hwx.symm
  have hgY := Y.mul_mem (Y.mul_mem (Y.mul_mem hδ₁ hδ₂) hδ₁) hδ₂
  refine ⟨_, hgY, ?_⟩
  rw [ao5_core hRA hRB hRV hVA hVB (Equiv.swap_mul_self r (p.μ r))
    (Equiv.swap_mul_self (n b) (n (p.μ b)))]
  exact Equiv.Perm.IsThreeCycle.isThreeCycle_sq hc

theorem alt_le_odd (p : OddInv α) (h9 : 9 ≤ Fintype.card α) (hodd : Odd (Fintype.card α))
    {Y : Subgroup (Perm α)} (hB : p.Contained Y) (htr : MulAction.IsPretransitive (↥Y) α) :
    alternatingGroup α ≤ Y := by
  have hprim := preprimitive_odd p (by omega) hodd hB htr
  obtain ⟨z, hz⟩ : ∃ z : α, z ≠ p.ω := by
    by_contra h
    push_neg at h
    have : Fintype.card α ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    omega
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥Y) p.ω z
  have hnω : (n : Perm α) p.ω ≠ p.ω := by
    intro h
    apply hz
    rw [← hn]
    exact h
  obtain ⟨g, hg, h3⟩ := three_cycle_odd p h9 hB n.2 hnω
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hg

end CFSG.QuasithinUnique.L246C127.AltBig
