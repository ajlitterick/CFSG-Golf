module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.A1b

variable {G : Type*} [Group G]

namespace A1b

theorem conjSub_eq_iff_mem_normalizer {g : G} {H : Subgroup G} :
    conjSub g H = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  constructor
  · intro h x
    rw [← mem_conjSub_iff, h]
  · intro h
    ext x
    rw [mem_conjSub_iff]
    exact (h x).symm

end A1b

private theorem exists_of_pair {X : Subgroup G} (a b : G) (hne : conjSub b X ≠ conjSub a X)
    (h1 : conjSub b X ≤ Subgroup.normalizer (conjSub a X : Set G))
    (h2 : conjSub a X ≤ Subgroup.normalizer (conjSub b X : Set G)) :
    ∃ g : G, conjSub g X ≠ X ∧ conjSub g X ≤ Subgroup.normalizer (X : Set G) ∧
      X ≤ Subgroup.normalizer (conjSub g X : Set G) := by
  have hab : conjSub a (conjSub (a⁻¹ * b) X) = conjSub b X := by
    rw [← conjSub_mul, mul_inv_cancel_left]
  have haa : conjSub a⁻¹ (conjSub a X) = X := by
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  refine ⟨a⁻¹ * b, ?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hab, h]
  · rw [← conjSub_le_conjSub_iff a, hab, conjSub_normalizer]
    exact h1
  · rw [← conjSub_le_conjSub_iff a, conjSub_normalizer, hab]
    exact h2


theorem conjSubgroup_eq_conjSub (A : Subgroup G) (g : G) :
    conjSubgroup A g = conjSub g⁻¹ A := by
  ext x
  rw [mem_conjSubgroup_iff, mem_conjSub_iff]
  simp


section A116

variable [Finite G]

omit [Finite G] in
theorem quotient_inf_eq (Y : Subgroup G) [Y.Normal] {C D : Subgroup G} (hYD : Y ≤ D) :
    C ⊓ D = C ⊓ (C.map (QuotientGroup.mk' Y) ⊓ D.map (QuotientGroup.mk' Y)).comap
        (QuotientGroup.mk' Y) ∧
      C.map (QuotientGroup.mk' Y) ⊓ D.map (QuotientGroup.mk' Y) =
        (C ⊓ D).map (QuotientGroup.mk' Y) := by
  have key : ∀ c ∈ C, ∀ d ∈ D, QuotientGroup.mk' Y c = QuotientGroup.mk' Y d → c ∈ D := by
    intro c _ d hd hcd
    have h1 : d⁻¹ * c ∈ Y := QuotientGroup.eq.1 hcd.symm
    have : c = d * (d⁻¹ * c) := by group
    rw [this]
    exact D.mul_mem hd (hYD h1)
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_comap]
    constructor
    · rintro ⟨hxC, hxD⟩
      exact ⟨hxC, Subgroup.mem_map_of_mem _ hxC, Subgroup.mem_map_of_mem _ hxD⟩
    · rintro ⟨hxC, -, d, hd, hdx⟩
      exact ⟨hxC, key x hxC d hd hdx.symm⟩
  · refine le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
    rintro z ⟨⟨c, hc, rfl⟩, ⟨d, hd, hdc⟩⟩
    exact ⟨c, ⟨hc, key c hc d hd hdc.symm⟩, rfl⟩

theorem isSylowIn_top {p : ℕ} [Fact p.Prime] (C : Sylow p G) :
    IsSylowIn p (C : Subgroup G) ⊤ := by
  refine isSylowIn_of_card_eq le_top ?_
  rw [Subgroup.card_top]
  exact Sylow.card_eq_multiplicity C

theorem isSylowIn_inf_of_quotient (Y : Subgroup G) [Y.Normal] {D : Subgroup G} (hYD : Y ≤ D)
    (C : Sylow 2 G)
    (h : IsSylowIn 2 ((C : Subgroup G).map (QuotientGroup.mk' Y) ⊓ D.map (QuotientGroup.mk' Y))
      (D.map (QuotientGroup.mk' Y))) :
    IsSylowIn 2 ((C : Subgroup G) ⊓ D) D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Y with hπ
  set Cs : Subgroup G := (C : Subgroup G) with hCs
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hrel : ∀ K : Subgroup G, Y.relIndex K = Nat.card (K.map π) := fun K =>
    (congrArg (fun L => L.relIndex K) hker).symm.trans (Subgroup.relIndex_ker (K := K) π)
  have hmap : (Cs ⊓ D).map π = Cs.map π ⊓ D.map π :=
    ((quotient_inf_eq Y (C := Cs) hYD).2).symm
  have hCD : Nat.card ↥(Cs ⊓ D) = Nat.card ↥(Cs.map π ⊓ D.map π) * Nat.card ↥(Cs ⊓ Y) := by
    have e : Y ⊓ (Cs ⊓ D) = Cs ⊓ Y := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hy, hc, _⟩
        exact ⟨hc, hy⟩
      · rintro ⟨hc, hy⟩
        exact ⟨hy, hc, hYD hy⟩
    have h1 := Subgroup.relIndex_mul_card (H := Y) (K := Cs ⊓ D)
    rw [e, hrel, hmap] at h1
    exact h1.symm
  have hD : Nat.card ↥D = Nat.card ↥(D.map π) * Nat.card ↥Y := by
    have h1 := Subgroup.relIndex_mul_card (H := Y) (K := D)
    rw [inf_eq_left.2 hYD, hrel] at h1
    exact h1.symm
  have hY : IsSylowIn 2 (Cs ⊓ Y) Y := (isSylowIn_top C).inf_normal le_top inferInstance
  have h2 := h.card_eq
  have h3 := hY.card_eq
  refine isSylowIn_of_card_eq inf_le_right ?_
  rw [hCD, h2, h3, hD, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp only [Finsupp.add_apply, pow_add]

end A116

section AxB

variable {p : ℕ} [hp : Fact p.Prime] {X K : Type*} [Group X] [Finite X] [Group K] [Finite K]

theorem thompson_AxB_element (hX : IsPGroup p X) (ρ : K →* MulAut X) {B : Subgroup K}
    (hB : IsPGroup p (B.map ρ)) {a : K} (ha : (orderOf a).Coprime p)
    (hcomm : ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a)
    (h : ∀ x : X, (∀ b ∈ B, ρ b x = x) → ρ a x = x) : ρ a = 1 := by
  have hcard : ¬ p ∣ Nat.card (Subgroup.zpowers a) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 ha.symm
  have key := CFSG.GroupTheory.thompson_A_times_B (p := p) (R := X) (A := Subgroup.zpowers a)
    (B := B.map ρ) hX hcard hB (ρ.comp (Subgroup.zpowers a).subtype) (B.map ρ).subtype ?_ ?_
  · exact key ⟨a, Subgroup.mem_zpowers a⟩
  · rintro ⟨a', ha'⟩ ⟨b', hb'⟩
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    have hc : Commute (ρ a) (ρ b) := hcomm b hb
    have := (hc.zpow_left k).eq
    simpa [map_zpow] using this
  · rintro ⟨a', ha'⟩ x hx
    have hfix : ρ a x = x := h x fun b hb => hx ⟨ρ b, Subgroup.mem_map_of_mem _ hb⟩
    let St : Subgroup K := (MulAction.stabilizer (MulAut X) x).comap ρ
    have haSt : a ∈ St := by
      change ρ a ∈ MulAction.stabilizer (MulAut X) x
      rw [MulAction.mem_stabilizer_iff]
      exact hfix
    have := (Subgroup.zpowers_le.2 haSt) ha'
    change ρ a' ∈ MulAction.stabilizer (MulAut X) x at this
    rwa [MulAction.mem_stabilizer_iff] at this

theorem thompson_AxB_one (hX : IsPGroup p X) (ρ : K →* MulAut X) {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) (hB : IsPGroup p (B.map ρ))
    (hA : opResidual p A = A)
    (h : ∀ a ∈ A, ∀ x : X, (∀ b ∈ B, ρ b x = x) → ρ a x = x) : ∀ a ∈ A, ρ a = 1 := by
  intro a ha
  have hle : A ≤ ρ.ker := by
    calc A = opResidual p A := hA.symm
      _ ≤ ρ.ker := by
        rw [opResidual, Subgroup.closure_le]
        rintro x ⟨hxA, hxc⟩
        exact MonoidHom.mem_ker.2 (thompson_AxB_element hX ρ hB hxc (hcomm x hxA) (h x hxA))
  exact MonoidHom.mem_ker.1 (hle ha)

theorem thompson_AxB_two (hX : IsPGroup p X) (ρ : K →* MulAut X) {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) (hB : IsPGroup p (B.map ρ))
    (hfaith : ∀ a ∈ A, ρ a = 1 → a = 1) (hOp : pCoreOf p A = ⊥) :
    ∀ a ∈ A, (∀ x : X, (∀ b ∈ B, ρ b x = x) → ρ a x = x) → a = 1 := by
  let A₀ : Subgroup K :=
    { carrier := {a | a ∈ A ∧ ∀ x : X, (∀ b ∈ B, ρ b x = x) → ρ a x = x}
      mul_mem' := fun {a a'} ha ha' => ⟨A.mul_mem ha.1 ha'.1, fun x hx => by
        rw [map_mul, MulAut.mul_apply, ha'.2 x hx, ha.2 x hx]⟩
      one_mem' := ⟨A.one_mem, fun x _ => by rw [map_one, MulAut.one_apply]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun x hx => by
        have h1 := ha.2 x hx
        rw [map_inv]
        calc (ρ a)⁻¹ x = (ρ a)⁻¹ (ρ a x) := by rw [h1]
          _ = x := MulAut.inv_apply_self X (ρ a) x⟩ }
  have hA₀A : A₀ ≤ A := fun a ha => ha.1
  have hA₀n : (A₀.subgroupOf A).Normal := by
    refine ⟨fun a₀ ha₀ g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha₀ ⊢
    refine ⟨A.mul_mem (A.mul_mem g.2 ha₀.1) (A.inv_mem g.2), fun x hx => ?_⟩
    have hy : ∀ b ∈ B, ρ b (ρ (g : K)⁻¹ x) = ρ (g : K)⁻¹ x := by
      intro b hb
      have hcg := hcomm (g : K)⁻¹ (A.inv_mem g.2) b hb
      have := congrArg (fun φ : MulAut X => φ x) hcg
      simp only [MulAut.mul_apply] at this
      rw [← this, hx b hb]
    have h2 := ha₀.2 _ hy
    change ρ ((g : K) * (a₀ : K) * (g : K)⁻¹) x = x
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h2, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply]
  have hA₀p : IsPGroup p A₀ := by
    refine CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one (p := p) fun a ha => ?_
    have ha' : (orderOf (a : K)).Coprime p := by
      rw [← Subgroup.orderOf_coe a] at ha
      exact ha
    apply Subtype.ext
    exact hfaith a a.2.1 (thompson_AxB_element hX ρ hB ha' (hcomm a a.2.1) a.2.2)
  have hle : A₀ ≤ pCoreOf p A := le_pCoreOf p hA₀A hA₀n hA₀p
  rw [hOp] at hle
  intro a ha h
  exact Subgroup.mem_bot.1 (hle ⟨ha, h⟩)

end AxB

end CFSG.Quasithin
