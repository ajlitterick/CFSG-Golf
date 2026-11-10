module

public import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin

section Pure

variable {E : Type*} [CommGroup E]

theorem conj_pair_apply_eq (hE : ∀ e : E, e * e = 1) {C : Subgroup E} {b s : MulAut E}
    (hbC : ∀ c ∈ C, b c = c) (hsC : ∀ c ∈ C, s c = c) {p : E} (hbp : b p * p⁻¹ ∈ C)
    (hsp : s p * p⁻¹ ∈ C) : (b * s * b * s⁻¹) p = p := by
  obtain ⟨cb, hcbC, hb⟩ : ∃ cb ∈ C, b p = cb * p :=
    ⟨b p * p⁻¹, hbp, by rw [inv_mul_cancel_right]⟩
  obtain ⟨cs, hcsC, hs⟩ : ∃ cs ∈ C, s p = cs * p :=
    ⟨s p * p⁻¹, hsp, by rw [inv_mul_cancel_right]⟩
  have hss : cs * cs = 1 := hE cs
  have hbb : cb * cb = 1 := hE cb
  have h1 : s (cs * p) = p := by
    rw [map_mul, hsC cs hcsC, hs, ← mul_assoc, hss, one_mul]
  have hsinv : s⁻¹ p = cs * p := by
    have h2 := MulAut.inv_apply_self E s (cs * p)
    rwa [h1] at h2
  have e1 : b (cs * p) = cs * (cb * p) := by rw [map_mul, hbC cs hcsC, hb]
  have e2 : s (cs * (cb * p)) = cb * p := by
    rw [map_mul, map_mul, hsC cs hcsC, hsC cb hcbC, hs, mul_left_comm cb cs p, ← mul_assoc, hss,
      one_mul]
  have e3 : b (cb * p) = p := by rw [map_mul, hbC cb hcbC, hb, ← mul_assoc, hbb, one_mul]
  simp only [MulAut.mul_apply]
  rw [hsinv, e1, e2, e3]


end Pure

theorem isFFModule_of_comap {E : Type*} [CommGroup E] [Finite E] {Q : Type*} [Group Q]
    (β : E →* Q) (hβs : Function.Surjective β) {X A : Subgroup (MulAut E)} (hAX : A ≤ X)
    (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) (P : Subgroup Q) (hidx : P.index ≤ Nat.card A)
    (hfix : ∀ v : E, β v ∈ P → ∀ a ∈ A, a v = v) : IsFFModule X := by
  refine ⟨A, hAX, hA1, hAe, ?_⟩
  have hle : P.comap β ≤ fixV A := fun v hv a ha => hfix v hv a ha
  have h1 := Subgroup.card_mul_index (P.comap β)
  rw [Subgroup.index_comap_of_surjective P hβs] at h1
  have h2 := Subgroup.card_le_of_le hle
  calc Nat.card E = Nat.card ↥(P.comap β) * P.index := h1.symm
    _ ≤ Nat.card ↥(fixV A) * Nat.card ↥A := Nat.mul_le_mul h2 hidx
    _ = Nat.card ↥A * Nat.card ↥(fixV A) := mul_comm _ _

theorem index_le_of_injective {Q : Type*} [Group Q] [Finite Q] (P : Subgroup Q) {A : Type*}
    [Finite A] (f : Q → A × ↥P) (hf : Function.Injective f) : P.index ≤ Nat.card A := by
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at h1
  have h2 := Subgroup.card_mul_index P
  have hpos : 0 < Nat.card ↥P := Nat.card_pos
  have h3 : Nat.card ↥P * P.index ≤ Nat.card ↥P * Nat.card A := by
    rw [h2, mul_comm]
    exact h1
  exact Nat.le_of_mul_le_mul_left h3 hpos

section Realization

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}

@[expose] def restrictHom (hLs : L ≤ stabSub V) {Γ : Type*} [Group Γ] (π : Γ →* ↥L) :
    Γ →* MulAut ↥V :=
  (resHom V).comp ((Subgroup.inclusion hLs).comp π)

theorem restrictHom_mem_autSub (hLs : L ≤ stabSub V) {Γ : Type*} [Group Γ] (π : Γ →* ↥L)
    (γ : Γ) : restrictHom hLs π γ ∈ autSub L V :=
  mem_autSub.mpr ⟨Subgroup.inclusion hLs (π γ), (π γ).2, rfl⟩

theorem restrictHom_injective {D : FFModel} (hD : D.Faithful) (hLs : L ≤ stabSub V) {Z : Subgroup W}
    {π : D.Gam →* ↥L} (hπ : D.RealizesVia L V Z π) : Function.Injective (restrictHom hLs π) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  by_contra hne
  obtain ⟨u, hu, hmov⟩ := G64.RealizesVia.exists_moved hD hπ hne
  apply hmov
  have h1 : ((π γ : ↥L) : MulAut W) u = u := by
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : W)) hγ
    exact this
  rw [h1, mul_inv_cancel]
  exact Z.one_mem

theorem isFFModule_of_realizesVia [Finite W] {D : FFModel} (hD : D.Faithful)
    (hLs : L ≤ stabSub V) {Z : Subgroup W} {π : D.Gam →* ↥L} (hπ : D.RealizesVia L V Z π)
    {Q : Type*} [Group Q] (β : ↥V →* Q) (hβs : Function.Surjective β) (A₀ : Subgroup D.Gam)
    (hA₀c : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hA₀2 : ∀ a ∈ A₀, a * a = 1) (hA₀1 : A₀ ≠ ⊥)
    (P : Subgroup Q) (hidx : P.index ≤ Nat.card ↥A₀)
    (hfix : ∀ v : ↥V, β v ∈ P → ∀ a ∈ A₀, ((π a : ↥L) : MulAut W) (v : W) = v) :
    IsFFModule (autSub L V) := by
  have hinj := restrictHom_injective hD hLs hπ
  set ρ := restrictHom hLs π with hρ
  refine isFFModule_of_comap β hβs (A := A₀.map ρ) ?_ ?_ ⟨?_, ?_⟩ P ?_ ?_
  · rintro _ ⟨a, -, rfl⟩
    exact restrictHom_mem_autSub hLs π a
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA₀c a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, sq, hA₀2 a ha, map_one]
  · rwa [Subgroup.card_map_of_injective hinj]
  · rintro v hv _ ⟨a, ha, rfl⟩
    exact Subtype.ext (hfix v hv a ha)

theorem conj_pair_apply_eq_of_lift (hW : ∀ w : W, w * w = 1) {Z : Subgroup W} {b s : MulAut W}
    (hbZ : ∀ z ∈ Z, b z = z) (hsZ : ∀ z ∈ Z, s z = z) (hbV : ∀ v ∈ V, b v ∈ V)
    (hsV : ∀ v ∈ V, s v ∈ V) {Q : Type*} [Group Q] (β : ↥V →* Q)
    (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z) {p : ↥V} (hbp : β ⟨b p, hbV p p.2⟩ = β p)
    (hsp : β ⟨s p, hsV p p.2⟩ = β p) : (b * s * b * s⁻¹) (p : W) = p := by
  have hmem : ∀ {g : MulAut W} (hgV : ∀ v ∈ V, g v ∈ V), β ⟨g p, hgV p p.2⟩ = β p →
      g p * (p : W)⁻¹ ∈ Z := by
    intro g hgV hg
    have h1 : β (⟨g p, hgV p p.2⟩ * p⁻¹) = 1 := by rw [map_mul, map_inv, hg, mul_inv_cancel]
    exact (hβk _).mp h1
  exact conj_pair_apply_eq hW hbZ hsZ (hmem hbV hbp) (hmem hsV hsp)


theorem exists_ambMap {D : FFModel} (hker : D.ker = ⊥) {Z : Subgroup W} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L V Z π) :
    ∃ β : ↥V →* D.Amb, (∀ m ∈ D.sec, ∃ u, β u = m) ∧ (∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : D.Gam) (u : ↥V) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V),
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = D.act γ (β u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.RealizesVia.exists_secMap hker hπ
  refine ⟨D.sec.subtype.comp f, fun m hm => ?_, fun u => ?_, fun γ u hu => hfe γ u hu⟩
  · obtain ⟨u, hu⟩ := hfs ⟨m, hm⟩
    exact ⟨u, by simp [hu]⟩
  · rw [← hfk u]
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

end Realization

end CFSG.Quasithin.RonanD35
