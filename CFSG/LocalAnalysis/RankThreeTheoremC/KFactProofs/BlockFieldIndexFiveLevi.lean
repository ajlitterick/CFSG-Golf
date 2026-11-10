module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped commutatorElement

theorem exists_isPGroup_map_eq_p {p : ℕ} [Fact p.Prime] {W W₁ : Type*} [Group W] [Group W₁]
    [Finite W] {ρ : W →* W₁} (hρ : Function.Surjective ρ) {U₁ : Subgroup W₁}
    (hU₁ : IsPGroup p U₁) : ∃ U : Subgroup W, U ≤ U₁.comap ρ ∧ IsPGroup p U ∧ U.map ρ = U₁ := by
  set C := U₁.comap ρ
  let ρ' : C →* U₁ := (ρ.comp C.subtype).codRestrict U₁ fun x => x.2
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite U₁ := Finite.of_surjective ρ' hρ'
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  have hPtop : ((P : Subgroup C).map ρ') = ⊤ := by
    rw [← Sylow.coe_mapSurjective hρ']
    obtain ⟨n, hn⟩ := hU₁.index ((P.mapSurjective hρ' : Sylow p U₁) : Subgroup U₁)
    have hnd := (P.mapSurjective hρ').not_dvd_index
    rcases n with _ | n
    · exact Subgroup.index_eq_one.1 (by simpa using hn)
    · exact absurd (hn ▸ dvd_pow_self p (Nat.succ_ne_zero n)) hnd
  refine ⟨(P : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have e : ((P : Subgroup C).map C.subtype).map ρ = ((P : Subgroup C).map ρ').map U₁.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e, hPtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

@[expose] def BlockOKP (p : ℕ) {G : Type*} [Group G] (H S : Subgroup G) : Prop :=
  ∀ g ∈ H, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∀ k : ℕ,
    (∀ s ∈ S, g ^ (p ^ k) * s * (g ^ (p ^ k))⁻¹ = s) →
    (∃ u ∈ S, ∀ s ∈ S, g * s * g⁻¹ = u * s * u⁻¹) ∨
      ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2


theorem exists_lift_elemAbelianP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A B : Type*} [Group A]
    [Finite A] [Group B] (β : A →* B)
    (h2 : IsPGroup 2 β.ker) {V : Subgroup A} {E : Subgroup B} (hEV : E ≤ V.map β)
    (hE : IsElemAbelian p E) :
    ∃ E' : Subgroup A, E' ≤ V ∧ IsElemAbelian p E' ∧ Nat.card E' = Nat.card E ∧
      (∀ x ∈ E', β x ∈ E) ∧ ∀ x ∈ E', β x = 1 → x = 1 := by
  classical
  have hE3 : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  set f : ↥V →* ↥(V.map β) := (β.comp V.subtype).codRestrict (V.map β) fun x => ⟨x, x.2, rfl⟩
    with hf
  have hfs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set U₁ : Subgroup ↥(V.map β) := E.subgroupOf (V.map β) with hU₁
  have hU₁3 : IsPGroup p U₁ := by
    intro x
    obtain ⟨k, hk⟩ := hE3 ⟨(x : B), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨U, hUle, hU3, hUm⟩ := exists_isPGroup_map_eq_p hfs hU₁3
  set E' : Subgroup A := U.map V.subtype with hE'
  have hUE : ∀ u ∈ U, β (u : A) ∈ E := fun u hu => by
    have := hUle hu
    rw [Subgroup.mem_comap, hU₁, Subgroup.mem_subgroupOf] at this
    exact this
  have hE'E : ∀ x ∈ E', β x ∈ E := by
    rintro _ ⟨u, hu, rfl⟩
    exact hUE u hu
  have hinj : ∀ x ∈ E', β x = 1 → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ h1
    have hxk : (u : A) ∈ β.ker := h1
    obtain ⟨e, he⟩ := hU3 ⟨u, hu⟩
    have hx2 : u ^ (p ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hx3 : (u : A) ^ (p ^ e) = 1 := by simpa using congrArg Subtype.val hx2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    have hd1 : orderOf (u : A) ∣ Nat.card β.ker := Subgroup.orderOf_dvd_natCard β.ker hxk
    have hd2 : orderOf (u : A) ∣ p ^ e := orderOf_dvd_of_pow_eq_one hx3
    have hcop : Nat.Coprime (orderOf (u : A)) (Nat.card β.ker) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hd2
      rw [hj, hn]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2)
    have := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact orderOf_eq_one_iff.1 this
  refine ⟨E', Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_, hE'E,
    hinj⟩
  · have hc := hE.1.is_comm.comm ⟨β a, hE'E a a.2⟩ ⟨β b, hE'E b b.2⟩
    have hc' : β ((a : A) * (b : A) * ((b : A) * (a : A))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · refine hinj _ (pow_mem hx p) ?_
    rw [map_pow]
    exact hE.2 _ (hE'E x hx)
  · refine Nat.card_congr (Equiv.ofBijective (fun u : E' => (⟨β u, hE'E u u.2⟩ : E)) ⟨?_, ?_⟩)
    · intro a b hab
      have hab' : β (a : A) = β (b : A) := congrArg Subtype.val hab
      have h1 : β ((a : A) * (b : A)⁻¹) = 1 := by
        rw [map_mul, map_inv, hab', mul_inv_cancel]
      have := hinj _ (mul_mem a.2 (inv_mem b.2)) h1
      exact Subtype.ext (mul_inv_eq_one.1 this)
    · rintro ⟨e, he⟩
      have : (⟨e, hEV he⟩ : ↥(V.map β)) ∈ U.map f := by
        rw [hUm]
        exact Subgroup.mem_subgroupOf.2 he
      obtain ⟨u, hu, hue⟩ := this
      exact ⟨⟨(u : A), ⟨u, hu, rfl⟩⟩,
        Subtype.ext (show β (u : A) = e from congrArg Subtype.val hue)⟩


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
