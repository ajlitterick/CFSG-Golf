module

public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.LieType.CentralExt
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section OddPart

variable {L : Type*} [Group L]

@[expose] def oddPart (K : Subgroup L) (hK : K ≤ center L) : Subgroup L where
  carrier := {c | c ∈ K ∧ Odd (orderOf c)}
  one_mem' := ⟨K.one_mem, by rw [orderOf_one]; exact odd_one⟩
  mul_mem' := by
    rintro c d ⟨hc, hco⟩ ⟨hd, hdo⟩
    refine ⟨K.mul_mem hc hd, Odd.of_dvd_nat (hco.mul hdo) ?_⟩
    have hcd : Commute c d := mem_center_iff.1 (hK hd) c
    exact hcd.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _)
  inv_mem' := by
    rintro c ⟨hc, hco⟩
    exact ⟨K.inv_mem hc, by rwa [orderOf_inv]⟩

variable {K : Subgroup L} {hK : K ≤ center L}

theorem mem_oddPart {c : L} : c ∈ oddPart K hK ↔ c ∈ K ∧ Odd (orderOf c) := Iff.rfl

theorem oddPart_le : oddPart K hK ≤ K := fun _ hc => hc.1

theorem oddPart_le_center : oddPart K hK ≤ center L := oddPart_le.trans hK

instance oddPart_normal : (oddPart K hK).Normal := normal_of_le_center oddPart_le_center

theorem not_two_dvd_card_oddPart [Finite L] : ¬ 2 ∣ Nat.card (oddPart K hK) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := oddPart K hK) 2 h
  have hodd := c.2.2
  rw [Subgroup.orderOf_coe, hc] at hodd
  exact Nat.not_even_iff_odd.2 hodd even_two

theorem isPGroup_map_mk_oddPart [Finite L] :
    IsPGroup 2 (K.map (QuotientGroup.mk' (oddPart K hK))) := by
  rintro ⟨_, c, hc, rfl⟩
  obtain ⟨m, n, hn, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨m, Subtype.ext ?_⟩
  change (QuotientGroup.mk' (oddPart K hK)) (c ^ 2 ^ m) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨K.pow_mem hc _, Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one ?_)⟩
  rw [← pow_mul, ← hcm, pow_orderOf_eq_one]

end OddPart

section Quotient

variable {L S : Type*} [Group L] [Group S] {π : L →* S} (hK : π.ker ≤ center L)

@[expose] noncomputable def quotientLift : L ⧸ oddPart π.ker hK →* S :=
  QuotientGroup.lift (oddPart π.ker hK) π oddPart_le

@[simp] theorem quotientLift_mk (x : L) : quotientLift hK (x : L ⧸ oddPart π.ker hK) = π x := rfl

theorem quotientLift_surjective (hπ : Function.Surjective π) :
    Function.Surjective (quotientLift hK) := by
  intro s
  obtain ⟨x, rfl⟩ := hπ s
  exact ⟨x, rfl⟩

theorem ker_quotientLift :
    (quotientLift hK).ker = π.ker.map (QuotientGroup.mk' (oddPart π.ker hK)) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  constructor
  · intro hy
    exact ⟨x, hy, rfl⟩
  · rintro ⟨x', hx', hxx⟩
    rw [MonoidHom.mem_ker, ← hxx]
    exact hx'

theorem ker_quotientLift_le_center : (quotientLift hK).ker ≤ center (L ⧸ oddPart π.ker hK) := by
  rw [ker_quotientLift]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_center_iff.2 fun y => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change ((y * x : L) : L ⧸ oddPart π.ker hK) = ((x * y : L) : L ⧸ oddPart π.ker hK)
  rw [mem_center_iff.1 (hK hx) y]

theorem isPGroup_ker_quotientLift [Finite L] : IsPGroup 2 (quotientLift hK).ker := by
  rw [ker_quotientLift]
  exact isPGroup_map_mk_oddPart

theorem ker_mk_oddPart_le_center :
    (QuotientGroup.mk' (oddPart π.ker hK)).ker ≤ center L := by
  rw [QuotientGroup.ker_mk']
  exact oddPart_le_center

theorem not_two_dvd_card_ker_mk_oddPart [Finite L] :
    ¬ 2 ∣ Nat.card (QuotientGroup.mk' (oddPart π.ker hK)).ker := by
  rw [QuotientGroup.ker_mk']
  exact not_two_dvd_card_oddPart

variable {a : MulAut L} {α : MulAut S}

theorem mem_ker_iff_apply (hcomm : ∀ x, π (a x) = α (π x)) {x : L} :
    a x ∈ π.ker ↔ x ∈ π.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hcomm, map_eq_one_iff _ α.injective]

theorem map_oddPart_eq (hcomm : ∀ x, π (a x) = α (π x)) :
    (oddPart π.ker hK).map a.toMonoidHom = oddPart π.ker hK := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxo⟩, rfl⟩
    refine ⟨(mem_ker_iff_apply hcomm).2 hx, ?_⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  · rintro ⟨hy, hyo⟩
    refine ⟨a.symm y, ⟨?_, ?_⟩, a.apply_symm_apply y⟩
    · rw [← mem_ker_iff_apply hcomm, a.apply_symm_apply]
      exact hy
    · rwa [MulEquiv.orderOf_eq]

@[expose] noncomputable def quotientAut (hcomm : ∀ x, π (a x) = α (π x)) :
    MulAut (L ⧸ oddPart π.ker hK) :=
  QuotientGroup.congr (oddPart π.ker hK) (oddPart π.ker hK) a (map_oddPart_eq hK hcomm)

@[simp] theorem quotientAut_mk (hcomm : ∀ x, π (a x) = α (π x)) (x : L) :
    quotientAut hK hcomm (x : L ⧸ oddPart π.ker hK) = ((a x : L) : L ⧸ oddPart π.ker hK) :=
  rfl


end Quotient

section Lifts

variable {L S : Type*} [Group L] [Group S] [Finite L] {π : L →* S}


theorem exists_fixed_two_lift (hK : π.ker ≤ center L) {a : MulAut L} {α : MulAut S}
    (hcomm : ∀ x, π (a x) = α (π x)) {y : L ⧸ oddPart π.ker hK}
    (hy : ∃ n : ℕ, orderOf y = 2 ^ n) (hfix : quotientAut hK hcomm y = y) :
    ∃ x : L, (x : L ⧸ oddPart π.ker hK) = y ∧ (∃ n : ℕ, orderOf x = 2 ^ n) ∧ a x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Function.Surjective (QuotientGroup.mk' (oddPart π.ker hK)) :=
    QuotientGroup.mk'_surjective _
  have hC := not_two_dvd_card_ker_mk_oddPart hK
  have hx := map_pLift hq hC hy
  have hxo := orderOf_pLift hq hC hy
  refine ⟨pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) y, hx, hxo, ?_⟩
  refine eq_of_pElement (ker_mk_oddPart_le_center hK) hC ?_ ?_ hxo
  · change ((a _ : L) : L ⧸ oddPart π.ker hK) = _
    rw [← quotientAut_mk hK hcomm]
    change quotientAut hK hcomm (QuotientGroup.mk' _ _) = QuotientGroup.mk' _ _
    rw [hx, hfix]
  · obtain ⟨n, hn⟩ := hxo
    exact ⟨n, by rw [MulEquiv.orderOf_eq]; exact hn⟩


end Lifts

section FixedQuotient

variable {L S : Type*} [Group L] [Group S] [Finite L] {π : L →* S}

theorem mem_sylow_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : (P : Subgroup G).Normal) {g : G} (hg : ∃ n : ℕ, orderOf g = p ^ n) :
    g ∈ (P : Subgroup G) := by
  obtain ⟨n, hn⟩ := hg
  have hp : IsPGroup p (zpowers g) := by
    rw [IsPGroup.iff_card]
    exact ⟨n, by rw [Nat.card_zpowers, hn]⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have := Sylow.unique_of_normal P hP
  rw [Subsingleton.elim Q P] at hQ
  exact hQ (mem_zpowers g)


end FixedQuotient

end CFSG.LocalAnalysis.ComponentInitial
