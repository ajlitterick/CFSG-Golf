module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic
public import CFSG.Walter.AStar.N1
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.ComponentClassification.WalterSchur

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {X P E : Subgroup Y}

omit [Finite Y] in
theorem omegaOne_eq_self (hP : ∀ p ∈ P, p * p = 1) : omegaOne P = P :=
  le_antisymm (omegaOne_le P) fun p hp =>
    Subgroup.subset_closure ⟨hp, by rw [sq]; exact hP p hp⟩

omit [Finite Y] in
theorem eq_of_isSylowOf (hP : IsSylowOf 2 P X) {R : Subgroup Y} (hR : IsPGroup 2 R)
    (hRX : R ≤ X) (hPR : P ≤ R) : R = P := by
  obtain ⟨Q, hQ⟩ := hP
  have hR' : IsPGroup 2 (R.subgroupOf X) := hR.comap_subtype
  have hQR : (Q : Subgroup X) ≤ R.subgroupOf X := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hPR (hQ ▸ Subgroup.mem_map_of_mem X.subtype hq)
  have h := Q.is_maximal' hR' hQR
  rw [← hQ, ← h, Subgroup.map_subgroupOf_eq_of_le hRX]

omit [Finite Y] in
theorem exists_sylow_sup (hP : IsSylowOf 2 P X) (hE2 : IsPGroup 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y)) (hEC : E ≤ Subgroup.centralizer (P : Set Y)) :
    ∃ S : Sylow 2 (X ⊔ E : Subgroup Y), (S : Subgroup (X ⊔ E : Subgroup Y)).map
      (X ⊔ E : Subgroup Y).subtype = P ⊔ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP
  have hPX : P ≤ X := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := by rw [← hQ]; exact Q.isPGroup'.map _
  set H := X ⊔ E with hHdef
  have hT2 : IsPGroup 2 (P ⊔ E : Subgroup Y) :=
    hP2.to_sup_of_normal_left' hE2 (hEC.trans (Subgroup.centralizer_le_normalizer _))
  have hTH : P ⊔ E ≤ H := sup_le_sup_right hPX E
  obtain ⟨S, hS⟩ := (hT2.comap_subtype (K := H)).exists_le_sylow
  refine ⟨S, le_antisymm ?_ ?_⟩
  ·
    rintro _ ⟨s, hs, rfl⟩
    have hsH : (s : Y) ∈ (X : Set Y) * (E : Set Y) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X E hEX]
      exact s.2
    obtain ⟨x, hx, e, he, hxe⟩ := Set.mem_mul.mp hsH
    set R := (S : Subgroup H).map H.subtype ⊓ X with hRdef
    have hR2 : IsPGroup 2 R := (S.isPGroup'.map H.subtype).to_le inf_le_left
    have hTS : P ⊔ E ≤ (S : Subgroup H).map H.subtype := by
      intro t ht
      exact ⟨⟨t, hTH ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
    have hPR : P ≤ R := le_inf (le_sup_left.trans hTS) hPX
    have hReq := eq_of_isSylowOf ⟨Q, hQ⟩ hR2 inf_le_right hPR
    have hxR : x ∈ R := by
      refine ⟨?_, hx⟩
      have he' : e ∈ (S : Subgroup H).map H.subtype := hTS (Subgroup.mem_sup_right he)
      have hs' : (s : Y) ∈ (S : Subgroup H).map H.subtype := ⟨s, hs, rfl⟩
      rw [show x = (s : Y) * e⁻¹ by rw [← hxe]; group]
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ he')
    rw [hReq] at hxR
    rw [Subgroup.coe_subtype, ← hxe]
    exact Subgroup.mul_mem_sup hxR he
  · intro t ht
    exact ⟨⟨t, hTH ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

theorem card_le_omegaOne_of_elementary (hX : IsSimpleGroup X)
    (hXnonab : ∃ a b : X, a * b ≠ b * a) (hP : IsSylowOf 2 P X) (hP2 : ∀ p ∈ P, p * p = 1)
    (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) (hE : IsElemAbelian 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e) :
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [omegaOne_eq_self hP2] at hEcent ⊢
  have hP' := hP
  obtain ⟨Q, hQ⟩ := hP'
  have hPX : P ≤ X := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hE2 : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 e e.2)⟩
  have hEC : E ≤ Subgroup.centralizer (P : Set Y) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun p hp => (hEcent e he p hp).symm
  set H := X ⊔ E with hHdef
  obtain ⟨S, hS⟩ := exists_sylow_sup hP hE2 hEX hEC
  have hTab : P ⊔ E ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
    have hPC : P ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro p hp
        exact Subgroup.mem_centralizer_iff.mpr fun q hq => hPc q hq p hp
      · exact hEC
    have hEC' : E ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [← Subgroup.le_centralizer_iff]
        exact hEC
      · intro e he
        exact Subgroup.mem_centralizer_iff.mpr fun f hf =>
          congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨e, he⟩)
    exact sup_le hPC hEC'
  have hSab : IsMulCommutative (S : Subgroup H) := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have ha : ((a : H) : Y) ∈ P ⊔ E := hS ▸ ⟨a, a.2, rfl⟩
    have hb : ((b : H) : Y) ∈ P ⊔ E := hS ▸ ⟨b, b.2, rfl⟩
    change ((a : H) : Y) * ((b : H) : Y) = ((b : H) : Y) * ((a : H) : Y)
    exact Subgroup.mem_centralizer_iff.mp (hTab hb) _ ha
  have hHab : Walter.HasAbelianSylowTwo H := Walter.hasAbelianSylowTwo_of_sylow S hSab
  have hXH : X ≤ H := le_sup_left
  set X' : Subgroup H := X.subgroupOf H with hX'def
  let eX : X' ≃* X := Subgroup.subgroupOfEquivOfLe hXH
  have : IsSimpleGroup X := hX
  have hX's : IsSimpleGroup X' := eX.isSimpleGroup
  have hX'nonab : ∃ a b : X', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXnonab
    refine ⟨eX.symm a, eX.symm b, fun h => hab ?_⟩
    simpa using congrArg eX h
  have hX'n : X'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
    (sup_le Subgroup.le_normalizer hEX)
  have hSN : (S : Subgroup H) ≤ Subgroup.normalizer (X' : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hinner := Walter.exists_inner_of_sylow_le_normalizer hHab X' hX'nonab S hSN
  have hEinner : ∀ e ∈ E, ∃ k ∈ X, ∀ x ∈ X, e * x * e⁻¹ = k * x * k⁻¹ := by
    intro e he
    have heS : (⟨e, Subgroup.mem_sup_right he⟩ : H) ∈ (S : Subgroup H) := by
      have hT : e ∈ (S : Subgroup H).map H.subtype := hS ▸ Subgroup.mem_sup_right he
      obtain ⟨s, hs, hse⟩ := hT
      rw [show (⟨e, Subgroup.mem_sup_right he⟩ : H) = s from Subtype.ext hse.symm]
      exact hs
    obtain ⟨k, hk, hkx⟩ := hinner _ heS
    refine ⟨k, Subgroup.mem_subgroupOf.mp hk, fun x hx => ?_⟩
    have h := congrArg Subtype.val (hkx ⟨x, hXH hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
    simpa using h
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hXnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  set ι : X →* MulAut X := MulAut.conj with hιdef
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZX]
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut X => φ x) (MonoidHom.mem_ker.mp hk)
    simp only [hιdef, MulAut.conj_apply, MulAut.one_apply] at h
    calc x * k = k * x * k⁻¹ * k := by rw [h]
      _ = k * x := by group
  set A := (conjAct hEX).range with hAdef
  have hAι : A ≤ ι.range := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hEinner e e.2
    refine ⟨⟨k, hk⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [conjAct_apply, hkx x x.2]
    rfl
  set At := A.comap ι with hAtdef
  have hAt : Nat.card At = Nat.card A := by
    have h := Subgroup.card_map_of_injective (K := At) hιinj
    rw [hAtdef, Subgroup.map_comap_eq, inf_eq_right.mpr hAι] at h
    exact h.symm
  have hAtQ : At ≤ (Q : Subgroup X) := by
    have hAtC : At ≤ Subgroup.centralizer ((Q : Subgroup X) : Set X) := by
      intro k hk
      obtain ⟨e, he⟩ := hk
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqP : (q : Y) ∈ P := hQ ▸ Subgroup.mem_map_of_mem X.subtype hq
      have h := congrArg (fun φ : MulAut X => ((φ q : X) : Y)) he
      simp only [conjAct_apply, hιdef, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      have h2 : ((k : X) : Y) * q * ((k : X) : Y)⁻¹ = q := by
        rw [← h, (hEcent e e.2 q hqP), mul_inv_cancel_right]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (q : Y) * ((k : X) : Y) = ((k : X) : Y) * q * ((k : X) : Y)⁻¹ * ((k : X) : Y) := by
            rw [h2]
        _ = ((k : X) : Y) * q := by group
    have hAt2 : IsPGroup 2 At := by
      intro k
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply hιinj
      obtain ⟨e, he⟩ := Subgroup.mem_comap.mp k.2
      rw [pow_one, Subgroup.coe_pow, map_pow, ← he, ← map_pow, OneMemClass.coe_one, map_one]
      have he2 : e ^ 2 = 1 := Subtype.ext (hE.2 e e.2)
      rw [he2, map_one]
    have hsup := Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_left' hAt2
      (hAtC.trans (Subgroup.centralizer_le_normalizer _))) le_sup_left
    rw [← hsup]
    exact le_sup_right
  have hAcard : Nat.card A ≤ Nat.card P := by
    rw [← hAt, ← hQ, Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_le_of_le hAtQ
  rw [card_eq_mul_card_range hEX, mul_comm]
  exact Nat.mul_le_mul_right _ hAcard

section NormalElementarySquare


end NormalElementarySquare

end CFSG.ComponentClassification.WalterSchur
