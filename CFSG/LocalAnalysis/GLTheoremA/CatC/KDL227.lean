module

public import CFSG.LocalAnalysis.GLTheoremA.S3.I112L227
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char (lie_char_part amb_lie_order card_alt)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut barOf)


namespace KDL227Aux

set_option linter.unusedSectionVars false


private theorem prime_dvd_9828 {r : ℕ} (hr : r.Prime) (h : r ∣ 9828) :
    r = 2 ∨ r = 3 ∨ r = 7 ∨ r = 13 := by
  have h9 : (9828 : ℕ) = 2 * 2 * 3 * 3 * 3 * 7 * 13 := by norm_num
  rw [h9] at h
  have e2 := fun {a : ℕ} (ha : a.Prime) => (Nat.prime_dvd_prime_iff_eq hr ha).1
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
            · exact Or.inl (e2 Nat.prime_two h)
            · exact Or.inl (e2 Nat.prime_two h)
          · exact Or.inr (Or.inl (e2 Nat.prime_three h))
        · exact Or.inr (Or.inl (e2 Nat.prime_three h))
      · exact Or.inr (Or.inl (e2 Nat.prime_three h))
    · exact Or.inr (Or.inr (Or.inl (e2 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (e2 (by norm_num) h)))

private theorem char_arith {r v M : ℕ} (hr : r.Prime) (h : 9828 = r ^ v * M)
    (hM : M < r ^ (2 * v)) : r = 3 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp at h hM
    omega
  · have hrd : r ∣ 9828 := h ▸ Dvd.dvd.mul_right (dvd_pow_self r hv.ne') M
    have hvd : r ^ v ∣ 9828 := h ▸ dvd_mul_right _ _
    rcases prime_dvd_9828 hr hrd with rfl | rfl | rfl | rfl
    · exfalso
      have hv2 : v ≤ 2 := by
        by_contra hv3
        have : 2 ^ 3 ∣ 2 ^ v := Nat.pow_dvd_pow 2 (by omega)
        have := this.trans hvd
        norm_num at this
      interval_cases v <;> omega
    · rfl
    · exfalso
      have hv2 : v ≤ 1 := by
        by_contra hv3
        have : 7 ^ 2 ∣ 7 ^ v := Nat.pow_dvd_pow 7 (by omega)
        have := this.trans hvd
        norm_num at this
      interval_cases v <;> omega
    · exfalso
      have hv2 : v ≤ 1 := by
        by_contra hv3
        have : 13 ^ 2 ∣ 13 ^ v := Nat.pow_dvd_pow 13 (by omega)
        have := this.trans hvd
        norm_num at this
      interval_cases v <;> omega

theorem not_isChevSimple_L227 {r : ℕ} (hr3 : r ≠ 3) {X : Type} [Group X] [Finite X]
    (hX : catalogIs X (onLie (isL2 27))) : ¬ IsChevSimple r X := by
  have hcard : Nat.card X = 9828 := card_of_catalogIs_L227 hX
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      have hd : d.1.characteristic = r := hi
      have hn : Nat.card X = lieOrderFormula d.1 := lieOrderBridge_holds d X ⟨e⟩
      obtain ⟨v, M, hv, hM⟩ := lie_char_part d.1 d.2
      rw [hd] at hv hM
      have hrp : r.Prime := hd ▸ TauCeti.LieTypeIndex.characteristic_prime d.1
      exact hr3 (char_arith hrp (hcard.symm.trans (hn.trans hv)) hM)
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hc : Nat.card X = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [hcard] at hc <;>
        norm_num [Nat.factorial] at hc
    | lie d =>
      obtain ⟨ld, hvld⟩ := d
      have hn : Nat.card X = lieOrderFormula ld := lieOrderBridge_holds ⟨ld, hvld⟩ X ⟨e⟩
      have hval := amb_lie_order r ld hvld hi
      rw [hcard] at hn
      rcases hval with h | h | h | h <;> omega


theorem alt_case {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (I : Subgroup S) (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hL : catalogIs (PSimple 3 I) (onLie (isL2 27))) : False := by
  have hcard : Nat.card (PSimple 3 I) = 9828 := card_of_catalogIs_L227 hL
  set α : MulAut (alternatingGroup (Fin n)) := MulAut.congr e β with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hβ, map_one]
  have hα1 : α ≠ 1 := fun h => hβ1 ((MulAut.congr e).injective (by rw [← hα, h, map_one]))
  have hC : GLAPComponent 3 (fixSubgroup α) (I.map e.toMonoidHom) := by
    rw [hα, CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr e β]
    exact glaPComponent_map Nat.prime_three e.toMonoidHom
      (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.FixedData3.coprime_inf_ker
        e.toMonoidHom e.injective _) hI
  obtain ⟨m, hm5, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn Nat.prime_three (by norm_num) α hα3 hα1 _ hC
  have e2 : PSimple 3 I ≃* alternatingGroup (Fin m) :=
    (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
      (I.equivMapOfInjective e.toMonoidHom e.injective)).trans f
  have hc : Nat.card (PSimple 3 I) = m.factorial / 2 :=
    (Nat.card_congr e2.toEquiv).trans (card_alt m (by omega))
  rw [hcard] at hc
  rcases lt_or_ge m 8 with h8 | h8
  · interval_cases m <;> norm_num [Nat.factorial] at hc
  · have := Nat.factorial_le h8
    norm_num [Nat.factorial] at this
    omega


private theorem lieIndexChar_eq (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

theorem lie_ne_three_case {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hd3 : d.1.characteristic ≠ 3)
    (β : MulAut S) (hβ : β ^ 3 = 1) (I : Subgroup S) (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hL : catalogIs (PSimple 3 I) (onLie (isL2 27))) : False := by
  have h := (lieComp_holds S hs hna d ⟨e⟩ β hβ I hI).1.chev
  rw [lieIndexChar_eq] at h
  exact not_isChevSimple_L227 hd3 hL h


private theorem prime_pow_27 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 27) :
    p = 3 ∧ f = 3 := by
  have hp3 : p = 3 := by
    have hd : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h]
      exact dvd_pow_self p hf.ne')
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 3 by norm_num [h])⟩

private theorem isL2_elim {n : ℕ} {ℓ : TauCeti.LieTypeIndex} (h : isL2 n ℓ) :
    ∃ q : TauCeti.PrimePower, ℓ = .A 1 q ∧ q.card = n := by
  cases ℓ
  case A r q =>
    rcases r with _ | _ | r
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  all_goals exact False.elim h

theorem catalog_iso_psl {S : Type} [Group S] (h : catalogIs S (onLie (isL2 27))) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | lie d =>
    obtain ⟨ℓ, hv⟩ := d
    have hℓ : isL2 27 ℓ := hi
    obtain ⟨q, rfl, hq⟩ := isL2_elim hℓ
    obtain ⟨p, f, hpp, hff⟩ := q
    have hpf : p ^ f = 27 := (TauCeti.PrimePower.card_def _).symm.trans hq
    obtain ⟨rfl, rfl⟩ := prime_pow_27 hpp hff hpf
    haveI : Fact (Nat.Prime 3) := ⟨hpp⟩
    exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 3, hpp, hff⟩ hv)⟩
  | sporadic name => exact False.elim hi

theorem isL227_of_catalogIs {X : Type} [Group X] (h : catalogIs X (onLie (isL2 27))) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X := by
  obtain ⟨e⟩ := catalog_iso_psl h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨GaloisField 3 3, inferInstance, inferInstance, ?_, ⟨e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3))⟩⟩
  rw [GaloisField.card 3 3 (by norm_num)]
  norm_num

theorem lie_three_inner_case {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hd3 : d.1.characteristic = 3)
    (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hinn : β ∈ innerAut S)
    (I : Subgroup S) (hI : GLAPComponent 3 (fixSubgroup β) I) : False := by
  have hChev : IsChevSimple 3 S := Or.inl ⟨TauCeti.CFSGIndex.lie d, hd3, ⟨e⟩⟩
  have hlayer := kdChevInner_of Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds Nat.prime_three (by norm_num))
    (kdAmbSolv_holds Nat.prime_three (by norm_num) u42_fixSubgroup_solvable) S hs hna hChev β hβ
    hβ1 hinn
  have hle : I ≤ GLAPLayer 3 (fixSubgroup β) := le_sSup hI
  rw [hlayer] at hle
  exact glaPComponent_ne_bot' hI (le_bot_iff.1 hle)

theorem lie_three_outer_case {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hd3 : d.1.characteristic = 3)
    (β ξ : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hout : β ∉ innerAut S)
    (hξ : ξ ^ 3 = 1) (hξβ : ξ * β = β * ξ)
    (I : Subgroup S) (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hL : catalogIs (PSimple 3 I) (onLie (isL2 27))) (hN : I.map ξ.toMonoidHom = I) :
    ∃ i ∈ I, ∀ y ∈ I, ξ y * (i * y * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf β = 3 := orderOf_eq_prime hβ hβ1
  have hdata := ((CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds
    (CFSG.Yardstones.Md42047359a2a.lieFamily d.1)).2 S hs hna d rfl ⟨e⟩ 3 Nat.prime_three
      (by norm_num) hd3.symm β hord hout)
  exact hdata.l227 rfl I hI (isL227_of_catalogIs hL) ξ hξ hξβ hN


open CFSG.HardMathSupport.Dickson.DefCharOuter.Export (FixedData3)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (map_glaPPrimeCoreOf_of_injective)

theorem map_fixSubgroup_conjNormal {Y : Type} [Group Y] (S : Subgroup Y) [S.Normal] (b : Y) :
    (fixSubgroup (MulAut.conjNormal (H := S) b)).map S.subtype =
      S ⊓ Subgroup.centralizer ({b} : Set Y) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hs
    refine ⟨s.2, ?_⟩
    have := congrArg Subtype.val hs
    simp only [MulAut.conjNormal_apply] at this
    simp only [Subgroup.coe_subtype]
    calc (s : Y) * b = b * s * b⁻¹ * b := by rw [this]
      _ = b * s := by group
  · rintro ⟨hy, hc⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    calc b * y * b⁻¹ = y * b * b⁻¹ := by rw [← hc]
      _ = y := by group


end KDL227Aux

end CFSG.LocalAnalysis.GLTheoremA
