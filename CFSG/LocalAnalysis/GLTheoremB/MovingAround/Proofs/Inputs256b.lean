module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116d
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)


@[expose] def Clause2W (J : Type) [Group J] : Prop :=
  IsAltType 5 J ∨ (Prop1310a5b.IsAltOrChev J ∧
    ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H →
      GLAPPrimeCore 3 H = ⊥ → Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H)

@[expose] def Concl256W (K : Type) [Group K] (x : MulAut K) (y : K) (L : Subgroup K) : Prop :=
  ∃ S : MulAut K → Set (Subgroup K),
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) ∧
    (∀ Y : Subgroup K, CFSG.Open.IsSubnormal Y (Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S) → L ≤ Y →
      ¬ IsAltType 5 (barOf 3 Y)) ∧
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, Clause2W (barOf 3 J)) ∧
    L ≤ ⨆ (J : Subgroup K) (_ : J ∈ S x), J

@[expose] def Input25_6A5Chev2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K →
    GLAPPrimeCore 3 K = ⊥ → ¬ IsPiGroup 3 K → (¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) →
    IsLieChar (· = 2) K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Concl256W K x y L

@[expose] def chev5Comps {K : Type} [Group K] (a : MulAut K) : Set (Subgroup K) :=
  {J | GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ IsChevSimple 5 (PSimple 3 J)}

@[expose] def InputGen2311Five : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    IsLieChar (· = 5) K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 →
        Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) chev5Comps = ⊤

@[expose] def a5Comps {K : Type} [Group K] (a : MulAut K) : Set (Subgroup K) :=
  {J | GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ IsAltType 5 (barOf 3 J)}

@[expose] def InputGen2324c : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    (IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K)) →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) a5Comps = ⊤

section Generic

theorem fixedSub_eq {K : Type} [Group K] (x : MulAut K) : Prop1310a5.fixedSub x = fixSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem alt5_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  decide

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isAltType_pSimple {K : Type} [Group K] {L : Subgroup K} (h : IsAltType 5 (barOf 3 L)) :
    IsAltType 5 (PSimple 3 L) :=
  Lemma1315b.isAltType_center_quot le_rfl h

theorem not_alt5_of_subnormal_top {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hcore : GLAPPrimeCore 3 K = ⊥) {x : MulAut K} (hx : x ≠ 1) {L : Subgroup K}
    (hLx : L ≤ fixSubgroup x) (hL5 : IsAltType 5 (barOf 3 L)) {Y : Subgroup K}
    (hY : CFSG.Open.IsSubnormal Y ⊤) (hLY : L ≤ Y) : ¬ IsAltType 5 (barOf 3 Y) := by
  intro hY5
  obtain ⟨eL⟩ := hL5
  have hqt : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K).symm hq
  rcases SporFacts.eq_or_le_center_of_isSubnormal hqt hY with rfl | hZ
  ·
    obtain ⟨eY⟩ := hY5
    have hct : GLAPPrimeCore 3 ↥(⊤ : Subgroup K) = ⊥ := by
      rw [← glaPPrimeCore_map_iso 3 (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K).symm, hcore,
        Subgroup.map_bot]
    have hK60 : Nat.card K = 60 := by
      rw [← Subgroup.card_top, ← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hct).trans
        QuotientGroup.quotientBot).toEquiv, Nat.card_congr eY.toEquiv, card_alt5]
    have hdvd : Nat.card (barOf 3 L) ∣ Nat.card L :=
      Subgroup.index_dvd_card (H := GLAPPrimeCore 3 ↥L)
    rw [Nat.card_congr eL.toEquiv, card_alt5] at hdvd
    have hLtop : L = ⊤ :=
      Subgroup.eq_top_of_le_card (H := L) (by rw [hK60]; exact Nat.le_of_dvd Nat.card_pos hdvd)
    apply hx
    ext k
    rw [MulAut.one_apply]
    have hk : k ∈ L := by rw [hLtop]; exact Subgroup.mem_top k
    exact mem_fixSubgroup.1 (hLx hk)
  ·
    have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', -, rfl⟩ := hZ (hLY ha)
      obtain ⟨b', hb', rfl⟩ := hZ (hLY hb)
      have h1 : a' * b' = b' * a' := Subgroup.mem_center_iff.1 hb' a'
      exact congrArg Subtype.val h1
    have key : ∀ u v : barOf 3 L, u * v = v * u := by
      intro u v
      obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) u
      obtain ⟨v0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) v
      rw [← map_mul, ← map_mul, show u0 * v0 = v0 * u0 from Subtype.ext (hcomm _ u0.2 _ v0.2)]
    obtain ⟨a, b, hab⟩ := alt5_noncomm
    apply hab
    have h2 := congrArg eL (key (eL.symm a) (eL.symm b))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

end Generic

section Types


end Types

section HSM23


end HSM23

section Chev5

theorem isAltOrChev_of_chev5 {J : Type} [Group J] (h : IsChevSimple 5 (J ⧸ Subgroup.center J)) :
    Prop1310a5b.IsAltOrChev J := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have h5 : idx.1.characteristic = 5 := hi
      exact Or.inr ⟨idx, ⟨e⟩, (by rw [h5]; norm_num : idx.1.characteristic ≠ 3)⟩
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | alternating n hn =>
      rcases hi with ⟨rfl, -⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
      · exact Or.inl ⟨5, ⟨e⟩⟩
      all_goals omega
    | lie d =>
      exfalso
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k <;> simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k <;> simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim

theorem isChevSimple_seven_of_isLpType {T : Type} [Group T] (h : IsLpType 2 7 T) : IsChevSimple 7 T := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  exact CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv f
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.He7.isChevSimple_seven_L2 F hc)


end Chev5

section Assembly


end Assembly

section Holds


end Holds

section Rows


@[expose] def Input25_6A5Rest : Prop :=
  InputGen2324c ∧ InputGen2311Five ∧ Input25_6A5Chev2

end Rows

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256b

end
