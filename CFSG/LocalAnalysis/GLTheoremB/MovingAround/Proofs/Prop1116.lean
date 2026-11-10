module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

namespace Prop1116

@[expose] def Pi19Ty (p : ℕ) (Y : Type) [Group Y] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ IsAltType n Y ∧ (n % p = 2 ∨ n % p = 4 ∨ (p = 3 ∧ n % 3 ≠ 0))) ∨
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) Y ∧ HasFixedPointFreeOrder ε n p)

@[expose] def Ke (p : ℕ) {G : Type} [Group G] (K : Subgroup G) (e : G) : Subgroup G :=
  GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({e} : Set G)) ⊔
    piLayer p (K ⊓ Subgroup.centralizer ({e} : Set G))


@[expose] def InputA7Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G),
    GLAPComponent 3 X K → B ≤ X → B ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian 3 B →
    2 ≤ CFSG.Open.pRank 3 B → IsAltType 7 (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →
      barX 3 X K ≤ barX 3 X (⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Ke 3 K e)

@[expose] def InputOmegaGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G),
    GLAPComponent p X K → B ≤ X → B ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian p B →
    2 ≤ CFSG.Open.pRank p B →
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧
      HasFixedPointFreeOrder ε n p) →
      barX p X K ≤ barX p X (⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Ke p K e)

@[expose] def InputSchurAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → CFSG.Open.IsQuasisimple X →
    GLAPPrimeCore p X = ⊥ → ∀ n : ℕ, n % p = 2 → IsAltType n (X ⧸ Subgroup.center X) →
      Subgroup.center X = ⊥

@[expose] def InputNotL27Pi : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLTwoTwentySeven X → ¬ Pi19Ty 3 (X ⧸ Subgroup.center X)

@[expose] def InputOmegaDvd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ) (ε : Bool) (n : ℕ), 1 ≤ n → IsOmegaTwo ε (n + 1) Y →
    HasFixedPointFreeOrder ε n p → p ∣ Nat.card Y

theorem pi19Ty_congr (p : ℕ) {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : Pi19Ty p Y) :
    Pi19Ty p Y' := by
  rcases h with ⟨n, hn, hA, hmod⟩ | ⟨ε, n, hn, hO, hfp⟩
  · exact Or.inl ⟨n, hn, l119_isAltType_congr n e hA, hmod⟩
  · refine Or.inr ⟨ε, n, hn, ?_, hfp⟩
    cases ε with
    | true => obtain ⟨f⟩ := hO; exact ⟨e.symm.trans f⟩
    | false => obtain ⟨f⟩ := hO; exact ⟨e.symm.trans f⟩

theorem pi19Ty_input {p : ℕ} {Y : Type} [Group Y] (h : Pi19Ty p Y) :
    (∃ n : ℕ, 5 ≤ n ∧ IsAltType n Y ∧ (n % p = 2 ∨ n % p = 4 ∨ (p = 3 ∧ n % 3 ≠ 0))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) Y ∧ HasFixedPointFreeOrder ε n p) ∨
      (p = 5 ∧ IsSporType .Fi22 Y) ∨
      (p = 3 ∧ (IsLThreeFour Y ∨ IsLpType 2 7 Y ∨ IsSporType .He Y)) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem pi19Ty_of_isPiGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Group L] [Finite L]
    (h : IsPiGroup p L) : Pi19Ty p (L ⧸ Subgroup.center L) := by
  obtain ⟨hq, -, hcase⟩ := h
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases hcase with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hO, hfp⟩ | ⟨hp3', ⟨f⟩⟩
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        subst h0
        have hfin : Nat.card (Fin (0 * p + 2)) = 2 := by simp
        have h2 := two_mul_nat_card_alternatingGroup (α := Fin (0 * p + 2))
        rw [Nat.card_perm, hfin] at h2
        have hf2 : Nat.factorial 2 = 2 := rfl
        have hc : Nat.card (L ⧸ Subgroup.center L) = 1 := by
          rw [Nat.card_congr f.toEquiv]
          omega
        have : 1 < Nat.card (L ⧸ Subgroup.center L) := Finite.one_lt_card
        omega
      · exact h0
    have h5 : 5 ≤ k * p + 2 := by
      have : p ≤ k * p := Nat.le_mul_of_pos_left p hk
      omega
    have hmod : (k * p + 2) % p = 2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    exact Or.inl ⟨k * p + 2, h5, ⟨f⟩, Or.inl hmod⟩
  · exact Or.inr ⟨ε, n, hn, hO, hfp⟩
  · subst hp3'
    exact Or.inl ⟨7, by norm_num, ⟨f⟩, Or.inr (Or.inr ⟨rfl, by norm_num⟩)⟩

theorem pi19Ty_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOm : InputOmegaDvd) {Y : Type} [Group Y]
    [Finite Y] (h : Pi19Ty p Y) : p ∣ Nat.card Y := by
  rcases h with ⟨n, hn, ⟨f⟩, hmod⟩ | ⟨ε, n, hn, hO, hfp⟩
  · have hpn : p ≤ n := by
      by_contra hlt
      push_neg at hlt
      rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcard : 2 * Nat.card Y = Nat.factorial n := by
      rw [Nat.card_congr f.toEquiv, two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    have hfac : p ∣ 2 * Nat.card Y := by
      rw [hcard]
      exact Nat.dvd_factorial hp.pos hpn
    rcases (Nat.Prime.dvd_mul hp).1 hfac with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
    · exact h2
  · exact hOm Y p ε n hn hO hfp

theorem le_cg_of_mem_elemAbelian {G : Type} [Group G] {p : ℕ} {A : Subgroup G} (hAel : IsElemAbelian p A)
    {a : G} (ha : a ∈ A) : A ≤ Subgroup.centralizer ({a} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩)

theorem cex117_false {G : Type} [Group G] [Finite G] (h117 : Prop117_cex_falseStatement) {m p : ℕ}
    {B M E A K : Subgroup G} {a : G} (hb : Cex117Base G m p B M E A a K) : False := by
  classical
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb', hn'⟩ := hex
    exact h117 ⟨hb', fun _ => hn'⟩
  · exact h117 ⟨hb, fun h' => absurd h' hex⟩

section Family

variable {G : Type} [Group G] [Finite G]

@[expose] def fam (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :=
  {Z | ∃ z ∈ A0, Z = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)}

theorem fam_base (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) : barX p C K ∈ fam p C K A0 :=
  ⟨1, A0.one_mem, by rw [map_one, gLBConj_one]⟩

theorem fam_comp {p : ℕ} {C K : Subgroup G} (hK : GLAPComponent p C K) (A0 : Subgroup ↥C) :
    ∀ Z ∈ fam p C K A0, IsComponentOf Z ⊤ := by
  rintro Z ⟨z, -, rfl⟩
  exact l119_conj_component hK z

theorem fam_bar_normalizes {p : ℕ} {C K : Subgroup G} (A0 : Subgroup ↥C) {y : ↥C} (hy : y ∈ A0) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) y ∈
      Subgroup.normalizer ((sSup (fam p C K A0) : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set _) := by
  set S : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) := sSup (fam p C K A0) with hS
  have hstep : ∀ g : ↥C ⧸ GLAPPrimeCore p ↥C, (∃ w : ↥C, w ∈ A0 ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥C) w = g) →
      S ≤ S.comap (MulAut.conj g).toMonoidHom := by
    rintro g ⟨w, hw, rfl⟩
    refine sSup_le fun Z hZ => ?_
    obtain ⟨z, hz, rfl⟩ := hZ
    intro x hx
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹ ∈ S
    have hmem : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ∈ fam p C K A0 :=
      ⟨z * w⁻¹, A0.mul_mem hz (A0.inv_mem hw), by
        rw [gLBConj_gLBConj, map_mul, map_inv]⟩
    have hsub : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ≤ S :=
      le_sSup hmem
    apply hsub
    rw [mem_gLBConj]
    have hcancel : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rw [hcancel]
    exact hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hstep _ ⟨y, hy, rfl⟩ hh
  · intro hh
    have hh' := hstep (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) ⟨y⁻¹, A0.inv_mem hy, rfl⟩ hh
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    have hh'' : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ ∈ S := hh'
    rw [e] at hh''
    exact hh''

end Family

section Steps

variable {G : Type} [Group G] [Finite G]

theorem layer_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {B M E A : Subgroup G} {a : G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hI19 : Input19_19) (hNot27 : InputNotL27Pi) (h115 : Prop115Statement)
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q)
    {X : Type} [Group X] [Finite X]
    (hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
      X ⧸ Subgroup.center X))
    (hTK : Pi19Ty p (X ⧸ Subgroup.center X)) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, ⟨e⟩⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  obtain ⟨eK⟩ := hQK
  have eP : ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) ≃*
      X ⧸ Subgroup.center X := e.symm.trans eK
  have hTP : Pi19Ty p ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) :=
    pi19Ty_congr p eP.symm hTK
  have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p P) :=
    hI19 (barOf p P) hPq p hp hp2 (pi19Ty_input hTP)
  have h2 : p = 3 → IsLTwoTwentySeven (barOf p P) → ¬ IsCompLocallyOTwoBalanced p 1 A P := by
    intro hp3 hL27 _
    exact (hNot27 (barOf p P) hL27 (hp3 ▸ hTP)).elim
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ h1 h2 with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact barX_mono p hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD


end Steps

end Prop1116

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
