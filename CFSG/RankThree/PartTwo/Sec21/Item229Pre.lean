module

public import CFSG.RankThree.PartTwo.Sec21.Item229Gen
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.RankThree.PartTwo.Sec21.Item227
public import CFSG.RankThree.PartTwo.Sec21.Item229Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item22Sec7
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open Matrix

variable {G : Type} [Group G]


theorem mem_of_mem_centralizer_of_orderOf_eq_three' {A : Subgroup G} (hA : A ∈ partTwoF G)
    {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : orderOf x = 3) : x ∈ A :=
  Sec4.mem_of_maximal_of_commute ⟨hA.1, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
    (by rw [← hx3]; exact pow_orderOf_eq_one x) fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha

theorem exists_coord_image_dStar [Finite G] (h2131 : Item2131One) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A, (wStar A).map (coordGL f) ≤ monomial ∧
      (coordGL f '' dStar A = swapRefl ∨ coordGL f '' dStar A = monoRefl) := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : IsMulCommutative A := hAe.1
  obtain ⟨f, hWf, G₀, hG₀W, ⟨eG₀⟩⟩ := h2131 G A E U c L hpair hA27
  obtain ⟨-, ⟨φ0, hφ0L, hφ0D⟩, hcase⟩ := h222 G A E U c L hpair
  have hDW := dStar_subset_wStar A
  have hinj := coordGL_injective f
  have hG₀m : G₀.map (coordGL f) ≤ monomial := (Subgroup.map_mono hG₀W).trans hWf
  let eG₀' : G₀.map (coordGL f) ≃* alternatingGroup (Fin 4) :=
    (G₀.equivMapOfInjective _ hinj).symm.trans eG₀
  have hDm : ∀ d ∈ dStar A, coordGL f d ∈ monomial := fun d hd => hWf ⟨d, hDW hd, rfl⟩
  have hDr : ∀ d ∈ dStar A, IsReflectionOn d := fun d hd => hd.1
  have hinv : ∀ g ∈ G₀, ∀ d ∈ dStar A, g * d * g⁻¹ ∈ dStar A :=
    fun g hg d hd => conj_mem_dStar_of_mem_wStar (hG₀W hg) hd
  have hcase0 := hcase φ0 hφ0L hφ0D
  obtain ⟨s, hsL, hsD, t, htL, htD, hst⟩ : ∃ s ∈ starOf A L, s ∈ dStar A ∧
      ∃ t ∈ starOf A L, t ∈ dStar A ∧ s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    have hcomm : ((starOf A L : Set (MulAut A)) ∩ dStar A).Pairwise Commute :=
      fun x hx y hy _ => hcon x hx.1 hx.2 y hy.1 hy.2
    have hab : IsMulCommutative (starOf A L) := by
      have h1 := Subgroup.isMulCommutative_closure hcomm
      have hgen := (h222 G A E U c L hpair).1
      rw [← hgen] at h1
      exact h1
    rcases hcase0 with ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
        ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
    · exact not_isMulCommutative_perm_three (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · rw [hA27] at h81
      norm_num at h81
  exact ⟨f, hWf, image_eq_swapRefl_or_eq_monoRefl hAc f hG₀m eG₀' hDm hDr hinv
    ⟨s, hsD, t, htD, hst⟩⟩

theorem nonempty_kOf_conj_mulEquiv [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    (w : Subgroup.normalizer (A : Set G)) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    Nonempty (kOf A (wConj A w * φ * (wConj A w)⁻¹) ≃* kOf A φ) := by
  rw [kOf_conj_of_unique hK w hφ]
  exact ⟨((kOf A φ).equivMapOfInjective _ (MulAut.conj (w : G)).injective).symm⟩

theorem nonempty_kOf_mulEquiv_of_conj [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) {g : MulAut A} (hg : g ∈ wStar A)
    (h : g * φ * g⁻¹ = ψ) : Nonempty (kOf A ψ ≃* kOf A φ) := by
  obtain ⟨w, rfl⟩ := hg
  rw [← h]
  exact nonempty_kOf_conj_mulEquiv hK w hφ

theorem mul_self_of_mem_dStar {A : Subgroup G} {φ : MulAut A} (hφ : φ ∈ dStar A) : φ * φ = 1 :=
  Sec7.mul_self_eq_one_of_orderOf_eq_two hφ.1.1

theorem nonempty_kOf_mulEquiv_of_orderOf_eq_three [Finite G] {A : Subgroup G}
    (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A)
    (h3 : orderOf (φ * ψ) = 3) : Nonempty (kOf A ψ ≃* kOf A φ) := by
  have hc := Sec7.conj_eq_of_orderOf_mul_eq_three (mul_self_of_mem_dStar hφ)
    (mul_self_of_mem_dStar hψ) (by rw [← h3]; exact pow_orderOf_eq_one _)
  exact nonempty_kOf_mulEquiv_of_conj hK hφ ((wStar A).mul_mem (dStar_subset_wStar A hφ)
    (dStar_subset_wStar A hψ)) hc

theorem mem_starOf_sup [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) :
    φ ∈ starOf A (kOf A φ ⊔ kOf A ψ) ∧ ψ ∈ starOf A (kOf A φ ⊔ kOf A ψ) :=
  ⟨starOf_mono A le_sup_left (mem_starOf_kOf h222 hpair hK hφ),
    starOf_mono A le_sup_right (mem_starOf_kOf h222 hpair hK hψ)⟩

theorem dvd_card_starOf {A X : Subgroup G} {g : MulAut A} (hg : g ∈ starOf A X) :
    orderOf g ∣ Nat.card (starOf A X) := by
  have := orderOf_dvd_natCard (⟨g, hg⟩ : starOf A X)
  rwa [Subgroup.orderOf_mk] at this


theorem not_dihedral_of_image_eq_swapRefl {A : Subgroup G}
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (hD : coordGL f '' dStar A = swapRefl)
    {Z : Subgroup (MulAut A)} (hZ : Z = Subgroup.closure ((Z : Set (MulAut A)) ∩ dStar A))
    (e : Z ≃* DihedralGroup 4) : False := by
  have hinj := coordGL_injective f
  have hsw : ∀ d ∈ dStar A, coordGL f d ∈ swapRefl := fun d hd => hD ▸ ⟨d, hd, rfl⟩
  have hcard : Nat.card Z = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  by_cases hcomm : ((Z : Set (MulAut A)) ∩ dStar A).Pairwise Commute
  · have hab := Subgroup.isMulCommutative_closure hcomm
    rw [← hZ] at hab
    exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
  · simp only [Set.Pairwise, not_forall] at hcomm
    obtain ⟨x, hx, y, hy, -, hxy⟩ := hcomm
    rcases swapRefl_commute_or_cube (hsw x hx.2) (hsw y hy.2) with hc | h3
    · exact hxy (hinj (by rw [map_mul, map_mul]; exact hc))
    · have h3' : (x * y) ^ 3 = 1 := hinj (by rw [map_pow, map_mul, h3, map_one])
      have hne : x * y ≠ 1 := by
        intro h1
        apply hxy
        have hx2 : x * x = 1 := mul_self_of_mem_dStar hx.2
        have : y = x := by
          calc y = x * x * y := by rw [hx2, one_mul]
            _ = x * (x * y) := by rw [mul_assoc]
            _ = x := by rw [h1, mul_one]
        rw [this]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf (x * y) = 3 := orderOf_eq_prime h3' hne
      have hxyZ : x * y ∈ Z := Z.mul_mem hx.1 hy.1
      have hdvd := orderOf_dvd_natCard (⟨x * y, hxyZ⟩ : Z)
      rw [Subgroup.orderOf_mk, hord, hcard] at hdvd
      norm_num at hdvd

theorem isSimpleGroup_projSL_two {m : ℕ} (hm : 2 ≤ m) :
    IsSimpleGroup (projSL 2 (GaloisField 2 m)) :=
  have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ le_rfl (Or.inr (by omega)) (Or.inr (by omega))

theorem exists_not_commute_of_mulEquiv_projSL {X : Type*} [Group X] {m : ℕ}
    (e : X ≃* projSL 2 (GaloisField 2 m)) : ∃ a b : X, a * b ≠ b * a := by
  let e' := e.trans (projSLTwoEquivSL (GaloisField 2 m))
  have hz : orderOf (e'.symm sl2OrderThree) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_sl2OrderThree
  obtain ⟨j, -, hjz⟩ := exists_inv_conj_of_mulEquiv_projSL e hz
  refine ⟨j, e'.symm sl2OrderThree, fun h => ?_⟩
  rw [h, mul_inv_cancel_right] at hjz
  have h2 : (e'.symm sl2OrderThree) ^ 2 = 1 := by
    rw [sq]
    calc e'.symm sl2OrderThree * e'.symm sl2OrderThree =
        e'.symm sl2OrderThree * (e'.symm sl2OrderThree)⁻¹ := by rw [← hjz]
      _ = 1 := mul_inv_cancel _
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hz] at this
  norm_num at this

theorem isPerfect_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact hab (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top a)) b
      (Subgroup.mem_top b)).symm
  · exact ht

theorem isPerfect_of_mulEquiv_projSL {X : Type*} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* projSL 2 (GaloisField 2 m)) : Group.IsPerfect X := by
  have := isSimpleGroup_projSL_two hm
  have : IsSimpleGroup X := e.isSimpleGroup
  exact isPerfect_of_isSimpleGroup (exists_not_commute_of_mulEquiv_projSL e)

theorem isPerfect_sup {X Y : Subgroup G} (hX : Group.IsPerfect X) (hY : Group.IsPerfect Y) :
    Group.IsPerfect (X ⊔ Y : Subgroup G) := by
  rw [Subgroup.isPerfect_iff] at hX hY ⊢
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (X ⊔ Y).mul_mem ((X ⊔ Y).mul_mem ((X ⊔ Y).mul_mem ha hb) ((X ⊔ Y).inv_mem ha))
      ((X ⊔ Y).inv_mem hb)
  · calc X = ⁅X, X⁆ := hX.symm
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc Y = ⁅Y, Y⁆ := hY.symm
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem not_lBar_SL3_of_simple [Finite G] {Y : Subgroup G} (hY : Group.IsPerfect Y)
    {S : Type} [Group S] [IsSimpleGroup S] (e : Y ≃* S) {n : ℕ} (hn : 0 < n) (he : Even n)
    (eL : lBar Y ≃* SL3 n) : False := by
  have : IsSimpleGroup Y := e.isSimpleGroup
  have hθ := inSubgroup_theta_eq_bot_of_isSimpleGroup hY
  have : IsSimpleGroup (SL3 n) :=
    (((mulEquiv_lBar_of_theta_eq_bot hθ).trans eL).symm.trans e).isSimpleGroup
  exact not_isSimpleGroup_SL3 hn he this

theorem card_of_mulEquiv_dihedral {X : Type*} [Group X] (e : X ≃* DihedralGroup 4) :
    Nat.card X = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

theorem card_of_mulEquiv_perm_three {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    Nat.card X = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl


theorem commute_kOf_of_not_conj [Finite G] (h228 : Item228) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) (hc : ψ * φ = φ * ψ)
    (hnconj : ∀ w ∈ wStar A, w * φ * w⁻¹ ≠ ψ) :
    ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x := by
  obtain ⟨-, hX2, -⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX2 hc with hb | ⟨-, -, -, -, -, -, -, w, hw, hwφ⟩ | ⟨-, -, -, -, w, hw, hwφ⟩
  · intro x hx y hy
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  · exact (hnconj w hw hwφ).elim
  · exact (hnconj w hw hwφ).elim


theorem inf_eq_bot_of_commute {X Y : Subgroup G} {m : ℕ}
    (e : X ≃* projSL 2 (GaloisField 2 m)) (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ⊓ Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hz.1⟩ : X) = 1 := eq_one_of_forall_commute_of_mulEquiv_projSL e fun x =>
    Subtype.ext (h x x.2 z hz.2)
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)


theorem iSup_fin_three (K : Fin 3 → Subgroup G) : (⨆ i, K i) = K 0 ⊔ K 1 ⊔ K 2 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup K 0) (le_iSup K 1)) (le_iSup K 2)

theorem iGroup_eq_sup_three [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {t₁ t₂ t₃ : MulAut A}
    (h₁ : t₁ ∈ dStar A) (h₂ : t₂ ∈ dStar A) (h₃ : t₃ ∈ dStar A)
    (hfuse : ∀ φ ∈ dStar A, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)),
      ∃ τ ∈ ({t₁, t₂, t₃} : Set (MulAut A)), g * τ * g⁻¹ = φ) :
    iGroup A = kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃ := by
  have hT : ({t₁, t₂, t₃} : Set (MulAut A)) ⊆ dStar A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  rw [iGroup_eq_iSup_of_fuse h222 hpair hK hT hfuse, iSup_insert, iSup_insert, iSup_singleton,
    sup_assoc]

theorem isChainSystem_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {t₁ t₂ t₃ : MulAut A}
    (h₁ : t₁ ∈ dStar A) (h₂ : t₂ ∈ dStar A) (h₃ : t₃ ∈ dStar A) (h12 : t₁ ≠ t₂)
    (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) (hAI : A ≤ kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃)
    (hc : ∀ x ∈ kOf A t₁, ∀ y ∈ kOf A t₃, x * y = y * x) (hinf : kOf A t₁ ⊓ kOf A t₃ = ⊥) :
    IsChainSystem 3 A ![kOf A t₁, kOf A t₂, kOf A t₃] where
  commute i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact hc
  inf_eq_bot i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact hinf
  elem := hpair.mem_S.1.1
  le := by
    rw [iSup_fin_three]
    simpa using hAI
  split i := by
    fin_cases i
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₁
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₂
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₃
  index i := by
    fin_cases i
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₁
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₂
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₃
  index₂ i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₁ h₂ h12
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₁ h₃ h13
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₂ h₁ h12.symm
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₂ h₃ h23
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₃ h₁ h13.symm
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₃ h₂ h23.symm


end CFSG.RankThree.PartTwo.Sec21
