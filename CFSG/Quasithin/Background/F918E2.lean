module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.SummandSwap
public import CFSG.Quasithin.Background.D2Offenders
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

open SummandSwap

variable {V : Type*} [CommGroup V]

private theorem le_stabSub_of_forall {A : Subgroup (MulAut V)} {U : Subgroup V}
    (h : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) : A ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, h g hg u⟩
  have := h g⁻¹ (A.inv_mem hg) (g u) hu
  simpa using this

section TwoSummand

variable {A : Subgroup (MulAut V)} {I : Subgroup V} {a : MulAut V}

private theorem aut_mem_sup_map (hAe : IsElemAbelian2 A) (haA : a ∈ A) {u : V}
    (hu : u ∈ I ⊔ I.map a.toMonoidHom) : a u ∈ I ⊔ I.map a.toMonoidHom := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  rw [map_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem a.toMonoidHom hy))
    (Subgroup.mem_sup_left ?_)
  have e : a (a w) = w := aut_sq_apply hAe haA w
  simpa [e] using hw


private theorem inf_centSub_sup_map (hAe : IsElemAbelian2 A) (haA : a ∈ A) :
    A ⊓ centSub (I ⊔ I.map a.toMonoidHom) = (A ⊓ stabSub I) ⊓ centSub I := by
  ext g
  constructor
  · rintro ⟨hg, hgc⟩
    have hgI : g ∈ centSub I := fun u hu => hgc u (Subgroup.mem_sup_left hu)
    exact ⟨⟨hg, centSub_le_stabSub I hgI⟩, hgI⟩
  · rintro ⟨⟨hg, -⟩, hgI⟩
    refine ⟨hg, fun u hu => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [map_mul, hgI y hy]
    show y * g (a w) = y * a w
    rw [aut_comm_apply hAe hg haA, hgI w hw]

section Ranks

variable [Finite V]

omit [Finite V] in
private theorem rk_map_aut (J : Subgroup V) (g : MulAut V) : rk ↥(J.map g.toMonoidHom) = rk J := by
  unfold rk
  rw [Subgroup.card_map_of_injective (by exact g.injective)]

private theorem rk_sup_map (hdisj : Disjoint I (I.map a.toMonoidHom)) :
    rk ↥(I ⊔ I.map a.toMonoidHom) = 2 * rk I := by
  have h := rk_sup_add_rk_inf I (I.map a.toMonoidHom)
  rw [disjoint_iff.mp hdisj, rk_bot, rk_map_aut] at h
  omega


end Ranks

end TwoSummand


section Decomp

variable {ι : Type*} {I : ι → Subgroup V}

private theorem summand_ne_bot (hrank : ∀ i, 2 ≤ rk (I i)) (i : ι) : I i ≠ ⊥ := by
  intro h
  have := hrank i
  rw [h, rk_bot] at this
  omega

private theorem support_closed (hind : iSupIndep I) (hinj : Function.Injective I)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {f : κ → ι} (hf : Function.Injective f) {y : κ → V}
    (hy : ∀ m, y m ∈ I (f m) ∧ y m ≠ 1) {g : MulAut V}
    (hg : g (∏ m, y m) = ∏ m, y m) (hk : ∀ m, ∃ l, (I (f m)).map g.toMonoidHom = I l) :
    ∀ m, ∃ m', (I (f m)).map g.toMonoidHom = I (f m') := by
  intro m₀
  choose l hl using hk
  by_contra hcon
  push Not at hcon
  have hl₀ : ∀ m', l m₀ ≠ f m' := fun m' h => hcon m' (by rw [hl m₀, h])
  set T : Subgroup V := ⨆ (j : ι) (_ : j ≠ l m₀), I j with hT
  have hIle : ∀ j, j ≠ l m₀ → I j ≤ T := fun j hj => le_iSup₂ (f := fun j _ => I j) j hj
  have hlne : ∀ m, m ≠ m₀ → l m ≠ l m₀ := by
    intro m hm h
    apply hm
    have h1 : (I (f m)).map g.toMonoidHom = (I (f m₀)).map g.toMonoidHom := by
      rw [hl m, hl m₀, h]
    exact hf (hinj (Subgroup.map_injective g.injective h1))
  have hgy : ∀ m, g (y m) ∈ I (l m) := fun m => by
    rw [← hl m]; exact Subgroup.mem_map_of_mem _ (hy m).1
  have h1 : ∏ m, y m ∈ T :=
    Subgroup.prod_mem _ fun m _ => hIle _ (hl₀ m).symm ((hy m).1)
  have h2 : ∏ m ∈ Finset.univ.erase m₀, g (y m) ∈ T :=
    Subgroup.prod_mem _ fun m hm => hIle _ (hlne m (Finset.ne_of_mem_erase hm)) (hgy m)
  have hEq : g (y m₀) * ∏ m ∈ Finset.univ.erase m₀, g (y m) = ∏ m, y m := by
    rw [Finset.mul_prod_erase Finset.univ (fun m => g (y m)) (Finset.mem_univ m₀), ← map_prod]
    exact hg
  have h3 : g (y m₀) ∈ T := by
    have : g (y m₀) = (∏ m, y m) * (∏ m ∈ Finset.univ.erase m₀, g (y m))⁻¹ := by
      rw [← hEq]; group
    rw [this]
    exact T.mul_mem h1 (T.inv_mem h2)
  have h4 : g (y m₀) = 1 := Subgroup.disjoint_def.mp (hind (l m₀)) (hgy m₀) h3
  exact (hy m₀).2 (g.injective (by rw [h4, map_one]))

private theorem map_mul_aut (g h : MulAut V) (J : Subgroup V) :
    J.map (g * h).toMonoidHom = (J.map h.toMonoidHom).map g.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem mem_stabSub_iff_map {g : MulAut V} {J : Subgroup V} :
    g ∈ stabSub J ↔ J.map g.toMonoidHom = J :=
  CFSG.Quasithin.StabLat.mem_stabSub_iff_map

private theorem inv_mul_mem_stabSub_of_map_eq {g h : MulAut V} {J : Subgroup V}
    (hgh : J.map g.toMonoidHom = J.map h.toMonoidHom) : g⁻¹ * h ∈ stabSub J := by
  rw [mem_stabSub_iff_map, map_mul_aut, ← hgh, ← map_mul_aut, inv_mul_cancel]
  ext u
  simp

private theorem exists_partner (hind : iSupIndep I) {A : Subgroup (MulAut V)}
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) {i : ι} {a : MulAut V}
    (haA : a ∈ A) (haI : a ∉ stabSub (I i)) :
    ∃ j, j ≠ i ∧ (I i).map a.toMonoidHom = I j ∧
      Disjoint (I i) ((I i).map a.toMonoidHom) := by
  obtain ⟨j, hj⟩ := hperm a haA i
  have hji : j ≠ i := by
    rintro rfl
    exact haI (mem_stabSub_iff_map.mpr hj)
  exact ⟨j, hji, hj, by rw [hj]; exact hind.pairwiseDisjoint hji.symm⟩

private theorem cosets_cover_of_fixed (hind : iSupIndep I)
    (hrank : ∀ i, 2 ≤ rk (I i)) {A : Subgroup (MulAut V)}
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) {i : ι} {a : MulAut V}
    (haA : a ∈ A) (haI : a ∉ stabSub (I i)) {x : V} (hx : x ∈ I i) (hx1 : x ≠ 1)
    (hfix : x * a x ∈ fixV A) : ∀ g ∈ A, g ∈ stabSub (I i) ∨ a⁻¹ * g ∈ stabSub (I i) := by
  obtain ⟨j, hji, hj, -⟩ := exists_partner hind hperm haA haI
  have hinj : Function.Injective I := hind.injective (summand_ne_bot hrank)
  intro g hg
  have hf : Function.Injective (![i, j] : Fin 2 → ι) := by
    intro m n h
    fin_cases m <;> fin_cases n <;> simp_all [eq_comm]
  have hy : ∀ m : Fin 2, (![x, a x] : Fin 2 → V) m ∈ I (![i, j] m) ∧
      (![x, a x] : Fin 2 → V) m ≠ 1 := by
    intro m
    fin_cases m
    · exact ⟨hx, hx1⟩
    · refine ⟨?_, fun h => hx1 (a.injective (by simpa using h))⟩
      show a x ∈ I j
      rw [← hj]
      exact Subgroup.mem_map_of_mem _ hx
  have hprod : ∏ m : Fin 2, (![x, a x] : Fin 2 → V) m = x * a x := by
    simp [Fin.prod_univ_two]
  have hg' : g (∏ m : Fin 2, (![x, a x] : Fin 2 → V) m) =
      ∏ m : Fin 2, (![x, a x] : Fin 2 → V) m := by
    rw [hprod]
    exact hfix g hg
  have hk : ∀ m : Fin 2, ∃ l, (I (![i, j] m)).map g.toMonoidHom = I l :=
    fun m => hperm g hg _
  obtain ⟨m', hm'⟩ := support_closed hind hinj hf hy hg' hk 0
  fin_cases m'
  · left
    exact mem_stabSub_iff_map.mpr (by simpa using hm')
  · right
    have h1 : (I i).map g.toMonoidHom = (I i).map a.toMonoidHom := by
      rw [hj]
      simpa using hm'
    exact inv_mul_mem_stabSub_of_map_eq h1.symm

end Decomp


section Main

variable [Finite V] {ι : Type*}

omit [Finite V] in
private theorem aut_ne_self {I : Subgroup V} {a : MulAut V}
    (hdisj : Disjoint I (I.map a.toMonoidHom)) {x : V} (hx : x ∈ I) (hx1 : x ≠ 1) : a x ≠ x := by
  intro h
  have h2 : x ∈ I.map a.toMonoidHom := by
    have := Subgroup.mem_map_of_mem a.toMonoidHom hx
    have e : a.toMonoidHom x = x := h
    rwa [e] at this
  exact hx1 (Subgroup.disjoint_def.mp hdisj hx h2)

omit [Finite V] in
private theorem commSub_ne_bot_of_moved {A : Subgroup (MulAut V)} {J : Subgroup V} {a : MulAut V}
    (haA : a ∈ A) {x : V} (hxJ : x ∈ J) (hmove : a x ≠ x) : commSub J A ≠ ⊥ := by
  rw [Ne, commSub_eq_bot_iff]
  exact fun h => hmove (h hxJ a haA)

private theorem relIndex_le_two_of_cos {G : Type*} [Group G] {A S : Subgroup G} {a : G}
    (haA : a ∈ A) (hcos : ∀ g ∈ A, g ∈ S ∨ a⁻¹ * g ∈ S) : (A ⊓ S).relIndex A ≤ 2 := by
  refine relIndex_le_of_cover ![1, a] (fun m => ?_) (fun g hg => ?_)
  · fin_cases m
    · exact A.one_mem
    · exact haA
  · rcases hcos g hg with h | h
    · exact ⟨0, by simpa using ⟨hg, h⟩⟩
    · exact ⟨1, by simpa using ⟨A.mul_mem (A.inv_mem haA) hg, h⟩⟩


private theorem rk_le_of_relIndex_le_four {A B : Subgroup (MulAut V)} (hBA : B ≤ A)
    (hle : B.relIndex A ≤ 4) : rk A ≤ rk B + 2 := by
  have hmul := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr hBA] at hmul
  have h0 : B.relIndex A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact (Nat.card_pos (α := A)).ne' hmul.symm
  unfold rk
  rw [← hmul, padicValNat.mul h0 Nat.card_pos.ne']
  have hv : 2 ^ padicValNat 2 (B.relIndex A) ≤ B.relIndex A :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero h0) pow_padicValNat_dvd
  have : padicValNat 2 (B.relIndex A) ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hcon
    omega
  omega


omit [Finite V] in
private theorem exists_ne_one_of_ne_bot {J : Subgroup V} (h : J ≠ ⊥) : ∃ x ∈ J, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h ((Subgroup.eq_bot_iff_forall _).mpr hcon)

private theorem four_summands_absurd (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : A ∈ kRPlusLe X 3 2) {I : ι → Subgroup V} (hind : iSupIndep I)
    (hrank : ∀ i, 2 ≤ rk (I i))
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) (i : ι) {a c : MulAut V}
    (haA : a ∈ A) (hcA : c ∈ A) (haI : a ∉ stabSub (I i)) (hcI : c ∉ stabSub (I i))
    (hacI : a⁻¹ * c ∉ stabSub (I i)) (hIB : commSub (I i) (A ⊓ stabSub (I i)) = ⊥) : False := by
  obtain ⟨⟨⟨hA2, hAr⟩, hAk⟩, hAplus⟩ := hA
  have hAe : IsElemAbelian2 A := hA2.isElemAbelian2
  have ha1 : a⁻¹ = a := aut_inv_eq hAe haA
  have hca : c * a = a * c := hAe.1 c hcA a haA
  have hinj : Function.Injective I := hind.injective (summand_ne_bot hrank)
  have hBc : ∀ b ∈ A ⊓ stabSub (I i), ∀ y ∈ I i, b y = y := fun b hb y hy =>
    commSub_eq_bot_iff.mp hIB hy b hb
  obtain ⟨k₂, hk₂⟩ := hperm a haA i
  obtain ⟨k₃, hk₃⟩ := hperm c hcA i
  obtain ⟨k₄, hk₄⟩ := hperm c hcA k₂
  rw [← hk₂] at hk₄
  have hS₁ : (I i).map (1 : MulAut V).toMonoidHom = I i := mem_stabSub_iff_map.mp (one_mem _)
  have hS₄ : (I i).map (c * a).toMonoidHom = I k₄ := (map_mul_aut c a (I i)).trans hk₄
  have hne : ∀ g h : MulAut V, g⁻¹ * h ∉ stabSub (I i) →
      (I i).map g.toMonoidHom ≠ (I i).map h.toMonoidHom :=
    fun g h hgh heq => hgh (inv_mul_mem_stabSub_of_map_eq heq)
  have h12 : i ≠ k₂ := fun h => hne 1 a (by simpa using haI) (by rw [hS₁, hk₂, ← h])
  have h13 : i ≠ k₃ := fun h => hne 1 c (by simpa using hcI) (by rw [hS₁, hk₃, ← h])
  have hacI' : a * c ∉ stabSub (I i) := by rwa [ha1] at hacI
  have h14 : i ≠ k₄ := fun h => hne 1 (c * a) (by rw [hca, inv_one, one_mul]; exact hacI')
    (by rw [hS₁, hS₄, ← h])
  have h23 : k₂ ≠ k₃ := fun h => hne a c hacI (by rw [hk₂, hk₃, h])
  have hh : a⁻¹ * (c * a) = c := by rw [hca]; exact inv_mul_cancel_left a c
  have h24 : k₂ ≠ k₄ := fun h => hne a (c * a) (by rw [hh]; exact hcI) (by rw [hk₂, hS₄, h])
  have h34 : k₃ ≠ k₄ := fun h => hne c (c * a) (by rw [inv_mul_cancel_left]; exact haI)
    (by rw [hk₃, hS₄, h])
  have hf : Function.Injective (![i, k₂, k₃, k₄] : Fin 4 → ι) := by
    intro m n h
    fin_cases m <;> fin_cases n <;> simp at h ⊢
    all_goals first
      | exact absurd h (by assumption)
      | exact absurd h.symm (by assumption)
  obtain ⟨x, hxI, hx1⟩ := exists_ne_one_of_ne_bot (summand_ne_bot hrank i)
  have hax : a x ∈ I k₂ := by
    rw [← hk₂]
    exact Subgroup.mem_map_of_mem a.toMonoidHom hxI
  have hcx : c x ∈ I k₃ := by
    rw [← hk₃]
    exact Subgroup.mem_map_of_mem c.toMonoidHom hxI
  have hcax : c (a x) ∈ I k₄ := by
    rw [← hk₄]
    exact Subgroup.mem_map_of_mem c.toMonoidHom (Subgroup.mem_map_of_mem a.toMonoidHom hxI)
  have hy : ∀ m : Fin 4, (![x, a x, c x, c (a x)] : Fin 4 → V) m ∈ I (![i, k₂, k₃, k₄] m) ∧
      (![x, a x, c x, c (a x)] : Fin 4 → V) m ≠ 1 := by
    intro m
    fin_cases m
    · exact ⟨hxI, hx1⟩
    · exact ⟨hax, fun h => hx1 (a.injective (by simpa using h))⟩
    · exact ⟨hcx, fun h => hx1 (c.injective (by simpa using h))⟩
    · exact ⟨hcax, fun h => hx1 (a.injective (c.injective (by simpa using h)))⟩
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV x)
  have hwinv : (x * a x)⁻¹ = x * a x :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV _)
  have hw1 : x * a x ∈ commSub ⊤ A := by
    have : a x * x⁻¹ ∈ commSub ⊤ A :=
      Subgroup.subset_closure ⟨a, haA, x, Subgroup.mem_top x, rfl⟩
    rwa [hxinv, mul_comm] at this
  have hv1 : c (x * a x) * (x * a x)⁻¹ ∈ commSub (commSub ⊤ A) A :=
    Subgroup.subset_closure ⟨c, hcA, x * a x, hw1, rfl⟩
  have hfixA : commSeries A 2 ≤ fixV A := commSub_eq_bot_iff.mp hAk
  have hvfix : (x * a x) * c (x * a x) ∈ fixV A := by
    have := hfixA hv1
    rwa [hwinv, mul_comm] at this
  have hprod : ∏ m : Fin 4, (![x, a x, c x, c (a x)] : Fin 4 → V) m =
      (x * a x) * c (x * a x) := by
    rw [Fin.prod_univ_four]
    simp [map_mul, mul_assoc]
  have hsupp : ∀ g ∈ A, ∀ m : Fin 4, ∃ m' : Fin 4,
      (I (![i, k₂, k₃, k₄] m)).map g.toMonoidHom = I (![i, k₂, k₃, k₄] m') := by
    intro g hg
    refine support_closed hind hinj hf hy ?_ (fun m => hperm g hg _)
    rw [hprod]
    exact hvfix g hg
  have hrep : ∀ m : Fin 4, I (![i, k₂, k₃, k₄] m) =
      (I i).map (![1, a, c, c * a] m).toMonoidHom := by
    intro m
    fin_cases m
    · exact hS₁.symm
    · exact hk₂.symm
    · exact hk₃.symm
    · exact hS₄.symm
  have hmem : ∀ m : Fin 4, (![1, a, c, c * a] : Fin 4 → MulAut V) m ∈ A := by
    intro m
    fin_cases m
    · exact A.one_mem
    · exact haA
    · exact hcA
    · exact A.mul_mem hcA haA
  have hcover : ∀ g ∈ A, ∃ m : Fin 4, (![1, a, c, c * a] m)⁻¹ * g ∈ A ⊓ stabSub (I i) := by
    intro g hg
    obtain ⟨m', hm'⟩ := hsupp g hg 0
    refine ⟨m', A.mul_mem (A.inv_mem (hmem m')) hg,
      inv_mul_mem_stabSub_of_map_eq ?_⟩
    rw [← hrep m']
    exact hm'.symm
  have hle4 : (A ⊓ stabSub (I i)).relIndex A ≤ 4 :=
    relIndex_le_of_cover ![1, a, c, c * a] hmem hcover
  have hrkA : rk A ≤ rk ↥(A ⊓ stabSub (I i)) + 2 := rk_le_of_relIndex_le_four inf_le_left hle4
  obtain ⟨-, -, -, hdisj⟩ := exists_partner hind hperm haA haI
  obtain ⟨U, hU⟩ : ∃ U : Subgroup V, U = I i ⊔ (I i).map a.toMonoidHom := ⟨_, rfl⟩
  have hUk : U = I i ⊔ I k₂ := by rw [hU, hk₂]
  have hU'c : U.map c.toMonoidHom = I k₃ ⊔ I k₄ := by
    rw [hU, Subgroup.map_sup, hk₃, hk₄]
  obtain ⟨W, hW⟩ : ∃ W : Subgroup V, W = U ⊔ U.map c.toMonoidHom := ⟨_, rfl⟩
  have hWk : W = (I i ⊔ I k₂) ⊔ (I k₃ ⊔ I k₄) := by rw [hW, hU'c, hUk]
  have hdisjU : Disjoint U (U.map c.toMonoidHom) := by
    rw [hU'c, hUk]
    have hst : Disjoint ({i, k₂} : Set ι) ({k₃, k₄} : Set ι) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hz'
      rcases hz with h1 | h1 <;> rcases hz' with h2 | h2
      · exact h13 (h1.symm.trans h2)
      · exact h14 (h1.symm.trans h2)
      · exact h23 (h1.symm.trans h2)
      · exact h24 (h1.symm.trans h2)
    have := hind.disjoint_biSup_biSup' hst (Set.toFinite _)
    simp only [iSup_insert, iSup_singleton] at this
    exact this
  have hIleW : ∀ m : Fin 4, I (![i, k₂, k₃, k₄] m) ≤ W := by
    intro m
    rw [hWk]
    fin_cases m
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  have hWst : A ≤ stabSub W := by
    apply le_stabSub_of_forall
    intro g hg w hw
    have hle : W.map g.toMonoidHom ≤ W := by
      rw [hWk, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
      obtain ⟨m0, hm0⟩ := hsupp g hg 0
      obtain ⟨m1, hm1⟩ := hsupp g hg 1
      obtain ⟨m2, hm2⟩ := hsupp g hg 2
      obtain ⟨m3, hm3⟩ := hsupp g hg 3
      have e0 : (I i).map g.toMonoidHom ≤ W := by
        have := hIleW m0
        rw [← hm0] at this
        exact this
      have e1 : (I k₂).map g.toMonoidHom ≤ W := by
        have := hIleW m1
        rw [← hm1] at this
        exact this
      have e2 : (I k₃).map g.toMonoidHom ≤ W := by
        have := hIleW m2
        rw [← hm2] at this
        exact this
      have e3 : (I k₄).map g.toMonoidHom ≤ W := by
        have := hIleW m3
        rw [← hm3] at this
        exact this
      rw [hWk] at e0 e1 e2 e3
      exact sup_le (sup_le e0 e1) (sup_le e2 e3)
    exact hle (Subgroup.mem_map_of_mem g.toMonoidHom hw)
  have hxW : x ∈ W := hIleW 0 hxI
  have hWA : commSub W A ≠ ⊥ := commSub_ne_bot_of_moved haA hxW (aut_ne_self hdisj hxI hx1)
  have hrkU : rk ↥U = 2 * rk (I i) := by rw [hU]; exact rk_sup_map hdisj
  have hrkW : rk ↥W = 4 * rk (I i) := by
    have h := rk_sup_add_rk_inf U (U.map c.toMonoidHom)
    rw [disjoint_iff.mp hdisjU, rk_bot, rk_map_aut, ← hW] at h
    omega
  have hfixW : ∀ v ∈ W ⊓ fixV A, ∃ y ∈ I i, (y * a y) * c (y * a y) = v := by
    rintro v ⟨hvW, hvA⟩
    rw [hW] at hvW
    obtain ⟨u, hu, hcu⟩ := exists_diag_of_fixed hAe hcA hdisjU hvW (hvA c hcA)
    have hau : a u = u := by
      have h1 := hvA a haA
      rw [← hcu, map_mul, aut_comm_apply hAe haA hcA u] at h1
      have hmem : a u ∈ U := by
        rw [hU] at hu ⊢
        exact aut_mem_sup_map hAe haA hu
      exact diag_injOn hdisjU hmem hu h1
    obtain ⟨y, hy, hyu⟩ := exists_diag_of_fixed hAe haA hdisj (hU ▸ hu) hau
    exact ⟨y, hy, by rw [← hcu, ← hyu]⟩
  have hfixW_rk : rk ↥(W ⊓ fixV A) ≤ rk (I i) := by
    have hsub : ((W ⊓ fixV A : Subgroup V) : Set V) ⊆
        (fun y : V => (y * a y) * c (y * a y)) '' (I i : Set V) := by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := hfixW v hv
      exact ⟨y, hy, rfl⟩
    have h1 := Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card ((fun y : V => (y * a y) * c (y * a y)) '' (I i : Set V)) ≤
        Nat.card (I i : Set V) := Nat.card_image_le (Set.toFinite _)
    have h3 : Nat.card ↥(W ⊓ fixV A) ≤ Nat.card ↥(I i) := le_trans h1 h2
    rw [card_eq_two_pow hV (W ⊓ fixV A), card_eq_two_pow hV (I i)] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  have hBcW : A ⊓ stabSub (I i) ≤ centSub W := by
    intro b hb
    have hbU : ∀ u ∈ U, b u = u := by
      have : b ∈ A ⊓ centSub (I i ⊔ (I i).map a.toMonoidHom) := by
        rw [inf_centSub_sup_map hAe haA]
        exact ⟨hb, fun y hy => hBc b hb y hy⟩
      rw [← hU] at this
      exact this.2
    intro w hw
    rw [hW] at hw
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hz
    rw [map_mul, hbU u hu]
    show u * b (c u') = u * c u'
    rw [aut_comm_apply hAe hb.1 hcA, hbU u' hu']
  obtain ⟨hAW2, hAWr⟩ := D2_5 hV (X := X) (A := A) (r := 2) ⟨⟨hA2, hAr⟩, hAplus⟩ hWst hWA
  have hpos : 0 < rk (autSub A W) := hAW2.rk_pos
  have n1 := rk_autSub_add_rk_inf hWst
  have n2 := rkIdx_autSub_add hWst
  have hBle : rk ↥(A ⊓ stabSub (I i)) ≤ rk ↥(A ⊓ centSub W) :=
    rk_mono (le_inf inf_le_left hBcW)
  have hq : (rkIdx (fixV (autSub A W)) : ℚ) ≤ 2 * rk (autSub A W) := by
    unfold rAV at hAWr
    rwa [div_le_iff₀ (by exact_mod_cast hpos)] at hAWr
  have hq' : rkIdx (fixV (autSub A W)) ≤ 2 * rk (autSub A W) := by exact_mod_cast hq
  have hi2 := hrank i
  omega

private theorem d29_cover (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : A ∈ kRPlusLe X 3 2) {I : ι → Subgroup V} (hind : iSupIndep I)
    (hrank : ∀ i, 2 ≤ rk (I i))
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) (i : ι) {a : MulAut V}
    (haA : a ∈ A) (haI : a ∉ stabSub (I i)) :
    ∀ g ∈ A, g ∈ stabSub (I i) ∨ a⁻¹ * g ∈ stabSub (I i) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcA, hcI, hacI⟩ := hcon
  by_cases hIB : commSub (I i) (A ⊓ stabSub (I i)) = ⊥
  · exact four_summands_absurd hV hA hind hrank hperm i haA hcA haI hcI hacI hIB
  · obtain ⟨⟨⟨hA2, -⟩, hAk⟩, -⟩ := hA
    obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ commSub (I i) (A ⊓ stabSub (I i)), x ≠ 1 :=
      exists_ne_one_of_ne_bot hIB
    have hle1 : commSub (I i) (A ⊓ stabSub (I i)) ≤ I i :=
      commSub_le_of_invariant fun x hx w hw => (mem_stabSub.mp hx.2 w).mpr hw
    have hxI : x ∈ I i := hle1 hxB
    have hfixA : commSeries A 2 ≤ fixV A := commSub_eq_bot_iff.mp hAk
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV x)
    have hfix : x * a x ∈ fixV A := by
      have h1 : a x * x⁻¹ ∈ commSub (commSub (I i) (A ⊓ stabSub (I i))) A :=
        Subgroup.subset_closure ⟨a, haA, x, hxB, rfl⟩
      have h2 := hfixA (commSub_mono (commSub_mono le_top inf_le_left) le_rfl h1)
      rwa [hxinv, mul_comm] at h2
    rcases cosets_cover_of_fixed hind hrank hperm haA haI hxI hx1 hfix c hcA with h | h
    · exact hcI h
    · exact hacI h

theorem d29_index_le_two (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : A ∈ kRPlusLe X 3 2)
    {I : ι → Subgroup V} (hind : iSupIndep I) (_hsup : ⨆ i, I i = ⊤)
    (hrank : ∀ i, 2 ≤ rk (I i))
    (hperm : ∀ g ∈ A, ∀ i, ∃ j, (I i).map g.toMonoidHom = I j) (i : ι) :
    (A ⊓ stabSub (I i)).relIndex A ≤ 2 := by
  by_cases hB : A ⊓ stabSub (I i) < A
  · obtain ⟨a, haA, haB⟩ := IsConcreteLE.exists_of_lt hB
    have hcos := d29_cover hV hA hind hrank hperm i haA (fun h => haB ⟨haA, h⟩)
    exact relIndex_le_two_of_cos haA hcos
  · have : A ≤ A ⊓ stabSub (I i) := by
      by_contra h
      exact hB (lt_of_le_not_ge inf_le_left h)
    rw [Subgroup.relIndex_eq_one.mpr this]
    norm_num


end Main

end CFSG.Quasithin
