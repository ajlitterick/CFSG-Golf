module

public import CFSG.RankThree.Lattice.SteinbergBIE6QplusData
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFourStab

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 Matrix

@[expose] def e6SimpleOrbit (J : Set (Fin Tag.E6.rank)) (j : Fin Tag.E6.rank) :
    Set (Fin Tag.E6.rank → ℤ) :=
  {β | ∃ k : ℕ, β = (e6Delta J)^[k] (Pi.single j 1)}

@[expose] def e6Orbits (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) :
    Set (Set (Fin Tag.E6.rank → ℤ)) :=
  {O | ∃ j : Fin Tag.E6.rank, Pi.single j 1 ∈ e6Xi J i₀ ∧ O = e6SimpleOrbit J j}

@[expose] def e6RelWeyl (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) :
    Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure (setReflection '' e6Orbits J i₀)


@[expose] def e6RootOrbit (J : Set (Fin Tag.E6.rank)) (α : Fin Tag.E6.rank → ℤ) :
    Set (Fin Tag.E6.rank → ℤ) :=
  {β | ∃ k : ℕ, β = (e6Delta J)^[k] α}

section Delta

variable (m : Fin 15)

theorem e6Delta_qp_add (x y : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (x + y) = e6Delta (e6QpSupport m) x + e6Delta (e6QpSupport m) y := by
  rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_add]

theorem e6Delta_qp_sub (x y : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (x - y) = e6Delta (e6QpSupport m) x - e6Delta (e6QpSupport m) y := by
  rw [e6Delta_qp, e6Delta_qp, e6Delta_qp, Matrix.mulVec_sub]

theorem e6Delta_qp_neg (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (-x) = -e6Delta (e6QpSupport m) x := by
  rw [e6Delta_qp, e6Delta_qp, Matrix.mulVec_neg]

theorem e6Delta_qp_zsmul (c : ℤ) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (c • x) = c • e6Delta (e6QpSupport m) x := by
  rw [e6Delta_qp, e6Delta_qp, Matrix.mulVec_smul]

theorem iform_permLattice_e6Rho (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice e6Rho x) (permLattice e6Rho y) = iform x y := by
  have hB : ∀ i j, Tag.E6.symmetrizedCartan (e6Rho i) (e6Rho j) =
      Tag.E6.symmetrizedCartan i j := fun i j => by
    rw [symmetrizedCartan_E6]
    exact TwistTag.cartan_perm TwistTag.E6 i j
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp e6Rho (fun i => ∑ j, x (e6Rho.symm i) * Tag.E6.symmetrizedCartan i j *
    y (e6Rho.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e6Rho (fun j => x (e6Rho.symm (e6Rho i)) *
    Tag.E6.symmetrizedCartan (e6Rho i) j * y (e6Rho.symm j))]
  simp [hB]

theorem iform_e6Delta (J : Set (Fin Tag.E6.rank)) (x y : Fin Tag.E6.rank → ℤ) :
    iform (e6Delta J x) (e6Delta J y) = iform x y := by
  rw [e6Delta, e6Delta, ← neg_one_smul ℤ (e6Longest J • permLattice e6Rho x),
    ← neg_one_smul ℤ (e6Longest J • permLattice e6Rho y), iform_smul_left, iform_smul_right,
    iform_smul, iform_permLattice_e6Rho]
  ring

theorem e6Delta_qp_single {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6Delta (e6QpSupport m) (Pi.single j 1) = Pi.single (e6QpPerm m j) 1 := by
  rw [e6Delta_qp]
  exact (e6QpPerm_check m).2 j hj

theorem e6QpPerm_mem_iff (j : Fin Tag.E6.rank) :
    j ∈ e6QpSupport m ↔ e6QpPerm m j ∈ e6QpSupport m :=
  (e6QpPerm_check m).1 j

theorem single_one_inj {a b : Fin Tag.E6.rank}
    (h : (Pi.single a 1 : Fin Tag.E6.rank → ℤ) = Pi.single b 1) : a = b := by
  by_contra hab
  have h' := congrFun h a
  simp [hab] at h'

theorem e6QpPerm_perm_of_mem {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6QpPerm m (e6QpPerm m j) = j := by
  have h := e6Delta_qp_involutive m (Pi.single j 1)
  rw [e6Delta_qp_single m hj, e6Delta_qp_single m ((e6QpPerm_mem_iff m j).1 hj)] at h
  exact single_one_inj h

end Delta

section Components

variable (m : Fin 15)

theorem e6Delta_eq_permLattice {x : Fin Tag.E6.rank → ℤ}
    (hx : ∀ i, i ∉ e6QpSupport m → x i = 0) :
    e6Delta (e6QpSupport m) x = permLattice (e6QpPerm m) x := by
  rw [e6Delta_qp]
  set M := toMat Tag.E6.rank (e6QpDeltaList m)
  have hcol : ∀ j ∈ e6QpSupport m, ∀ k, M k j = if k = e6QpPerm m j then 1 else 0 :=
    fun j hj k => by
      have h := congrFun ((e6QpPerm_check m).2 j hj) k
      rw [Matrix.mulVec_single_one] at h
      have h' : M k j = (Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) k := h
      rw [h', Pi.single_apply]
  funext k
  simp only [Matrix.mulVec, dotProduct, permLattice, Function.comp_apply]
  rw [Finset.sum_eq_single ((e6QpPerm m).symm k)]
  · by_cases hk : (e6QpPerm m).symm k ∈ e6QpSupport m
    · rw [hcol _ hk, Equiv.apply_symm_apply]
      simp
    · rw [hx _ hk, mul_zero]
  · intro j _ hj
    by_cases hjJ : j ∈ e6QpSupport m
    · have hne : k ≠ e6QpPerm m j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
      rw [hcol j hjJ]
      simp [hne]
    · rw [hx j hjJ, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cartan_symm_E6 (a b : Fin Tag.E6.rank) : Tag.E6.cartan b a = Tag.E6.cartan a b := by
  have h := symmetrizedCartan_symm Tag.E6 a b
  rw [symmetrizedCartan_E6] at h
  exact h.symm

theorem iform_single_single_E6' (a b : Fin Tag.E6.rank) :
    iform (Pi.single a 1 : Fin Tag.E6.rank → ℤ) (Pi.single b 1) = Tag.E6.cartan a b := by
  rw [iform_single_left]
  have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
  simp [hd, Pi.single_apply]

theorem cartan_e6QpPerm {a b : Fin Tag.E6.rank} (ha : a ∈ e6QpSupport m)
    (hb : b ∈ e6QpSupport m) :
    Tag.E6.cartan (e6QpPerm m a) (e6QpPerm m b) = Tag.E6.cartan a b := by
  rw [← iform_single_single_E6', ← iform_single_single_E6', ← e6Delta_qp_single m ha,
    ← e6Delta_qp_single m hb, iform_e6Delta]

theorem e6JAdj_symm {J : Set (Fin Tag.E6.rank)} {a b : Fin Tag.E6.rank} (h : e6JAdj J a b) :
    e6JAdj J b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [cartan_symm_E6]; exact h.2.2.2⟩

theorem e6JAdj_e6QpPerm {a b : Fin Tag.E6.rank} (h : e6JAdj (e6QpSupport m) a b) :
    e6JAdj (e6QpSupport m) (e6QpPerm m a) (e6QpPerm m b) :=
  ⟨(e6QpPerm_mem_iff m a).1 h.1, (e6QpPerm_mem_iff m b).1 h.2.1,
    fun e => h.2.2.1 ((e6QpPerm m).injective e),
    by rw [cartan_e6QpPerm m h.1 h.2.1]; exact h.2.2.2⟩

theorem mem_e6JComponent_self (J : Set (Fin Tag.E6.rank)) (i : Fin Tag.E6.rank) :
    i ∈ e6JComponent J i :=
  Relation.ReflTransGen.refl

theorem mem_of_mem_e6JComponent {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hi : i ∈ J) (hj : j ∈ e6JComponent J i) : j ∈ J := by
  induction hj with
  | refl => exact hi
  | tail _ h _ => exact h.2.1

theorem e6JComponent_tail {J : Set (Fin Tag.E6.rank)} {i j k : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) (h : e6JAdj J j k) : k ∈ e6JComponent J i :=
  Relation.ReflTransGen.tail hj h

theorem e6JComponent_symm {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) : i ∈ e6JComponent J j := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.head (e6JAdj_symm h) ih

theorem e6JComponent_eq {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent J i) : e6JComponent J j = e6JComponent J i := by
  ext k
  constructor
  · intro hk
    exact Relation.ReflTransGen.trans hj hk
  · intro hk
    exact Relation.ReflTransGen.trans (e6JComponent_symm hj) hk

theorem e6QpPerm_mem_e6JComponent {i j : Fin Tag.E6.rank}
    (hj : j ∈ e6JComponent (e6QpSupport m) i) :
    e6QpPerm m j ∈ e6JComponent (e6QpSupport m) (e6QpPerm m i) := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (e6JAdj_e6QpPerm m h)

theorem e6JComponent_eq_of_adj {i i' a b : Fin Tag.E6.rank} (hi : i ∈ e6QpSupport m)
    (hi' : i' ∈ e6QpSupport m) (ha : a ∈ e6JComponent (e6QpSupport m) i)
    (hb : b ∈ e6JComponent (e6QpSupport m) i') (h : a = b ∨ Tag.E6.cartan a b ≠ 0) :
    e6JComponent (e6QpSupport m) i = e6JComponent (e6QpSupport m) i' := by
  have hbi : b ∈ e6JComponent (e6QpSupport m) i := by
    by_cases hab : a = b
    · exact hab ▸ ha
    · have h' := h.resolve_left hab
      exact e6JComponent_tail ha ⟨mem_of_mem_e6JComponent hi ha,
        mem_of_mem_e6JComponent hi' hb, hab, h'⟩
  rw [← e6JComponent_eq hbi]
  exact e6JComponent_eq hb

end Components

section Xi

variable (m : Fin 15)

theorem isRoot_e6Delta (J : Set (Fin Tag.E6.rank)) {x : Fin Tag.E6.rank → ℤ}
    (hx : IsRoot Tag.E6 x) : IsRoot Tag.E6 (e6Delta J x) :=
  IsRoot.neg (IsRoot.smul (IsRoot.permLattice (fun i j => TwistTag.cartan_perm TwistTag.E6 i j) hx)
    _)

theorem e6Delta_qp_iterate (k : ℕ) (x : Fin Tag.E6.rank → ℤ) :
    (e6Delta (e6QpSupport m))^[k] x = if Even k then x else e6Delta (e6QpSupport m) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hk : Even k
    · rw [ite_eq_left hk, ite_eq_right (Nat.not_even_iff_odd.2 hk.add_one)]
    · rw [ite_eq_right hk, ite_eq_left (Nat.not_odd_iff_even.1 fun h => hk (by
        rcases h with ⟨r, hr⟩
        exact ⟨r, by omega⟩)), e6Delta_qp_involutive]

theorem mem_parabolicRoots_of_support {S : Set (Fin Tag.E6.rank)} {x : Fin Tag.E6.rank → ℤ}
    (hx : x ∈ parabolicRoots Tag.E6 S) {k : Fin Tag.E6.rank} (hk : x k ≠ 0) : k ∈ S := by
  by_contra h
  exact hk (hx.2 k h)

theorem e6Delta_image_parabolicRoots {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m) :
    e6Delta (e6QpSupport m) '' parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) i₀) =
      parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m i₀)) := by
  have key : ∀ {a : Fin Tag.E6.rank}, a ∈ e6QpSupport m → ∀ x ∈ parabolicRoots Tag.E6
      (e6JComponent (e6QpSupport m) a), e6Delta (e6QpSupport m) x ∈
        parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m a)) := by
    intro a ha x hx
    have hxJ : ∀ i, i ∉ e6QpSupport m → x i = 0 := fun i hi =>
      hx.2 i fun hic => hi (mem_of_mem_e6JComponent ha hic)
    refine ⟨isRoot_e6Delta _ hx.1, fun k hk => ?_⟩
    rw [e6Delta_eq_permLattice m hxJ, permLattice, Function.comp_apply]
    by_contra hne
    have hmem := mem_parabolicRoots_of_support hx hne
    have := e6QpPerm_mem_e6JComponent m hmem
    rw [Equiv.apply_symm_apply] at this
    exact hk this
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact key hi₀ x hx
  · intro hy
    have hπ := (e6QpPerm_mem_iff m i₀).1 hi₀
    have h := key hπ y hy
    rw [e6QpPerm_perm_of_mem m hi₀] at h
    exact ⟨_, h, e6Delta_qp_involutive m y⟩

theorem e6Xi_eq {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m) :
    e6Xi (e6QpSupport m) i₀ = parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) i₀) ∪
      parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) (e6QpPerm m i₀)) := by
  rw [← e6Delta_image_parabolicRoots m hi₀]
  ext y
  simp only [e6Xi, Set.mem_iUnion, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨k, x, hx, rfl⟩
    rw [e6Delta_qp_iterate]
    split_ifs
    · exact Or.inl hx
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (hy | ⟨x, hx, rfl⟩)
    · exact ⟨0, y, hy, rfl⟩
    · exact ⟨1, x, hx, rfl⟩

theorem reflect_mem_parabolicRoots_component {a b j : Fin Tag.E6.rank} (ha : a ∈ e6QpSupport m)
    (hb : b ∈ e6QpSupport m) (hj : j ∈ e6JComponent (e6QpSupport m) a) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) b)) :
    reflect Tag.E6 j γ ∈ parabolicRoots Tag.E6 (e6JComponent (e6QpSupport m) b) := by
  by_cases hK : e6JComponent (e6QpSupport m) a = e6JComponent (e6QpSupport m) b
  · refine ⟨(isRoot_reflect_iff j).2 hγ.1, fun i hi => ?_⟩
    have hij : i ≠ j := fun h => hi (hK ▸ h ▸ hj)
    rw [reflect_apply_of_ne j hij]
    exact hγ.2 i hi
  · have hc : ∑ k, Tag.E6.cartan j k * γ k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : γ k = 0
      · rw [hk, mul_zero]
      · have hkb := mem_parabolicRoots_of_support hγ hk
        by_cases hjk : Tag.E6.cartan j k = 0
        · rw [hjk, zero_mul]
        · exact absurd (e6JComponent_eq_of_adj m ha hb hj hkb (Or.inr hjk)) hK
    have : reflect Tag.E6 j γ = γ := by
      rw [reflect, hc, zero_smul, sub_zero]
    rw [this]
    exact hγ

end Xi

@[expose] def e6XiOrth (J : Set (Fin Tag.E6.rank)) (i₀ : Fin Tag.E6.rank) : Prop :=
  ∀ α ∈ e6Xi J i₀, ∀ k : ℕ, (e6Delta J)^[k] α ≠ α → iform α ((e6Delta J)^[k] α) = 0

section Orbits

variable (m : Fin 15)

theorem single_mem_parabolicRoots_iff {S : Set (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank} :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 S ↔ j ∈ S := by
  constructor
  · intro h
    exact mem_parabolicRoots_of_support h (by simp)
  · intro h
    exact ⟨isRoot_single Tag.E6 j, fun i hi => by
      have : i ≠ j := fun e => hi (e ▸ h)
      simp [this]⟩

theorem mem_e6QpSupport_of_single_mem_e6Xi {i₀ j : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) : j ∈ e6QpSupport m := by
  rw [e6Xi_eq m hi₀, Set.mem_union, single_mem_parabolicRoots_iff,
    single_mem_parabolicRoots_iff] at hj
  rcases hj with h | h
  · exact mem_of_mem_e6JComponent hi₀ h
  · exact mem_of_mem_e6JComponent ((e6QpPerm_mem_iff m i₀).1 hi₀) h

theorem e6RootOrbit_qp_eq (x : Fin Tag.E6.rank → ℤ) :
    e6RootOrbit (e6QpSupport m) x = {x, e6Delta (e6QpSupport m) x} := by
  ext y
  simp only [e6RootOrbit, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [e6Delta_qp_iterate]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem e6SimpleOrbit_qp_eq {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m) :
    e6SimpleOrbit (e6QpSupport m) j = {Pi.single j 1, Pi.single (e6QpPerm m j) 1} := by
  have h := e6RootOrbit_qp_eq m (Pi.single j 1)
  rw [e6Delta_qp_single m hj] at h
  exact h

theorem e6Delta_reflect {j : Fin Tag.E6.rank} (hj : j ∈ e6QpSupport m)
    (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (reflect Tag.E6 j x) =
      reflect Tag.E6 (e6QpPerm m j) (e6Delta (e6QpSupport m) x) := by
  have hc : ∀ (a : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ),
      ∑ k, Tag.E6.cartan a k * y k = iform (Pi.single a 1) y := fun a y => by
    rw [iform_single_left]
    have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
    rw [hd, one_mul]
  rw [reflect, reflect, e6Delta_qp_sub, e6Delta_qp_zsmul, e6Delta_qp_single m hj, hc, hc,
    ← e6Delta_qp_single m hj, iform_e6Delta]

theorem iform_single_single_e6QpPerm_of_orth {i₀ j : Fin Tag.E6.rank}
    (hi₀ : i₀ ∈ e6QpSupport m) (horth : e6XiOrth (e6QpSupport m) i₀)
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (hne : e6QpPerm m j ≠ j) :
    Tag.E6.cartan j (e6QpPerm m j) = 0 := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have h := horth _ hj 1 (by
    rw [Function.iterate_one, e6Delta_qp_single m hjJ]
    exact fun e => hne (single_one_inj e))
  rw [Function.iterate_one, e6Delta_qp_single m hjJ, iform_single_single_E6'] at h
  exact h

theorem setReflection_e6SimpleOrbit {i₀ j : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
    (horth : e6XiOrth (e6QpSupport m) i₀) (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    setReflection (e6SimpleOrbit (e6QpSupport m) j) =
      if e6QpPerm m j = j then simple Tag.E6 j
      else simple Tag.E6 j * simple Tag.E6 (e6QpPerm m j) := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  rw [e6SimpleOrbit_qp_eq m hjJ]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, hπ, Set.pair_eq_singleton]
    rw [setReflection_eq_list_prod (Set.finite_singleton _) (Set.pairwise_singleton _ _)
      (l := [Pi.single j 1]) (List.nodup_singleton _) (fun β => by simp)]
    simp [simple_eq_rootReflection]
  · rw [ite_eq_right hπ]
    have hc := iform_single_single_e6QpPerm_of_orth m hi₀ horth hj hπ
    have hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single (e6QpPerm m j) 1 :=
      fun e => hπ (single_one_inj e).symm
    have hcomm : Commute (rootReflection (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
        (rootReflection (Pi.single (e6QpPerm m j) 1)) :=
      commute_rootReflection_of_iform_eq_zero (isRoot_single _ _) (isRoot_single _ _)
        (by rw [iform_single_single_E6']; exact hc)
    rw [setReflection_eq_list_prod ((Set.finite_singleton _).insert _)
      (Set.pairwise_pair.2 fun _ => ⟨hcomm, hcomm.symm⟩)
      (l := [Pi.single j 1, Pi.single (e6QpPerm m j) 1]) (by simp [hne]) (fun β => by simp)]
    simp [simple_eq_rootReflection]

end Orbits

@[expose] def e6OrbitRefl (m : Fin 15) (j : Fin Tag.E6.rank) : WeylGroup Tag.E6 :=
  if e6QpPerm m j = j then simple Tag.E6 j else simple Tag.E6 j * simple Tag.E6 (e6QpPerm m j)

section OrbitRefl

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ horth in
theorem setReflection_eq_e6OrbitRefl {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    setReflection (e6SimpleOrbit (e6QpSupport m) j) = e6OrbitRefl m j :=
  setReflection_e6SimpleOrbit m hi₀ horth hj

theorem e6OrbitRefl_smul (j : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    e6OrbitRefl m j • x =
      if e6QpPerm m j = j then reflect Tag.E6 j x
      else reflect Tag.E6 j (reflect Tag.E6 (e6QpPerm m j) x) := by
  rw [e6OrbitRefl]
  split_ifs
  · rw [simple_smul]
  · rw [mul_smul, simple_smul, simple_smul]

theorem reflect_single_of_cartan_eq_zero {a b : Fin Tag.E6.rank} (h : Tag.E6.cartan a b = 0) :
    reflect Tag.E6 a (Pi.single b 1) = Pi.single b 1 := by
  have hs : ∑ k, Tag.E6.cartan a k * (Pi.single b 1 : Fin Tag.E6.rank → ℤ) k = 0 := by
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp [h]
  rw [reflect, hs, zero_smul, sub_zero]

theorem reflect_comm_of_cartan_eq_zero {a b : Fin Tag.E6.rank} (h : Tag.E6.cartan a b = 0)
    (x : Fin Tag.E6.rank → ℤ) :
    reflect Tag.E6 a (reflect Tag.E6 b x) = reflect Tag.E6 b (reflect Tag.E6 a x) := by
  have h' : Tag.E6.cartan b a = 0 := by rw [cartan_symm_E6]; exact h
  simp only [reflect]
  have e1 : ∑ k, Tag.E6.cartan a k * (x - (∑ l, Tag.E6.cartan b l * x l) •
      (Pi.single b 1 : Fin Tag.E6.rank → ℤ)) k = ∑ k, Tag.E6.cartan a k * x k := by
    simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, h]
  have e2 : ∑ k, Tag.E6.cartan b k * (x - (∑ l, Tag.E6.cartan a l * x l) •
      (Pi.single a 1 : Fin Tag.E6.rank → ℤ)) k = ∑ k, Tag.E6.cartan b k * x k := by
    simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, h']
  rw [e1, e2]
  abel

include hi₀ horth in
theorem cartan_e6QpPerm_eq_zero {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (hne : e6QpPerm m j ≠ j) :
    Tag.E6.cartan j (e6QpPerm m j) = 0 :=
  iform_single_single_e6QpPerm_of_orth m hi₀ horth hj hne

include hi₀ horth in
theorem e6OrbitRefl_smul_single {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) :
    e6OrbitRefl m j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = -Pi.single j 1 ∧
      e6OrbitRefl m j • (Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) =
        -Pi.single (e6QpPerm m j) 1 := by
  rw [e6OrbitRefl_smul, e6OrbitRefl_smul]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, ite_eq_left hπ, hπ, reflect_single_self]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hπ, ite_eq_right hπ]
    have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ
    have hc' : Tag.E6.cartan (e6QpPerm m j) j = 0 := by rw [cartan_symm_E6]; exact hc
    rw [reflect_single_of_cartan_eq_zero hc', reflect_single_self, reflect_single_self]
    refine ⟨rfl, ?_⟩
    rw [show -(Pi.single (e6QpPerm m j) 1 : Fin Tag.E6.rank → ℤ) =
      (-1 : ℤ) • Pi.single (e6QpPerm m j) 1 by simp]
    rw [show reflect Tag.E6 j ((-1 : ℤ) • Pi.single (e6QpPerm m j) 1) =
      (-1 : ℤ) • reflect Tag.E6 j (Pi.single (e6QpPerm m j) 1) by
        rw [← reflMat_mulVec, ← reflMat_mulVec, Matrix.mulVec_smul],
      reflect_single_of_cartan_eq_zero hc]

include hi₀ horth in
theorem e6OrbitRefl_smul_e6Delta {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) (x : Fin Tag.E6.rank → ℤ) :
    e6OrbitRefl m j • e6Delta (e6QpSupport m) x =
      e6Delta (e6QpSupport m) (e6OrbitRefl m j • x) := by
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hπJ := (e6QpPerm_mem_iff m j).1 hjJ
  rw [e6OrbitRefl_smul, e6OrbitRefl_smul]
  by_cases hπ : e6QpPerm m j = j
  · rw [ite_eq_left hπ, ite_eq_left hπ, e6Delta_reflect m hjJ, hπ]
  · rw [ite_eq_right hπ, ite_eq_right hπ, e6Delta_reflect m hjJ, e6Delta_reflect m hπJ,
      e6QpPerm_perm_of_mem m hjJ]
    exact reflect_comm_of_cartan_eq_zero (cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ) _

theorem e6OrbitRefl_mul_self (j : Fin Tag.E6.rank) (hc : e6QpPerm m j ≠ j →
    Tag.E6.cartan j (e6QpPerm m j) = 0) : e6OrbitRefl m j * e6OrbitRefl m j = 1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, e6OrbitRefl_smul, e6OrbitRefl_smul, one_smul]
  split_ifs with hπ
  · rw [reflect_reflect]
  · rw [reflect_comm_of_cartan_eq_zero (hc hπ), reflect_reflect, reflect_reflect]


include hi₀ in
theorem e6OrbitRefl_smul_mem_e6Xi {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) : e6OrbitRefl m j • γ ∈ e6Xi (e6QpSupport m) i₀ := by
  have hπ₀ := (e6QpPerm_mem_iff m i₀).1 hi₀
  have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
  have hπJ := (e6QpPerm_mem_iff m j).1 hjJ
  have hcomp : ∀ k, Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ →
      ∃ a ∈ e6QpSupport m, k ∈ e6JComponent (e6QpSupport m) a := fun k hk => by
    rw [e6Xi_eq m hi₀, Set.mem_union, single_mem_parabolicRoots_iff,
      single_mem_parabolicRoots_iff] at hk
    rcases hk with h | h
    · exact ⟨i₀, hi₀, h⟩
    · exact ⟨_, hπ₀, h⟩
  have hπj : Pi.single (e6QpPerm m j) 1 ∈ e6Xi (e6QpSupport m) i₀ := by
    rw [← e6Delta_qp_single m hjJ]
    rw [e6Xi_eq m hi₀] at hj ⊢
    rcases hj with h | h
    · right
      rw [← e6Delta_image_parabolicRoots m hi₀]
      exact ⟨_, h, rfl⟩
    · left
      rw [← e6Delta_image_parabolicRoots m hi₀] at h
      obtain ⟨y, hy, hye⟩ := h
      rw [← hye, e6Delta_qp_involutive]
      exact hy
  have hrefl : ∀ k, Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ → ∀ y ∈ e6Xi (e6QpSupport m) i₀,
      reflect Tag.E6 k y ∈ e6Xi (e6QpSupport m) i₀ := fun k hk y hy => by
    obtain ⟨a, ha, hka⟩ := hcomp k hk
    rw [e6Xi_eq m hi₀] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (reflect_mem_parabolicRoots_component m ha hi₀ hka hy)
    · exact Or.inr (reflect_mem_parabolicRoots_component m ha hπ₀ hka hy)
  rw [e6OrbitRefl_smul]
  split_ifs
  · exact hrefl j hj γ hγ
  · exact hrefl j hj _ (hrefl _ hπj γ hγ)

end OrbitRefl

section RelWeyl

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

@[expose] def IsE6OrbitGen (m : Fin 15) (i₀ : Fin Tag.E6.rank) (r : WeylGroup Tag.E6) : Prop :=
  ∃ j, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ ∧ r = e6OrbitRefl m j

include hi₀ horth in
theorem setReflection_image_e6Orbits :
    setReflection '' e6Orbits (e6QpSupport m) i₀ = {r | IsE6OrbitGen m i₀ r} := by
  ext r
  constructor
  · rintro ⟨O, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, setReflection_eq_e6OrbitRefl m hi₀ horth hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, setReflection_eq_e6OrbitRefl m hi₀ horth hj⟩

include hi₀ horth in
theorem IsE6OrbitGen.mul_self {r : WeylGroup Tag.E6} (hr : IsE6OrbitGen m i₀ r) : r * r = 1 := by
  obtain ⟨j, hj, rfl⟩ := hr
  exact e6OrbitRefl_mul_self m j (cartan_e6QpPerm_eq_zero m hi₀ horth hj)


include hi₀ horth in
theorem IsE6OrbitGen.mem {r : WeylGroup Tag.E6} (hr : IsE6OrbitGen m i₀ r) :
    r ∈ e6RelWeyl (e6QpSupport m) i₀ := by
  refine Subgroup.subset_closure ?_
  rw [setReflection_image_e6Orbits m hi₀ horth]
  exact hr


end RelWeyl


section Weights

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)

include hi₀ in
theorem isRoot_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    IsRoot Tag.E6 γ := by
  rw [e6Xi_eq m hi₀] at hγ
  rcases hγ with h | h
  · exact h.1
  · exact h.1

include hi₀ in
theorem support_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    ∀ i, i ∉ e6QpSupport m → γ i = 0 := by
  have hπ₀ := (e6QpPerm_mem_iff m i₀).1 hi₀
  rw [e6Xi_eq m hi₀] at hγ
  intro i hi
  rcases hγ with h | h
  · exact h.2 i fun hc => hi (mem_of_mem_e6JComponent hi₀ hc)
  · exact h.2 i fun hc => hi (mem_of_mem_e6JComponent hπ₀ hc)

include hi₀ in
theorem neg_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    -γ ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hγ ⊢
  rcases hγ with h | h
  · exact Or.inl ⟨IsRoot.neg h.1, fun i hi => by simp [h.2 i hi]⟩
  · exact Or.inr ⟨IsRoot.neg h.1, fun i hi => by simp [h.2 i hi]⟩

include hi₀ in
theorem e6Delta_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    e6Delta (e6QpSupport m) γ ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hγ ⊢
  rcases hγ with h | h
  · right
    rw [← e6Delta_image_parabolicRoots m hi₀]
    exact ⟨_, h, rfl⟩
  · left
    rw [← e6Delta_image_parabolicRoots m hi₀] at h
    obtain ⟨y, hy, hye⟩ := h
    rw [← hye, e6Delta_qp_involutive]
    exact hy

include hi₀ in
theorem height_e6Delta_of_mem_e6Xi {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) : height (e6Delta (e6QpSupport m) γ) = height γ := by
  rw [e6Delta_eq_permLattice m (support_of_mem_e6Xi m hi₀ hγ), height_permLattice]


include hi₀ horth in
theorem height_e6OrbitRefl_smul_pos {j : Fin Tag.E6.rank}
    (hj : Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) (hpos : 0 < height γ) (h1 : γ ≠ Pi.single j 1)
    (h2 : γ ≠ Pi.single (e6QpPerm m j) 1) : 0 < height (e6OrbitRefl m j • γ) := by
  have hr := isRoot_of_mem_e6Xi m hi₀ hγ
  rw [e6OrbitRefl_smul]
  split_ifs with hπ
  · exact height_reflect_pos hr hpos h1
  · have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hj hπ
    have hc' : Tag.E6.cartan (e6QpPerm m j) j = 0 := by rw [cartan_symm_E6]; exact hc
    have hr' := (isRoot_reflect_iff (e6QpPerm m j)).2 hr
    refine height_reflect_pos hr' (height_reflect_pos hr hpos h2) fun e => h1 ?_
    rw [← reflect_reflect Tag.E6 (e6QpPerm m j) γ, e, reflect_single_of_cartan_eq_zero hc']

end Weights

section Step

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)


end Step

section LengthFormula

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)


end LengthFormula

section Folded

variable (m : Fin 15) {i₀ : Fin Tag.E6.rank} (hi₀ : i₀ ∈ e6QpSupport m)
  (horth : e6XiOrth (e6QpSupport m) i₀)


theorem height_reflect_eq_E6 (t : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    height (reflect Tag.E6 t v) = height v - ∑ l, Tag.E6.cartan t l * v l := by
  simp only [reflect, height, Pi.sub_apply, Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply]


theorem sum_cartan_mul_eq_iform (a : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ) :
    ∑ k, Tag.E6.cartan a k * y k = iform (Pi.single a 1) y := by
  rw [iform_single_left]
  have hd : Tag.E6.symmetrizer a a = 1 := by fin_cases a <;> rfl
  rw [hd, one_mul]

include hi₀ in
theorem single_mem_e6Xi_of_ne_zero {x : Fin Tag.E6.rank → ℤ} (hx : x ∈ e6Xi (e6QpSupport m) i₀)
    {k : Fin Tag.E6.rank} (hk : x k ≠ 0) : Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ := by
  rw [e6Xi_eq m hi₀] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (single_mem_parabolicRoots_iff.2 (mem_parabolicRoots_of_support h hk))
  · exact Or.inr (single_mem_parabolicRoots_iff.2 (mem_parabolicRoots_of_support h hk))


include hi₀ horth in
theorem exists_smul_e6Orbit_eq {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6Xi (e6QpSupport m) i₀) :
    ∃ w ∈ e6RelWeyl (e6QpSupport m) i₀, ∃ O ∈ e6Orbits (e6QpSupport m) i₀,
      (w • ·) '' O = e6RootOrbit (e6QpSupport m) γ := by
  have himg : ∀ {j : Fin Tag.E6.rank}, Pi.single j 1 ∈ e6Xi (e6QpSupport m) i₀ →
      ∀ x, (e6OrbitRefl m j • ·) '' e6RootOrbit (e6QpSupport m) x =
        e6RootOrbit (e6QpSupport m) (e6OrbitRefl m j • x) := fun hj x => by
    rw [e6RootOrbit_qp_eq, e6RootOrbit_qp_eq, Set.image_pair,
      e6OrbitRefl_smul_e6Delta m hi₀ horth hj]
  have hcomp : ∀ (a b : WeylGroup Tag.E6) (S : Set (Fin Tag.E6.rank → ℤ)),
      ((a * b) • ·) '' S = (a • ·) '' ((b • ·) '' S) := fun a b S => by
    rw [Set.image_image]
    congr 1
    funext x
    rw [mul_smul]
  have hpos : ∀ n : ℕ, ∀ γ ∈ e6Xi (e6QpSupport m) i₀, height γ = n → 0 < height γ →
      ∃ w ∈ e6RelWeyl (e6QpSupport m) i₀, ∃ O ∈ e6Orbits (e6QpSupport m) i₀,
        (w • ·) '' O = e6RootOrbit (e6QpSupport m) γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hγ hn hp
      by_cases hs : ∃ j, γ = Pi.single j 1
      · obtain ⟨j, rfl⟩ := hs
        refine ⟨1, one_mem _, e6SimpleOrbit (e6QpSupport m) j, ⟨j, hγ, rfl⟩, ?_⟩
        ext x
        simp [e6SimpleOrbit, e6RootOrbit]
      · simp only [not_exists] at hs
        have hγr := isRoot_of_mem_e6Xi m hi₀ hγ
        have hδγ := e6Delta_mem_e6Xi m hi₀ hγ
        have hδr := isRoot_of_mem_e6Xi m hi₀ hδγ
        have hγnn := (IsRoot.height_pos_iff hγr).1 hp
        have hδnn := (IsRoot.height_pos_iff hδr).1
          (by rw [height_e6Delta_of_mem_e6Xi m hi₀ hγ]; exact hp)
        set q := γ + e6Delta (e6QpSupport m) γ with hq
        have hq0 : q ≠ 0 := fun h => by
          have h1 : height q = height γ + height γ := by
            rw [hq, height_add, height_e6Delta_of_mem_e6Xi m hi₀ hγ]
          have h2 : height (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [height]
          rw [h, h2] at h1
          omega
        have hexp : iform q q = ∑ k, q k * iform (Pi.single k 1) q := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← sum_cartan_mul_eq_iform, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [symmetrizedCartan_E6]
          ring
        obtain ⟨k, hk⟩ : ∃ k, 0 < q k * iform (Pi.single k 1) q := by
          by_contra! h
          have := iform_self_pos hq0
          rw [hexp] at this
          exact absurd (Finset.sum_nonpos fun k _ => h k) (not_le.2 this)
        have hqk : 0 ≤ q k := by rw [hq, Pi.add_apply]; linarith [hγnn k, hδnn k]
        have hqk' : 0 < q k := lt_of_le_of_ne hqk fun e => by rw [← e, zero_mul] at hk; omega
        have hik : 0 < iform (Pi.single k 1) q := pos_of_mul_pos_right hk hqk
        have hkΞ : Pi.single k 1 ∈ e6Xi (e6QpSupport m) i₀ := by
          by_cases hγk : γ k = 0
          · refine single_mem_e6Xi_of_ne_zero m hi₀ hδγ fun e => ?_
            rw [hq, Pi.add_apply, hγk, e, add_zero] at hqk'
            exact lt_irrefl 0 hqk'
          · exact single_mem_e6Xi_of_ne_zero m hi₀ hγ hγk
        have hkJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hkΞ
        have hπkJ := (e6QpPerm_mem_iff m k).1 hkJ
        have hsplit : iform (Pi.single k 1) q = iform (Pi.single k 1) γ +
            iform (Pi.single (e6QpPerm m k) 1) γ := by
          rw [hq, iform_add_right]
          congr 1
          rw [show (Pi.single k 1 : Fin Tag.E6.rank → ℤ) =
            e6Delta (e6QpSupport m) (Pi.single (e6QpPerm m k) 1) by
              rw [e6Delta_qp_single m hπkJ, e6QpPerm_perm_of_mem m hkJ], iform_e6Delta]
        have hdec : height (e6OrbitRefl m k • γ) < height γ := by
          rw [e6OrbitRefl_smul]
          split_ifs with hπ
          · rw [height_reflect_eq_E6, sum_cartan_mul_eq_iform]
            rw [hπ] at hsplit
            omega
          · have hc := cartan_e6QpPerm_eq_zero m hi₀ horth hkΞ hπ
            rw [height_reflect_eq_E6, height_reflect_eq_E6, sum_cartan_mul_eq_iform,
              sum_cartan_mul_eq_iform, reflect, iform_sub_right, iform_smul_right,
              iform_single_single_E6', hc, mul_zero, sub_zero]
            omega
        have hrΞ := e6OrbitRefl_smul_mem_e6Xi m hi₀ hkΞ hγ
        have hrp := height_e6OrbitRefl_smul_pos m hi₀ horth hkΞ hγ hp (hs k) (hs _)
        obtain ⟨w, hw, O, hO, hwO⟩ := ih (height (e6OrbitRefl m k • γ)).toNat (by omega)
          (e6OrbitRefl m k • γ) hrΞ (by omega) hrp
        have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m k) := ⟨k, hkΞ, rfl⟩
        refine ⟨e6OrbitRefl m k * w, mul_mem (hgen.mem m hi₀ horth) hw, O, hO, ?_⟩
        rw [hcomp, hwO, himg hkΞ, ← mul_smul, hgen.mul_self m hi₀ horth, one_smul]
  have hr := isRoot_of_mem_e6Xi m hi₀ hγ
  rcases IsRoot.height_pos_or_neg hr with hp | hn
  · exact hpos (height γ).toNat γ hγ (by omega) hp
  · have hnγ := neg_mem_e6Xi m hi₀ hγ
    obtain ⟨w, hw, O, hO, hwO⟩ := hpos (height (-γ)).toNat (-γ) hnγ
      (by rw [height_neg]; omega) (by rw [height_neg]; omega)
    obtain ⟨j, hj, rfl⟩ := hO
    have hjJ := mem_e6QpSupport_of_single_mem_e6Xi m hi₀ hj
    have hgen : IsE6OrbitGen m i₀ (e6OrbitRefl m j) := ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := e6OrbitRefl_smul_single m hi₀ horth hj
    refine ⟨w * e6OrbitRefl m j, mul_mem hw (hgen.mem m hi₀ horth), _, ⟨j, hj, rfl⟩, ?_⟩
    rw [hcomp, e6SimpleOrbit_qp_eq m hjJ, Set.image_pair, h1, h2, Set.image_pair, smul_neg,
      smul_neg]
    rw [e6SimpleOrbit_qp_eq m hjJ, Set.image_pair, e6RootOrbit_qp_eq, e6Delta_qp_neg] at hwO
    rw [e6RootOrbit_qp_eq]
    have := congrArg (fun S : Set (Fin Tag.E6.rank → ℤ) => (fun x => -x) '' S) hwO
    simpa [Set.image_pair] using this

end Folded

end CFSG.RankThree.Lattice
