module

public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
public import CFSG.RankThree.Chevalley.SteinbergCEF4LatticeTools
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
open scoped Pointwise

variable {k : Type} [Field k]

theorem mem_normalizer_torusPow_of_mem_normalizer {τ : Tag} {n : ℕ} {g : ModGL τ k}
    (hg : g ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k))) :
    g ∈ Subgroup.normalizer {h : ModGL τ k | h ∈ torusGroup τ k ∧ h ^ n = 1} := by
  refine Subgroup.mem_set_normalizer_iff.2 fun x => ?_
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, conj_pow, conj_eq_one_iff,
    ← Subgroup.mem_normalizer_iff.1 hg x]

theorem exists_eq_mul_canonicalRep_of_mem_normalizer
    {τ : Tag} {V : Set (ModGL τ k)}
    (hVH : V ⊆ torusGroup τ k)
    (hCV : adjointGroup τ k ⊓ Subgroup.centralizer V = torusGroup τ k) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k ⊓ Subgroup.normalizer V) :
    ∃ h ∈ torusGroup τ k, ∃ w : WeylGroup τ, g = h * canonicalRep (coxeterSystem τ) k w := by
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  have hTB := triangular_borel_structure.{0, 0} τ k
  have hB := Chevalley_toral_centralizer_Bruhat_factors τ k 1
  have hg1 : g ∈ toralCentralizer τ k 1 :=
    mem_toralCentralizer.2 ⟨hgC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := hB.1 g hg1
  have huU : u ∈ posUnipotent τ k := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan τ k (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hnN := canonicalRep_mem_normalizer (R := k) w
  have hnC := canonicalRep_mem_adjointGroup (coxeterSystem τ) k w
  set n := canonicalRep (coxeterSystem τ) k w with hn
  have key : ∀ x ∈ V, g * x * g⁻¹ = n * x * n⁻¹ := by
    intro x hx
    have hxT := hVH hx
    have hyV : g * x * g⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.1 hgN x).1 hx
    have hyT := hVH hyV
    have htT : n * x * n⁻¹ ∈ torusGroup τ k := (Subgroup.mem_normalizer_iff.1 hnN x).1 hxT
    have hu' : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹ ∈ posUnipotent τ k :=
      (Subgroup.mem_normalizer_iff.1 (hTB.2.2.1 (inv_mem htT)) u).1 huU
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ rootSpan τ k (inversionSet w) := by
      have hmap := map_rootSpan_of_forall (S := inversionSet w)
        (f := (MulAut.conj x⁻¹).toMonoidHom) fun α hα =>
          map_conj_rootSubgroup_of_mem_torusGroup (inv_mem hxT) hα.1
      rw [← hmap]
      exact ⟨v, hvI, rfl⟩
    have heq : h * (n * x * n⁻¹) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹) * n *
        (x⁻¹ * v * x⁻¹⁻¹) = g * x * g⁻¹ * h * u * n * v := by
      rw [hgeq]
      group
    obtain ⟨-, h1, -⟩ := hB.2.1 w w _ _ _ _ _ _ (mul_mem hh htT) (mul_mem hyT hh) hu' huU hv' hvI
      heq
    exact (mul_left_cancel (h1.trans (hTB.1 _ hyT _ hh))).symm
  have hm : n⁻¹ * g ∈ adjointGroup τ k ⊓ Subgroup.centralizer V := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hnC) hgC,
      Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    calc x * (n⁻¹ * g) = n⁻¹ * (n * x * n⁻¹) * g := by group
      _ = n⁻¹ * (g * x * g⁻¹) * g := by rw [key x hx]
      _ = n⁻¹ * g * x := by group
  rw [hCV] at hm
  exact ⟨n * (n⁻¹ * g) * n⁻¹, (Subgroup.mem_normalizer_iff.1 hnN _).1 hm, w, by rw [← hn]; group⟩

theorem eq_one_of_mem_posUnipotent_of_conj_rootDiagUnit_eq
    {τ : Tag} {u : ModGL τ k}
    (hu : u ∈ posUnipotent τ k) {A : Set (Fin τ.rank → kˣ)}
    (hA : ∀ α, IsRoot τ α → 0 < height α → ∃ a ∈ A, rootChar a α ≠ 1)
    (hconj : ∀ a ∈ A, rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u) : u = 1 := by
  set S := {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β} with hSdef
  have hS : S.Finite := (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have := hS.to_subtype
  set e := Finite.equivFin S
  set α : Fin (Nat.card S) → Fin τ.rank → ℤ := fun i => (e.symm i).1 with hαdef
  have hinj : Function.Injective α := Subtype.val_injective.comp e.symm.injective
  have hrange : Set.range α = S := by
    ext β
    refine ⟨?_, fun hβ => ⟨e ⟨β, hβ⟩, by simp only [hαdef, Equiv.symm_apply_apply]⟩⟩
    rintro ⟨i, rfl⟩
    exact (e.symm i).2
  have hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i) := fun i => (e.symm i).2
  obtain ⟨c, -, rfl⟩ := ((positive_root_collection τ k).2 α hinj hrange).surjOn hu
  have hinj' := (positive_root_product_injectivity τ k α hinj hpos).2
  have hc : ∀ i, c i = 0 := by
    intro i
    obtain ⟨a, haA, ha⟩ := hA (α i) (hpos i).1 (hpos i).2
    have h1 := hconj a haA
    rw [rootDiagUnit_conj_list_prod a α (fun j => (hpos j).1) c] at h1
    have h2 : (rootChar a (α i) : k) * c i = c i := congrFun (hinj' h1) i
    have h3 : ((rootChar a (α i) : k) - 1) * c i = 0 := by rw [sub_mul, h2, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 fun h => ha (Units.val_eq_one.1 h))
  have e1 : (fun i => pinnedX τ k (α i) (c i)) = fun _ => 1 :=
    funext fun i => by rw [hc i, pinnedX_zero]
  simp only [e1, List.ofFn_const, List.prod_replicate, one_pow]

theorem rootChar_pow_val_eq {τ : Tag} {p : ℕ} [NeZero p] {ζ : kˣ} (hζ : orderOf ζ = p)
    (x : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ζ ^ (x i).val) v = ζ ^ (charVal x v).val := by
  have e : rootChar (fun i => ζ ^ (x i).val) v = ζ ^ (∑ i, ((x i).val : ℤ) * v i) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  rw [e, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hζ, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, charVal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ZMod.natCast_zmod_val, mul_comm]


theorem eq_of_pow_val_eq_pow_val {p : ℕ} [NeZero p] {ζ : kˣ} (hζ : orderOf ζ = p)
    {m n : ZMod p} (h : ζ ^ m.val = ζ ^ n.val) : m = n := by
  refine ZMod.val_injective p (pow_injOn_Iio_orderOf ?_ ?_ h)
  · rw [Set.mem_Iio, hζ]
    exact ZMod.val_lt m
  · rw [Set.mem_Iio, hζ]
    exact ZMod.val_lt n

theorem exists_pow_val_eq_of_pow_eq_one {p : ℕ} [NeZero p] {ζ : kˣ} (hζ : orderOf ζ = p)
    {b : kˣ} (hb : b ^ p = 1) : ∃ m : ZMod p, ζ ^ m.val = b := by
  have hprim : IsPrimitiveRoot ζ p := hζ ▸ IsPrimitiveRoot.orderOf ζ
  obtain ⟨i, hi, rfl⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p b).2 hb)
  exact ⟨i, by rw [ZMod.val_natCast_of_lt hi]⟩

theorem pow_val_eq_zpow_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} [NeZero p] {x : G}
    (hx : x ^ p = 1) (a : ZMod p) (m : ℤ) (hm : (m : ZMod p) = a) : x ^ a.val = x ^ m := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq]
  refine Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hx)) ?_
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, hm]

theorem F4_eq_one_or_neg_of_scalar_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {w : WeylGroup .F4} {a : ZMod p}
    (h : ∀ (v : Fin Tag.F4.rank → ℤ) (i : Fin Tag.F4.rank), a * ((w • v) i : ZMod p) = v i) :
    w = 1 ∨ ∀ v : Fin Tag.F4.rank → ℤ, w • v = -v := by
  have h' : ∀ (v : Fin Tag.F4.rank → ℤ) (i : Fin Tag.F4.rank),
      (((w⁻¹ • v) i : ℤ) : ZMod p) = a * (v i : ZMod p) := fun v i => by
    have := h (w⁻¹ • v) i
    rw [smul_inv_smul] at this
    exact this.symm
  have hscalar : (invTranspose (weylToAut .F4 w)).map (Int.castRingHom (ZMod p)) =
      Matrix.scalar (Fin Tag.F4.rank) a := by
    rw [invTranspose_weylToAut_eq]
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, weylMatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, eq_intCast, h' (Pi.single i 1) j, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rcases eq_one_or_neg_one_of_map_eq_scalar hp2 (mem_charMatrices.2 ⟨w, rfl⟩) hscalar with
    h1 | h1
  · left
    rw [invTranspose_weylToAut_eq] at h1
    have h2 : weylMatrix w⁻¹ = 1 := by
      rw [← Matrix.transpose_transpose (weylMatrix w⁻¹), h1, Matrix.transpose_one]
    exact inv_eq_one.1 (weylMatrix_injective (h2.trans weylMatrix_one.symm))
  · right
    rw [invTranspose_weylToAut_eq] at h1
    have h2 : weylMatrix w⁻¹ = -1 := by
      rw [← Matrix.transpose_transpose (weylMatrix w⁻¹), h1, Matrix.transpose_neg,
        Matrix.transpose_one]
    intro v
    have h3 : w⁻¹ • (w • v) = -(w • v) := by
      rw [← weylMatrix_mulVec, h2, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [inv_smul_smul] at h3
    have h4 := congrArg Neg.neg h3
    rw [neg_neg] at h4
    exact h4.symm

theorem F4_eq_one_of_smul_modEq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {w : WeylGroup .F4}
    (h : ∀ (v : Fin Tag.F4.rank → ℤ) (i : Fin Tag.F4.rank), ((w • v) i : ZMod p) = v i) :
    w = 1 := by
  rcases F4_eq_one_or_neg_of_scalar_mod hp2 (a := 1) fun v i => by rw [one_mul, h] with h1 | h1
  · exact h1
  · exfalso
    have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)⟩
    have h2 := h (Pi.single ⟨0, by decide⟩ 1) ⟨0, by decide⟩
    rw [h1, Pi.neg_apply, Pi.single_eq_same, Int.cast_neg, Int.cast_one] at h2
    exact ZMod.neg_one_ne_one h2

theorem F4_root_natAbs_le {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (i : Fin Tag.F4.rank) :
    (α i).natAbs ≤ 4 := by
  have h : ∀ β ∈ f4RootList, ∀ j : Fin Tag.F4.rank, (β j).natAbs ≤ 4 := by decide
  exact h α (isRoot_iff_mem_f4RootList.1 hα) i

theorem F4_exists_rootChar_mulSingle_ne_one {p : ℕ} (hp4 : 4 < p) {ζ : kˣ}
    (hζ : orderOf ζ = p) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    ∃ i, rootChar (Pi.mulSingle i ζ) α ≠ 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hα.ne_zero
  refine ⟨i, fun h1 => ?_⟩
  rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at h1
  exact not_dvd_of_natAbs_lt hi (lt_of_le_of_lt (F4_root_natAbs_le hα i) hp4) h1

theorem F4_rootDiagUnit_mem_torusGroup (a : Fin Tag.F4.rank → kˣ) :
    rootDiagUnit .F4 a ∈ torusGroup .F4 k := by
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) k
  exact (hdiag B hB a).2.1

theorem torusGroup_le_adjointGroup_F4 : torusGroup .F4 k ≤ adjointGroup .F4 k :=
  le_sup_left.trans ((triangular_borel_structure.{0, 0} .F4 k).2.2.2.2.2.2.2.2.2.2.2 k).1

theorem conj_eq_self_of_commute_of_conj_mul_eq {G : Type*} [Group G] {d h u : G}
    (hdh : d * h = h * d) (hd : d * (h * u) * d⁻¹ = h * u) : d * u * d⁻¹ = u := by
  calc d * u * d⁻¹ = h⁻¹ * (d * (h * u) * d⁻¹) := by rw [← mul_assoc d h u, hdh]; group
    _ = u := by rw [hd]; group

section Torsion

variable {p : ℕ}

theorem F4_rootDiagUnit_pow_val_mem {ζ : kˣ} (hζ : orderOf ζ = p)
    (x : Fin Tag.F4.rank → ZMod p) :
    rootDiagUnit .F4 (fun i => ζ ^ (x i).val) ∈
      {h : ModGL .F4 k | h ∈ torusGroup .F4 k ∧ h ^ p = 1} := by
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine ⟨F4_rootDiagUnit_mem_torusGroup _, ?_⟩
  rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := .F4) (K := k)]
  congr 1
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← pow_mul, mul_comm, pow_mul, hζp, one_pow]

theorem F4_bijOn_rootDiagUnit_pow_val [NeZero p] {ζ : kˣ} (hζ : orderOf ζ = p) :
    Set.BijOn (fun x : Fin Tag.F4.rank → ZMod p => rootDiagUnit .F4 fun i => ζ ^ (x i).val)
      Set.univ {h : ModGL .F4 k | h ∈ torusGroup .F4 k ∧ h ^ p = 1} := by
  refine ⟨fun x _ => F4_rootDiagUnit_pow_val_mem hζ x, fun x _ y _ hxy => ?_, fun h hh => ?_⟩
  · funext i
    exact eq_of_pow_val_eq_pow_val hζ (congrFun (rootDiagUnit_injective hxy) i)
  · obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh.1
    have hap' : rootDiagUnit .F4 (a ^ p) = rootDiagUnit .F4 1 := by
      rw [← rootDiagUnit_pow, hh.2, rootDiagUnit_one]
    have hap : a ^ p = 1 := rootDiagUnit_injective hap'
    have hai : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun hap i
    choose m hm using fun i => exists_pow_val_eq_of_pow_eq_one hζ (hai i)
    refine ⟨m, Set.mem_univ _, ?_⟩
    change rootDiagUnit .F4 (fun i => ζ ^ (m i).val) = rootDiagUnit .F4 a
    congr 1
    exact funext hm

theorem F4_natCard_torusPow [Finite k] (hp : p.Prime) (hpk : p ∣ Nat.card kˣ) :
    Nat.card {h : ModGL .F4 k | h ∈ torusGroup .F4 k ∧ h ^ p = 1} = p ^ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpk
  rw [← Nat.card_congr (F4_bijOn_rootDiagUnit_pow_val hζ).equiv, Nat.card_univ, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl


theorem F4_centralizer_eq_torusGroup_of_regular
    (hp : p.Prime) (hp3 : 3 < p)
    {a : Fin Tag.F4.rank → kˣ} (ha : orderOf (rootDiagUnit .F4 a) = p)
    (hreg : ∀ α, IsRoot .F4 α → rootChar a α ≠ 1) :
    adjointGroup .F4 k ⊓ Subgroup.centralizer {rootDiagUnit .F4 a} = torusGroup .F4 k := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} .F4 k).1
  refine le_antisymm (fun z hz => ?_) (le_inf torusGroup_le_adjointGroup_F4 fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact hTcomm _ (F4_rootDiagUnit_mem_torusGroup a) _ hh)
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .F4 k a).1 z hz
  have hker : rootCharKernel a = ∅ :=
    Set.eq_empty_of_forall_notMem fun α hα => hreg α hα.1 hα.2
  have hbot : rootSpan .F4 k (∅ : Set (Fin Tag.F4.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [hker, Set.empty_inter, hbot, Subgroup.mem_bot] at hu hv
  subst hu hv
  have hoa : orderOf a = p := (orderOf_rootDiagUnit a).symm.trans ha
  have hap : a ^ p = 1 := hoa ▸ pow_orderOf_eq_one a
  have hai : ∀ j, a j ^ p = 1 := fun j => by simpa using congrFun hap j
  have ha1 : a ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hoa
    exact hp.one_lt.ne hoa
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha1
  have hζ : orderOf (a i) = p := orderOf_eq_prime (hai i) hi
  choose x hx using fun j => exists_pow_val_eq_of_pow_eq_one hζ (hai j)
  have hax : ∀ v, rootChar a v = a i ^ (charVal x v).val := fun v => by
    rw [← rootChar_pow_val_eq hζ x v]
    congr 1
    exact (funext hx).symm
  have hwx : w ∈ charStabilizer x := fun v => by
    have h1 := hw v
    rw [hax, hax] at h1
    exact eq_of_pow_val_eq_pow_val hζ h1
  have hkerx : charRootKernel x = ∅ := Set.eq_empty_of_forall_notMem fun α hα =>
    hreg α hα.1 (by rw [hax, hα.2, ZMod.val_zero, pow_zero])
  rw [charStabilizer_eq_closure hp3 x, hkerx] at hwx
  have hempty : {s : WeylGroup .F4 | ∃ α ∈ (∅ : Set (Fin Tag.F4.rank → ℤ)),
      s = rootReflection α} = ∅ := by
    ext s
    simp
  rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at hwx
  subst hwx
  rw [canonicalRep_one, mul_one, mul_one, mul_one]
  exact hh

end Torsion


end CFSG.RankThree.Chevalley
