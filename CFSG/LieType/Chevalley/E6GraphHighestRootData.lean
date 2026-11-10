module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.TwistPerfect

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphHighestRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

abbrev e6Idx (i : Fin 6) : Fin TwistTag.E6.tag.rank := i

@[expose] def sRoot : Fin TwistTag.E6.tag.rank → ℤ := (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)

@[expose] def a5Path : Fin 5 → Fin TwistTag.E6.tag.rank := fun l => e6Idx (![0, 2, 3, 4, 5] l)

@[expose] def a5Interval (i j : Fin 5) : Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ l ∈ Finset.Icc i j, Pi.single (a5Path l) 1

@[expose] def a5Roots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 ≤ p.2).image fun p => a5Interval p.1 p.2) ∪
    ((Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 ≤ p.2).image fun p => -a5Interval p.1 p.2)


theorem filter_coord_zero :
    (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 0) = a5Roots := by
  decide +kernel


@[expose] def degOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (rootFinset TwistTag.E6.tag).filter (fun β => β (e6Idx 1) = 1)


theorem filter_pos_coord_pos :
    (rootFinset TwistTag.E6.tag).filter (fun β => 0 < height β ∧ 0 < β (e6Idx 1)) =
      insert e6HighestRoot degOneRoots := by
  decide +kernel


theorem sub_e6HighestRoot_mem :
    ∀ β ∈ degOneRoots, β - e6HighestRoot ∈ rootFinset TwistTag.E6.tag := by
  decide +kernel

@[expose] def fixedDegOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  degOneRoots.filter (fun β => permLattice TwistTag.E6.perm β = β)

@[expose] def movedDegOneRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  degOneRoots.filter (fun β => permLattice TwistTag.E6.perm β ≠ β)


theorem permLattice_mem_degOneRoots : ∀ β ∈ degOneRoots,
    permLattice TwistTag.E6.perm β ∈ degOneRoots := by
  decide +kernel

theorem iform_permLattice :
    ∀ β ∈ movedDegOneRoots, iform β (permLattice TwistTag.E6.perm β) = 0 := by
  decide +kernel

theorem sum_mul_symmetrizedCartan_e6HighestRoot : ∀ j : Fin TwistTag.E6.tag.rank,
    ∑ i, e6HighestRoot i * TwistTag.E6.tag.symmetrizedCartan i j =
      (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) j := by
  decide

theorem iform_e6HighestRoot (l : Fin TwistTag.E6.tag.rank → ℤ) :
    iform e6HighestRoot l = l (e6Idx 1) := by
  have h : iform e6HighestRoot l =
      ∑ j, (∑ i, e6HighestRoot i * TwistTag.E6.tag.symmetrizedCartan i j) * l j := by
    rw [iform, Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [h]
  simp only [sum_mul_symmetrizedCartan_e6HighestRoot, Pi.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[expose] def tailGen
    : Fin 3 → WeylGroup TwistTag.E6.tag :=
  ![simple TwistTag.E6.tag (e6Idx 3),
    simple TwistTag.E6.tag (e6Idx 0) * simple TwistTag.E6.tag (e6Idx 5),
    simple TwistTag.E6.tag (e6Idx 2) * simple TwistTag.E6.tag (e6Idx 4)]

@[expose] def tailAct (b : Fin 3) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  match b with
  | 0 => reflect TwistTag.E6.tag (e6Idx 3) v
  | 1 => reflect TwistTag.E6.tag (e6Idx 0) (reflect TwistTag.E6.tag (e6Idx 5) v)
  | 2 => reflect TwistTag.E6.tag (e6Idx 2) (reflect TwistTag.E6.tag (e6Idx 4) v)

theorem tailGen_smul
    (b : Fin 3) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    tailGen b • v = tailAct b v := by
  fin_cases b <;> simp [tailGen, tailAct, mul_smul]

theorem list_prod_tailGen_smul
    (bw : List (Fin 3)) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (bw.map tailGen).prod • v = bw.foldr tailAct v := by
  induction bw with
  | nil => simp
  | cons b bw ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, tailGen_smul, List.foldr_cons]

@[expose] def tailWeyl
    : Subgroup (WeylGroup TwistTag.E6.tag) :=
  Subgroup.closure (Set.range tailGen)

@[expose] def weylA
    : Subgroup (WeylGroup TwistTag.E6.tag) :=
  Subgroup.closure (simple TwistTag.E6.tag '' {i | i ≠ e6Idx 1})


@[expose] def fixedBlockWords : List (List (Fin 3)) :=
  [[], [0], [0, 2], [0, 2, 0], [0, 2, 1], [0, 2, 1, 0], [0, 2, 1, 0, 2], [0, 2, 1, 0, 2, 0]]

theorem exists_fixedBlockWord : ∀ β ∈ fixedDegOneRoots, ∃ bw ∈ fixedBlockWords,
    bw.reverse.foldr tailAct (Pi.single (e6Idx 1) 1) = β := by
  decide +kernel

theorem exists_tailWeyl_smul_single
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ fixedDegOneRoots) :
    ∃ w ∈ tailWeyl, w • (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) = β := by
  obtain ⟨bw, -, hbw⟩ := exists_fixedBlockWord β hβ
  refine ⟨(bw.reverse.map tailGen).prod, Subgroup.list_prod_mem _ fun g hg => ?_, ?_⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨b, rfl⟩
  · rw [list_prod_tailGen_smul, hbw]


section Words

variable {K : Type} [Field K]

theorem neg_one_units_of_two (h2 : (2 : K) = 0) : (-1 : Kˣ) = 1 :=
  Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination -h2)

theorem weylElt_mul_canonicalRep_of_two
    {τ : Tag} (h2 : (2 : K) = 0) (i : Fin τ.rank)
    (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [neg_one_units_of_two h2, torusElt_one, one_mul]

@[expose] def wordElt
    (K : Type) [Field K] (ω : List (Fin TwistTag.E6.tag.rank)) :
    ModGL TwistTag.E6.tag K :=
  (ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod

theorem wordElt_eq_canonicalRep
    (h2 : (2 : K) = 0) (ω : List (Fin TwistTag.E6.tag.rank)) :
    wordElt K ω = canonicalRep (coxeterSystem TwistTag.E6.tag) K
      ((coxeterSystem TwistTag.E6.tag).wordProd ω) := by
  induction ω with
  | nil => rw [wordElt, List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil, canonicalRep_one]
  | cons i ω ih =>
    rw [wordElt, List.map_cons, List.prod_cons, ← wordElt, ih, weylElt_mul_canonicalRep_of_two h2,
      CoxeterSystem.wordProd_cons]

theorem wordElt_conj_pinnedX
    (h2 : (2 : K) = 0) (ω : List (Fin TwistTag.E6.tag.rank))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    wordElt K ω * pinnedX TwistTag.E6.tag K β c * (wordElt K ω)⁻¹ =
      pinnedX TwistTag.E6.tag K ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) c := by
  rw [wordElt_eq_canonicalRep h2, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ hβ]

theorem wordElt_mem_adjointGroup
    (ω : List (Fin TwistTag.E6.tag.rank)) :
    wordElt K ω ∈ adjointGroup TwistTag.E6.tag K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem wordElt_mem_graphFixedRootGroup
    (h2 : (2 : K) = 0) {σ : K →+* K}
    {ω : List (Fin TwistTag.E6.tag.rank)}
    (hω : weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd ω) =
      (coxeterSystem TwistTag.E6.tag).wordProd ω) :
    wordElt K ω ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [wordElt_eq_canonicalRep h2]
  exact canonicalRep_mem_graphFixedRootGroup hω

theorem diagramMap_conj_wordElt
    (h2 : (2 : K) = 0) {ω : List (Fin TwistTag.E6.tag.rank)}
    (hω : weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd ω) =
      (coxeterSystem TwistTag.E6.tag).wordProd ω) :
    diagramMap TwistTag.E6 K * wordElt K ω * (diagramMap TwistTag.E6 K)⁻¹ = wordElt K ω := by
  rw [wordElt_eq_canonicalRep h2, ← twistHom_id_eq, twistHom_canonicalRep, hω]

end Words

@[expose] def fusionWord : List (Fin TwistTag.E6.tag.rank) :=
  ([1, 3, 0, 5, 2, 4, 3, 2, 4, 0, 5, 1] : List (Fin 6))

@[expose] def upWord : List (Fin TwistTag.E6.tag.rank) := ([1, 3, 2, 4, 3, 1] : List (Fin 6))


theorem fusionWord_smul_e6HighestRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • e6HighestRoot =
      Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1 := by
  rw [wordProd_smul]
  decide

theorem fusionWord_smul_sRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd fusionWord • sRoot = Pi.single (e6Idx 3) 1 := by
  rw [wordProd_smul]
  decide

theorem upWord_smul_sRoot :
    (coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse • sRoot = e6HighestRoot := by
  rw [wordProd_smul]
  decide


theorem weylTwist_fusionWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd fusionWord) =
      (coxeterSystem TwistTag.E6.tag).wordProd fusionWord :=
  weylTwist_wordProd_eq (by decide)

theorem weylTwist_upWord :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse) =
      (coxeterSystem TwistTag.E6.tag).wordProd upWord.reverse :=
  weylTwist_wordProd_eq (by decide)


theorem two_eq_zero_of_card {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (2 : F) = 0 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hF, ← Nat.sub_add_cancel hn, pow_succ, Nat.mul_mod_left])
  exact two_eq_zero_of_ringChar hF2

theorem conj_commute {K : Type} [Field K] {G : Subgroup (ModGL TwistTag.E6.tag K)} (η : MulAut G)
    (hη : ∀ g : G, (η g : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K * g *
      (diagramMap TwistTag.E6 K)⁻¹) {x : ModGL TwistTag.E6.tag K} (hx : x ∈ G)
    (hPx : diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹ = x) :
    η ⟨x, hx⟩ = ⟨x, hx⟩ ∧ η * MulAut.conj ⟨x, hx⟩ = MulAut.conj ⟨x, hx⟩ * η := by
  have h1 : η ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext (by rw [hη]; exact hPx)
  refine ⟨h1, ?_⟩
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h1]


end CFSG.LieType.Chevalley.E6GraphHighestRoot
