module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenGen
public import CFSG.RankThree.Lattice.SteinbergBIGenCells

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups
open scoped Pointwise


theorem e6RootSpan_le_adjointGroup {Ω : Type} [Field Ω] (S : Set (Fin Tag.E6.rank → ℤ)) :
    rootSpan Tag.E6 Ω S ≤ adjointGroup Tag.E6 Ω :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)


@[expose] def fixedRootGroup (S : Set (Fin Tag.E6.rank → ℤ)) : Subgroup (ModGL Tag.E6 Ω) :=
  rootSpan Tag.E6 Ω S ⊓ D.psi.eqLocus (MonoidHom.id _)

@[expose] def fixedTorus : Subgroup (ModGL Tag.E6 Ω) :=
  D.torus ⊓ D.psi.eqLocus (MonoidHom.id _)


@[expose] def cell (n : ModGL Tag.E6 Ω) : Set (ModGL Tag.E6 Ω) :=
  D.orbitBorel * {n} * D.orbitBorel


theorem gen_e : D.gen.e = D.f :=
  rfl


theorem gen_roots : D.gen.roots = D.Ξ := by
  ext α
  constructor
  · rintro ⟨h, -⟩
    have h' : α ∈ kernelRoots D.chi := h
    rwa [D.kernelRoots_chi] at h'
  · intro h
    have h' : α ∈ kernelRoots D.chi := by rwa [D.kernelRoots_chi]
    exact ⟨h', Set.mem_univ _⟩

theorem gen_rootSpanJ : D.gen.rootSpanJ = D.rootGroup := by
  show rootSpan Tag.E6 Ω D.gen.roots = rootSpan Tag.E6 Ω D.Ξ
  rw [D.gen_roots]


theorem gen_torusJ : D.gen.torusJ = D.torus := by
  show D.gen.rootSpanJ ⊓ torusGroup Tag.E6 Ω = D.rootGroup ⊓ torusGroup Tag.E6 Ω
  rw [D.gen_rootSpanJ]


theorem mem_gen_simpleRootsJ {β : Fin Tag.E6.rank → ℤ} :
    β ∈ D.gen.simpleRootsJ ↔ ∃ j ∈ D.support, β = Pi.single j 1 := by
  constructor
  · rintro ⟨hβ, -⟩
    exact D.mem_unionSimpleRoots_iff.1 hβ
  · rintro ⟨j, hj, rfl⟩
    refine ⟨D.mem_unionSimpleRoots_iff.2 ⟨j, hj, rfl⟩, ?_⟩
    rw [D.gen_roots]
    exact hj

theorem gen_orbits : D.gen.orbits = D.orbits := by
  ext O
  constructor
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨j, hj, rfl⟩ := D.mem_gen_simpleRootsJ.1 hβ
    exact ⟨j, hj, (D.simpleOrbit_eq_thetaOrbit j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, D.mem_gen_simpleRootsJ.2 ⟨j, hj, rfl⟩, D.simpleOrbit_eq_thetaOrbit j⟩

theorem mem_gen_orbits {O : Set (Fin Tag.E6.rank → ℤ)} : O ∈ D.gen.orbits ↔ O ∈ D.orbits := by
  rw [D.gen_orbits]


theorem orbitRoot_mem {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    orbitRoot O ∈ O := by
  classical
  obtain ⟨j, -, rfl⟩ := hO
  have h : ∃ i : Fin Tag.E6.rank, Pi.single i 1 ∈ D.simpleOrbit j := ⟨j, ⟨0, rfl⟩⟩
  unfold orbitRoot orbitIndex
  split_ifs
  exact (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter fun i : Fin Tag.E6.rank =>
    Pi.single i 1 ∈ D.simpleOrbit j) _)).2

theorem eq_pair_of_mem_orbits {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ O) : O = {β, D.δ β} := by
  obtain ⟨j, -, rfl⟩ := hO
  rw [D.simpleOrbit_eq_thetaOrbit, D.thetaOrbit_eq] at hβ ⊢
  rcases hβ with rfl | rfl
  · rfl
  · rw [D.δ_δ, Set.pair_comm]

theorem mem_Ξ_of_mem_orbits {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ O) : β ∈ D.Ξ := by
  obtain ⟨j, hj, rfl⟩ := hO
  rw [D.simpleOrbit_eq_thetaOrbit, D.thetaOrbit_eq] at hβ
  rcases hβ with rfl | rfl
  · exact hj
  · exact D.δ_mem_Ξ hj

theorem gen_orbitVec (O : Set (Fin Tag.E6.rank → ℤ)) (j : ℕ) :
    D.gen.orbitVec O j = D.δ^[j] (GenFixedRootDatum.orbitRoot O) :=
  thetaPowVec_eq (D.theta_pow_toReal j _).symm

@[expose] def orbitFrob (O : Set (Fin Tag.E6.rank → ℤ)) : D.orbitField O →+* D.orbitField O :=
  (iterateFrobenius Ω 2 D.f).restrict (D.orbitField O) (D.orbitField O) fun x hx => by
    rw [D.mem_orbitField] at hx ⊢
    rw [iterateFrobenius_def, ← pow_mul, mul_comm, pow_mul, hx]

theorem coe_orbitFrob (O : Set (Fin Tag.E6.rank → ℤ)) (c : D.orbitField O) :
    (D.orbitFrob O c : Ω) = iterateFrobenius Ω 2 D.f c :=
  rfl

theorem orbitFrob_orbitFrob {O : Set (Fin Tag.E6.rank → ℤ)} (h2 : orbitCard O = 2)
    (c : D.orbitField O) : D.orbitFrob O (D.orbitFrob O c) = c := by
  apply Subtype.ext
  have hc := D.mem_orbitField.1 c.2
  rw [h2, sq, pow_mul] at hc
  rw [coe_orbitFrob, coe_orbitFrob, iterateFrobenius_def, iterateFrobenius_def]
  exact hc

theorem map_iterateFrobenius_mul_zero (B : SL2 Ω) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * 0)) B = B := by
  ext i i'
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_subtype_map_orbitFrob (O : Set (Fin Tag.E6.rank → ℤ)) (A : SL2 (D.orbitField O)) :
    Matrix.SpecialLinearGroup.map (D.orbitField O).subtype
        (Matrix.SpecialLinearGroup.map (D.orbitFrob O) A) =
      Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f)
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  ext i i'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem map_iterateFrobenius_map_of_card_two {O : Set (Fin Tag.E6.rank → ℤ)}
    (h2 : orbitCard O = 2) (A : SL2 (D.orbitField O)) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f)
          (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A)) =
      Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A := by
  ext i i'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    iterateFrobenius_def]
  have hc := D.mem_orbitField.1 ((A : Matrix (Fin 2) (Fin 2) (D.orbitField O)) i i').2
  rw [h2, sq, pow_mul] at hc
  exact hc

theorem prod_range_two (β : Fin Tag.E6.rank → ℤ) (B : SL2 Ω) :
    ((List.range 2).map fun j => rootSL2 Tag.E6 Ω (D.δ^[j] β)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * j)) B)).prod =
      rootSL2 Tag.E6 Ω β B *
        rootSL2 Tag.E6 Ω (D.δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f) B) := by
  rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_cons, List.prod_nil, mul_one, D.map_iterateFrobenius_mul_zero,
    Nat.mul_one]
  rfl

theorem exists_orbitMap_eq_gen {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ σ : D.orbitField O →+* D.orbitField O, Function.Bijective σ ∧
      ∀ A, D.orbitMap O A = D.gen.orbitMap O (Matrix.SpecialLinearGroup.map σ A) := by
  have hO' : O ∈ D.gen.orbits := D.mem_gen_orbits.2 hO
  set α₀ := orbitRoot O with hα₀def
  set β₀ := GenFixedRootDatum.orbitRoot O with hβ₀def
  have hα₀ : α₀ ∈ O := D.orbitRoot_mem hO
  have hβ₀ : β₀ ∈ O := D.gen.orbitRoot_mem hO'
  have hOα := D.eq_pair_of_mem_orbits hO hα₀
  have hgen : ∀ A : SL2 (D.orbitField O), D.gen.orbitMap O A =
      ((List.range (orbitCard O)).map fun j => rootSL2 Tag.E6 Ω (D.δ^[j] β₀)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * j))
          (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A))).prod := by
    intro A
    refine (D.gen.orbitMap_eq_prod O A).trans ?_
    congr 1
    refine List.map_congr_left fun j _ => ?_
    refine (D.gen.orbitFactor_apply O j A).trans ?_
    rw [D.gen_orbitVec]
    rfl
  by_cases hβα : β₀ = α₀
  · refine ⟨RingHom.id _, Function.bijective_id, fun A => ?_⟩
    have hA : Matrix.SpecialLinearGroup.map (RingHom.id (D.orbitField O)) A = A := by
      ext i i'
      simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [hA, hgen, hβα]
    rfl
  · have hβ₀' : β₀ = D.δ α₀ := by
      rw [hOα] at hβ₀
      rcases hβ₀ with h | h
      · exact absurd h hβα
      · exact h
    have hne : α₀ ≠ D.δ α₀ := fun h => hβα (hβ₀'.trans h.symm)
    have h2 : orbitCard O = 2 := by
      rw [orbitCard, hOα]
      exact Set.ncard_pair hne
    have hinv := D.orbitFrob_orbitFrob h2
    refine ⟨D.orbitFrob O, Function.Involutive.bijective hinv, fun A => ?_⟩
    have h2' : GenFixedRootDatum.orbitCard O = 2 := h2
    rw [hgen, D.map_subtype_map_orbitFrob, orbitMap, h2, D.prod_range_two, D.prod_range_two,
      D.map_iterateFrobenius_map_of_card_two h2, hβ₀', D.δ_δ]
    have hc := D.gen.commute_rootRankOneGroup_orbitVec hO' (i := 0) (j := 1) (by omega)
      (by omega) (by omega)
    rw [D.gen_orbitVec, D.gen_orbitVec, Function.iterate_zero, id, Function.iterate_one,
      ← hβ₀def, hβ₀', D.δ_δ] at hc
    exact (hc _ ⟨_, rfl⟩ _ ⟨_, rfl⟩).symm

theorem orbitSwap_eq (O : Set (Fin Tag.E6.rank → ℤ)) (σ : D.orbitField O →+* D.orbitField O) :
    Matrix.SpecialLinearGroup.map σ (D.orbitSwap O) = WSL := by
  ext i i'
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_WSL, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases i' <;>
    simp [orbitSwap, D.neg_one_eq_one_orbitField O]

theorem exists_orbitX_eq_gen {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ σ : D.orbitField O →+* D.orbitField O, Function.Bijective σ ∧
      (∀ A, D.orbitMap O A = D.gen.orbitMap O (Matrix.SpecialLinearGroup.map σ A)) ∧
      (∀ c, D.orbitX O c = D.gen.orbitX O (σ c)) ∧ (∀ c, D.orbitY O c = D.gen.orbitY O (σ c)) ∧
      D.orbitN O = D.gen.orbitN O := by
  obtain ⟨σ, hσ, h⟩ := D.exists_orbitMap_eq_gen hO
  refine ⟨σ, hσ, h, fun c => ?_, fun c => ?_, ?_⟩
  · rw [orbitX, h, map_uSL]
    rfl
  · rw [orbitY, h, map_vSL]
    rfl
  · rw [orbitN, h, D.orbitSwap_eq]
    rfl


theorem gen_orbitGroup : D.gen.orbitGroup = D.orbitGroup := by
  show Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext g
  constructor
  · rintro ⟨O, hO, c, hc⟩
    have hO' := D.mem_gen_orbits.1 hO
    obtain ⟨σ, hσ, -, hX, hY, -⟩ := D.exists_orbitX_eq_gen hO'
    obtain ⟨c', rfl⟩ := hσ.2 c
    exact ⟨O, hO', c', by rw [hX, hY]; exact hc⟩
  · rintro ⟨O, hO, c, hc⟩
    obtain ⟨σ, -, -, hX, hY, -⟩ := D.exists_orbitX_eq_gen hO
    exact ⟨O, D.mem_gen_orbits.2 hO, σ c, by rw [← hX, ← hY]; exact hc⟩

theorem orbitGroup_le_rootGroup : D.orbitGroup ≤ D.rootGroup := by
  rw [← D.gen_orbitGroup, ← D.gen_rootSpanJ]
  exact D.gen.orbitGroup_le_rootSpanJ


theorem map_subtype_fixed {H : Subgroup (ModGL Tag.E6 Ω)} (hH : H ≤ adjointGroup Tag.E6 Ω) :
    (H.subgroupOf (adjointGroup Tag.E6 Ω) ⊓ D.gen.F.toMonoidHom.eqLocus (MonoidHom.id _)).map
        (adjointGroup Tag.E6 Ω).subtype = H ⊓ D.psi.eqLocus (MonoidHom.id _) := by
  ext g
  constructor
  · rintro ⟨x, ⟨hxH, hxF⟩, rfl⟩
    exact ⟨Subgroup.mem_subgroupOf.1 hxH, congrArg Subtype.val hxF⟩
  · rintro ⟨hgH, hgF⟩
    exact ⟨⟨g, hH hgH⟩, ⟨Subgroup.mem_subgroupOf.2 hgH, Subtype.ext hgF⟩, rfl⟩

theorem gen_fixedGroup :
    D.gen.fixedGroup.map (adjointGroup Tag.E6 Ω).subtype = D.fixedGroup := by
  rw [GenFixedRootDatum.fixedGroup, D.gen_rootSpanJ]
  exact D.map_subtype_fixed (e6RootSpan_le_adjointGroup _)


theorem torus_le_adjointGroup : D.torus ≤ adjointGroup Tag.E6 Ω :=
  inf_le_left.trans (e6RootSpan_le_adjointGroup _)

theorem gen_fixedTorus :
    D.gen.fixedTorus.map (adjointGroup Tag.E6 Ω).subtype = D.fixedTorus := by
  rw [GenFixedRootDatum.fixedTorus, D.gen_torusJ]
  exact D.map_subtype_fixed D.torus_le_adjointGroup


end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice
