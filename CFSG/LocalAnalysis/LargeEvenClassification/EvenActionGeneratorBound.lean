module

public import CFSG.LocalAnalysis.LargeEvenClassification.CongruenceLeadingResidue
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFrattini

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def binaryHomRange {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) : Submodule (ZMod 2) F :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' f.range)

theorem binaryHomRange_mem {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) (z : F) :
    z ∈ binaryHomRange f ↔ ∃ g : G, f g = Multiplicative.ofAdd z := Iff.rfl


theorem binaryHom_frattini_le_ker {G F : Type*} [Group G] [AddCommGroup F]
    [Module (ZMod 2) F] (f : G →* Multiplicative F) : frattini G ≤ f.ker := by
  let Image := f.range
  let : Module (ZMod 2) (Additive Image) := elementaryZModModule (fun z => by
    apply Subtype.ext
    change Multiplicative.ofAdd (2 • z.val.toAdd) = 1
    rw [two_nsmul, ZModModule.add_self]
    rfl)
  have h := elementary_quotient_kills_frattini Nat.prime_two f.rangeRestrict f.rangeRestrict_surjective
  intro g hg
  exact congrArg Subtype.val (h hg)

theorem binaryHom_quotient_generator_rank {G F : Type*} [Group G] [Finite G]
    [AddCommGroup F] [Module (ZMod 2) F] (hpgroup : IsPGroup 2 G)
    (Normal : Subgroup G) [Normal.Normal] (f : G →* Multiplicative F) (hker : f.ker = Normal) :
    pGeneratorRank 2 (G ⧸ Normal) = Module.finrank (ZMod 2) (binaryHomRange f) := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Finite (binaryHomRange f) := by
    let rangeEquiv : f.range ≃ binaryHomRange f := {
      toFun := fun z => ⟨z.val.toAdd, z.property⟩
      invFun := fun z => ⟨Multiplicative.ofAdd z.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact Finite.of_equiv f.range rangeEquiv
  let e : G ⧸ Normal ≃* f.range := QuotientGroup.liftEquiv Normal f.rangeRestrict_surjective (by
    rw [MonoidHom.ker_rangeRestrict, hker])
  have hquotient := hpgroup.to_quotient Normal
  rw [pGeneratorRank_eq_group_rank Nat.prime_two hquotient, Group.rank_congr e,
    ← pGeneratorRank_eq_group_rank Nat.prime_two
      (hquotient.of_injective e.symm.toMonoidHom e.symm.injective)]
  have hexponent (z : f.range) : z ^ 2 = 1 := by
    apply Subtype.ext
    change Multiplicative.ofAdd (2 • z.val.toAdd) = 1
    rw [two_nsmul, ZModModule.add_self]
    rfl
  rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two hexponent]
  have hcard : Nat.card f.range = Nat.card (binaryHomRange f) := by
    apply Nat.card_congr
    exact { toFun := fun z => ⟨z.val.toAdd, z.property⟩
            invFun := fun z => ⟨Multiplicative.ofAdd z.val, z.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard, ← FiniteField.pow_finrank_eq_natCard 2 (binaryHomRange f), Nat.log_pow (by decide : 1 < 2)]

theorem binary_leading_image_frattini_saving {G F : Type*} [Group G] [Finite G]
    [AddCommGroup F] [Finite F] [Module (ZMod 2) F] (hpgroup : IsPGroup 2 G)
    (Normal : Subgroup G) [Normal.Normal] (leading : Normal →* Multiplicative F)
    (C : Submodule (ZMod 2) F)
    (hC : C ≤ binaryHomRange (leading.comp ((frattini G).comap Normal.subtype).subtype)) :
    pGeneratorRank 2 G + Module.finrank (ZMod 2) C ≤
      pGeneratorRank 2 (G ⧸ Normal) + pGeneratorRank 2 Normal := by
  let Killed := (frattini G).comap Normal.subtype
  let basis := Module.finBasis (ZMod 2) C
  have hlift (i : Fin (Module.finrank (ZMod 2) C)) :
      ∃ g : Killed, leading g.val = Multiplicative.ofAdd (basis i).val :=
    (binaryHomRange_mem _ _).mp (hC (basis i).property)
  let family : Fin (Module.finrank (ZMod 2) C) → Normal :=
    fun i => (Classical.choose (hlift i)).val
  have hfamily (i : Fin (Module.finrank (ZMod 2) C)) :
      leading (family i) = Multiplicative.ofAdd (basis i).val := Classical.choose_spec (hlift i)
  have hkilled (i : Fin (Module.finrank (ZMod 2) C)) : (family i : G) ∈ frattini G :=
    (Classical.choose (hlift i)).property
  let : CommGroup (Normal ⧸ frattini Normal) :=
    pGroupFrattiniCommGroup Nat.prime_two (hpgroup.to_subgroup Normal)
  let module : Module (ZMod 2) (Additive (Normal ⧸ frattini Normal)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two (hpgroup.to_subgroup Normal))
  let := module
  let quotient := QuotientGroup.lift (frattini Normal) leading (binaryHom_frattini_le_ker leading)
  let linear := quotient.toAdditiveLeft.toZModLinearMap 2
  have himages : (fun i => linear (Additive.ofMul
      ((QuotientGroup.mk' (frattini Normal)) (family i)))) = fun i => (basis i).val := by
    funext i
    change (quotient ((QuotientGroup.mk' (frattini Normal)) (family i))).toAdd = (basis i).val
    change (leading (family i)).toAdd = (basis i).val
    rw [hfamily]
    rfl
  have hindependent : LinearIndependent (ZMod 2) (fun i => Additive.ofMul
      ((QuotientGroup.mk' (frattini Normal)) (family i))) := by
    apply LinearIndependent.of_comp linear
    rw [Function.comp_def, himages]
    exact basis.linearIndependent.map' C.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hsaving := pGeneratorRank_normal_independent_saving Nat.prime_two hpgroup
    Normal family hkilled module hindependent
  simpa only [Fintype.card_fin] using hsaving

section EvenAction

variable {R F : Type*} [Ring R] [Ring F] [Module (ZMod 2) F]
variable (residue : R →+* F)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)
variable (Action : Subgroup Rˣ)
variable (heven : Action ≤ principalCongruenceSubgroup R 2)

@[expose] def evenActionInclusion : Action →* principalCongruenceSubgroup R 2 :=
  Action.inclusion heven

@[expose] noncomputable def evenActionLeadingHom : Action →* Multiplicative F :=
  (principalLeadingResidueHom residue hkernel 2 (by decide) hcancelTwo).comp
    (evenActionInclusion Action heven)

@[expose] def evenActionDeep : Subgroup Action :=
  (principalFourSubgroup R).comap Action.subtype

instance evenActionDeep_normal : (evenActionDeep Action).Normal := by
  let : (principalFourSubgroup R).Normal := principal_four_normal R
  exact Subgroup.Normal.comap inferInstance Action.subtype

omit [Module (ZMod 2) F] in
theorem evenActionLeadingHom_ker :
    (evenActionLeadingHom residue hkernel hcancelTwo Action heven).ker = evenActionDeep Action := by
  ext u
  change principalLeadingResidueHom residue hkernel 2 (by decide) hcancelTwo
    (evenActionInclusion Action heven u) = 1 ↔ (u.val ∈ principalFourSubgroup R)
  rw [principalLeadingResidueHom_kernel, show (2 : ℕ) * 2 = 4 from rfl,
    principalCongruenceSubgroup_four]
  rfl

@[expose] def evenActionDeepInclusion : evenActionDeep Action →* principalCongruenceSubgroup R 4 where
  toFun u := ⟨u.val.val, (principalCongruenceSubgroup_four R).symm ▸ u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def evenActionDeepLeadingHom : evenActionDeep Action →* Multiplicative F :=
  (principalLeadingResidueHom residue hkernel 4 (by decide) hcancelFour).comp
    (evenActionDeepInclusion Action)

@[expose] def evenActionKilledDeep : Subgroup (evenActionDeep Action) :=
  (frattini Action).comap (evenActionDeep Action).subtype

@[expose] noncomputable def evenActionKilledResidueHom : evenActionKilledDeep Action →* Multiplicative F :=
  (evenActionDeepLeadingHom residue hkernel hcancelFour Action).comp
    (evenActionKilledDeep Action).subtype

include heven in
theorem evenAction_square_residue_mem_killed [Finite Action] (hpgroup : IsPGroup 2 Action) (u : Action) :
    let x := (evenActionLeadingHom residue hkernel hcancelTwo Action heven u).toAdd
    x + x * x ∈ binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  dsimp only
  let g : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven u
  have hdeep : u ^ 2 ∈ evenActionDeep Action := by
    change u.val ^ 2 ∈ principalFourSubgroup R
    rw [← principalCongruenceSubgroup_four]
    exact principal_two_square_mem_four g.val g.property
  let witness : evenActionKilledDeep Action :=
    ⟨⟨u ^ 2, hdeep⟩, pGroup_pow_mem_frattini Nat.prime_two hpgroup u⟩
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨witness, ?_⟩
  apply Multiplicative.toAdd.injective
  exact principal_two_square_leading residue hcancelFour g

include heven in
theorem evenAction_commutator_residue_mem_killed [Finite Action] (hpgroup : IsPGroup 2 Action)
    (u v : Action) :
    let x := (evenActionLeadingHom residue hkernel hcancelTwo Action heven u).toAdd
    let y := (evenActionLeadingHom residue hkernel hcancelTwo Action heven v).toAdd
    x * y - y * x ∈ binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  dsimp only
  let g : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven u
  let h : principalCongruenceSubgroup R 2 := evenActionInclusion Action heven v
  have hdeep : u * v * u⁻¹ * v⁻¹ ∈ evenActionDeep Action := by
    change u.val * v.val * u.val⁻¹ * v.val⁻¹ ∈ principalFourSubgroup R
    rw [← principalCongruenceSubgroup_four]
    exact principal_two_commutator_mem_four g.val h.val g.property h.property
  let witness : evenActionKilledDeep Action :=
    ⟨⟨u * v * u⁻¹ * v⁻¹, hdeep⟩, pGroup_commutator_mem_frattini Nat.prime_two hpgroup u v⟩
  apply (binaryHomRange_mem _ _).mpr
  refine ⟨witness, ?_⟩
  apply Multiplicative.toAdd.injective
  exact principal_two_commutator_leading residue hkernel hcancelFour g h

include heven in
theorem evenAction_residue_span_le_killed [Finite Action] (hpgroup : IsPGroup 2 Action) :
    residueSquareCommutatorSpan (binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven)) ≤
      binaryHomRange (evenActionKilledResidueHom residue hkernel hcancelFour Action) := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl⟩
  · obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp hx
    have h := evenAction_square_residue_mem_killed residue hkernel hcancelTwo hcancelFour Action heven hpgroup u
    rw [hu] at h
    exact h
  · obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp hx
    obtain ⟨v, hv⟩ := (binaryHomRange_mem _ _).mp hy
    have h := evenAction_commutator_residue_mem_killed residue hkernel hcancelTwo hcancelFour Action heven
      hpgroup u v
    rw [hu, hv] at h
    exact h

include heven hcancelFour in
theorem evenAction_generator_rank_saving [Finite Action] [Finite F] (hpgroup : IsPGroup 2 Action) :
    let W := binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven)
    pGeneratorRank 2 Action + Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) ≤
      Module.finrank (ZMod 2) W + pGeneratorRank 2 (evenActionDeep Action) := by
  dsimp only
  have hsaving := binary_leading_image_frattini_saving hpgroup (evenActionDeep Action)
    (evenActionDeepLeadingHom residue hkernel hcancelFour Action)
    (residueSquareCommutatorSpan (binaryHomRange
      (evenActionLeadingHom residue hkernel hcancelTwo Action heven)))
    (evenAction_residue_span_le_killed residue hkernel hcancelTwo hcancelFour Action heven hpgroup)
  rw [binaryHom_quotient_generator_rank hpgroup (evenActionDeep Action)
    (evenActionLeadingHom residue hkernel hcancelTwo Action heven)
    (evenActionLeadingHom_ker residue hkernel hcancelTwo Action heven)] at hsaving
  exact hsaving

include residue hkernel hcancelTwo hcancelFour heven in
theorem evenAction_generator_rank_bound [Finite Action] [Finite F] (hpgroup : IsPGroup 2 Action)
    (hresidue : ∀ W : Submodule (ZMod 2) F,
      Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 2) :
    pGeneratorRank 2 Action ≤ pGeneratorRank 2 (evenActionDeep Action) + 2 := by
  have hsaving := evenAction_generator_rank_saving residue hkernel hcancelTwo hcancelFour Action heven hpgroup
  have hbound := hresidue (binaryHomRange (evenActionLeadingHom residue hkernel hcancelTwo Action heven))
  omega


end EvenAction

section CanonicalRankTwo

variable {Abelian : Type*} [AddCommGroup Abelian]
variable (upper lower : ℕ) (hle : lower ≤ upper) (hlower : 3 ≤ lower)
variable (coordinates : Abelian ≃+ (ZMod (2 ^ upper) × ZMod (2 ^ lower)))

include hle coordinates in
theorem rank_two_endomorphism_characteristic : (2 : AddMonoid.End Abelian) ^ upper = 0 := by
  rw [← Nat.cast_ofNat, ← Nat.cast_pow]
  apply AddMonoid.End.ext
  intro x
  change (2 ^ upper : ℕ) • x = 0
  apply coordinates.injective
  rw [map_nsmul, map_zero]
  apply Prod.ext
  · change (2 ^ upper : ℕ) • (coordinates x).1 = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · change (2 ^ upper : ℕ) • (coordinates x).2 = 0
    rw [nsmul_eq_mul]
    have hcast : ((2 ^ upper : ℕ) : ZMod (2 ^ lower)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 hle)
    rw [hcast, zero_mul]


end CanonicalRankTwo

end CFSG.LargeEvenClassification.Helpers
