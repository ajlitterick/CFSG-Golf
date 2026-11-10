module

public import CFSG.YGroups.Y433.Relabel

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

abbrev Y343 : Type := YGroup 3 4 3

namespace Y343

@[expose] def armStart : ℕ → ℕ
  | 1 => 1
  | 2 => 4
  | 3 => 8
  | _ => 0

@[expose] noncomputable def A : Y343 := yGen 3 4 3 0

@[expose] noncomputable def B (i : ℕ) : Y343 := yGen 3 4 3 (armStart i)

@[expose] noncomputable def C (i : ℕ) : Y343 := yGen 3 4 3 (armStart i + 1)

@[expose] noncomputable def D (i : ℕ) : Y343 := yGen 3 4 3 (armStart i + 2)

@[expose] noncomputable def E₂ : Y343 := yGen 3 4 3 (armStart 2 + 3)

@[expose] noncomputable def T (i : ℕ) : Y343 := A * B i * C i

@[expose] noncomputable def F (i j k : ℕ) : Y343 := (A * B i * C i * D i * B j * C j * B k) ^ 9


theorem spider : (T 1 * T 2 * T 3) ^ 10 = 1 := by
  have h := evalWord_yGen_of_mem (p := 3) (q := 4) (r := 3)
    (w := (List.replicate 10 (spiderWord 3 4)).flatten) (by
      simp only [yRels, List.mem_append]
      refine Or.inr ?_
      simp)
  rw [Y443.evalWord_replicate_flatten] at h
  rw [← h, Relabel.evalWord_spiderWord]
  rfl

end Y343

@[expose] noncomputable def Q343Extra : Y343 := Y343.F 3 1 2

theorem Q343Extra_eq_evalWord :
    Q343Extra = evalWord (yGen 3 4 3) [0, 8, 9, 10, 1, 2, 4] ^ 9 := by
  simp only [Q343Extra, Y343.F, Y343.A, Y343.B, Y343.C, Y343.D, Y343.armStart, evalWord_cons,
    evalWord_nil, mul_one, mul_assoc, Nat.reduceAdd]

abbrev Q343 : Type := Y343 ⧸ Subgroup.normalClosure {Q343Extra}

@[expose] def delE1 (c : ℕ) : ℕ := if c < 4 then c else c - 1

theorem yRels_343_eq :
    yRels 3 4 3 = ((yRels 4 4 3).filter (fun w => decide (4 ∉ w))).map (List.map delE1) := by
  decide +kernel


namespace Q343

@[expose] noncomputable def π : Y343 →* Q343 :=
  QuotientGroup.mk' (Subgroup.normalClosure {Q343Extra})

@[expose] noncomputable def vA : Q343 := π Y343.A

@[expose] noncomputable def vB (i : ℕ) : Q343 := π (Y343.B i)

@[expose] noncomputable def vC (i : ℕ) : Q343 := π (Y343.C i)

@[expose] noncomputable def vD (i : ℕ) : Q343 := π (Y343.D i)


theorem π_surjective : Function.Surjective π := QuotientGroup.mk'_surjective _


theorem ker_π : π.ker = Subgroup.normalClosure {Q343Extra} := QuotientGroup.ker_mk' _

noncomputable def lift {G : Type*} [Group G] (img : ℕ → G)
    (h : ∀ w ∈ yRels 3 4 3, evalWord img w = 1)
    (hextra : evalWord img [0, 8, 9, 10, 1, 2, 4] ^ 9 = 1) : Q343 →* G :=
  QuotientGroup.lift _ (yModelHom img h) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Q343Extra_eq_evalWord, map_pow,
      Relabel.yModelHom_evalWord _ (by decide)]
    exact hextra)

theorem lift_π {G : Type*} [Group G] (img : ℕ → G) (h : ∀ w ∈ yRels 3 4 3, evalWord img w = 1)
    (hextra : evalWord img [0, 8, 9, 10, 1, 2, 4] ^ 9 = 1) {c : ℕ} (hc : c < 11) :
    lift img h hextra (π (yGen 3 4 3 c)) = img c :=
  (QuotientGroup.lift_mk _ _ _).trans (yModelHom_yGen hc)

end Q343


namespace Q343Presented


theorem lift_of_eq_mk {rels : Set (FreeGroup (Fin (ngen 3 4 3)))}
    (r : FreeGroup (Fin (ngen 3 4 3))) :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) r = PresentedGroup.mk rels r := by
  have : FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]


end Q343Presented


end CFSG.YGroups
