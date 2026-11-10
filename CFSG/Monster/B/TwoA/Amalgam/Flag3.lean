module

public import CFSG.Monster.B.TwoA.Amalgam.Flag3Quot
public import CFSG.Monster.B.TwoA.Amalgam.Flag3Lin

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 MulAction

open scoped IsMulCommutative

attribute [local instance] k3SetAction subspaceAction parAction

theorem exists_phiP3_eq
    (A : Additive E3 ≃ₗ[ZMod 2] Additive E3) (π : Equiv.Perm Five) :
    ∃ g : Pc 2, (phiP3 g).1 = A ∧ (phiP3 g).2 = π := by
  obtain ⟨g, hg⟩ := phiP3_surjective (A, π)
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

instance finiteDimensional_additive_E3 :
    FiniteDimensional (ZMod 2) (Additive E3) :=
  Module.Finite.of_finite

theorem finrank_additive_E3 :
    Module.finrank (ZMod 2) (Additive E3) = 3 :=
  finrank_additive_of_card natCard_E3_pow

theorem exists_smul_eq_sub
    {j : ℕ} (S T : SubspaceDim (ZMod 2) (Additive E3) j) :
    ∃ g : Pc 2, (phiP3 g).1 • S = T := by
  obtain ⟨A, hA⟩ := exists_linearEquiv_map_eq (S.2.trans T.2.symm)
  obtain ⟨g, hg, -⟩ := exists_phiP3_eq A 1
  exact ⟨g, (congrArg (· • S) hg).trans (Subtype.ext ((subspace_smul_coe A S).trans hA))⟩

theorem exists_smul_eq_five
    (C' C'' : Five) : ∃ g : Pc 2, (phiP3 g).2 C' = C'' := by
  obtain ⟨g, -, hg⟩ := exists_phiP3_eq 1 (Equiv.swap C' C'')
  exact ⟨g, (congrArg (fun τ : Equiv.Perm Five => τ C') hg).trans (Equiv.swap_apply_left C' C'')⟩

theorem exists_gl_flag
    (p p' : SubspaceDim (ZMod 2) (Additive E3) 1)
    (l l' : SubspaceDim (ZMod 2) (Additive E3) 2) (hpl : p.1 ≤ l.1) (hpl' : p'.1 ≤ l'.1) :
    ∃ A : Additive E3 ≃ₗ[ZMod 2] Additive E3, A • p = p' ∧ A • l = l' := by
  have h1 : Module.finrank (ZMod 2) p.1 = Module.finrank (ZMod 2) p'.1 := p.2.trans p'.2.symm
  have h2 : Module.finrank (ZMod 2) l.1 = Module.finrank (ZMod 2) l'.1 := l.2.trans l'.2.symm
  have hex := exists_linearEquiv_map_eq_map_eq hpl hpl' h1 h2
  obtain ⟨A, hA⟩ := hex
  exact ⟨A, Subtype.ext ((subspace_smul_coe A p).trans hA.1),
    Subtype.ext ((subspace_smul_coe A l).trans hA.2)⟩

theorem p3_flag_transitive
    (p p' : SubspaceDim (ZMod 2) (Additive E3) 1)
    (l l' : SubspaceDim (ZMod 2) (Additive E3) 2) (C' C'' : Five) (hpl : p.1 ≤ l.1)
    (hpl' : p'.1 ≤ l'.1) :
    ∃ g : Pc 2, (phiP3 g).1 • p = p' ∧ (phiP3 g).1 • l = l' ∧ (phiP3 g).2 C' = C'' :=
  (exists_gl_flag p p' l l' hpl hpl').elim fun A hA =>
    (exists_phiP3_eq A (Equiv.swap C' C'')).elim fun g hg =>
      ⟨g, (congrArg (· • p) hg.1).trans hA.1, (congrArg (· • l) hg.1).trans hA.2,
        (congrArg (fun τ : Equiv.Perm Five => τ C') hg.2).trans (Equiv.swap_apply_left C' C'')⟩

theorem mk_eq_mk_iff_pt
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ↔ (phiP3 x).1 • ptE1 = (phiP3 g).1 • ptE1 :=
  mk_eq_mk_iff_of_hom ((MonoidHom.fst _ _).comp phiP3) ptE1 (fun g => mem_Pc0_iff g) x g

theorem mk_eq_mk_iff_ln
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g ↔ (phiP3 x).1 • lnE2 = (phiP3 g).1 • lnE2 :=
  mk_eq_mk_iff_of_hom ((MonoidHom.fst _ _).comp phiP3) lnE2 (fun g => mem_Pc1_iff g) x g

theorem mk_eq_mk_iff_five
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = g ↔ (phiP3 x).2 fiveC = (phiP3 g).2 fiveC :=
  mk_eq_mk_iff_of_hom ((MonoidHom.snd _ _).comp phiP3) fiveC (fun g => mem_Pc3_iff g) x g

theorem exists_pt_equiv :
    ∃ f : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 1,
      (∀ g : Pc 2, f g = (phiP3 g).1 • ptE1) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a :=
  exists_quotient_equiv_of_hom ((MonoidHom.fst _ _).comp phiP3) ptE1
    (fun x => exists_smul_eq_sub ptE1 x) (fun g => mem_Pc0_iff g)

theorem exists_ln_equiv :
    ∃ f : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 2,
      (∀ g : Pc 2, f g = (phiP3 g).1 • lnE2) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a :=
  exists_quotient_equiv_of_hom ((MonoidHom.fst _ _).comp phiP3) lnE2
    (fun x => exists_smul_eq_sub lnE2 x) (fun g => mem_Pc1_iff g)

theorem exists_five_equiv :
    ∃ f : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2) ≃ Five,
      (∀ g : Pc 2, f g = (phiP3 g).2 fiveC) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).2 (f a) :=
  exists_quotient_equiv_of_hom ((MonoidHom.snd _ _).comp phiP3) fiveC
    (fun x => exists_smul_eq_five fiveC x) (fun g => mem_Pc3_iff g)


theorem natCard_points_E3 :
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 1) = 7 := by
  rw [card_subspaces (by rw [finrank_additive_E3]; norm_num), ZMod.card, finrank_additive_E3]
  decide

theorem natCard_lines_E3 :
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 2) = 7 := by
  rw [card_subspaces (by rw [finrank_additive_E3]; norm_num), ZMod.card, finrank_additive_E3]
  decide

theorem index_Pc0_subgroupOf :
    ((Pc 0).subgroupOf (Pc 2)).index = 7 := by
  obtain ⟨f, -, -⟩ := exists_pt_equiv
  exact (Nat.card_congr f).trans natCard_points_E3

theorem index_Pc1_subgroupOf :
    ((Pc 1).subgroupOf (Pc 2)).index = 7 := by
  obtain ⟨f, -, -⟩ := exists_ln_equiv
  exact (Nat.card_congr f).trans natCard_lines_E3

theorem index_Pc3_subgroupOf :
    ((Pc 3).subgroupOf (Pc 2)).index = 5 := by
  obtain ⟨f, -, -⟩ := exists_five_equiv
  exact (Nat.card_congr f).trans natCard_orbit_subgeom


end CFSG.Monster.B.TwoA.Amalgam
