module

public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421Elim
public import CFSG.Quasithin.Background.F1Rank
public import CFSG.Quasithin.Recognition.F112WSetup

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S1421

section L16

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isQuasithinSub_of_qtke (hK : quasithinIsQTKECat G) (X : Subgroup G) : IsQuasithinSub X := by
  intro p hp hp2 R _ hRne hR2
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
    (pRank_le_two_of_isTwoLocal hK hloc hp hp2)

omit [Finite G] in
theorem psi_mem_pCore_iff {P : Subgroup G} (e : OTwoQuot P ≃* Equiv.Perm (Fin 3)) (x : ↥P) :
    psi e x = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥P := by
  unfold psi
  rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    QuotientGroup.mk'_apply, e.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem isSolvable_yT (F : Facts1422 T M) : Group.IsSolvable ↥(yOfL22 T M ⊔ T) := by
  obtain ⟨e⟩ := F.sThree
  have hS3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have h2 : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ T)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(yOfL22 T M ⊔ T)) 2).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ T)).subtype (psi e)
    (fun x hx => ⟨⟨x, (psi_mem_pCore_iff e x).mp hx⟩, rfl⟩)

theorem isSolvable_l2_sup (h : Hyp1421 G T M) (F : Facts1422 T M) {S : Subgroup G} (hST : S ≤ T) :
    Group.IsSolvable ↥(l2Of T H (yOfL22 T M) ⊔ S) := by
  have hle : l2Of T H (yOfL22 T M) ⊔ S ≤ yOfL22 T M ⊔ T :=
    sup_le (sup_le le_sup_left ((s2_le_T h).trans le_sup_right)) (hST.trans le_sup_right)
  have := isSolvable_yT F
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem vz_le_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    VZ T M ≤ pCoreOf 2 (l2Of T H (yOfL22 T M)) := by
  obtain ⟨hVred, -⟩ := isTwoReducedIn_VZ_of_hyp h
  refine le_pCoreOf_of_le_normalizer 2 ((vz_le_y h F).trans le_sup_left) ?_
    (isPGroup_of_isElemAbelian hVred.2.2.1)
  exact sup_le ((yOfL22_le T M).trans hVred.2.1) ((s2_le_T h).trans ((T_le_M h).trans hVred.2.1))

theorem Z_le_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (l2Of T H (yOfL22 T M)) :=
  (le_conjClosure _ _).trans (vz_le_pCoreOf_l2 h F)

theorem Z_le_centralizer_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    quasithinOmegaOneCenter T ≤
      Subgroup.centralizer (pCoreOf 2 (l2Of T H (yOfL22 T M)) : Set G) := by
  have h1 : pCoreOf 2 (l2Of T H (yOfL22 T M)) ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_s2_l2 h F)).trans (s2_le_T h)
  exact (quasithinOmegaOneCenter_le_center T).trans
    (inf_le_right.trans (Subgroup.centralizer_le h1))

theorem not_l2_le_normalizer_Z (h : Hyp1421 G T M) (F : Facts1422 T M) :
    ¬ l2Of T H (yOfL22 T M) ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  fun hh => not_y_le_normalizer_Z h F (le_sup_left.trans hh)


end L16

end S1421

end CFSG.Quasithin
