module

public import CFSG.Monster.B.TwoA.Amalgam.Flag2Map

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.ThreePlane
  CFSG.Monster.B.TwoA.Unitary.LinThree
open scoped Pointwise

attribute [local instance] vAction

theorem exists_quotient_equiv {G X : Type*} [Group G] (H : Subgroup G) (f : G → X)
    (hf : ∀ g h, f g = f h ↔ g⁻¹ * h ∈ H) (hs : Function.Surjective f) :
    ∃ e : G ⧸ H ≃ X, ∀ g, e (QuotientGroup.mk g) = f g := by
  refine ⟨Equiv.ofBijective (Quotient.lift f fun a b hab =>
    (hf a b).2 (QuotientGroup.leftRel_apply.1 hab)) ⟨?_, ?_⟩, fun g => rfl⟩
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 ((hf a b).1 hxy)
  · intro x
    obtain ⟨g, rfl⟩ := hs x
    exact ⟨QuotientGroup.mk g, rfl⟩


theorem fst_eq_iff
    (g h : Pc 1) :
    (piTwo g).1 vX = (piTwo h).1 vX ↔ g⁻¹ * h ∈ (Pc 0).subgroupOf (Pc 1) := by
  rw [Pc_zero_subgroupOf, Subgroup.mem_comap, Subgroup.mem_prod, MulAction.mem_stabilizer_iff,
    map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, mul_smul, inv_smul_eq_iff]
  exact ⟨fun e => ⟨e.symm, Subgroup.mem_top _⟩, fun e => e.1.symm⟩

theorem snd_pt_eq_iff
    (g h : Pc 1) :
    (piTwo g).2 • pPt = (piTwo h).2 • pPt ↔ g⁻¹ * h ∈ (Pc 2).subgroupOf (Pc 1) := by
  rw [Pc_two_subgroupOf_Pc_one, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, mul_smul,
    inv_smul_eq_iff]
  exact ⟨fun e => ⟨Subgroup.mem_top _, e.symm⟩, fun e => e.2.symm⟩

theorem snd_ln_eq_iff
    (g h : Pc 1) :
    (piTwo g).2 • ellLine = (piTwo h).2 • ellLine ↔ g⁻¹ * h ∈ (Pc 3).subgroupOf (Pc 1) := by
  rw [Pc_three_subgroupOf_Pc_one, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, mul_smul,
    inv_smul_eq_iff]
  exact ⟨fun e => ⟨Subgroup.mem_top _, e.symm⟩, fun e => e.2.symm⟩

theorem exists_piTwo
    (σ : Equiv.Perm Vsharp) (s : SigmaL3) : ∃ g : Pc 1, piTwo g = (σ, s) :=
  piTwo_surjective (σ, s)

theorem exists_fst_eq
    (v : Vsharp) : ∃ g : Pc 1, (piTwo g).1 vX = v := by
  classical
  obtain ⟨g, hg⟩ := exists_piTwo (Equiv.swap vX v) 1
  exact ⟨g, by rw [hg]; exact Equiv.swap_apply_left vX v⟩


theorem exists_snd_ln_eq
    {S : Set PlanePoint} (hS : S ∈ planeLines) :
    ∃ g : Pc 1, (piTwo g).2 • ellLine = S := by
  obtain ⟨s, hs⟩ := exists_smul_ellLine hS
  obtain ⟨g, hg⟩ := exists_piTwo 1 s
  exact ⟨g, by rw [hg]; exact hs⟩

theorem exists_equiv_vsharp :
    ∃ e : Pc 1 ⧸ (Pc 0).subgroupOf (Pc 1) ≃ Vsharp,
    ∀ g, e (QuotientGroup.mk g) = (piTwo g).1 vX :=
  exists_quotient_equiv _ (fun g => (piTwo g).1 vX) fst_eq_iff exists_fst_eq


theorem exists_equiv_lines :
    ∃ e : Pc 1 ⧸ (Pc 3).subgroupOf (Pc 1) ≃ planeLines,
    ∀ g, (e (QuotientGroup.mk g) : Set PlanePoint) = (piTwo g).2 • ellLine := by
  obtain ⟨e, he⟩ := exists_quotient_equiv ((Pc 3).subgroupOf (Pc 1))
    (fun g => (⟨(piTwo g).2 • ellLine, smul_mem_planeLines _ ellLine_mem_planeLines⟩ :
      planeLines))
    (fun g h => Subtype.ext_iff.trans (snd_ln_eq_iff g h))
    (fun S => by
      obtain ⟨g, hg⟩ := exists_snd_ln_eq S.2
      exact ⟨g, Subtype.ext hg⟩)
  exact ⟨e, fun g => congrArg Subtype.val (he g)⟩


theorem exists_flag
    (v : Vsharp) {x : PlanePoint} {S : Set PlanePoint} (hS : S ∈ planeLines)
    (hx : x ∈ S) : ∃ g : Pc 1, (piTwo g).1 vX = v ∧ (piTwo g).2 • pPt = x ∧
      (piTwo g).2 • ellLine = S := by
  classical
  obtain ⟨s, hs1, hs2⟩ := exists_smul_flag hS hx
  obtain ⟨g, hg⟩ := exists_piTwo (Equiv.swap vX v) s
  refine ⟨g, ?_, ?_, ?_⟩ <;> rw [hg]
  · exact Equiv.swap_apply_left vX v
  · exact hs1
  · exact hs2


end CFSG.Monster.B.TwoA.Amalgam
