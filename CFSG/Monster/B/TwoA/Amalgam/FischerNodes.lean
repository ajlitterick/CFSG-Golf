module

public import CFSG.Monster.B.TwoA.Amalgam.FischerSliceNative
public import CFSG.Monster.B.TwoA.Fischer.AffineCayley
public import CFSG.Monster.B.TwoA.Fischer.SliceSimple
public import CFSG.Monster.B.TwoA.Fischer.CliqueM22
public import CFSG.Monster.B.TwoA.Fischer.SplitAffineM22Main

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
open scoped IsMulCommutative

section Slice

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem native_Fischer_maximal_clique_stabilizer_kernel :
    ∀ v w : CVert, w ∈ sphereThree v →
    (∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      (Subtype.val '' D).ncard = 22) ∧
    (∀ (u u' : CVert) (D D' : Set (cgraph.commonNeighbors v w)),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D → u ∈ Subtype.val '' D →
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D' → u' ∈ Subtype.val '' D' →
      ∃ a ∈ cnGroup v w, cvPerm a u = u' ∧ cvPerm a '' (Subtype.val '' D) = Subtype.val '' D') ∧
    ∀ D : Set (cgraph.commonNeighbors v w),
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D →
      (∀ x ∈ (Subtype.val '' D), ∀ y ∈ (Subtype.val '' D), ∃ a ∈ setStab cvPerm clabelS
          (cgraph.commonNeighbors v w) (Subtype.val '' D), cvPerm a x = y) ∧
      Nat.card (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)).range = 443520 ∧
      ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) = Subgroup.closure
          (clabelS '' (Subtype.val '' D)) ∧
      CFSG.IsElementaryAbelian 2 (ptStab cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)) ∧
      Nat.card (ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)) = 2 ^ 10 ∧
      Nat.card (setStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D))
          = 454164480 ∧
      11 ∣ Nat.card (setStabPerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (Subtype.val '' D)).range ∧
      ∀ u ∈ (Subtype.val '' D), ∀ L : LocalChart cvPerm clabelS (cgraph.commonNeighbors v w) u,
        ∃ W : Submodule F4 UnitarySix.V, IsMaxIso W ∧
          L.τ '' {z | (z : CVert) ∈ (Subtype.val '' D)} = planePts W ∧
          ((ptStab cvPerm clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D)).subgroupOf
              (sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u)).map L.φ = kerL W ∧
          Subgroup.zpowers (clabelS u) ≤ ptStab cvPerm clabelS (cgraph.commonNeighbors v w)
              (Subtype.val '' D) ∧
          ∀ a : sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u, (a : Shat) ∈ ptStab cvPerm
              clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) →
            (L.φ a = 1 ↔ (a : Shat) ∈ Subgroup.zpowers (clabelS u)) := by
  intro v w hw
  obtain ⟨h1, h2, h3⟩ := (native_isFischerSlice hw).maximal_clique_stabilizer_kernel
  exact ⟨fun D hD => h1 _ ((isSliceMaxClique_image_iff hw D).2 hD),
    fun u u' D D' hD hu hD' hu' => h2 u u' _ _ ((isSliceMaxClique_image_iff hw D).2 hD) hu
      ((isSliceMaxClique_image_iff hw D').2 hD') hu',
    fun D hD => h3 _ ((isSliceMaxClique_image_iff hw D).2 hD)⟩


theorem native_three_transposition_group_simple :
    ∀ v w : CVert, w ∈ sphereThree v →
    IsSimpleGroup (cnGroup v w) ∧ ¬ IsMulCommutative (cnGroup v w) ∧
    Nat.card (cnGroup v w) = 64561751654400 ∧
    commutator (cnGroup v w) = ⊤ ∧
    (∃ D : ConjClasses (cnGroup v w),
      D.carrier = {g : cnGroup v w | (g : Shat) ∈ clabelS '' (cgraph.commonNeighbors v w)}) ∧
    (clabelS '' (cgraph.commonNeighbors v w)).ncard = 3510 ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), orderOf (clabelS y) = 2) ∧
    Subgroup.closure {g : cnGroup v w | (g : Shat) ∈ clabelS '' (cgraph.commonNeighbors v w)} = ⊤ ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), ∀ z ∈ (cgraph.commonNeighbors v w),
        orderOf (clabelS y * clabelS z) ∈ ({1, 2, 3} : Finset ℕ)) ∧
    (∀ y ∈ (cgraph.commonNeighbors v w), ∀ z ∈ (cgraph.commonNeighbors v w), y ≠ z →
        (orderOf (clabelS y * clabelS z) = 2 ↔
          (sliceGraph clabelS (cgraph.commonNeighbors v w)).Adj y z)) ∧
    ∀ [Fintype (cgraph.commonNeighbors v w)] [DecidableRel
        ((sliceGraph clabelS (cgraph.commonNeighbors v w)).induce
            (cgraph.commonNeighbors v w)).Adj],
      ((sliceGraph clabelS (cgraph.commonNeighbors v w)).induce
          (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126 :=
  fun _ _ hw => (native_isFischerSlice hw).simple

end Slice

section M22

open CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22


end M22

end CFSG.Monster.B.TwoA.Amalgam
