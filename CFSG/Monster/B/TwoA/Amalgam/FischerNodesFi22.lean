module

public import CFSG.Monster.B.TwoA.Amalgam.FischerSliceNative
public import CFSG.Monster.B.TwoA.Amalgam.ExactOrder
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodesAdj
public import CFSG.Monster.B.TwoA.Fischer.PinnedFi22Main
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.InducedData
import Certificates.Kernel.Sporadic.Fi22.F1BridgeK
import Certificates.Kernel.Sporadic.Fi22.Ext2073
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.Fi22.F1Bridge
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
open CFSG.Monster.B.Fischer (J psi fi22P fi22PermEquiv fi22Theta fi22Graph fi22R fi22U
  fi22U_mem_R fi22OuterZ o tPerm)

theorem native_three_transposition_group_pinned_Fi22_of
    {v w : CVert} (hw : w ∈ sphereThree v)
    (Φ : cgraph.commonNeighbors v w ≃ CFSG.Monster.B.Fischer.Y)
    (hΦ : ∀ a : cnGroup v w, Φ.permCongr (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
      (native_isFischerSlice hw).mapsTo a) ∈ J) :
    ∃ χ : cnGroup v w ≃* fi22P,
      (∀ a : cnGroup v w, (χ a : Equiv.Perm (Fin 3510)) =
        (Φ.trans psi).permCongr (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (native_isFischerSlice hw).mapsTo a)) ∧
      ∃ e : cnGroup v w ≃* CFSG.Blueprint.NativeSporadic.Fi22,
        ∀ a : cnGroup v w, fi22PermEquiv (e a) = χ a :=
  (native_isFischerSlice hw).three_transposition_group_pinned_Fi22 Φ hΦ

section Canonical

open CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2
open scoped IsMulCommutative

theorem permCongr_slicePerm_eq
    {v w : CVert} (hw : w ∈ sphereThree v)
    (Φ : cgraph.commonNeighbors v w ≃ CFSG.Monster.B.Fischer.Y) (ψ : cnGroup v w ≃* J)
    (hψ : ∀ (h : cnGroup v w) (y y' : cgraph.commonNeighbors v w),
      (y' : CVert) = cvPerm (h : Shat) y →
        (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ y) = Φ y')
    (a : cnGroup v w) :
    Φ.permCongr (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
      (native_isFischerSlice hw).mapsTo a) = (ψ a : Equiv.Perm CFSG.Monster.B.Fischer.Y) := by
  refine Equiv.ext fun p => ?_
  rw [Equiv.permCongr_apply]
  have h := hψ a (Φ.symm p) (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
    (native_isFischerSlice hw).mapsTo a (Φ.symm p)) (slicePerm_apply _ _ _ _ _ _)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem native_exists_pinned_Fi22_inputs
    {v w : CVert} (hw : w ∈ sphereThree v) :
    ∃ Φ : cgraph.commonNeighbors v w ≃ CFSG.Monster.B.Fischer.Y,
      (∀ a : cnGroup v w, Φ.permCongr (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
        (native_isFischerSlice hw).mapsTo a) ∈ J) ∧
      ∃ (x : CVert) (hx : x ∈ cgraph.commonNeighbors v w), Φ ⟨x, hx⟩ = o ∧
        Φ.permCongr (slicePerm cvPerm clabelS (cgraph.commonNeighbors v w)
          (native_isFischerSlice hw).mapsTo ⟨clabelS x, lab_mem_sliceGroup hx⟩) = tPerm := by
  have h := (native_isFischerSlice hw).exists_canonical_identification
  obtain ⟨Φ, ψ, hψ, x, hx, hxo, hxT⟩ := h
  refine ⟨Φ, fun a => ?_, x, hx, hxo, (permCongr_slicePerm_eq hw Φ ψ hψ _).trans hxT⟩
  rw [permCongr_slicePerm_eq hw Φ ψ hψ]
  exact (ψ a).2

theorem native_three_transposition_group_nonempty_mulEquiv_Fi22
    {v w : CVert}
    (hw : w ∈ sphereThree v) : Nonempty (cnGroup v w ≃* CFSG.Blueprint.NativeSporadic.Fi22) := by
  obtain ⟨Φ, hΦ, _⟩ := native_exists_pinned_Fi22_inputs hw
  obtain ⟨_, _, e, _⟩ := native_three_transposition_group_pinned_Fi22_of hw Φ hΦ
  exact ⟨e⟩

end Canonical

end CFSG.Monster.B.TwoA.Amalgam
