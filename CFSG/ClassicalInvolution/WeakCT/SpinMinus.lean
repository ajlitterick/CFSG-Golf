module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinLevi
public import CFSG.ClassicalInvolution.WeakCT.TwistedTorus

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

theorem rootedTree_edgeUp_last {m : ℕ} (hm : 0 < m) :
    RootedTree (edgeUp m) (parentDown m) (depthDown m) ⟨m - 1, by omega⟩ := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 : k.val ≠ m - 1 := fun h => hk (Fin.ext h)
    have h2 := k.2
    simp only [parentDown, depthDown]
    omega
  · have h1 : k.val ≠ m - 1 := fun h => hk (Fin.ext h)
    have h2 := k.2
    right
    simp only [edgeUp, parentDown]
    omega
  · simp only [edgeUp] at hij hji
    omega
  · simp only [edgeUp] at hij
    have h2 := j.2
    right
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [parentDown]
      omega


end CFSG.ClassicalInvolution.WeakCT
