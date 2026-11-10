module

public import CFSG.ClassicalInvolution.RouteD.TWT4Hbad
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT6

section Statement

variable (p f : ℕ) [Fact p.Prime]


end Statement

section Conj

variable {G : Type} [Group G]

theorem isTwinAt_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K T : Subgroup G} {z : G}
    (h : IsTwinAt Ω K T z) (g : G) :
    IsTwinAt Ω (conjSub g K) (conjSub g T) (g * z * g⁻¹) where
  mem := by
    rw [centralizingMembers_conj hΩ g z]
    exact ⟨T, h.mem, rfl⟩
  ne := fun hEq => h.ne (conjSub_injective g hEq)
  comm_T := by
    intro N hN hNT
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_T N₀ hN₀ fun hEq => hNT (by rw [hEq]))
  comm_K := by
    intro N hN hNK
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_K N₀ hN₀ fun hEq => hNK (by rw [hEq]))

end Conj

section Reduction


end Reduction

end CFSG.ClassicalInvolution.RouteD.TWT6
