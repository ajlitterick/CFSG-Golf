module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Y

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem mem_normalizer_X' {c : G}
    (hc : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    c ∈ Subgroup.normalizer (conjSub g (piGen π) : Set G) := by
  have hN := S.normal_cent
  have key : ∀ d ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G),
      ∀ x ∈ conjSub g (piGen π), d * x * d⁻¹ ∈ conjSub g (piGen π) := by
    intro d hd x hx
    have h1 : (⟨x, S.le_cent hx⟩ : ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set G))) ∈
        (conjSub g (piGen π)).subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := hx
    exact hN.conj_mem _ h1 ⟨d, hd⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key c hc x
  · intro hx
    have := key c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this

theorem fam_conj_of_cent' {c : G} (hc : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G))
    {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    conjSub c L ∈ fam K (conjSub g (piGen π)) := by
  have hQ := S.Q_eq_pi
  have hL0 : conjSub g⁻¹ L ∈ π := by rw [← hQ]; exact ⟨L, hL, rfl⟩
  have hc0 : g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have := hc
    calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [this]
      _ = z * (g⁻¹ * c * g) := by group
  have h1 := S.conj_pi_of_cent hc0 hL0
  rw [← hQ] at h1
  obtain ⟨M, hM, hMe⟩ := h1
  have : conjSub c L = M := by
    have e : conjSub c L = conjSub g (conjSub (g⁻¹ * c * g) (conjSub g⁻¹ L)) := by
      have e' : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
      rw [← conjSub_mul, ← conjSub_mul, e']
    rw [e, ← hMe, conjSub_conjSub_inv]
  rw [this]; exact hM


end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
