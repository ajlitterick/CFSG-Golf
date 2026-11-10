module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Split

variable {τ : Tag} {K : Type} [Field K]

theorem odd_card_highTorusLine {f : ℕ} (hf : 1 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    Odd (Nat.card (EPilot.highTorusLine τ K)) := by
  have h : Nat.card (EPilot.highTorusLine τ K) ∣ Nat.card Kˣ := card_range_dvd _
  rw [Nat.card_units, hKc] at h
  refine Odd.of_dvd_nat (Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one) h
  exact (Nat.even_pow' (by omega)).2 even_two

theorem commute_of_mem_highTorusLine {x y : ModGL τ K} (hx : x ∈ EPilot.highTorusLine τ K)
    (hy : y ∈ EPilot.highTorusLine τ K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem highTorusLine_subgroupOf_le_centralizer_self :
    (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ≤
      centralizer ((EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy => Subtype.ext
    (commute_of_mem_highTorusLine (Subgroup.mem_subgroupOf.1 hy) (Subgroup.mem_subgroupOf.1 hx))


theorem highTorusLine_le_adjointGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    EPilot.highTorusLine τ K ≤ adjointGroup τ K :=
  (EPilot.highTorusLine_le_highRootSL2 hτ).trans EPilot.highRootSL2_le_adjointGroup

theorem rootDiagUnit_highDiag_mem_adjointGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (c : Kˣ) :
    rootDiagUnit τ (EPilot.highDiag τ c) ∈ adjointGroup τ K :=
  highTorusLine_le_adjointGroup hτ (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c)

theorem highTorusLine_subgroupOf_le_centralizer_perpLevi :
    (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ≤
      centralizer ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy => Subtype.ext
    (EPilot.commute_of_mem_highTorusLine_of_mem_rootSpan (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy)).eq.symm


theorem centralizer_le_highTorusLine_sup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c) {X : Subgroup (adjointGroup τ K)}
    (hcX : (⟨rootDiagUnit τ (EPilot.highDiag τ c), rootDiagUnit_highDiag_mem_adjointGroup hτ c⟩ :
      adjointGroup τ K) ∈ X) :
    centralizer (X : Set (adjointGroup τ K)) ≤
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  intro g hg
  have hgc := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg _ hcX)
  have hm : (g : ModGL τ K) ∈ toralCentralizer τ K (EPilot.highDiag τ c) := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    change rootDiagUnit τ (EPilot.highDiag τ c) * (g : ModGL τ K) = (g : ModGL τ K) *
      rootDiagUnit τ (EPilot.highDiag τ c) at hgc
    rw [hgc, mul_inv_cancel_right]
  rw [(EPilot.toralCentralizer_highDiag_eq_sup hτ (ringChar.eq K 2) hc).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      EPilot.highTorusLine_le_normalizer_perpLevi] at hm
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.1 hm
  have hg' : g = ⟨t, highTorusLine_le_adjointGroup hτ ht⟩ *
      ⟨d, EPilot.rootSpan_le_adjointGroup' _ hd⟩ := Subtype.ext htd.symm
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ht))
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hd))

theorem centralizer_eq_highTorusLine_sup_of_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {c : Kˣ} (hc : 3 ≤ orderOf c) {A : Subgroup (adjointGroup τ K)}
    (hAT : A ≤ (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K))
    (hcA : (⟨rootDiagUnit τ (EPilot.highDiag τ c), rootDiagUnit_highDiag_mem_adjointGroup hτ c⟩ :
      adjointGroup τ K) ∈ A) :
    centralizer (A : Set (adjointGroup τ K)) =
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  refine le_antisymm (centralizer_le_highTorusLine_sup hτ hc hcA) (sup_le (fun x hx => ?_) ?_)
  · exact Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 (highTorusLine_subgroupOf_le_centralizer_self hx) a (hAT ha)
  · rw [← Subgroup.le_centralizer_iff]
    exact hAT.trans highTorusLine_subgroupOf_le_centralizer_perpLevi

theorem centralizer_highTorusLine_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    centralizer ((EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) =
      (EPilot.highTorusLine τ K).subgroupOf (adjointGroup τ K) ⊔
        (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  exact centralizer_eq_highTorusLine_sup_of_le hτ hc le_rfl
    (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c))

end Split


end CFSG.SeitzReduction.E6Pilot
