module

public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBridge

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Range

variable {G H : Type*} [Group G] [Group H] {f : G →* H}


end Range

variable {α : RankTwoAmalgam.{0}} {Y Yb : Type} [Group Y] [Group Yb]

section Lift


end Lift

section Transfer

variable {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful)

include hβ hι


end Transfer

section Nbrs


variable {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful)

include hβ hι


end Nbrs

section Orbits

@[expose] def burnsideF46_TwoOrb (c : α.Completion Y) (u : c.Γ) (n : ℕ) : Prop :=
  ∃ q₁ ∈ GPath.nbPaths c.graph u n, ∃ q₂ ∈ GPath.nbPaths c.graph u n,
    GPath.nbPaths c.graph u n = pathOrbit (stv c u) q₁ ∪ pathOrbit (stv c u) q₂ ∧
    Disjoint (pathOrbit (stv c u) q₁) (pathOrbit (stv c u) q₂) ∧
    Nat.card ↥(pathOrbit (stv c u) q₁) = Nat.card ↥(pathOrbit (stv c u) q₂)


end Orbits

section Smul

variable {c : α.Completion Y}

theorem burnsideF46_pathOrbit_smul {u : c.Γ} {n : ℕ} (q : GPath c.graph n) (g : c.G0) :
    pathOrbit (stv c (g • u)) (g • q) = (fun r => g • r) '' pathOrbit (stv c u) q := by
  ext r
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : g⁻¹ * h * g ∈ stv c u := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hh,
        inv_smul_smul]
    refine ⟨(g⁻¹ * h * g) • q, ⟨_, hh', rfl⟩, ?_⟩
    show g • ((g⁻¹ * h * g) • q) = h • g • q
    rw [← GPath.mul_smul', ← GPath.mul_smul']
    congr 1
    group
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    have hh' : g * h * g⁻¹ ∈ stv c (g • u) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp hh]
    refine ⟨g * h * g⁻¹, hh', ?_⟩
    show (g * h * g⁻¹) • g • q = g • h • q
    rw [← GPath.mul_smul', ← GPath.mul_smul']
    congr 1
    group

theorem burnsideF46_nbPaths_smul {u : c.Γ} {n : ℕ} (g : c.G0) :
    GPath.nbPaths c.graph (g • u) n = (fun r => g • r) '' GPath.nbPaths c.graph u n := by
  ext r
  constructor
  · intro hr
    refine ⟨g⁻¹ • r, ?_, ?_⟩
    · have := nbPaths_smul hr g⁻¹
      rwa [inv_smul_smul] at this
    · show g • g⁻¹ • r = r
      rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  · rintro ⟨q, hq, rfl⟩
    exact nbPaths_smul hq g

theorem burnsideF46_twoOrb_smul {u : c.Γ} {n : ℕ} (h : burnsideF46_TwoOrb c u n) (g : c.G0) :
    burnsideF46_TwoOrb c (g • u) n := by
  obtain ⟨q₁, hq₁, q₂, hq₂, hcov, hdisj, hcard⟩ := h
  have hinj : Function.Injective (fun r : GPath c.graph n => g • r) := fun r r' h => by
    have := congrArg (fun t : GPath c.graph n => g⁻¹ • t) h
    simpa [← GPath.mul_smul', GPath.one_smul'] using this
  refine ⟨g • q₁, nbPaths_smul hq₁ g, g • q₂, nbPaths_smul hq₂ g, ?_, ?_, ?_⟩
  · rw [burnsideF46_nbPaths_smul, hcov, Set.image_union, burnsideF46_pathOrbit_smul,
      burnsideF46_pathOrbit_smul]
  · rw [burnsideF46_pathOrbit_smul, burnsideF46_pathOrbit_smul]
    exact (Set.disjoint_image_iff hinj).mpr hdisj
  · rw [burnsideF46_pathOrbit_smul, burnsideF46_pathOrbit_smul,
      Nat.card_image_of_injective hinj, Nat.card_image_of_injective hinj]
    exact hcard

theorem burnsideF46_affLab_smul {u : c.Γ} {lab : ZMod 5 → c.Γ} (A : AffLab c.G0 c.graph u lab)
    (g : c.G0) : AffLab c.G0 c.graph (g • u) (fun i => g • lab i) := by
  refine ⟨fun i j h => A.inj (smul_left_cancel g h), fun i => (GraphAction.adj_smul g u _).mpr
    (A.adj i), fun w hw => ?_, fun h hh => ?_⟩
  · have hw' : c.graph.Adj u (g⁻¹ • w) := by
      have := (GraphAction.adj_smul g⁻¹ (g • u) w).mpr hw
      rwa [inv_smul_smul] at this
    obtain ⟨i, hi⟩ := A.surj _ hw'
    exact ⟨i, by rw [hi, smul_inv_smul]⟩
  · have hh' : (g⁻¹ * h * g) • u = u := by
      rw [mul_smul, mul_smul, hh, inv_smul_smul]
    obtain ⟨αc, βc, hα, hab⟩ := A.aff _ hh'
    refine ⟨αc, βc, hα, fun i => ?_⟩
    show h • g • lab i = g • lab (αc * i + βc)
    rw [← hab i, mul_smul, mul_smul, smul_inv_smul]

theorem burnsideF46_nontriv_smul {u : c.Γ} {n : ℕ}
    (h : ∀ q ∈ GPath.nbPaths c.graph u n,
      ∃ t ∈ (q.stabPath : Subgroup c.G0), ∃ w, c.graph.Adj u w ∧ t • w ≠ w)
    (g : c.G0) {q : GPath c.graph n} (hq : q ∈ GPath.nbPaths c.graph (g • u) n) :
    ∃ t ∈ (q.stabPath : Subgroup c.G0), ∃ w, c.graph.Adj (g • u) w ∧ t • w ≠ w := by
  have hq' : g⁻¹ • q ∈ GPath.nbPaths c.graph u n := by
    have := nbPaths_smul hq g⁻¹
    rwa [inv_smul_smul] at this
  obtain ⟨t, ht, w, hw, htw⟩ := h _ hq'
  have e : q = g • (g⁻¹ • q) := by rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  refine ⟨g * t * g⁻¹, ?_, g • w, (GraphAction.adj_smul g u w).mpr hw, ?_⟩
  · rw [e, GPath.stabPath_smul]
    exact mul_mem_conjSub ht
  · rw [mul_smul, mul_smul, inv_smul_smul]
    exact fun hc => htw (smul_left_cancel g hc)

theorem burnsideF46_card_stabPath_smul {u : c.Γ} {n : ℕ} (k : ℕ)
    (h : ∀ q ∈ GPath.nbPaths c.graph u n, Nat.card (q.stabPath : Subgroup c.G0) = k)
    (g : c.G0) {q : GPath c.graph n} (hq : q ∈ GPath.nbPaths c.graph (g • u) n) :
    Nat.card (q.stabPath : Subgroup c.G0) = k := by
  have hq' : g⁻¹ • q ∈ GPath.nbPaths c.graph u n := by
    have := nbPaths_smul hq g⁻¹
    rwa [inv_smul_smul] at this
  have e : q = g • (g⁻¹ • q) := by rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  rw [e, GPath.stabPath_smul]
  show Nat.card ((g⁻¹ • q).stabPath.map (MulAut.conj g).toMonoidHom) = k
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h _ hq'

end Smul

end CFSG.ASVolI
