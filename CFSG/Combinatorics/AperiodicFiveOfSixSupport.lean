module

public import CFSG.Combinatorics.AperiodicCentralInvolutionSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Cycle

variable {V : Type*} {G : SimpleGraph V} {v : V} (C : G.Walk v v)


end Cycle

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)


include F hr haper in
theorem mem_of_five {q₀ q₁ q₂ q₃ q₄ q₅ : {v : V // col v = false}} (h₀ : q₀ ∈ oppSet G col w)
    (h₁ : q₁ ∈ oppSet G col w) (h₂ : q₂ ∈ oppSet G col w) (h₃ : q₃ ∈ oppSet G col w)
    (h₄ : q₄ ∈ oppSet G col w) (a01 : (pointGraph G col).Adj q₀ q₁)
    (a12 : (pointGraph G col).Adj q₁ q₂) (a23 : (pointGraph G col).Adj q₂ q₃)
    (a34 : (pointGraph G col).Adj q₃ q₄) (a45 : (pointGraph G col).Adj q₄ q₅)
    (a50 : (pointGraph G col).Adj q₅ q₀) (n02 : q₀ ≠ q₂) (n03 : q₀ ≠ q₃) (n13 : q₁ ≠ q₃) :
    q₅ ∈ oppSet G col w := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have d30 : G.dist (q₃ : V) q₀ = 6 := (hd _ _ 3).mp
    (dist_eq_three_of_path F h₃ h₂ h₁ h₀ a23.symm a12.symm a01.symm n13.symm n02.symm)
  have d34 : G.dist (q₃ : V) q₄ = 2 := (hA _ _).mp a34
  have d45 : G.dist (q₄ : V) q₅ = 2 := (hA _ _).mp a45
  have d50 : G.dist (q₅ : V) q₀ = 2 := (hA _ _).mp a50
  have d40 : G.dist (q₄ : V) q₀ = 4 := by
    have h1 := F.moore.conn.dist_triangle (u := (q₃ : V)) (v := (q₄ : V)) (w := (q₀ : V))
    have h2 := F.moore.conn.dist_triangle (u := (q₄ : V)) (v := (q₅ : V)) (w := (q₀ : V))
    omega
  have hnd : [q₃, q₂, q₁, q₀].Nodup := by
    simp [a23.ne.symm, n13.symm, n03.symm, a12.ne.symm, n02.symm, a01.ne.symm]
  obtain ⟨α, β, δ', -, -, -, hαβ, hβδ, hcase⟩ :=
    path_dichotomy F hr haper ⟨h₃, h₂, h₁, h₀, a23.symm, a12.symm, a01.symm, hnd⟩
  obtain ⟨l, hl⟩ : ∃ l, c q₃ q₄ = l := ⟨_, rfl⟩
  have hq₄ : r l q₃ = q₄ := F.r_eq hr h₃ h₄ a34 hl
  have hmem : ∀ {y₁ y₂ : {v : V // col v = false}}, (y₁, y₂) ∈
      {m : {v : V // col v = false} × {v : V // col v = false} |
        q₃ ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
          q₀ ∈ oppSet G col w ∧ (pointGraph G col).Adj q₃ m.1 ∧
          (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 q₀ ∧
          [q₃, m.1, m.2, q₀].Nodup} → y₁ = q₄ → q₅ ∈ oppSet G col w := by
    intro y₁ y₂ hm h1
    obtain ⟨-, -, hy₂, -, -, h12, h20, -⟩ := hm
    rw [h1] at h12
    rw [Subtype.ext (eq_of_mid F.moore d40 d45 d50 ((hA _ _).mp h12) ((hA _ _).mp h20))]
    exact hy₂
  rcases hcase with ⟨hαδ, hset⟩ | ⟨-, e, heα, heβ, hσ, hset⟩
  ·
    rw [hset] at hmem
    rcases fin_three_cases hαβ hβδ hαδ l with rfl | rfl | rfl
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄
    · exact hmem (y₂ := r δ' (r l q₃)) (by simp) hq₄
    · exact hmem (y₂ := r α (r l q₃)) (by simp) hq₄
  ·
    rw [hset] at hmem
    rcases fin_three_cases hαβ heβ.symm heα.symm l with rfl | rfl | rfl
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄
    · exfalso
      rw [hq₄] at hσ
      have h3 := dist_sigmaMap F hr haper h₄
      rw [← hσ] at h3
      have := (hd _ _ 3).mp h3
      omega
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄

end CFSG.Combinatorics.AperiodicOppositeComponents
