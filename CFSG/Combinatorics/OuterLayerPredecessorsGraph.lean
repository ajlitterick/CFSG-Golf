module

public import CFSG.Combinatorics.OuterLayerPredecessorsSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

section General


end General

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}}

theorem existsUnique_pred (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = i) :
    ∃! s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
      (pointGraph G col).Adj x s := by
  obtain ⟨m, xm, hmchar, ⟨a, t, hN, ha, ht, -⟩, -⟩ := inner_layer_lines H col w hi x hx
  have ham : G.Adj (a : V) m :=
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hxa : (x : V) ≠ a := fun e => by
    rw [Subtype.ext e] at hx
    omega
  refine ⟨a, ⟨ha, (point_adj_iff H.conn col x a).mpr
    (dist_eq_two_of_adj_adj H.conn col hxa (x.2.trans a.2.symm) xm ham)⟩, fun s ⟨hs, hxs⟩ => ?_⟩
  obtain ⟨n, xn, sn⟩ :=
    exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col x s).mp hxs)
  have hnm : n = m := (hmchar n xn).mp ⟨s, sn, hs⟩
  rw [hnm] at sn
  have hsN : (s : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr sn.symm
  rw [hN] at hsN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsN
  rcases hsN with h | h | h
  · exact absurd (Subtype.ext h).symm hxs.ne
  · exact Subtype.ext h
  · rw [Subtype.ext h] at hs
    omega

theorem outerRelGraph_adj_iff (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}} :
    (outerRelGraph G col w i).Adj x y ↔ x ≠ y ∧ ∃ s : {v : V // col v = false},
      (pointGraph G col).dist w s = i - 1 ∧ (pointGraph G col).Adj x s ∧
      (pointGraph G col).Adj y s ∧ ∀ m m' : V, G.Adj ((x : {v : V // col v = false}) : V) m →
        G.Adj (s : V) m → G.Adj ((y : {v : V // col v = false}) : V) m' → G.Adj (s : V) m' →
          m ≠ m' := by
  have hne : ∀ {a b : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}},
      a ≠ b → (a : {v : V // col v = false}) ≠ b := fun h e => h (Subtype.ext e)
  rw [outerRelGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, hR | hR⟩
    · exact ⟨hxy, exists_pred_of_outerRel H hi x.2 y.2 (hne hxy) hR⟩
    · obtain ⟨s, hs, hys, hxs, hl⟩ := exists_pred_of_outerRel H hi y.2 x.2 (hne hxy.symm) hR
      exact ⟨hxy, s, hs, hxs, hys, fun m m' xm sm ym' sm' => (hl m' m ym' sm' xm sm).symm⟩
  · rintro ⟨hxy, s, hs, hxs, hys, hl⟩
    exact ⟨hxy, Or.inl (outerRel_of_pred H hi x.2 y.2 hs hxs hys hl)⟩


theorem exists_outward_point (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {s : {v : V // col v = false}} (hs : (pointGraph G col).dist w s = i - 1) (m : V) :
    ∃ (z : {v : V // col v = false}) (L : V), (pointGraph G col).dist w z = i ∧
      (pointGraph G col).Adj z s ∧ G.Adj (z : V) L ∧ G.Adj (s : V) L ∧ L ≠ m := by
  have hd := point_dist_eq_iff H.conn col
  have hs' : G.dist (w : V) s = 2 * (i - 1) := (hd w s _).mp hs
  obtain ⟨b, c, hbc, hsb, hsc, hb, hc⟩ : ∃ b c : V, b ≠ c ∧ G.Adj (s : V) b ∧
      G.Adj (s : V) c ∧ G.dist (w : V) b = G.dist (w : V) s + 1 ∧
        G.dist (w : V) c = G.dist (w : V) s + 1 := by
    rcases hi with rfl | rfl
    · have hsw : (w : V) = s := H.conn.dist_eq_zero_iff.mp (by omega)
      obtain ⟨b, c, d, hbc, -, -, hN⟩ := Finset.card_eq_three.mp
        (show (G.neighborFinset (s : V)).card = 3 by
          rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg])
      have hsb : G.Adj (s : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      have hsc : G.Adj (s : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      refine ⟨b, c, hbc, hsb, hsc, ?_, ?_⟩
      · rw [hsw, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hsb]
      · rw [hsw, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hsc]
    · obtain ⟨a, b, c, hN, -, hb, hc, hbc⟩ := nbr_structure H col (k := 1) (by norm_num)
        (by omega : G.dist (w : V) s = 1 + 1)
      have hsb : G.Adj (s : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      have hsc : G.Adj (s : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      exact ⟨b, c, hbc, hsb, hsc, by omega, by omega⟩
  obtain ⟨L, hsL, hL, hLm⟩ : ∃ L : V, G.Adj (s : V) L ∧
      G.dist (w : V) L = G.dist (w : V) s + 1 ∧ L ≠ m := by
    by_cases hbm : b = m
    · exact ⟨c, hsc, hc, fun h => hbc (hbm.trans h.symm)⟩
    · exact ⟨b, hsb, hb, hbm⟩
  obtain ⟨z, _, hNL, -, hz, -⟩ :=
    nbrs_of_pred H col (k := G.dist (w : V) s) (by omega) hL hsL rfl
  have hzL : G.Adj z L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  have hzcol : col z = false := col_eq_false_of_adj col (col_eq_true_of_adj col s.2 hsL) hzL
  refine ⟨⟨z, hzcol⟩, L, (hd w _ i).mpr (show G.dist (w : V) z = 2 * i by omega), ?_, hzL, hsL,
    hLm⟩
  refine (point_adj_iff H.conn col _ s).mpr (dist_eq_two_of_adj_adj H.conn col (fun e => ?_)
    (hzcol.trans s.2.symm) hzL hsL)
  have e' : z = (s : V) := e
  rw [e'] at hz
  omega

theorem outerRelGraph_components (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ∃ e : (outerRelGraph G col w i).ConnectedComponent ≃
        {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1},
      (∀ x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i},
        (pointGraph G col).Adj (x : {v : V // col v = false})
          (e ((outerRelGraph G col w i).connectedComponentMk x))) ∧
      ∀ x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}, x ≠ y →
        (outerRelGraph G col w i).connectedComponentMk x =
          (outerRelGraph G col w i).connectedComponentMk y →
        (¬ (outerRelGraph G col w i).Adj x y ↔ ∃ m : V, ¬ IsOuterLine G col w i m ∧
          G.neighborFinset m = {((e ((outerRelGraph G col w i).connectedComponentMk x) :
            {v : V // col v = false}) : V), ((x : {v : V // col v = false}) : V),
            ((y : {v : V // col v = false}) : V)}) := by
  have hu := fun x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} =>
    existsUnique_pred H hi x.2
  choose pr hpr using fun x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} =>
    (hu x).exists
  have hπ : ∀ (x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i})
      (t : {v : V // col v = false}), (pointGraph G col).dist w t = i - 1 →
      (pointGraph G col).Adj (x : {v : V // col v = false}) t → t = pr x :=
    fun x t ht hxt => (hu x).unique ⟨ht, hxt⟩ (hpr x)
  let π : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} →
      {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1} :=
    fun x => ⟨pr x, (hpr x).1⟩
  have hadjπ : ∀ x y, (outerRelGraph G col w i).Adj x y → π x = π y := by
    intro x y hxy
    obtain ⟨-, t, ht, hxt, hyt, -⟩ := (outerRelGraph_adj_iff H hi).mp hxy
    exact Subtype.ext ((hπ x t ht hxt).symm.trans (hπ y t ht hyt))
  have hwalkπ : ∀ x y (p : (outerRelGraph G col w i).Walk x y), π x = π y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadjπ _ _ h).trans ih
  let e₀ : (outerRelGraph G col w i).ConnectedComponent →
      {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1} :=
    SimpleGraph.ConnectedComponent.lift π fun x y p _ => hwalkπ x y p
  have hline : ∀ (a b : {v : V // col v = false}), (pointGraph G col).Adj a b → ∀ m m' : V,
      G.Adj (a : V) m → G.Adj (b : V) m → G.Adj (a : V) m' → G.Adj (b : V) m' → m = m' :=
    fun a b hab m m' h1 h2 h3 h4 =>
      (exists_unique_common_line H col hab).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have hcol : ∀ x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}, x ≠ y →
      pr x = pr y → ¬ (outerRelGraph G col w i).Adj x y → ∀ mx : V,
      G.Adj ((x : {v : V // col v = false}) : V) mx → G.Adj (pr x : V) mx →
        G.Adj ((y : {v : V // col v = false}) : V) mx := by
    intro x y hxy hpp hn mx xmx smx
    by_contra hym
    apply hn
    refine (outerRelGraph_adj_iff H hi).mpr ⟨hxy, pr x, (hpr x).1, (hpr x).2,
      by rw [hpp]; exact (hpr y).2, fun m m' h1 h2 h3 h4 hmm => hym ?_⟩
    rw [← hmm, hline _ _ (hpr x).2 m mx h1 h2 xmx smx] at h3
    exact h3
  have hinj : Function.Injective e₀ := by
    intro C D
    induction C, D using SimpleGraph.ConnectedComponent.ind₂ with
    | h x y => ?_
    intro hxy
    have hpp : pr x = pr y := congrArg Subtype.val hxy
    apply SimpleGraph.ConnectedComponent.sound
    by_cases hxy' : x = y
    · rw [hxy']
    by_cases hadj : (outerRelGraph G col w i).Adj x y
    · exact hadj.reachable
    obtain ⟨mx, xmx, smx⟩ :=
      exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col _ _).mp (hpr x).2)
    have hymx := hcol x y hxy' hpp hadj mx xmx smx
    have hys : (pointGraph G col).Adj (y : {v : V // col v = false}) (pr x) := by
      rw [hpp]
      exact (hpr y).2
    obtain ⟨z, L, hz, hzs, hzL, hsL, hLm⟩ := exists_outward_point H hi (hpr x).1 mx
    have key : ∀ u : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i},
        (pointGraph G col).Adj (u : {v : V // col v = false}) (pr x) →
        G.Adj ((u : {v : V // col v = false}) : V) mx →
          (outerRelGraph G col w i).Adj u ⟨z, hz⟩ := by
      intro u hus hum
      have hl : ∀ m m' : V, G.Adj ((u : {v : V // col v = false}) : V) m → G.Adj (pr x : V) m →
          G.Adj (z : V) m' → G.Adj (pr x : V) m' → m ≠ m' := fun m m' h1 h2 h3 h4 hmm =>
        hLm ((hline z (pr x) hzs m' L h3 h4 hzL hsL).symm.trans
          (hmm.symm.trans (hline _ _ hus m mx h1 h2 hum smx)))
      refine (outerRelGraph_adj_iff H hi).mpr ⟨fun hu => hl L L ?_ hsL hzL hsL rfl,
        pr x, (hpr x).1, hus, hzs, hl⟩
      rw [hu]
      exact hzL
    exact (key x (hpr x).2 xmx).reachable.trans (key y hys hymx).reachable.symm
  have hsurj : Function.Surjective e₀ := by
    intro s
    obtain ⟨z, -, hz, hzs, -⟩ := exists_outward_point H hi s.2 (s : V)
    exact ⟨(outerRelGraph G col w i).connectedComponentMk ⟨z, hz⟩,
      Subtype.ext (hπ ⟨z, hz⟩ s s.2 hzs).symm⟩
  refine ⟨Equiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun x => (hpr x).2, fun x y hxy hcc => ?_⟩
  have hpp : pr x = pr y := congrArg Subtype.val (congrArg e₀ hcc)
  have hys : (pointGraph G col).Adj (y : {v : V // col v = false}) (pr x) := by
    rw [hpp]
    exact (hpr y).2
  show ¬ (outerRelGraph G col w i).Adj x y ↔ ∃ m : V, ¬ IsOuterLine G col w i m ∧
    G.neighborFinset m = {(pr x : V), ((x : {v : V // col v = false}) : V),
      ((y : {v : V // col v = false}) : V)}
  constructor
  · intro hn
    obtain ⟨mx, xmx, smx⟩ :=
      exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col _ _).mp (hpr x).2)
    have hymx := hcol x y hxy hpp hn mx xmx smx
    refine ⟨mx, fun h => ?_, neighborFinset_eq H smx xmx hymx
      (fun h => (hpr x).2.ne (Subtype.ext h).symm) (fun h => hys.ne (Subtype.ext h).symm)
      (fun h => hxy (Subtype.ext (Subtype.ext h)))⟩
    have h1 := h.2 (pr x) smx
    have h2 := (hpr x).1
    omega
  · rintro ⟨m, -, hN⟩ hadj
    have hmem : ∀ {u : V}, u ∈ ({(pr x : V), ((x : {v : V // col v = false}) : V),
        ((y : {v : V // col v = false}) : V)} : Finset V) → G.Adj u m := fun hu =>
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; exact hu)).symm
    obtain ⟨-, t, ht, hxt, -, hl⟩ := (outerRelGraph_adj_iff H hi).mp hadj
    rw [hπ x t ht hxt] at hl
    exact hl m m (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) rfl

end CFSG.Combinatorics.OuterLayer
