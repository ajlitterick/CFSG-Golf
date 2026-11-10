module

public import CFSG.Combinatorics.AperiodicCentralInvolutionSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Defs

variable {V : Type*}

open scoped Classical in
noncomputable def sibling (G : SimpleGraph V) (col : G.Coloring Bool)
    (w t : {v : V // col v = false}) : {v : V // col v = false} :=
  if h : ∃ t', (pointGraph G col).dist w t' = 2 ∧ (pointGraph G col).Adj t t' then
    Classical.choose h else t

noncomputable def ptMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w x : {v : V // col v = false}) : {v : V // col v = false} :=
  if (pointGraph G col).dist w x = 3 then sigmaMap G col w x
  else if (pointGraph G col).dist w x = 2 then sibling G col w x else x

open scoped Classical in
noncomputable def lineMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (m : V) : V :=
  if h : ∃ m', col m' = true ∧ ∀ u : {v : V // col v = false}, G.Adj (u : V) m →
      G.Adj (ptMap G col w u : V) m' then Classical.choose h else m


end Defs

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


include F in
theorem line_eq_of_two {u v m m' : V} (huv : u ≠ v) (hu : col u = false) (hv : col v = false)
    (hum : G.Adj u m) (hvm : G.Adj v m) (hum' : G.Adj u m') (hvm' : G.Adj v m') : m = m' :=
  pred_unique F.moore.cyc F.moore.conn (k := 1) (by norm_num)
    (show G.dist u v = 1 + 1 from dist_eq_two_of_adj_adj F.moore.conn col huv (hu.trans hv.symm)
      hum hvm) hvm hvm' (SimpleGraph.dist_eq_one_iff_adj.mpr hum)
    (SimpleGraph.dist_eq_one_iff_adj.mpr hum')


end CFSG.Combinatorics.AperiodicOppositeComponents
