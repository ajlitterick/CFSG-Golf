module

public import CFSG.Sporadic.Schreier.Co1WeightStab

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem exists_plane_decomp
    (w : Vec24) : ∃ u : Fin 12 → Vec24, (∀ k, u k ∈ plane k) ∧
    w = ∑ k, u k := by
  have hw : w ∈ Submodule.span (ZMod 2)
      (Set.range fun p : Fin 12 × Fin 2 => (zM ^ p.2.val) *ᵥ q p.1) := by
    rw [span_q]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hw
  refine ⟨fun k => ∑ e : Fin 2, c (k, e) • ((zM ^ e.val) *ᵥ q k), fun k => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ ?_
    exact zM_pow_mulVec_mem_plane (q_mem_plane k) _
  · rw [← hc, Fintype.sum_prod_type]

theorem plane_decomp_unique
    {u u' : Fin 12 → Vec24} (hu : ∀ k, u k ∈ plane k)
    (hu' : ∀ k, u' k ∈ plane k) (h : ∑ k, u k = ∑ k, u' k) : ∀ k, u k = u' k := by
  choose α β hαβ using fun k => Submodule.mem_span_pair.mp (hu k)
  choose α' β' hαβ' using fun k => Submodule.mem_span_pair.mp (hu' k)
  have hli := linearIndependent_q
  rw [Fintype.linearIndependent_iffₛ] at hli
  have hsum : ∀ (x y : Fin 12 → ZMod 2) (w : Fin 12 → Vec24),
      (∀ k, x k • q k + y k • zM *ᵥ q k = w k) →
      ∑ p : Fin 12 × Fin 2, (fun p => if p.2 = 0 then x p.1 else y p.1) p •
        ((zM ^ p.2.val) *ᵥ q p.1) = ∑ k, w k := by
    intro x y w hw
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_two, ← hw k]
    simp
  have h0 := hli _ _ ((hsum α β u hαβ).trans (h.trans (hsum α' β' u' hαβ').symm))
  intro k
  rw [← hαβ k, ← hαβ' k]
  have h1 := h0 (k, 0)
  have h2 := h0 (k, 1)
  simp only [↓reduceIte, one_ne_zero] at h1 h2
  rw [h1, h2]


end CFSG.Sporadic.Co1Schreier
