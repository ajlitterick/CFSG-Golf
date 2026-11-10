module

public import CFSG.ClassicalInvolution.RouteD.PatternB
public import CFSG.ClassicalInvolution.RouteD.PatternD
public import CFSG.ClassicalInvolution.RouteD.PatternExc
public import CFSG.ClassicalInvolution.RouteD.Leaf

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

theorem CharReach.comp_equiv {ι κ : Type} (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {v w : κ → ZMod 2} (h : CharReach N v w) :
    CharReach M (v ∘ e) (w ∘ e) := by
  induction h with
  | refl => exact CharReach.refl' _ _
  | @tail b c _ hs ih =>
    obtain ⟨i, rfl⟩ := hs
    refine ih.trans' ?_
    have : (charRefl N i b) ∘ e = charRefl M (e.symm i) (b ∘ e) := by
      funext x
      simp [charRefl, hMN]
    rw [this]
    exact CharReach.single' _ _

theorem PatternLemma.of_equiv {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ} (hMN : ∀ x y, M x y = N (e x) (e y))
    (h : PatternLemma N) : PatternLemma M := by
  intro v hv
  have hv' : v ∘ e.symm ≠ 0 := by
    intro h0
    apply hv
    funext x
    have := congrFun h0 (e x)
    simpa using this
  obtain ⟨w, hw, j, rfl⟩ := h (v ∘ e.symm) hv'
  refine ⟨Pi.single j 1 ∘ e, ?_, e.symm j, ?_⟩
  · have := CharReach.comp_equiv e hMN hw
    simpa [Function.comp_def] using this
  · funext x
    simp [Pi.single_apply, Equiv.eq_symm_apply]


section Sum


end Sum

end CFSG.ClassicalInvolution.RouteD
