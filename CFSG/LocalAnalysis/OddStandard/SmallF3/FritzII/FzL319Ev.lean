module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

abbrev FzUT : Type := UT3 F4c

@[expose] def fzW : F4c := ⟨0, 1⟩

@[expose] def fzE1 : FzUT := ⟨1, 0, 0⟩

@[expose] def fzEW : FzUT := ⟨fzW, 0, 0⟩

@[expose] def fzF1 : FzUT := ⟨0, 1, 0⟩

@[expose] def fzFW : FzUT := ⟨0, fzW, 0⟩

@[ext] structure FzAutD where
  g1 : FzUT
  g2 : FzUT
  g3 : FzUT
  g4 : FzUT

instance : DecidableEq FzAutD := fun d d' =>
  decidable_of_iff (d.g1 = d'.g1 ∧ d.g2 = d'.g2 ∧ d.g3 = d'.g3 ∧ d.g4 = d'.g4)
    (by cases d; cases d'; simp)

@[expose] def fzPw {H : Type*} [Group H] (b : ZMod 2) (g : H) : H := if b = 0 then 1 else g

@[expose] def fzEv (d : FzAutD) (x : FzUT) : FzUT :=
  fzPw x.a.a d.g1 * fzPw x.a.b d.g2 * fzPw x.b.a d.g3 * fzPw x.b.b d.g4 *
    fzPw (x.c + x.a * x.b).a ⁅d.g1, d.g3⁆ * fzPw (x.c + x.a * x.b).b ⁅d.g1, d.g4⁆

@[expose] def fzIdD : FzAutD := ⟨fzE1, fzEW, fzF1, fzFW⟩

theorem fzUT_word (x : FzUT) :
    x = fzPw x.a.a fzE1 * fzPw x.a.b fzEW * fzPw x.b.a fzF1 * fzPw x.b.b fzFW *
      fzPw (x.c + x.a * x.b).a ⁅fzE1, fzF1⁆ * fzPw (x.c + x.a * x.b).b ⁅fzE1, fzFW⁆ := by
  revert x
  decide +kernel

theorem fzEv_id (x : FzUT) : fzEv fzIdD x = x := (fzUT_word x).symm

theorem fzPw_map {H H' : Type*} [Group H] [Group H'] (σ : H →* H') (b : ZMod 2) (g : H) :
    σ (fzPw b g) = fzPw b (σ g) := by
  unfold fzPw
  split_ifs
  · exact map_one σ
  · rfl

theorem fzUT_hom_apply (σ : FzUT →* FzUT) (x : FzUT) :
    σ x = fzEv ⟨σ fzE1, σ fzEW, σ fzF1, σ fzFW⟩ x := by
  conv_lhs => rw [fzUT_word x]
  simp only [map_mul, fzPw_map, map_commutatorElement, fzEv]

@[expose] def fzGens (σ : MulAut FzUT) : FzAutD := ⟨σ fzE1, σ fzEW, σ fzF1, σ fzFW⟩

theorem fzEv_gens (σ : MulAut FzUT) (x : FzUT) : fzEv (fzGens σ) x = σ x :=
  (fzUT_hom_apply σ.toMonoidHom x).symm

@[expose] def FzCheap (d : FzAutD) : Prop :=
  d.g1 ≠ 1 ∧ d.g2 ≠ 1 ∧ d.g3 ≠ 1 ∧ d.g4 ≠ 1 ∧
  d.g1 * d.g1 = 1 ∧ d.g2 * d.g2 = 1 ∧ d.g3 * d.g3 = 1 ∧ d.g4 * d.g4 = 1 ∧
  d.g1 * d.g2 = d.g2 * d.g1 ∧ d.g3 * d.g4 = d.g4 * d.g3 ∧
  ⁅d.g2, d.g3⁆ = ⁅d.g1, d.g4⁆ ∧ ⁅d.g2, d.g4⁆ = ⁅d.g1, d.g3⁆ * ⁅d.g1, d.g4⁆ ∧
  ⁅d.g1, d.g3⁆ ≠ 1

@[expose] def FzHom (d : FzAutD) : Prop := ∀ x y : FzUT, fzEv d (x * y) = fzEv d x * fzEv d y

@[expose] def FzInj (d : FzAutD) : Prop := ∀ x : FzUT, fzEv d x = 1 → x = 1

@[expose] def FzIsAut (d : FzAutD) : Prop := FzCheap d ∧ FzHom d ∧ FzInj d

instance : DecidablePred FzIsAut := fun d => by
  unfold FzIsAut FzCheap FzHom FzInj
  infer_instance


end CFSG.OddStandard.SmallF3.FritzII
