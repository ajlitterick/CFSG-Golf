module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.SimsE22

open CFSG.Open


section Conjugates

variable {P : Type*} [Group P]

def cj (h : P) (X : Subgroup P) : Subgroup P := X.map (MulAut.conj h).toMonoidHom

theorem mem_cj {h x : P} {X : Subgroup P} : x ∈ cj h X ↔ h⁻¹ * x * h ∈ X := by
  unfold cj
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cj_cj (a b : P) (X : Subgroup P) : cj a (cj b X) = cj (a * b) X := by
  ext x
  simp only [mem_cj, mul_inv_rev, mul_assoc]

theorem cj_one (X : Subgroup P) : cj 1 X = X := by
  ext x
  simp [mem_cj]


abbrev Conjs (X0 : Subgroup P) : Type _ := {X : Subgroup P // ∃ h : P, X = cj h X0}

instance conjsMulAction (X0 : Subgroup P) : MulAction P (Conjs X0) where
  smul a X := ⟨cj a X.1, by
    obtain ⟨h, hX⟩ := X.2
    exact ⟨a * h, by rw [hX, cj_cj]⟩⟩
  one_smul X := Subtype.ext (by
    show cj 1 X.1 = X.1
    exact cj_one _)
  mul_smul a b X := Subtype.ext (by
    show cj (a * b) X.1 = cj a (cj b X.1)
    exact (cj_cj a b X.1).symm)

instance finite_conjs [Finite P] (X0 : Subgroup P) : Finite (Conjs X0) :=
  Finite.of_surjective (fun h : P => (⟨cj h X0, h, rfl⟩ : Conjs X0))
    (fun X => by
      obtain ⟨h, hh⟩ := X.2
      exact ⟨h, Subtype.ext hh.symm⟩)


end Conjugates

section Transport


end Transport


end CFSG.Quasithin.SimsE22
