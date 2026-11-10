module

public import CFSG.Quasithin.Vol2.KGFactJ4Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocMain
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QTRankInvProof

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem burnsideC31_conj_comp_conj_inv (g : J) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id J := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideC31_conj_inv_comp_conj (g : J) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id J := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideC31_kw_parabolic
    {P : Subgroup J} (hP : IsPGroup 2 ↥P) (hne : P ≠ ⊥) (g : J)
    (hg : P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (P : Set J)) :
    Subgroup.normalizer (P : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J)).map
          (MulAut.conj g).toMonoidHom := by
  set P' : Subgroup J := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
  have hP' : IsPGroup 2 ↥P' := hP.map _
  have hne' : P' ≠ ⊥ := by
    intro h
    apply hne
    have h2 := congrArg (fun K : Subgroup J => K.map (MulAut.conj g).toMonoidHom) h
    simp only [hP'def, Subgroup.map_map, burnsideC31_conj_comp_conj_inv, Subgroup.map_id,
      Subgroup.map_bot] at h2
    exact h2
  have hN' : Subgroup.normalizer (P' : Set J) =
      (Subgroup.normalizer (P : Set J)).map (MulAut.conj g⁻¹).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)).symm
  have hNP : Subgroup.normalizer (P : Set J) =
      (Subgroup.normalizer (P' : Set J)).map (MulAut.conj g).toMonoidHom := by
    rw [hN', Subgroup.map_map, burnsideC31_conj_comp_conj_inv, Subgroup.map_id]
  have hP0 : P0 ≤ Subgroup.normalizer (P' : Set J) := by
    rw [hN']
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rwa [Subgroup.map_map, burnsideC31_conj_inv_comp_conj, Subgroup.map_id] at h1
  rw [hNP]
  rcases CFSG.Quasithin.J4Loc.j4TwoLocalOvergroups P' hP' hne' hP0 with h1 | h1 | h1
  · exact Or.inl (Subgroup.map_mono h1)
  · exact Or.inr (Or.inl (Subgroup.map_mono h1))
  · exact Or.inr (Or.inr (Subgroup.map_mono h1))


end CFSG.ASVolI
