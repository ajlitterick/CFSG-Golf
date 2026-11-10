module

public import CFSG.Milestones.ASVolI.A3Aut.Case5

public section

namespace CFSG.ASVolI

open CFSG.Open
open scoped Pointwise

section Util


theorem burnsideAut_exists_equiv_sylow {X P : Type} [Group X] [Group P] [Finite P] (e : X ≃* P)
    {Q : Subgroup X} {R : Subgroup P} (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q ⊤)
    (hR : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤) : ∃ e' : X ≃* P, Q.map e'.toMonoidHom = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : CFSG.QuasithinUnique.IsSylowTwoOf (Q.map e.toMonoidHom) ⊤ := by
    have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e (X := Q) (Y := ⊤)).2 hQ
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hQ'
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (h1.toSylow h2) (h3.toSylow h4)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hR' : R = MulAut.conj g • Q.map e.toMonoidHom :=
    (congrArg (fun S : Sylow 2 P => (S : Subgroup P)) hg).symm
  rw [hR']
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨e q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩


end Util

end CFSG.ASVolI
