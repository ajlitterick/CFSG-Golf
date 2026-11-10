module

public import CFSG.GH74.GLS.LU.Compat
public import CFSG.GH74.GLS.LU.Final
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.GH74.GLS.LU

open Matrix Subgroup Blueprint Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports

theorem nonempty_mulEquiv_of_lieModel_psl {G G' : Type} [Group G] [Group G'] {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (h : LieModel G StatedLieTag.PSL 4 p f)
    (h' : LieModel G' StatedLieTag.PSL 4 p f) : Nonempty (G ≃* G') := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ {X : Type} [Group X], LieModel X StatedLieTag.PSL 4 p f →
      Nonempty (X ≃* ProjectiveSpecialLinearGroup (Fin 4) (GaloisField p f)) := by
    intro X _ hX
    rcases hX with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 4 p f hf hK)⟩
    · omega
    · omega
    · omega
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  exact ⟨e.trans e'.symm⟩

theorem nonempty_mulEquiv_of_lieModel_psu {G G' : Type} [Group G] [Group G'] {p f : ℕ}
    (h : LieModel G StatedLieTag.PSU 4 p f) (h' : LieModel G' StatedLieTag.PSU 4 p f) :
    Nonempty (G ≃* G') := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · rcases h' with ⟨-, -, K', _, _, hK', ⟨e'⟩⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · let _ : Fintype K := Fintype.ofFinite K
      let _ : Fintype K' := Fintype.ofFinite K'
      have hcard : Fintype.card K = Fintype.card K' := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK']
      let φ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
      let e1 := statedProjCongr (glCongr (ι := Fin 4) φ) (glCongr_statedSU φ 4 (p ^ f))
        (glCongr_statedScalars φ)
      exact ⟨(e.trans e1).trans e'.symm⟩
    · omega
    · omega
    · omega
  · omega
  · omega
  · omega


end CFSG.GH74.GLS.LU
