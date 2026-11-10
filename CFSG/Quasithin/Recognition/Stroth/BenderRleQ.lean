module

public import CFSG.Quasithin.Recognition.Stroth.BenderJn
public import CFSG.Quasithin.Recognition.Stroth.BenderOriented
public import CFSG.Quasithin.Background.D15Chief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev zTilde (L1 L2 S : Subgroup G) (q : ℕ) : Subgroup G :=
  omegaOneCenterOf (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))

theorem normalizer_zTilde (L1 L2 S : Subgroup G) (q : ℕ) :
    P1 L1 L2 S ≤ Subgroup.normalizer (zTilde L1 L2 S q : Set G) :=
  (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans <|
    (normalizer_le_normalizer_jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf
        (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S)))

theorem zTilde_le_pCoreOf (L1 L2 S : Subgroup G) (q : ℕ) :
    zTilde L1 L2 S q ≤ Q1 L1 L2 S :=
  (A4.omegaOneCenterOf_le (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))).trans
    (jAtLeast_le (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))

namespace OrientedBenderPair

variable {L1 L2 S : Subgroup G} {q r : ℕ}


private theorem exists_maxElemAbelian_not_le_pCoreOf
    (h : OrientedBenderPair L1 L2 S q r) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q1 L1 L2 S := by
  by_contra hcon
  push Not at hcon
  exact h.j_not_le (by
    rw [thompsonJ]
    exact iSup₂_le fun A hA => hcon A hA)


end OrientedBenderPair

end CFSG.Quasithin.Stroth

end
