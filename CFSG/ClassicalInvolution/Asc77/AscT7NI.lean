module

public import CFSG.ClassicalInvolution.Asc77.AscT7NH
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RL

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
@[expose] def C21_14_Y_conn_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W → u ∈ W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        SectionConnected Ω u →
          rLayer Ω u ≤ sigmaGen Ω K ∨ rLayer Ω u ≤ rLayer Ω (t * z)

theorem c21_14_Y_ne_W_of_conn_W (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hc : C21_14_Y_conn_W p f) : C21_14_Y_ne_W p f := by
  intro G _ _ _ Ω K K' z u J t W h huW hα hne
  by_cases hconn : SectionConnected Ω u
  · exact hc G Ω K K' z u J t W h huW hα hne hconn
  · exact ((c21_14_Y_disc_of_hyp51 hHt hHu) G Ω K K' z u J t W h hconn).2 hα

theorem c21_normCent_of_conn_W (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hc : C21_14_Y_conn_W p f) : C21_NormCent p f :=
  c21_normCent_of_Y_ne (c21_3_of_hyp51 hHt hHu) (c21_14_Y_ne_W_of_conn_W hHt hHu hc)


end CFSG.ClassicalInvolution.Asc77
