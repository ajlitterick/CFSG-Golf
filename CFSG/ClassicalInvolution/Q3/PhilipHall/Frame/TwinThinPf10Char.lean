module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Dec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Loc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem mkQ_embed_mem_true (α : Finset (Fin n)) (hα : α.card = 4) {k : Wr 4} (hk : k ∈ kList) :
    mkQ n (embed (emb α hα) k) ∈ memBar α hα true := ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, rfl⟩

theorem mkQ_embed_mem_false (α : Finset (Fin n)) (hα : α.card = 4) {k : Wr 4}
    (hk : k ∈ kStarList) : mkQ n (embed (emb α hα) k) ∈ memBar α hα false :=
  ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, rfl⟩


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
