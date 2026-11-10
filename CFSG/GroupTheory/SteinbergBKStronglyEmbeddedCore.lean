module

public import CFSG.Assembly.OrderReductions.StrongEmbedding
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.SteinbergBK

variable {G : Type*} [Group G]

theorem isStronglyEmbedded_iff (H : Subgroup G) :
    IsStronglyEmbedded H ↔ CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded H := by
  rw [CFSG.OrderReductions.InvolutionGraph.stronglyEmbedded_right_conjugate_iff]
  rfl


end CFSG.GroupTheory.SteinbergBK
