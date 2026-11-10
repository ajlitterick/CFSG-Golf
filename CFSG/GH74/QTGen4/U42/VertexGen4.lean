module

public import CFSG.GH74.QTGen4.GL4.Embed
public import CFSG.GH74.QTGen4.U42.VertexGen4B

public section

namespace CFSG.GH74.QTGen4.U42.VertexGen4

open CFSG.Quasithin CFSG.Open


@[expose] def cj {G : Type} [Group G] {L X : Subgroup G} (hN : X ≤ Subgroup.normalizer (L : Set G))
    (g : ↥X) : ↥L →* ↥L where
  toFun l := ⟨(g : G) * l * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN g.2) l).mp l.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])


end CFSG.GH74.QTGen4.U42.VertexGen4

end
