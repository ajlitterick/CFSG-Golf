module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.LargeExtraspecial.S7Perm

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBS3

variable {G : Type} [Group G]


instance pCore_normal_subgroup (L : Subgroup G) : (pCore 2 ↥L).Normal :=
  CFSG.LieType.BorelTits.pCore_normal 2


@[expose] def conjSubHom (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x.1).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem conjSubHom_coe {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((conjSubHom L g hg x : ↥L) : G) = g * x * g⁻¹ := by
  unfold conjSubHom
  rfl


end DSBS3

open DSBS3


end CFSG.GH74.QTGen4.DSGen4
