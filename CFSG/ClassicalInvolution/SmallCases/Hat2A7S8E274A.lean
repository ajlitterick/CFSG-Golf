module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

namespace Asc77


namespace T8


end T8

end Asc77

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Local
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


end Local
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


end Main
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Coset
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem fixesUniqueCoset_z {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset z (H274 Ω K z) :=
  Q3.Q3CL.Frame.T8.fixesUniqueCoset_z hs.toFrame hcomp
end Coset
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Fuse


end Fuse
end T8
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
