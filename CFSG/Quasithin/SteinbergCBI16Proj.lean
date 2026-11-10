module

public import CFSG.Quasithin.SteinbergCBI16Alt5

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Trace

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [Fintype G] {W : Type*}
  [AddCommGroup W] [Module k W]


end Trace

theorem trace5 : ∀ c < 2 ^ 4, ∑ σ : ↥(alternatingGroup (Fin 5)),
    coords5.actA σ⁻¹ (toV 4 c) 0 • coords5.actA σ (Pi.single 0 1) = toV 4 c := by
  decide +kernel


end CFSG.Quasithin.SteinbergCB.I16
