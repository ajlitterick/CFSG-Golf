module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentTangent
public import CFSG.LieType.AlgebraicGroups.SplitTorusTwoTorsion
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.CoordinateConjugation
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LieType.AlgebraicGroups.DiagonalSubgroupTorus
public import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv CategoryTheory Subgroup
open scoped CFSG.ConvolutionPoints

section Matrix
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]
  {Z : Subgroup (ModGL τ k)}


omit [IsAlgClosed k] in
theorem isPointClosed_map_conj {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (g : ModGL τ k) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      (Z.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))) := by
  have h := isPointClosed_preimage_mul_mul g⁻¹ g hZ
  have hs : (Z.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k)) =
      (fun x => g⁻¹ * x * g) ⁻¹' (Z : Set (ModGL τ k)) := by
    ext x
    change x ∈ Z.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Z
    rw [Subgroup.mem_map_equiv]
    rfl
  rwa [hs]


end Matrix

section GeneralPower
universe u


end GeneralPower

section Power


end Power

end CFSG.LieType.AlgebraicGroups
