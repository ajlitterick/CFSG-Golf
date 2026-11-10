module

public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.ClassicalInvolution.Q3.Q3YSInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open Matrix CFSG.LieType.SteinbergBR.EvenSp CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic

section Planes

variable {K : Type} [Field K]


@[expose] noncomputable def spPlane (n : ℕ) :
    (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) →* StatedSp n K :=
  MonoidHom.codRestrict
    ((planeHom (K := K) (n := n)).comp
      (MonoidHom.compLeft Matrix.SpecialLinearGroup.toGL (Fin n)))
    (StatedSp n K) (fun g => planeHom_mem_statedSp _ (fun j => by
      simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]))

theorem spPlane_val (n : ℕ) (g : Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :
    (((spPlane n g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      planeMat fun j => (g j : Matrix (Fin 2) (Fin 2) K) := rfl

theorem spPlane_injective (n : ℕ) : Function.Injective (spPlane (K := K) n) := by
  intro g g' h
  have h1 : planeHom (fun j => Matrix.SpecialLinearGroup.toGL (g j)) =
      planeHom (fun j => Matrix.SpecialLinearGroup.toGL (g' j)) :=
    congrArg (fun x : StatedSp n K => (x : GL (Fin n ⊕ Fin n) K)) h
  have h2 := planeHom_injective h1
  funext j
  apply Subtype.ext
  have := congrFun h2 j
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using congrArg
    (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) this


def pswap : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]


end Planes

section Main

open Matrix


end Main

end CFSG.ClassicalInvolution.Q3.Q3YS
