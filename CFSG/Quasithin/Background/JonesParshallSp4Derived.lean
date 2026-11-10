module

public import CFSG.Quasithin.Background.JonesParshallSp4Two

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit

section RingEquiv

variable {F F' : Type} [Field F] [Field F']

@[expose] def glIxRingEquiv (e : F ≃+* F') : GL Ix F ≃* GL Ix F' where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    change e.symm (e ((g : Matrix Ix Ix F) i j)) = _
    rw [RingEquiv.symm_apply_apply]
  right_inv g := by
    ext i j
    change e (e.symm ((g : Matrix Ix Ix F') i j)) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' := map_mul _

theorem glIxRingEquiv_coe (e : F ≃+* F') (g : GL Ix F) :
    ((glIxRingEquiv e g : GL Ix F') : Matrix Ix Ix F') = (g : Matrix Ix Ix F).map e := rfl

theorem spJ_map (e : F ≃+* F') : (spJ F).map e = spJ F' := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [spJ, one_apply, apply_ite]

theorem glIxRingEquiv_mem {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {g : GL Ix K}
    (hg : g ∈ sp4 K) : glIxRingEquiv e g ∈ sp4 K' := by
  change ((glIxRingEquiv e g : GL Ix K') : Matrix Ix Ix K')ᵀ * spJ K' *
    ((glIxRingEquiv e g : GL Ix K') : Matrix Ix Ix K') = spJ K'
  have hg' : (g : Matrix Ix Ix K)ᵀ * spJ K * g = spJ K := hg
  rw [glIxRingEquiv_coe, ← spJ_map e, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg']


@[expose] def vecIxRingEquiv (e : F ≃+* F') : (Ix → F) ≃+ (Ix → F') where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp

theorem vecIxRingEquiv_smul (e : F ≃+* F') (g : GL Ix F) (v : Ix → F) :
    vecIxRingEquiv e (g • v) = glIxRingEquiv e g • vecIxRingEquiv e v := by
  funext i
  change e (((g : Matrix Ix Ix F) *ᵥ v) i) = (((g : Matrix Ix Ix F).map e) *ᵥ fun j => e (v j)) i
  exact RingHom.map_mulVec e.toRingHom _ _ i

end RingEquiv


end CFSG.Quasithin.JonesParshall
