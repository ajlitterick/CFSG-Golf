module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def maskHom (n k : ℕ) (cs : List ℕ) : Wn n →* Wn k where
  toFun v := Multiplicative.ofAdd (∑ j : Fin n, Multiplicative.toAdd v j • bvec k (cs.getD j 0))
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, add_smul, Finset.sum_add_distrib, ofAdd_add]

theorem maskHom_toW {n k : ℕ} {cs : List ℕ} (hcs : cs.length = n) (m : ℕ) :
    maskHom n k cs (toW n m) = toW k (actM cs m) := by
  unfold maskHom toW
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  congr 1
  rw [bvec_actM k cs m, hcs, ← Fin.sum_univ_eq_sum_range
    (fun j => if m.testBit j then bvec k (cs.getD j 0) else 0) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp


section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem congrHom_apply_eg (eg : V ≃* W) (g : MulAut V) (v : V) :
    congrHom eg g (eg v) = eg (g v) := by
  rw [congrHom_apply, MulEquiv.symm_apply_apply]


end Transport

end CFSG.Quasithin.H156
