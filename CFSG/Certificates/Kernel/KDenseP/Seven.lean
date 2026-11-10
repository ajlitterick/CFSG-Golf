module

public import CFSG.Certificates.Kernel.KDenseP.Glue
public import CFSG.Monster.AxisCount.DenseModSeven

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.Monster.AxisCount

noncomputable abbrev to7 : ZMod (2 ^ 3 - 1) →+* ZMod 7 := ZMod.castHom (by norm_num) (ZMod 7)

theorem res7_eq (v : Native.DVec) (k : ℕ) : DVec.res7 v k = to7 (resN 3 v k) := by
  simp only [resN, DVec.res7, map_mul, map_pow, map_intCast, map_ofNat]
  norm_num

theorem cong7D_of_resN {u v : Native.DVec} (h : ∀ k < 196884, resN 3 u k = resN 3 v k) :
    Cong7D u v :=
  fun k hk => by rw [res7_eq, res7_eq, h k hk]


end CFSG.KC.KDenseP

end
