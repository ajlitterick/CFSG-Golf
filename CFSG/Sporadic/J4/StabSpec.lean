module

public import CFSG.Sporadic.J4.GlobalSpec
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Global
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

section Facts

variable (hF : J4NativeFacts)
include hF


theorem globalAt_all : ∀ i < nPts, globalAt GD0 i = true := by
  have h := hF.global
  unfold globalOK at h
  rw [GD0_fields.1] at h
  exact parAllR_eq_true h

noncomputable abbrev schr (s : J) (i : ℕ) : J := (trans (idx nPts s i))⁻¹ * s * trans i

theorem testA {i : ℕ} (hi : i < nPts) (h : reqA GD0 i = true) : schr (a⁻¹) i ∈ Hj := by
  have hg := globalAt_all hF i hi
  unfold globalAt at hg
  simp only [h, Bool.true_or, ite_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  simpa [sGen] using globalTest_spec hF hi hg.1

theorem testB {i : ℕ} (hi : i < nPts) (h : reqB GD0 i = true) : schr (b⁻¹) i ∈ Hj := by
  have hg := globalAt_all hF i hi
  unfold globalAt at hg
  simp only [h, Bool.or_true, ite_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  simpa [sGen] using globalTest_spec hF hi hg.2


noncomputable abbrev nb (i : ℕ) : ℕ := idx nPts (b⁻¹ : J) i


noncomputable abbrev root0 : Fin nPts := ⟨0, nPts_pos hF⟩

omit hF in
theorem val_smul (g : J) (x : Fin nPts) : (g • x).val = idx nPts g x.val := by
  rw [idx_of_lt g x.isLt]


end Facts

end CFSG.Sporadic.J4
