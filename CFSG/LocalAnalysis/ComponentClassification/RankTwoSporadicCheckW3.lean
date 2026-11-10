module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW2

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped commutatorElement

structure ClosW where
  pw : List (List ℕ)
  comms : List (ℕ × ℕ)
  genQ : List (List ℕ)
  sw : List ℕ
deriving Inhabited

@[expose] def witOKW3 (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array (Array ℕ)) (cE : ArrCert)
    (cs : Array ArrCert) (pf : PerfW) (cl : ClosW) : Wit → Bool
  | .closing s t c kc v gens _ =>
    let gs := (gens.map fun l => powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray
    let pts := (cl.pw.map (wordG n gs)).toArray
    let qs := (cl.comms.map fun ij => commutatorA n pts[ij.1]! pts[ij.2]!).toArray
    allowU && !(eqA n (maskA n basis s) (idA n)) && !(eqA n (maskA n basis t) (idA n)) &&
      validK n c && inX c && commA n c (maskA n basis t) && eqA n (powA n c (2 ^ kc)) (idA n) &&
      validK n (maskA n basis v) &&
      eqA n (commutatorA n (maskA n basis v) c) (maskA n basis s) &&
      gens.all (fun l => l.1.all (CFac.okK n inX basis)) &&
      lettersLt gs.size cl.pw && ((List.range pts.size).all fun j => validK n pts[j]!) &&
      cl.comms.all (fun ij => decide (ij.1 < pts.size) && decide (ij.2 < pts.size)) &&
      lettersLt qs.size cl.genQ &&
      ((List.range gs.size).all fun i => eqA n gs[i]! (wordG n qs (cl.genQ.getD i []))) &&
      lettersLt gs.size [cl.sw] && eqA n (maskA n basis s) (wordG n gs cl.sw)
  | w => witOKW2 n ps inX outX allowPW allowInX allowU basis cE cs pf w


section Soundness

variable {n : ℕ}
variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}
  {basis : Array (Array ℕ)}

theorem witOKW3_sound {ps : List ℕ} {allowPW allowInX allowU : Bool} {cE : ArrCert}
    {cs : Array ArrCert} {pf : PerfW} {cl : ClosW} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hE : enumOK n basis ps cE = true) {w : Wit}
    (h : witOKW3 n ps inX outX allowPW allowInX allowU basis cE cs pf cl w = true) :
    MonoW X allowPW (closure (permsA n basis)) ∨ (w.isMono = false ∧
      (4 ≤ Nat.card (closure (permsA n basis)) →
        WitW X allowPW allowInX allowU (closure (permsA n basis)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ k < basis.size, validA n basis[k]! = true := fun k hk => enumOK_gens_valid hE hk
  cases w with
  | closing s t c kc v gens comms0 =>
    simp only [witOKW3, CFac.okK_eq, validK_eq, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hs1⟩, ht1⟩, hcv⟩, hcX⟩, hct⟩, hcpow⟩, hvv⟩, hvc⟩, hgens⟩,
      hpw⟩, hval⟩, hcomms⟩, hlq⟩, hgq⟩, hls⟩, hsw⟩ := h
    set E := closure (permsA n basis)
    obtain ⟨s', hs'E, hs'⟩ := rep_maskA hb s
    obtain ⟨t', ht'E, ht'⟩ := rep_maskA hb t
    obtain ⟨v', hv'E, hv'⟩ := rep_maskA hb v
    have hcr := rep_of_validA hcv
    have hne : ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
        eqA n a (idA n) = false → g ≠ 1 := by
      rintro a g ha hf rfl
      rw [(eqA_iff ha rep_idA).2 rfl] at hf
      exact Bool.noConfusion hf
    set C := ⁅X ⊓ centralizer (E : Set (Equiv.Perm (Fin n))),
      X ⊓ centralizer (E : Set (Equiv.Perm (Fin n)))⁆
    have hcf : ∀ f : CFac, CFac.ok n inX basis f = true → ∃ g ∈ C, Rep n (f.val n) g := by
      intro f hf
      simp only [CFac.ok, Bool.and_eq_true] at hf
      obtain ⟨⟨⟨⟨hv1, hv2⟩, hx1⟩, hx2⟩, hcb⟩ := hf
      have hr1 := rep_of_validA hv1
      have hr2 := rep_of_validA hv2
      have hcent : ∀ {a : Array ℕ}, Rep n a (permOfArr n a) →
          (∀ k < basis.size, commA n a basis[k]! = true) →
          permOfArr n a ∈ centralizer (E : Set (Equiv.Perm (Fin n))) := by
        intro a ha hk
        refine mem_centralizer_closure_of_commute ?_
        rintro _ ⟨k, hk', rfl⟩
        exact (commA_iff ha (rep_of_validA (hb k hk'))).1 (hk k hk')
      have hk1 : ∀ k < basis.size, commA n f.x₁ basis[k]! = true := fun k hk => by
        have := allLt_spec hcb hk
        simp only [Bool.and_eq_true] at this
        exact this.1
      have hk2 : ∀ k < basis.size, commA n f.x₂ basis[k]! = true := fun k hk => by
        have := allLt_spec hcb hk
        simp only [Bool.and_eq_true] at this
        exact this.2
      exact ⟨_, commutator_mem_commutator ⟨hin _ hv1 hx1, hcent hr1 hk1⟩
        ⟨hin _ hv2 hx2, hcent hr2 hk2⟩, rep_commutatorA hv1 hv2⟩
    set gs := (gens.map fun l => powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray
    set P := closure (permsA n gs)
    have hgsC : ∀ i < gs.size, ∃ g ∈ C, Rep n gs[i]! g := by
      refine rep_toArray fun l hl => ?_
      obtain ⟨y, hy, hyr⟩ := rep_prodA (H := C) (l := l.1.map (CFac.val n)) (by
          intro a ha
          rw [List.mem_map] at ha
          obtain ⟨f, hf, rfl⟩ := ha
          exact hcf f (hgens l hl f hf))
      exact ⟨y ^ l.2, pow_mem hy _, rep_powA hyr _⟩
    have hgsP : ∀ i < gs.size, ∃ g ∈ P, Rep n gs[i]! g := by
      intro i hi
      obtain ⟨g, -, hr⟩ := hgsC i hi
      refine ⟨g, ?_, hr⟩
      rw [← permOfArr_eq_of_rep hr]
      exact subset_closure (mem_permsA hi)
    have hPle : P ≤ C := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨g, hg', hr⟩ := hgsC i hi
      change permOfArr n gs[i]! ∈ _
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    set pts := (cl.pw.map (wordG n gs)).toArray
    have hvalj : ∀ j < pts.size, validA n pts[j]! = true :=
      fun j hj => hval j (List.mem_range.2 hj)
    have hmemP : ∀ j < pts.size, permOfArr n pts[j]! ∈ P := by
      intro j hj
      obtain ⟨g, hg', hr⟩ := rep_toArray (fun w hw => rep_wordG hgsP (lettersLt_spec hpw w hw)) j hj
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    set qs := (cl.comms.map fun ij => commutatorA n pts[ij.1]! pts[ij.2]!).toArray
    have hqs : ∀ i < qs.size, ∃ g ∈ ⁅P, P⁆, Rep n qs[i]! g := by
      refine rep_toArray fun ij hij => ?_
      have h12 := hcomms ij hij
      exact ⟨_, commutator_mem_commutator (hmemP _ h12.1) (hmemP _ h12.2),
        rep_commutatorA (hvalj _ h12.1) (hvalj _ h12.2)⟩
    have hqsQ : ∀ i < qs.size, ∃ g ∈ closure (permsA n qs), Rep n qs[i]! g := by
      intro i hi
      obtain ⟨g, -, hr⟩ := hqs i hi
      refine ⟨g, ?_, hr⟩
      rw [← permOfArr_eq_of_rep hr]
      exact subset_closure (mem_permsA hi)
    have hQ : closure (permsA n qs) ≤ ⁅P, P⁆ := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨g, hg', hr⟩ := hqs i hi
      change permOfArr n qs[i]! ∈ _
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    have hgsRep : ∀ i < gs.size, ∃ g, Rep n gs[i]! g := fun i hi => by
      obtain ⟨g, -, hr⟩ := hgsP i hi
      exact ⟨g, hr⟩
    have hPQ : P ≤ closure (permsA n qs) :=
      closure_le_of_words hqsQ hlq hgsRep (List.all_eq_true.2 hgq)
    have hcommP : ⁅P, P⁆ ≤ P := by
      rw [commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hperf : ⁅P, P⁆ = P := le_antisymm hcommP (hPQ.trans hQ)
    have hsP : s' ∈ P := by
      have hl : ∀ i ∈ cl.sw, i < gs.size := lettersLt_spec hls cl.sw (List.mem_singleton_self _)
      obtain ⟨g, hg', hr⟩ := rep_wordG hgsP hl
      rw [eq_of_eqA hs' hr hsw]
      exact hg'
    have hc2 : IsPGroup 2 (zpowers (permOfArr n c)) := by
      have hpow : permOfArr n c ^ 2 ^ kc = 1 := eq_of_eqA (rep_powA hcr _) rep_idA hcpow
      obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    have hvc' : ⁅v', permOfArr n c⁆ = s' := by
      have h1 := rep_commutatorA hvv hcv
      rw [permOfArr_eq_of_rep hv'] at h1
      exact eq_of_eqA h1 hs' hvc
    refine Or.inr ⟨rfl, fun _ => Or.inr (Or.inr (Or.inr ⟨hU, s', hs'E, hne hs' hs1,
      ⟨t', ht'E, hne ht' ht1, permOfArr n c, hin _ hcv hcX, (commA_iff hcr ht').1 hct, hc2, v',
        hv'E, hvc'⟩, P, hPle, hperf, hsP⟩))⟩
  | order4 l m => exact witOKW2_sound (cs := cs) (pf := pf) hps hin hout hE h
  | twoGroup gens k => exact witOKW2_sound (cs := cs) (pf := pf) hps hin hout hE h
  | perfect gens comms x k conjs e g => exact witOKW2_sound (cs := cs) (pf := pf) hps hin hout hE h
  | inX => exact witOKW2_sound (cs := cs) (pf := pf) hps hin hout hE h
  | small => exact witOKW2_sound (cs := cs) (pf := pf) hps hin hout hE h


end Soundness

end CFSG.ComponentClassification.RankTwoSporadic.Cert
