module

public import CFSG.Monster.B.Mathieu.CertData
public import Certificates.Data.Kernel.Mathieu.Raw

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.KD.Mathieu

@[expose] def decLetter (k : ℕ) : ℤ := if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -((k / 2 : ℕ) : ℤ)

@[expose] def decWord (w : List ℕ) : List ℤ := w.map decLetter

@[expose] def decStr (l : List ℕ) : String := String.ofList (l.map Char.ofNat)

@[expose] def decChain (n : ℕ) (G : List (List ℕ)) (B : List ℕ) (S D : List (List ℕ)) :
    ChainRecord :=
  { degree := n, generators := G, base := B, strongGenerators := S, derivations := D.map decWord }

@[expose] def decNGs (n : ℕ) : List (List ℕ) → List (List (List ℕ)) → List (List ℕ) →
    List (List (List ℕ)) → List (List (List ℕ)) → List NormalGenRecord
  | r :: R, c :: C, b :: B, s :: S, d :: D =>
    { representative := r, conjugators := c.map decWord,
      chain := decChain n (s.take c.length) b s d } :: decNGs n R C B S D
  | _, _, _, _, _ => []

@[expose] def decSylows (n : ℕ) : List ℕ → List (List (List ℕ)) → List (List (List ℕ)) →
    List (List (List (List ℕ))) → List (List (List ℕ)) → List (List (List (List ℕ))) →
    List (List (List (List ℕ))) → List SylowRecord
  | p :: P, g :: SG, r :: R, c :: C, b :: B, s :: S, d :: D =>
    { prime := p, generators := g, normalGeneration := decNGs n r c b s d } ::
      decSylows n P SG R C B S D
  | _, _, _, _, _, _, _ => []

@[expose] def decGroup (t : List ℕ) (sp : List (List ℕ)) (n : ℕ) (G : List (List ℕ))
    (B : List ℕ) (S D : List (List ℕ)) (P : List ℕ) (SG : List (List (List ℕ)))
    (R : List (List (List ℕ))) (C : List (List (List (List ℕ)))) (NB : List (List (List ℕ)))
    (NS ND : List (List (List (List ℕ)))) : GroupRecord :=
  { group := decStr t, seedPaths := sp.map decStr, chain := decChain n G B S D,
    sylows := decSylows n P SG R C NB NS ND }

@[expose] noncomputable def m11RecordK : GroupRecord :=
  decGroup (tags.getD 0 []) (seeds.getD 0 []) 11 m11G m11B m11S m11D m11P m11SG m11NR m11NC
    m11NB m11NS m11ND

@[expose] noncomputable def m12RecordK : GroupRecord :=
  decGroup (tags.getD 1 []) (seeds.getD 1 []) 12 m12G m12B m12S m12D m12P m12SG m12NR m12NC
    m12NB m12NS m12ND

@[expose] noncomputable def m22RecordK : GroupRecord :=
  decGroup (tags.getD 2 []) (seeds.getD 2 []) 22 m22G m22B m22S m22D m22P m22SG m22NR m22NC
    m22NB m22NS m22ND

@[expose] noncomputable def m23RecordK : GroupRecord :=
  decGroup (tags.getD 3 []) (seeds.getD 3 []) 23 m23G m23B m23S m23D m23P m23SG m23NR m23NC
    m23NB m23NS m23ND

@[expose] noncomputable def m24RecordK : GroupRecord :=
  decGroup (tags.getD 4 []) (seeds.getD 4 []) 24 m24G m24B m24S m24D m24P m24SG m24NR m24NC
    m24NB m24NS m24ND

@[expose] noncomputable def certificateFileK : CertificateFile :=
  { schemaVersion := schema, description := decStr desc, permutationConvention := decStr conv,
    groups := [m11RecordK, m12RecordK, m22RecordK, m23RecordK, m24RecordK] }

@[expose] noncomputable def MathieuCertificateK (t : String) : Option GroupRecord :=
  certificateFileK.groups.find? fun r => r.group == t


end CFSG.Monster.B.Mathieu
