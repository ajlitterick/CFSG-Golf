module

public import Certificates.Kernel.Sp62Syl.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSp62Syl

open CFSG.KD.Sp62Syl CFSG.KD.U42Syl CFSG.KD.Sp62W CFSG.KC.Mat8P
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6

theorem ch465002_q : (Nat.beq (mulP (numC cG1) (numC cG1)) oneP &&
    qwK (gensT.map numC) (numC cG1) QW) = true := by decide +kernel

theorem ch465002_t : (TW.length == 81 && ttK (gensT.map numC) TP TW 0) = true := by decide +kernel

theorem ch465002_r : (RW.length == 640 && rowsK (gensT.map numC) (gensWD.map numC)
    (gensT.map fun c => numC (mulC c c)) (numC cG1) (numC cTau) (numC cIo) (numC cGD) WP RW 0) =
    true := by decide +kernel

theorem ch465002_len : (CH.length == 160 && KB.length == 161 &&
    (CH.map List.length).sum == 51840) = true := by decide +kernel

theorem ch465002_k0 : lk 0 KB 0 = 0 := by decide +kernel

#kc_each CertificateChecks.KernelSp62Syl ch465002C (fun c => chunkK WP TP CH KB c) 0 160

#kc_forall_chunks ch465002_c (fun c => chunkK WP TP CH KB c = true) 160
  CertificateChecks.KernelSp62Syl.ch465002C 1


end CertificateChecks.KernelSp62Syl
