# Golfing the CFSG formalisation: status

Last updated 2026-11-10. Integration branch: `iface/next`. Tools: `tools/` (branch `golf/tools`, PR #1).

## Score

The score is the total size of the repository's `.lean` files that `Comparator/Solution.lean`
transitively imports (`python3 -I tools/cfsg_score.py --diff tools/baseline.json`).

| | bytes | lines | modules |
|---|---|---|---|
| original | 2,147.4 MB | 42,779,430 | 226,887 |
| `iface/next` | 2,013.4 MB | 40,462,103 | 223,507 |
| change | −134.0 MB (−6.24%) | −2,317,327 | −3,380 |

Contributions:

| change | saving | how it was checked |
|---|---|---|
| one proof of the odd order theorem instead of two | 13.6 MB | new one-line file elaborates against built oleans; axioms OK |
| certificate import lists removed from files that never use a certificate | 9.7 MB | every name a file mentions is still visible (`tools/check_import_removal.py`); 30 files had their lists restored |
| 103,060 declarations unreachable from the main theorem removed | 89.3 MB | 0 conflicts on 8,990 of them against compiled constants (`tools/check_dead_against_oleans.py`); sample re-elaborated |
| 141,407 redundant import lines removed | 8.1 MB | visible and re-exported module sets identical for all 227,676 modules (`tools/impreduce`) |
| sectional 2-rank four theorem takes its quasithin input from the quasithin milestones; the restricted copy `CFSG/GH74/QTGen4` (1,918 modules) is deleted | 12.9 MB | no import cycle; the quasithin milestones do not depend on the theorem (`domtree --path`); not yet elaborated |
| Thompson's fixed-point-free theorem: third-party copy derived from the in-house proof | 0.9 MB | statements agree; no import cycle; not yet elaborated |

None of this is verified by a full build yet. The build of `iface/next` (checked out as
`build/current` in the build checkout) is running in tmux session `cfsg-baseline-1102a`.

## What the analysis showed

* **Dead code is small.** Only about 4% of the source is unreachable from the main theorem at
  declaration level. Exact duplicate declarations are 18 MB; near-copied files about 40 MB at most.
* **Proofs are 68% of the bytes, statements 19%, import lines 3.7%, comments 3%.** Binder
  prefixes are already shared through `variable` (0.15% recoverable). No mechanical proof-level
  pattern is common enough to matter. Tactic use is low-level (`have`, `rw`, `exact`); `grind`
  and `aesop` are essentially unused.
* **The remaining 2.0 GB is mathematics.** Further large savings need shorter arguments, not
  clean-up. The map below says where the bytes are.

## Size map

"Dominated bytes" of a declaration is the source that is reachable from the roots only through
it: what would be freed if it were proved without its present dependencies
(`tools/text_reach.py --save` + `tools/domtree`). Chains of wrappers are collapsed.

- **293.6 MB** `large_even`  (CFSG/Assembly/LargeEven.lean)
  - **168.8 MB** `standard_type_recognition_rank_four → … → lc_gl_standard_type_lie_char_two_recognition_rank_four`  (CFSG/Milestones/LC_GL_standard_type_recognition_rank_four.lean)
    - **153.8 MB** `lc_gl_standard_type_lie_char_two_of_yardstones → ggV2I1Inputs_of_yardstones`  (CFSG/Yardstones/M3f9567aba59d/Reduction.lean)
      - **6.5 MB** `useInput_holds`  (CFSG/LocalAnalysis/StandardType/ZS/UseInputHolds.lean)
      - **6.4 MB** `ggV2I1Inputs_of_round12`  (CFSG/LocalAnalysis/StandardType/GGAssemblyTwelve.lean)
  - **91.0 MB** `pretrichotomy_rank_four → lc_gl_constructed_pretrichotomy_rank_four`  (CFSG/Milestones/LC_GL_constructed_pretrichotomy_rank_four.lean)
    - **48.2 MB** `lc_gl_theorem_a`  (CFSG/Milestones/LC_GL_theorem_A.lean)
      - **8.5 MB** `ys11 → ys11_holds`  (CFSG/LocalAnalysis/GLTheoremA/S12/YS11Final.lean)
      - **7.3 MB** `ys09`  (CFSG/Yardstones/Md0ec50421ce4/Goals.lean)
      - **7.2 MB** `ys05`  (CFSG/Yardstones/Md0ec50421ce4/Goals.lean)
    - **17.4 MB** `movingAround → … → movingAroundLeaves_of_inputs`  (CFSG/LocalAnalysis/GLTheoremB/MovingAround/Proofs/Assembly14.lean)
  - **21.6 MB** `preuniqueness_exclusion_rank_four → lc_gl_preuniqueness_exclusion_rank_four`  (CFSG/Milestones/LC_GL_preuniqueness_exclusion_rank_four.lean)
    - **12.5 MB** `lc_gl_theorem_c_rank_four → lc_gl_theorem_c_rank_four_of_goals`  (CFSG/Yardstones/Md8ed6d263d89/MilestoneProof.lean)
      - **8.1 MB** `lc_gl_embedding_theorem_d1_rank_four → … → d1_of_obligations`  (CFSG/LocalAnalysis/AGLEmbedding/D1AssemblyIII.lean)
    - **8.9 MB** `lc_gl_uniqueness_exclusion_rank_four`  (CFSG/Milestones/LC_GL_uniqueness_exclusion_rank_four.lean)
- **174.9 MB** `rank_three_even`  (CFSG/Assembly/RankThreeEven.lean)
  - **52.6 MB** `core_uniqueness_exclusion → r3e_rank_three_core_uniqueness_exclusion`  (CFSG/Milestones/R3E_rank_three_core_uniqueness_exclusion.lean)
    - **31.7 MB** `cl_lit_aschbacher_1983_uniqueness_case_rank_three`  (CFSG/Milestones/CL_LIT_Aschbacher_1983_uniqueness_case_rank_three.lean)
      - **20.9 MB** `ascSectionNineteen`  (CFSG/Yardstones/Me2c15c2c995a/Goals.lean)
    - **20.8 MB** `cl_lit_gl83_theorem_c_preuniqueness_rank_three`  (CFSG/Milestones/CL_LIT_GL83_Theorem_C_preuniqueness_rank_three.lean)
      - **6.9 MB** `agl81TheoremAResiduesE3_holds → … → agl81TheoremAResiduesE3_of_blockCExtremal`  (CFSG/Yardstones/Mdac756b924db/FrontierPrintBlockCExtremal.lean)
  - **20.0 MB** `part_one_outcome → … → part_one_outcome_of_remaining`  (CFSG/RankThree/PartOne/S12/PartOneRemaining.lean)
    - **16.3 MB** `vanishingRecognition_of_remaining`  (CFSG/RankThree/PartOne/S12/FinalRemaining.lean)
  - **13.9 MB** `item1730_of_l3_316`  (CFSG/RankThree/PartTwo/Sec15/Gagen155R1L3Leaf.lean)
    - **13.1 MB** `item1730_of_l3Pt_316 → item1730_of_l3Pt`  (CFSG/RankThree/PartTwo/Sec15/Gagen155BigHostClosed.lean)
      - **9.0 MB** `item1730_of_res1OpenFPt → … → item1730_of_routeS16_leaves5`  (CFSG/RankThree/PartTwo/Sec14/Ronan143QRouteLeaves5.lean)
  - **9.6 MB** `strothSigma6_holds → strothSigma6_of_h224`  (CFSG/CGT/Stroth77/StrothSigma6Holds.lean)
- **125.7 MB** `component_type → … → ct_standard_recognition_assembly`  (CFSG/Milestones/CT_standard_recognition_assembly.lean)
  - **38.2 MB** `ct_even_standard_residual_reduction → ct_even_standard_residual_reduction_of_goals`  (CFSG/Yardstones/M41b0c98b3153/MilestoneProof.lean)
    - **22.6 MB** `ct_even_standard_residual_reduction_of_yardstones`  (CFSG/Yardstones/M41b0c98b3153/Reduction.lean)
      - **20.8 MB** `ct_seitz_centerless_reduction_frontier → … → seitz_reduction_of_split`  (CFSG/LocalAnalysis/SeitzReduction/SeitzFamiliesFinalElevenGLS3.lean)
  - **31.3 MB** `ct_odd_standard_recognition_frontier_models`  (CFSG/Milestones/CT_odd_standard_recognition_frontier.lean)
    - **24.9 MB** `smallF3StandardOddLie_holds → smallF3StandardOddLieU_of_leaves`  (CFSG/LocalAnalysis/OddStandard/SmallF3/Wire/Top.lean)
      - **7.6 MB** `smallF3U33Core_of_fz59`  (CFSG/LocalAnalysis/OddStandard/SmallF3/FritzII/FzU33Holds.lean)
    - **6.1 MB** `oddLieThm187bResidualHigherRank_holds`  (CFSG/Yardstones/M0362f3a873a3/Goals.lean)
  - **18.8 MB** `ctss_sporadic_standard_centerless_m12_j2_and_other_quotients_frontier_models`  (CFSG/Milestones/CTSS_sporadic_standard_centerless_M12_J2_and_other_quotients_frontier.lean)
    - **9.0 MB** `ctss_models_of_yardstones → … → modelsStatement_of_frontier'`  (CFSG/LocalAnalysis/EvenSporadicStandard/Frontier/MainNoA8.lean)
  - **11.1 MB** `ct_even_small_lie_standard_frontier_models`  (CFSG/Milestones/CT_even_small_Lie_standard_frontier.lean)
    - **9.4 MB** `frontier_models_of_epsilonOne`  (CFSG/LocalAnalysis/EvenSmallLie/FrontierFinal.lean)
- **74.1 MB** `qt_faithful_local_nonempty_classification → qt_h13_maximal_local_catalog_assembly`  (CFSG/Milestones/QT_H13_maximal_local_catalog_assembly.lean)
  - **7.7 MB** `ys11_appendixCFInputs → ys11_of_rqEq`  (CFSG/Quasithin/H13/QTH13Slot11RqEq.lean)
  - **7.0 MB** `ys09_fiveQuotientEliminations`  (CFSG/Yardstones/M64f425cd8476/Goals.lean)
    - **6.7 MB** `ys09_of_leaves_big12`  (CFSG/Quasithin/H13/QTH13SlotRed09Big12.lean)
  - **6.4 MB** `ys07_stmt11_0_1 → … → stmt11_0_1_of_remainingW`  (CFSG/Quasithin/Vol2/Ch11SecWire11Main.lean)
  - **6.0 MB** `stmt10_0_1_of_remainingA`  (CFSG/Quasithin/Vol2/Ch10Reselect/Wire10A.lean)
- **54.8 MB** `cl_lit_gh74_sectional_two_rank_four_models`  (CFSG/Milestones/CL_LIT_GH74_sectional_two_rank_four.lean)
  - **43.6 MB** `milestone_forms_of_leaves35`  (CFSG/GH74/FinalAssemblyDeep35.lean)
    - **30.9 MB** `milestone_forms_of_leaves13`  (CFSG/GH74/FinalAssemblyDeep13.lean)
- **42.1 MB** `gf2nType_of_noSqE1`  (CFSG/RankThree/GF2n/Parrott/GF2nTypeOfNoSqE1.lean)
  - **37.5 MB** `gf2nType_of_noSqE1_parrott_h5_janko_gh`  (CFSG/RankThree/GF2n/Parrott/GF2nTypeOfParrottCitedT1.lean)
    - **36.0 MB** `gf2nType_of_noSqE1_parrott`  (CFSG/RankThree/GF2n/Tim81/GF2nTypeNoSqE1Parrott.lean)
      - **27.9 MB** `gf2nType_of_tim79a_1111`  (CFSG/RankThree/GF2n/Tim81/GF2nTypeTim79a1111.lean)
- **14.1 MB** `odd_order_theorem`  (CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/FinalTheorem.lean)
  - **13.7 MB** `pfSection14FinalDataBridge_theorem`  (CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/FinalTheorem.lean)
- **9.7 MB** `ct_rank_two_standard_recognition_models → ct_rank_two_standard_recognition_of_leaves`  (CFSG/LocalAnalysis/ComponentClassification/RankTwoFrontierLeaves.lean)
  - **6.1 MB** `rankTwoSporadicStandard_of_open`  (CFSG/LocalAnalysis/ComponentClassification/RankTwoSporadicFinal.lean)
- **8.4 MB** `exists_mulEquiv_m22Stab_of_parabolics → … → proof7078`  (Certificates/Kernel/CosetW/Assembly.lean)
- **8.1 MB** `toCoreStep'`  (CFSG/ClassicalInvolution/MilestoneAssemblyWired14.lean)

About 430 MB is shared infrastructure that no single leaf dominates.

## Mathematical shortenings: done, rejected, open

Done (same pattern each time: a theorem proved twice, or a restricted re-proof of something the
main line already proves):

* **Odd order theorem.** Two complete proofs; the in-house one is now a corollary of the Qiuzhen one.
* **Quasithin input of the Gorenstein–Harada theorem.** The theorem is proved unconditionally by
  its own induction (hypothesis `KGH`). Its no-component case needed "a simple, 4-generated,
  `KGH` group of even characteristic with e(G) ≤ 2 is in the catalogue", and this was proved by a
  separate copy of the quasithin development for 4-generated groups. But `KGH` implies K-proper
  (`kProper_of_kgh`), so such a group is a QTKE-group and the three quasithin milestones apply
  directly. See `gh74_qtke_gen4_of_quasithin`.
* **Thompson's theorem** on fixed-point-free automorphisms of prime order (Huppert V.8.14).

Audited and rejected:

* **Bypassing Gorenstein–Harada altogether** (now about 42 MB). Of 34 real application sites, 25
  apply it to the group under classification itself; only about 7 apply it to a proper section,
  where the existing catalogue filter `CFSG.GH74.Filter.filter` would do. The main component-type,
  rank-three and large-even leaves depend on the theorem, so they cannot be used to prove it.
* **Groups of GF(2^n)-type** (`gf2nType_of_noSqE1`, 42 MB: Stroth 1980 14.3 MB, Smith 1981 7.2,
  Parrott 5.3, Timmesfeld 1981 3.7, …). Every consumer needs only "G is in the catalogue", but each
  case with |B| ≥ 4 is reachable, the papers are proved for all finite groups, and no second proof
  of any of them exists in the repository. Under 1 MB is avoidable without new mathematics.
  Leads that need new mathematics: refuting Timmesfeld 1979a Case V locally would remove Parrott
  and Janko (6–7 MB); another proof of the rank-4 milestone would remove the Smith E7/E8 lanes (3–5 MB).

Open, small, found by the duplicates audit (not yet done, each needs a short bridge):

1. Solvable signalizer functor theorem for p = 2 (`two_signalizer_completeness`, 369 kB) versus the
   general `glauberman_solvable_signalizer_functor`: 30–60 lines.
2. Huppert II §8 lemmas on PSL2 copied twice inside the third-party sources (about 155 kB): aliases.
3. Glauberman's ZJ theorem three times (`theoremA` 150 kB, `G_theorem_8_2_11` 214 kB, in-house
   `ZJCharacteristic` 104 kB): needs bridges between p-stability definitions, 60–100 lines.

Open, larger:

0. **Rank three versus rank at least four.** Several results are proved twice with disjoint
   hypotheses e(G) = 3 and e(G) ≥ 4 although the published statements are uniform for e(G) ≥ 3:
   AGL81 Theorem D1 (`agl81TheoremAResiduesE3` 6.9 MB against `lc_gl_embedding_theorem_d1_rank_four`
   8.1 MB), Aschbacher's Theorem 16.69 (`ascSixteenSixtyNine` 9.9 MB against `uc_theorem_16_69_four`
   2.4 MB), Sections 18, 19, 22, 23 of the uniqueness case, and GL83 Theorem C.
   `AGLEmbeddingD2.AGLGlobal` is already stated for 3 ≤ e(G). Generalising the e ≥ 4 proofs to
   e ≥ 3 would remove the e = 3 copies. This is a refactor that needs compile feedback, not glue.

A sweep of all 31 yardstone directories and the `CL_LIT_*` milestones for further duplicated or
restricted re-proofs found nothing else above 15 kB: every large yardstone has a single producer.

4. **Parallel families**: `StandardType/ClassicalPosition/BlockModelDualPair{PSp,POmegaPlus,POmegaMinus}`
   (three files of about 8,000 lines with matching theorems). The `HSFLit*` / `SmallF3/L33/Fritz`
   pairs (1.3 MB) are parallel adaptations over different data, not duplicates.
5. **Unreachable modules** (about 2,250, not counted in the score): the lakefile and `CFSG.lean`
   refer to 27 of them, so deleting them needs lakefile edits.

## Tools

| tool | purpose |
|---|---|
| `cfsg_score.py`, `cfsg_modules.py` | score and import graph |
| `text_reach.py`, `domtree/domtree.rs`, `graphq.py` | declaration mention graph, dead list, dominator tree, queries |
| `delete_dead.py` | apply a dead list |
| `DeclEdges.lean`, `check_dead_against_oleans.py` | test a dead list against compiled terms |
| `impreduce/` | redundant import lines, with a visibility-preservation check |
| `check_import_removal.py` | names hidden by an import removal |
| `sealed_dirs.py`, `subtree_users.py` | developments consumed through few entry points |
| `dup_decls.py`, `dup_statements.py`, `similar_statements.py` | duplicate declarations and statements |
| `DeclReach.lean` | exact reachability from compiled oleans (after a full build) |
| `check_change.sh`, `verify_final.sh` | build-based verification, axioms and statement check |

## Build notes

Lake 5 has no `-j`; `LEAN_NUM_THREADS` on the Lake process bounds parallel jobs. A few modules
need far more memory than the rest (kernel computations by `decide +kernel`; one reached 36.7 GB),
so `run.sh` builds those listed in `giants_known.txt` one at a time before the parallel loop and
again after any out-of-memory kill.
