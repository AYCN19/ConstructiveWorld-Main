# Live_X naming conventions (S/G dual families + legacy-name shells)

- **S family** `S<NN>_<Theme>`: split groups of the 219 large library (S01-S15, adopted from the _CW219_split scheme).
- **G family** `G<NN>_<Theme>`: bounded merge groups of small modules (merge criteria: same topic + <60KB + few dependents + collision pre-check passed).
- **Standalone modules**: hub modules (dependents >= 3, e.g. UpReqAlgebra/UpRealLeB/UpReqDist) and medium-to-large modules keep their original names.
- **Old names removed (no shells)**: the old file names of G-group members no longer exist; their repository-wide `Require Import <old-name>` references were uniformly rewritten to `Require Import G<NN>_<Theme>` by the build scripts.
- **CW_ConstructiveWorld_219.v**: removed from both trees (the 219 aggregate-shell era has ended; S01-S15 are each registered independently and the build order no longer goes through the aggregate shell).
- **CW214KL_scan**: retired; name-level verification that 219 is a superset of 214 (3,943/3,943 names matched; 214-only names = 0), with the dependents' Require now targeting `CW_ConstructiveWorld_219`.
- Suffix semantics: `Req` = req-setoid migrated version; `B` = B-form promotion (Or-form detour); `D` = discharge module (resolution by instantiation); `_P2` = phase 2; `M3` = M3 experiment.
- Build order: order.txt (per-module registration surface in topological order; the 219 aggregate shell is now history).

## G-group inventory
- **G01_CoreMicro**: UpHlogZ + UpExtras + UpFEP + UpLogMono + UpPPO
- **G02_Debt**: UpDebtSqrtAbs + UpDebtDual + UpDebtGibbsT
- **G04_ProjFam**: UpPLA + UpPredRelax + UpProj + UpProjBPC
- **G05_LogSmall**: UpReqLogPrimD + UpReqLogD + UpReqLogLinD
- **G06_BForm**: UpReqPPOB + UpReqSumB + UpReqMinPProjB + UpReqLatticeB
- **G07_KLWall**: UpReqKLCvx + UpReqPowB + UpReqJensen + UpReqKLStrict + UpReqKLEnergy
- **G08_Gibbs**: UpReqHlogZD + UpReqGibbsD + UpReqGibbsE2
- **G09_MiscSmall**: UpReqPCT + UpReqBoltzDirect + UpReqSqPos + UpReqOrderArgmin
- **G10_LoebFam**: UpLoeb + UpLoebD2 + UpRefuted + UpQKBound
- **G11_IDLFam**: UpCLQuery + UpIDL
- **G12_ZPosFam**: UpReqZPosD + UpReqZPosI + UpReqZPosI2 + UpReqZAuto + UpReqZPosFinal
- **G13_EvictFam**: UpEvictId + UpEvictIdReq