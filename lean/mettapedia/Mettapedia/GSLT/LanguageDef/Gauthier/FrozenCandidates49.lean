import Mettapedia.GSLT.LanguageDef.Gauthier.OEISSequenceSemantics
import Mettapedia.Sequences.OEIS.Elementary49

namespace Mettapedia.GSLT.LanguageDef.GauthierFrozenCandidates49

open GauthierOEISSequenceSemantics
open Mettapedia.Sequences.OEIS


/-- An authenticated program paired with the already-frozen formal sequence specification. -/
structure AdjudicationTarget where
  oeisId : String
  publishedTermCount : Nat
  spec : SequenceSpec
  candidate : FrozenCandidate

def candidate00 : FrozenCandidate where
  programSha256 := "3050537ef6c33c923ca61d4ca58c2ca52c3a4ba86094755ced29c0ddd136dfc4"
  tokens := [10, 10, 5, 1, 10, 10, 3, 10, 1, 2, 3, 9, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw)))
  recognized := rfl

def candidate01 : FrozenCandidate where
  programSha256 := "a07a3cf4592fd5b5eb29aaa6beaa703544b3aee5f308c46598dc83b1cda9025c"
  tokens := [2, 2, 2, 10, 10, 3, 5, 10, 3, 5, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X))) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate02 : FrozenCandidate where
  programSha256 := "e1cd41782fa2c64345341616688dc15a85a43d7b131846f2e87dbf9f6f819a20"
  tokens := [2, 2, 2, 10, 10, 3, 5, 10, 3, 5, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X))) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate03 : FrozenCandidate where
  programSha256 := "3c566ba8debc314c7af13030d2a2d2533e58081e2ed18a12cae393bfca2bfb21"
  tokens := [2, 2, 10, 10, 3, 5, 10, 3, 5, 10, 1, 9, 1, 2, 3, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.o) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw))
  recognized := rfl

def candidate04 : FrozenCandidate where
  programSha256 := "5a997ff30fd3baf6a7db8e495f5f310df07e60bdd71771d590ade5c43d5b5d8b"
  tokens := [2, 2, 2, 2, 3, 5, 3, 10, 5, 10, 1, 9, 1, 2, 3, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.o) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw))
  recognized := rfl

def candidate05 : FrozenCandidate where
  programSha256 := "17661542a03ec29cfd87278650e0609e9d9080ce1c0594a8a8149184228f81bc"
  tokens := [1, 2, 2, 3, 10, 10, 3, 5, 10, 3, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate06 : FrozenCandidate where
  programSha256 := "1c91563f3591808a05b7c077de7c816ee5c3d7d66e9a58e7611636578086368f"
  tokens := [1, 2, 2, 3, 10, 10, 3, 5, 10, 3, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate07 : FrozenCandidate where
  programSha256 := "2b17b9973f1c49173f456b8b4c88b712ec8b6d3267e89886e1b18089d58f2ca5"
  tokens := [1, 2, 10, 10, 3, 10, 3, 5, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X))) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate08 : FrozenCandidate where
  programSha256 := "5a257dbf96f47e6e11c1f841da91c397d2cb65f927bfa65bed8dc30513d07420"
  tokens := [1, 2, 2, 2, 3, 3, 10, 5, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate09 : FrozenCandidate where
  programSha256 := "74168b3a141e263248ebd8deaa43cd79397f026b4bed12b239754cbe1bbc774a"
  tokens := [1, 2, 10, 10, 3, 10, 3, 5, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X))) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate10 : FrozenCandidate where
  programSha256 := "7c796ed4bfd0db216d49a36a743de8d818c78cf48869d8d9d71c11e959dfc671"
  tokens := [1, 2, 10, 10, 3, 5, 10, 3, 10, 3, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate11 : FrozenCandidate where
  programSha256 := "917488aec90369187e822b0880eb36ce0bba1f142a4533144c4756f012eb0089"
  tokens := [1, 2, 2, 2, 3, 3, 10, 5, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate12 : FrozenCandidate where
  programSha256 := "b85498c082740b857598b6284a2415173c161c66baa21d942e8f60b55465345b"
  tokens := [1, 2, 10, 10, 3, 5, 10, 3, 10, 3, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X) GauthierE2.P.X)) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate13 : FrozenCandidate where
  programSha256 := "3cfa24870d5d001ca285934ad6867442cfdb99f50d62bae4ee8870a961b7f4a0"
  tokens := [10, 10, 5, 10, 5, 2, 11, 9, 11, 5, 10, 3, 11, 10, 0, 10, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X) GauthierE2.P.Y GauthierE2.P.X GauthierE2.P.z GauthierE2.P.X)
  recognized := rfl

def candidate14 : FrozenCandidate where
  programSha256 := "05eb2e00b04eadb6274b59562de996fd7ed7eae32b2f99286a42498cfd3ebf2e"
  tokens := [10, 11, 5, 11, 10, 10, 10, 5, 2, 10, 9, 10, 13, 1, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.loop2 (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.Y) GauthierE2.P.Y GauthierE2.P.X (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.o)
  recognized := rfl

def candidate15 : FrozenCandidate where
  programSha256 := "c7f025767c0c6ca4a7ac872e2dfd71f414ee13ba2ce52df71b37ed81d54ec54d"
  tokens := [2, 2, 11, 3, 3, 10, 5, 2, 10, 9, 10, 3, 10, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.Y)) GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.o)
  recognized := rfl

def candidate16 : FrozenCandidate where
  programSha256 := "9b0f17a55de93d1ec886e3c2bf9fcdcf826d0a57a08ee7da46d99a6103e601fb"
  tokens := [1, 2, 2, 2, 3, 3, 3, 10, 5, 2, 10, 9, 10, 4, 10, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.o)
  recognized := rfl

def candidate17 : FrozenCandidate where
  programSha256 := "f435b308386f4d261e887e5751f3c61eda4a2a1e3cb030d88fa68be208bc473f"
  tokens := [10, 10, 5, 10, 5, 2, 10, 10, 5, 9, 10, 5]
  program := (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X)
  recognized := rfl

def candidate18 : FrozenCandidate where
  programSha256 := "6b867a7b1353d84e3c6c5e7c5d557d791d4370ca2c4947fae7ed8b3a9e32f856"
  tokens := [11, 1, 2, 3, 6, 10, 3, 10, 0, 9, 2, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi GauthierE2.P.Y (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw)) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.z) GauthierE2.P.tw)
  recognized := rfl

def candidate19 : FrozenCandidate where
  programSha256 := "1772953009d476604ec462179b13b53f43f42f2ee1d9cc956b3e34f150a83cc0"
  tokens := [10, 10, 3, 10, 3, 1, 10, 10, 3, 3, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.o)
  recognized := rfl

def candidate20 : FrozenCandidate where
  programSha256 := "31972e2673f005c6354e77537ebbce2975432077bedef58ed34092292cbba6b3"
  tokens := [2, 2, 2, 2, 3, 3, 3, 10, 5, 10, 3, 10, 1, 2, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw))
  recognized := rfl

def candidate21 : FrozenCandidate where
  programSha256 := "35254e0b8fed2ca13acffe6cb29f4da0d136033dae6eebeb9fb247056c462663"
  tokens := [2, 10, 11, 3, 5, 11, 3, 10, 10, 10, 3, 1, 2, 3, 1, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y)) GauthierE2.P.Y) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.o)
  recognized := rfl

def candidate22 : FrozenCandidate where
  programSha256 := "6a61f90694fe194e4ce9e84d93fd866ec3660399e337d47b79888dcac714413a"
  tokens := [1, 2, 3, 10, 5, 1, 10, 10, 3, 3, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.o)
  recognized := rfl

def candidate23 : FrozenCandidate where
  programSha256 := "fac5de6251537759552b870b831a2443f02d769087ebf36dcf9c23517c916705"
  tokens := [2, 2, 3, 10, 10, 3, 5, 10, 3, 10, 1, 2, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw))
  recognized := rfl

def candidate24 : FrozenCandidate where
  programSha256 := "b1fd5dac96863ce1e4398b0dc3596ac78a836e6f7d85e67722b737bf06517aaf"
  tokens := [1, 2, 2, 3, 3, 10, 5, 1, 10, 10, 3, 3, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.o)
  recognized := rfl

def candidate25 : FrozenCandidate where
  programSha256 := "b3c5509b887eaabd2a0e1027e91cef3a38b57da70d9aac79fbedcb1d7ea212b3"
  tokens := [10, 10, 5, 2, 2, 9, 10, 5, 11, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate26 : FrozenCandidate where
  programSha256 := "f1837d9de488faa7f5a73d26414e9eb426a5b3201a1601cdbf5f7b0d2ad6ba29"
  tokens := [10, 10, 5, 2, 2, 9, 10, 5, 11, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate27 : FrozenCandidate where
  programSha256 := "81968dca3a8471e810b421dcba6ee22ac375978fc67f4c2276d7a2e315b65b53"
  tokens := [1, 2, 2, 10, 10, 3, 5, 10, 3, 5, 4, 10, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.diff GauthierE2.P.o (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X))) GauthierE2.P.X GauthierE2.P.o)
  recognized := rfl

def candidate28 : FrozenCandidate where
  programSha256 := "dba931cee529c62f5c8284b78fbb0974327221981a029c00f99a6b4d0711eb2d"
  tokens := [10, 10, 5, 10, 5, 1, 1, 10, 10, 3, 10, 3, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X)))
  recognized := rfl

def candidate29 : FrozenCandidate where
  programSha256 := "c57882d00078998c452c5feee21dc0c7d0399e0f60379d118fd421c54acf6d67"
  tokens := [10, 10, 5, 2, 1, 1, 2, 3, 10, 5, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.X)))
  recognized := rfl

def candidate30 : FrozenCandidate where
  programSha256 := "49e6cea5ab07ccf1dfac616e36e42e5e49c7ed074c227c30ddf946f24587efef"
  tokens := [10, 10, 5, 1, 1, 2, 2, 3, 10, 5, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.X)))
  recognized := rfl

def candidate31 : FrozenCandidate where
  programSha256 := "40a6264f8fe47688ea5a24ed363ad7c7056268ad2c51ae18e375d389691fb322"
  tokens := [10, 10, 5, 2, 11, 9, 11, 5, 10, 4, 1, 11, 3, 2, 0, 10, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.diff (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.Y) GauthierE2.P.tw GauthierE2.P.z GauthierE2.P.X)
  recognized := rfl

def candidate32 : FrozenCandidate where
  programSha256 := "9cf360977d936ab9faa9c9ce97f841c845138e370b4010950d8c2b889fcd1af1"
  tokens := [2, 2, 2, 3, 3, 10, 5, 10, 1, 9, 10, 10, 5, 4]
  program := (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.o) (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X))
  recognized := rfl

def candidate33 : FrozenCandidate where
  programSha256 := "31e67b33415139484f1e98b9ae340ee640e991b15376af15db8f8f7113151788"
  tokens := [10, 11, 3, 10, 10, 11, 3, 10, 10, 3, 10, 9, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y) GauthierE2.P.X (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X))
  recognized := rfl

def candidate34 : FrozenCandidate where
  programSha256 := "afa9f3965f8df53a2b2a118ccfd796e9f6c83a8b5e83d8f9b23df8fc1c9b30e5"
  tokens := [1, 2, 2, 3, 3, 11, 5, 10, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.Y) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate35 : FrozenCandidate where
  programSha256 := "c84a91cc1c18a23e4862dcc3c132c8a0c56920f21f0d22008e9be7909ab3d668"
  tokens := [1, 2, 2, 3, 3, 11, 5, 10, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.Y) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate36 : FrozenCandidate where
  programSha256 := "5e4f1c706155b24a365ac6ad7b1d25d00a503fde49018b33433562db8cc410ef"
  tokens := [11, 2, 6, 11, 3, 2, 6, 10, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.addi (GauthierE2.P.divi GauthierE2.P.Y GauthierE2.P.tw) GauthierE2.P.Y) GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate37 : FrozenCandidate where
  programSha256 := "b6ca269b5ea0d59c9519f69f9192e3b95e9942eb1c0b987b89b3d52dbfcc6f75"
  tokens := [11, 2, 6, 11, 3, 2, 6, 10, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.addi (GauthierE2.P.divi GauthierE2.P.Y GauthierE2.P.tw) GauthierE2.P.Y) GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate38 : FrozenCandidate where
  programSha256 := "78d66fc4eb4ee86362206a65ff4ae62a238a480c5c8f57418e839ef2d202168f"
  tokens := [10, 10, 5, 10, 5, 2, 11, 9, 10, 3, 1, 11, 3, 2, 0, 10, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.addi (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.Y) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.Y) GauthierE2.P.tw GauthierE2.P.z GauthierE2.P.X)
  recognized := rfl

def candidate39 : FrozenCandidate where
  programSha256 := "38267157535d3be5d545c09c56e5002fe275c4b26242b21ecccf118ca13fb391"
  tokens := [10, 11, 5, 1, 2, 3, 11, 5, 10, 1, 1, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.Y) (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.o GauthierE2.P.o)
  recognized := rfl

def candidate40 : FrozenCandidate where
  programSha256 := "2b27d37087e6991555e6d585392b0b5c5b2238e6213c8b7e29a9b76015a8e4ea"
  tokens := [2, 2, 3, 10, 10, 3, 5, 10, 3, 10, 1, 10, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X))
  recognized := rfl

def candidate41 : FrozenCandidate where
  programSha256 := "99ba9697b84ba6d95ac9f9b366d35b52f5892814200a8ec24c3c0459d12b09fe"
  tokens := [2, 2, 2, 2, 3, 3, 3, 10, 5, 10, 3, 10, 1, 10, 3, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X))
  recognized := rfl

def candidate42 : FrozenCandidate where
  programSha256 := "033355faf1caf67567a2d92d26473769db996d032d3b3dd3cbb0ecc5ae4dfdc2"
  tokens := [1, 10, 3, 1, 2, 2, 2, 3, 3, 3, 6, 10, 3, 2, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)))) GauthierE2.P.X) GauthierE2.P.tw)
  recognized := rfl

def candidate43 : FrozenCandidate where
  programSha256 := "5abf680ec8c2a6953ed3dcbc14b34b7f8662949dbc88729e5129f232a8671eb4"
  tokens := [10, 1, 2, 2, 2, 3, 3, 3, 6, 10, 3, 2, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.addi (GauthierE2.P.divi GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)))) GauthierE2.P.X) GauthierE2.P.tw)
  recognized := rfl

def candidate44 : FrozenCandidate where
  programSha256 := "e7db3927184dac20e4d8cdb1f001d9f0dde3b20e8844756f6e400a950487415c"
  tokens := [1, 2, 2, 3, 3, 10, 5, 1, 10, 3, 1, 10, 3, 9, 1, 4]
  program := (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X)) GauthierE2.P.o)
  recognized := rfl

def candidate45 : FrozenCandidate where
  programSha256 := "315061126a0a0fb9eb5c6b0de9be9daa0977d662244d07020ff5276021a5f81e"
  tokens := [10, 10, 5, 10, 10, 5, 2, 2, 9, 7]
  program := (GauthierE2.P.modu (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.tw))
  recognized := rfl

def candidate46 : FrozenCandidate where
  programSha256 := "310209b1db332a56d73abbd2476b62292b37548b20f7114124632ba8cdbb61cc"
  tokens := [10, 10, 5, 10, 5, 10, 10, 5, 2, 2, 9, 7]
  program := (GauthierE2.P.modu (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.X) (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.tw))
  recognized := rfl

def candidate47 : FrozenCandidate where
  programSha256 := "8032502b1f23e78427eba8af7439f0fef580c0ca5e9c84520c7199646bedb265"
  tokens := [10, 10, 5, 2, 10, 9, 1, 2, 2, 2, 3, 3, 3, 7]
  program := (GauthierE2.P.modu (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))))
  recognized := rfl

def candidate48 : FrozenCandidate where
  programSha256 := "1c91f9fe1a2d60f21c8ace4d01f48390119cfeaf92c7e95506b95303cfd76baf"
  tokens := [1, 2, 3, 11, 5, 10, 3, 10, 10, 3, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.Y) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o)
  recognized := rfl

def candidate49 : FrozenCandidate where
  programSha256 := "5827e789fa9d2bc4e615d9449204e8e75b4653b226ffb6f5834d8980d7493870"
  tokens := [10, 10, 5, 2, 10, 9, 10, 5, 2, 10, 9, 10, 5]
  program := (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X)
  recognized := rfl

def candidate50 : FrozenCandidate where
  programSha256 := "ede2452071ef41babc6405a3a07dfef097c55b547fa0ca18b0f941e2ec7e0fdc"
  tokens := [10, 11, 5, 11, 5, 10, 2, 1, 10, 3, 10, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.mult (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X) GauthierE2.P.X)
  recognized := rfl

def candidate51 : FrozenCandidate where
  programSha256 := "482ec3a3ecda98447eab8f6844cd063b34ffd4d0e883a5bb558c158820938407"
  tokens := [2, 11, 11, 3, 5, 10, 3, 10, 10, 3, 1, 9, 11, 4]
  program := (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o) GauthierE2.P.Y)
  recognized := rfl

def candidate52 : FrozenCandidate where
  programSha256 := "a0f1e8c36d71f4a85ac4c61d96d86f7c0ae08ebbf9d8976d6165b49b9b954644"
  tokens := [2, 11, 11, 3, 5, 10, 3, 10, 10, 3, 1, 9, 0, 4]
  program := (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o) GauthierE2.P.z)
  recognized := rfl

def candidate53 : FrozenCandidate where
  programSha256 := "e636fc49ee7c5ad2f434c255d8bc459360e9e3fb4ce551ac9c093e79cdc590ec"
  tokens := [10, 10, 14, 11, 3, 11, 15, 2, 2, 3, 10, 11, 13, 10, 10, 3, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.loop2 (GauthierE2.P.addi (GauthierE2.P.push GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.Y) (GauthierE2.P.pop GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.X GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o)
  recognized := rfl

def candidate54 : FrozenCandidate where
  programSha256 := "75c54f39f9f12562f53f69a68ebdf74518d7e77c9689328b0ea8db3529c12bc2"
  tokens := [1, 2, 2, 3, 3, 10, 5, 10, 1, 10, 3, 9, 10, 5]
  program := (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X)) GauthierE2.P.X)
  recognized := rfl

def candidate55 : FrozenCandidate where
  programSha256 := "100558a6cb2ae00df76c30b0881533eee0f18cba6da1bd1c178fdd07a4524088"
  tokens := [10, 11, 3, 2, 2, 3, 10, 9, 11, 3, 10, 10, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.X)
  recognized := rfl

def candidate56 : FrozenCandidate where
  programSha256 := "975be6368879232421dd8be635610729f6478f1e10d8f6c524fbee96a8c520e8"
  tokens := [2, 2, 2, 2, 3, 11, 3, 5, 11, 3, 5, 10, 3, 10, 10, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw) GauthierE2.P.Y)) GauthierE2.P.Y)) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.X)
  recognized := rfl

def candidate57 : FrozenCandidate where
  programSha256 := "5fedb7d978591fe8c623744762daec5f8983dbeb39634f063f47abccc022e75b"
  tokens := [10, 11, 3, 10, 10, 11, 3, 10, 10, 3, 0, 9, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y) GauthierE2.P.X (GauthierE2.P.loop (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.z))
  recognized := rfl

def candidate58 : FrozenCandidate where
  programSha256 := "a39e8e8c5125edbf1d0d754e3e16f536bd200965aa362f36976f2f8f2d61f266"
  tokens := [1, 2, 3, 11, 5, 10, 3, 10, 10, 10, 5, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.Y) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X))
  recognized := rfl

def candidate59 : FrozenCandidate where
  programSha256 := "77a8721aedece68c431585da131d084664783ee5f3ef96718cffe7c38a8071ee"
  tokens := [10, 11, 5, 11, 10, 1, 2, 10, 10, 5, 5, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.Y) GauthierE2.P.Y GauthierE2.P.X GauthierE2.P.o (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X)))
  recognized := rfl

def candidate60 : FrozenCandidate where
  programSha256 := "5b2b98ef2490d5c04e7c4eddf6e591f26fa6825abfba0f97ed96340b80fbc6ed"
  tokens := [1, 2, 2, 2, 3, 5, 11, 3, 3, 10, 10, 1, 1, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.Y)) GauthierE2.P.X GauthierE2.P.X GauthierE2.P.o GauthierE2.P.o)
  recognized := rfl

def candidate61 : FrozenCandidate where
  programSha256 := "5556e03bf47ccdba1c891991ec96823c7e2cfea02deea81aad73f434d1557036"
  tokens := [10, 10, 5, 2, 11, 11, 5, 9, 11, 6, 11, 3, 10, 0, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.z)
  recognized := rfl

def candidate62 : FrozenCandidate where
  programSha256 := "8b130750b76166f3a4f0865ea410ee3ad03f8a5161e32437b0878e837fc1fe60"
  tokens := [10, 10, 5, 2, 11, 11, 5, 9, 11, 6, 11, 3, 10, 10, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.X)
  recognized := rfl

def candidate63 : FrozenCandidate where
  programSha256 := "b346bbf930c58c9b5ed6c46b15ffe46de67c4792a0b6808463599d33adb6c026"
  tokens := [10, 10, 5, 2, 11, 11, 5, 9, 11, 6, 11, 3, 10, 11, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.tw (GauthierE2.P.mult GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.Y) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.Y)
  recognized := rfl

def candidate64 : FrozenCandidate where
  programSha256 := "3fe3a9ba97bad94e2beb35519e43b6d7a66b290e54b1a8e5b7460b1368d17403"
  tokens := [2, 2, 2, 2, 3, 5, 10, 3, 5, 11, 4, 10, 10, 1, 2, 13]
  program := (GauthierE2.P.loop2 (GauthierE2.P.diff (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw)) GauthierE2.P.X)) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.X GauthierE2.P.o GauthierE2.P.tw)
  recognized := rfl

def candidate65 : FrozenCandidate where
  programSha256 := "b318894a8a060ced731960046d6544d5948c2b9c8aab61e746b9ed4c8fad127b"
  tokens := [2, 2, 10, 10, 3, 5, 10, 3, 5, 10, 3, 11, 5, 10, 1, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.X)) GauthierE2.P.X) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.o)
  recognized := rfl

def candidate66 : FrozenCandidate where
  programSha256 := "ac2195d2453e654ff4272932a577f69777d4cab39ec4fd9208de8b3adbb4c2ee"
  tokens := [1, 2, 2, 2, 3, 3, 3, 11, 5, 10, 3, 10, 2, 9]
  program := (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.Y) GauthierE2.P.X) GauthierE2.P.X GauthierE2.P.tw)
  recognized := rfl

def candidate67 : FrozenCandidate where
  programSha256 := "2411c1ec9faee89a45f5973d31f7ae0a9e0d2bd5b082aecef6a919e54059cc7f"
  tokens := [1, 2, 3, 10, 5, 10, 1, 10, 3, 9, 2, 5]
  program := (GauthierE2.P.mult (GauthierE2.P.loop (GauthierE2.P.mult (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw) GauthierE2.P.X) GauthierE2.P.X (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.X)) GauthierE2.P.tw)
  recognized := rfl

def candidate68 : FrozenCandidate where
  programSha256 := "8dec5142e11099e5f0d316d7fba8a217ade4369f15b37c2ae752b406dfbca7a6"
  tokens := [2, 11, 11, 3, 5, 10, 3, 10, 10, 3, 1, 9, 10, 4]
  program := (GauthierE2.P.diff (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.Y GauthierE2.P.Y)) GauthierE2.P.X) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.o) GauthierE2.P.X)
  recognized := rfl

def candidate69 : FrozenCandidate where
  programSha256 := "65b0812b9023f08e245b63c22a7c46034317673457fbf3a3cd63248628844424"
  tokens := [2, 10, 10, 3, 5, 2, 10, 9, 10, 3, 10, 5]
  program := (GauthierE2.P.mult (GauthierE2.P.addi (GauthierE2.P.loop (GauthierE2.P.mult GauthierE2.P.tw (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X)) GauthierE2.P.tw GauthierE2.P.X) GauthierE2.P.X) GauthierE2.P.X)
  recognized := rfl

def candidate70 : FrozenCandidate where
  programSha256 := "a1667572ab2f08624baa798f0bbc82080829280e7f2ee334bee2c4f7172238ba"
  tokens := [11, 11, 5, 1, 2, 2, 3, 3, 6, 11, 3, 10, 0, 9, 2, 6]
  program := (GauthierE2.P.divi (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi (GauthierE2.P.mult GauthierE2.P.Y GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.o (GauthierE2.P.addi GauthierE2.P.tw GauthierE2.P.tw))) GauthierE2.P.Y) GauthierE2.P.X GauthierE2.P.z) GauthierE2.P.tw)
  recognized := rfl

def candidate71 : FrozenCandidate where
  programSha256 := "d7817a02be72382b7722a97ed5cf50fa3473e61e5e2e401addc15d25823a1493"
  tokens := [11, 1, 2, 3, 6, 11, 3, 10, 10, 3, 0, 9, 10, 3]
  program := (GauthierE2.P.addi (GauthierE2.P.loop (GauthierE2.P.addi (GauthierE2.P.divi GauthierE2.P.Y (GauthierE2.P.addi GauthierE2.P.o GauthierE2.P.tw)) GauthierE2.P.Y) (GauthierE2.P.addi GauthierE2.P.X GauthierE2.P.X) GauthierE2.P.z) GauthierE2.P.X)
  recognized := rfl
def targets : List AdjudicationTarget :=
  [ { oeisId := "A002063", publishedTermCount := 24, spec := Mettapedia.Sequences.OEIS.Elementary49.A002063.spec, candidate := candidate00 }
  , { oeisId := "A002276", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A002276.spec, candidate := candidate01 }
  , { oeisId := "A002276", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A002276.spec, candidate := candidate02 }
  , { oeisId := "A002277", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A002277.spec, candidate := candidate03 }
  , { oeisId := "A002277", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A002277.spec, candidate := candidate04 }
  , { oeisId := "A002452", publishedTermCount := 23, spec := Mettapedia.Sequences.OEIS.Elementary49.A002452.spec, candidate := candidate05 }
  , { oeisId := "A002452", publishedTermCount := 23, spec := Mettapedia.Sequences.OEIS.Elementary49.A002452.spec, candidate := candidate06 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate07 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate08 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate09 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate10 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate11 }
  , { oeisId := "A003464", publishedTermCount := 22, spec := Mettapedia.Sequences.OEIS.Elementary49.A003464.spec, candidate := candidate12 }
  , { oeisId := "A008455", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A008455.spec, candidate := candidate13 }
  , { oeisId := "A008790", publishedTermCount := 18, spec := Mettapedia.Sequences.OEIS.Elementary49.A008790.spec, candidate := candidate14 }
  , { oeisId := "A009975", publishedTermCount := 17, spec := Mettapedia.Sequences.OEIS.Elementary49.A009975.spec, candidate := candidate15 }
  , { oeisId := "A009992", publishedTermCount := 16, spec := Mettapedia.Sequences.OEIS.Elementary49.A009992.spec, candidate := candidate16 }
  , { oeisId := "A010807", publishedTermCount := 15, spec := Mettapedia.Sequences.OEIS.Elementary49.A010807.spec, candidate := candidate17 }
  , { oeisId := "A011865", publishedTermCount := 65, spec := Mettapedia.Sequences.OEIS.Elementary49.A011865.spec, candidate := candidate18 }
  , { oeisId := "A013708", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A013708.spec, candidate := candidate19 }
  , { oeisId := "A013708", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A013708.spec, candidate := candidate20 }
  , { oeisId := "A013708", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A013708.spec, candidate := candidate21 }
  , { oeisId := "A013708", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A013708.spec, candidate := candidate22 }
  , { oeisId := "A013708", publishedTermCount := 21, spec := Mettapedia.Sequences.OEIS.Elementary49.A013708.spec, candidate := candidate23 }
  , { oeisId := "A013710", publishedTermCount := 18, spec := Mettapedia.Sequences.OEIS.Elementary49.A013710.spec, candidate := candidate24 }
  , { oeisId := "A014899", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A014899.spec, candidate := candidate25 }
  , { oeisId := "A014899", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A014899.spec, candidate := candidate26 }
  , { oeisId := "A014992", publishedTermCount := 18, spec := Mettapedia.Sequences.OEIS.Elementary49.A014992.spec, candidate := candidate27 }
  , { oeisId := "A016779", publishedTermCount := 36, spec := Mettapedia.Sequences.OEIS.Elementary49.A016779.spec, candidate := candidate28 }
  , { oeisId := "A016780", publishedTermCount := 31, spec := Mettapedia.Sequences.OEIS.Elementary49.A016780.spec, candidate := candidate29 }
  , { oeisId := "A016814", publishedTermCount := 44, spec := Mettapedia.Sequences.OEIS.Elementary49.A016814.spec, candidate := candidate30 }
  , { oeisId := "A022521", publishedTermCount := 35, spec := Mettapedia.Sequences.OEIS.Elementary49.A022521.spec, candidate := candidate31 }
  , { oeisId := "A024064", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A024064.spec, candidate := candidate32 }
  , { oeisId := "A028895", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A028895.spec, candidate := candidate33 }
  , { oeisId := "A028895", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A028895.spec, candidate := candidate34 }
  , { oeisId := "A028895", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A028895.spec, candidate := candidate35 }
  , { oeisId := "A033436", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A033436.spec, candidate := candidate36 }
  , { oeisId := "A033436", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A033436.spec, candidate := candidate37 }
  , { oeisId := "A036087", publishedTermCount := 18, spec := Mettapedia.Sequences.OEIS.Elementary49.A036087.spec, candidate := candidate38 }
  , { oeisId := "A047656", publishedTermCount := 15, spec := Mettapedia.Sequences.OEIS.Elementary49.A047656.spec, candidate := candidate39 }
  , { oeisId := "A053540", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A053540.spec, candidate := candidate40 }
  , { oeisId := "A053540", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A053540.spec, candidate := candidate41 }
  , { oeisId := "A057358", publishedTermCount := 75, spec := Mettapedia.Sequences.OEIS.Elementary49.A057358.spec, candidate := candidate42 }
  , { oeisId := "A057358", publishedTermCount := 75, spec := Mettapedia.Sequences.OEIS.Elementary49.A057358.spec, candidate := candidate43 }
  , { oeisId := "A064751", publishedTermCount := 23, spec := Mettapedia.Sequences.OEIS.Elementary49.A064751.spec, candidate := candidate44 }
  , { oeisId := "A070439", publishedTermCount := 101, spec := Mettapedia.Sequences.OEIS.Elementary49.A070439.spec, candidate := candidate45 }
  , { oeisId := "A070478", publishedTermCount := 96, spec := Mettapedia.Sequences.OEIS.Elementary49.A070478.spec, candidate := candidate46 }
  , { oeisId := "A070512", publishedTermCount := 101, spec := Mettapedia.Sequences.OEIS.Elementary49.A070512.spec, candidate := candidate47 }
  , { oeisId := "A085473", publishedTermCount := 47, spec := Mettapedia.Sequences.OEIS.Elementary49.A085473.spec, candidate := candidate48 }
  , { oeisId := "A089081", publishedTermCount := 11, spec := Mettapedia.Sequences.OEIS.Elementary49.A089081.spec, candidate := candidate49 }
  , { oeisId := "A099762", publishedTermCount := 30, spec := Mettapedia.Sequences.OEIS.Elementary49.A099762.spec, candidate := candidate50 }
  , { oeisId := "A102083", publishedTermCount := 45, spec := Mettapedia.Sequences.OEIS.Elementary49.A102083.spec, candidate := candidate51 }
  , { oeisId := "A102083", publishedTermCount := 45, spec := Mettapedia.Sequences.OEIS.Elementary49.A102083.spec, candidate := candidate52 }
  , { oeisId := "A102083", publishedTermCount := 45, spec := Mettapedia.Sequences.OEIS.Elementary49.A102083.spec, candidate := candidate53 }
  , { oeisId := "A116156", publishedTermCount := 20, spec := Mettapedia.Sequences.OEIS.Elementary49.A116156.spec, candidate := candidate54 }
  , { oeisId := "A132754", publishedTermCount := 46, spec := Mettapedia.Sequences.OEIS.Elementary49.A132754.spec, candidate := candidate55 }
  , { oeisId := "A140689", publishedTermCount := 42, spec := Mettapedia.Sequences.OEIS.Elementary49.A140689.spec, candidate := candidate56 }
  , { oeisId := "A147875", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A147875.spec, candidate := candidate57 }
  , { oeisId := "A147875", publishedTermCount := 48, spec := Mettapedia.Sequences.OEIS.Elementary49.A147875.spec, candidate := candidate58 }
  , { oeisId := "A155957", publishedTermCount := 13, spec := Mettapedia.Sequences.OEIS.Elementary49.A155957.spec, candidate := candidate59 }
  , { oeisId := "A168416", publishedTermCount := 57, spec := Mettapedia.Sequences.OEIS.Elementary49.A168416.spec, candidate := candidate60 }
  , { oeisId := "A190578", publishedTermCount := 28, spec := Mettapedia.Sequences.OEIS.Elementary49.A190578.spec, candidate := candidate61 }
  , { oeisId := "A190578", publishedTermCount := 28, spec := Mettapedia.Sequences.OEIS.Elementary49.A190578.spec, candidate := candidate62 }
  , { oeisId := "A190578", publishedTermCount := 28, spec := Mettapedia.Sequences.OEIS.Elementary49.A190578.spec, candidate := candidate63 }
  , { oeisId := "A194268", publishedTermCount := 45, spec := Mettapedia.Sequences.OEIS.Elementary49.A194268.spec, candidate := candidate64 }
  , { oeisId := "A196258", publishedTermCount := 15, spec := Mettapedia.Sequences.OEIS.Elementary49.A196258.spec, candidate := candidate65 }
  , { oeisId := "A209294", publishedTermCount := 40, spec := Mettapedia.Sequences.OEIS.Elementary49.A209294.spec, candidate := candidate66 }
  , { oeisId := "A212697", publishedTermCount := 26, spec := Mettapedia.Sequences.OEIS.Elementary49.A212697.spec, candidate := candidate67 }
  , { oeisId := "A236267", publishedTermCount := 46, spec := Mettapedia.Sequences.OEIS.Elementary49.A236267.spec, candidate := candidate68 }
  , { oeisId := "A244630", publishedTermCount := 43, spec := Mettapedia.Sequences.OEIS.Elementary49.A244630.spec, candidate := candidate69 }
  , { oeisId := "A249013", publishedTermCount := 59, spec := Mettapedia.Sequences.OEIS.Elementary49.A249013.spec, candidate := candidate70 }
  , { oeisId := "A343028", publishedTermCount := 72, spec := Mettapedia.Sequences.OEIS.Elementary49.A343028.spec, candidate := candidate71 }
  ]

theorem target_count : targets.length = 72 := by decide

#print axioms target_count

end Mettapedia.GSLT.LanguageDef.GauthierFrozenCandidates49
