import Lake
open Lake DSL

package «algorithms»

require mettail_core from "../batteries/mettail-core"

require gf_core from "../batteries/gf-core"

@[default_target]
lean_lib «Algorithms»

lean_exe simpleMeTTa where
  root := `Algorithms.MeTTa.Simple.Main

lean_exe gfRoundTrip where
  root := `Algorithms.GF.RoundTrip

lean_exe gfGenSig where
  root := `Algorithms.GF.GenSig

lean_exe gfGenLex where
  root := `Algorithms.GF.GenLex

lean_exe gfDemo where
  root := `Algorithms.GF.Demo

lean_exe gfEntailVerify where
  root := `Algorithms.GF.EntailmentVerifier

lean_exe gfEntailEval where
  root := `Algorithms.GF.EntailmentEval

lean_exe gfAtomDemo where
  root := `Algorithms.GF.AtomDemo

lean_exe gfEntailPoC where
  root := `Algorithms.GF.EntailmentPoC

lean_exe gfEntailEval2 where
  root := `Algorithms.GF.EntailmentEval2

lean_exe gfEntailEval3 where
  root := `Algorithms.GF.EntailmentEval3
