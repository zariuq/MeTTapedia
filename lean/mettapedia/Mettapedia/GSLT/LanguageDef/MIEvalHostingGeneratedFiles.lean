import Mettapedia.GSLT.LanguageDef.MIEvalHosting

open Mettapedia.GSLT.LanguageDef.MIEvalHosting

def mettaAddGeneratedKernelSignatureFile : String :=
  "; =============================================================================\n" ++
  "; kernel_signature_metta_add_generated_v0.metta\n" ++
  ";\n" ++
  "; Classification: derived/generated.\n" ++
  ";\n" ++
  "; Generated from addDeclsKernelReachabilitySig via the generic LF-signature\n" ++
  "; renderer.  This file compares the generated signature expression with the\n" ++
  "; kernel fixture used by the proof-term checks; it does not define a checker\n" ++
  "; and does not validate traces.\n" ++
  "; =============================================================================\n\n" ++
  "!(import! &self kernel_signature_metta_add_v0)\n\n" ++
  "(= (ma-generated-metta-add-sig)\n" ++
  addDeclsKernelReachabilitySigMettaExpr ++
  ")\n\n" ++
  "; petta_skip_next\n" ++
  "!(assertEqual (ma-generated-metta-add-sig) (ma-metta-add-sig))\n" ++
  "!(assertEqual (sig-has-name MeTTaAdd:rewrite:add-s (ma-generated-metta-add-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaAdd:rewrite:add-z (ma-generated-metta-add-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaAdd:reduces-apply-head (ma-generated-metta-add-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaAdd:reduces-apply-second (ma-generated-metta-add-sig)) True)\n" ++
  "!(assertEqual (sig-has-name __ldMultiBinder (ma-generated-metta-add-sig)) False)\n" ++
  "!(assertEqual (sig-admitted (ma-generated-metta-add-sig)) True)\n"

def mettaRevGeneratedKernelSignatureFile : String :=
  "; =============================================================================\n" ++
  "; kernel_signature_metta_rev_generated_v0.metta\n" ++
  ";\n" ++
  "; Classification: derived/generated.\n" ++
  ";\n" ++
  "; Generated from revDeclsKernelReachabilitySig via the generic LF-signature\n" ++
  "; renderer.  This is the reverse-table side of the one-table bridge: the\n" ++
  "; self-interpreter table, LanguageDef adapter, and kernel reachability\n" ++
  "; signature share the same source declarations.  This file does not define a\n" ++
  "; checker and does not validate traces.\n" ++
  "; =============================================================================\n\n" ++
  "!(import! &self kernel_signature_lf_v0)\n\n" ++
  "(= (mr-generated-metta-rev-sig)\n" ++
  revDeclsKernelReachabilitySigMettaExpr ++
  ")\n\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:rewrite:append-nil (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:rewrite:append-cons (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:rewrite:rev-nil (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:rewrite:rev-cons (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:reduces-apply-head (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name MeTTaRev:reduces-apply-second (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name name:Z (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name name:S (mr-generated-metta-rev-sig)) True)\n" ++
  "!(assertEqual (sig-has-name __ldMultiBinder (mr-generated-metta-rev-sig)) False)\n" ++
  "!(assertEqual (sig-admitted (mr-generated-metta-rev-sig)) True)\n"
