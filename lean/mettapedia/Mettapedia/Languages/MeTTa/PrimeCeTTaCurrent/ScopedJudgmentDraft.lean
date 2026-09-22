import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent

/-!
# Recorded probes of an experimental scoped-judgment draft

These are dated source inspections and literal runtime observations from the
September 10 review, not an adopted language or Lean execution evidence for C.
The experimental draft and its opt baseline share a repository revision but
have different worktree sources. Neither replaces the earlier current-runtime
snapshots. The original review used existing binaries; no C rebuild, complete
correctness gate or Horn processing is asserted here.

The five probe topics retain successful beta/eta conversion and dependent-type
round trips alongside publication, routing, prefix-ownership and proof-binder
controls. An inert expression records the printed result, not a decoded proof
of a particular residual status. Rejection of a submitted proof is not falsity
of its proposition. Source membership and the arithmetic/string checks below
certify bookkeeping only, not the observations or a C-to-Lean correspondence.

Requirement IDs are links for the existing comparison layer, not another
requirement ledger. They are intentionally not resolved by importing candidate
theory into this observation leaf. The source report is
`reports/nik/2026-09-10-codex-draft2-probe-review.md`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraft

def reviewDocument : String :=
  "reports/nik/2026-09-10-codex-draft2-probe-review.md"

def experimentalProfile : String :=
  "CeTTa experimental scoped-judgment draft2, 2026-09-10, uncommitted additions"

def optBaseProfile : String :=
  "CeTTa opt baseline reviewed 2026-09-10, without scoped-judgment draft additions"

def optBaseSource : InspectedSourceSnapshot where
  date := "2026-09-10"
  repositoryRevision := "681ac7ea9e259c5ecd35755e87449c62ced56039"
  files := [
    ⟨"src/eval.c", "21184df86e8ebdb0a14a916d151cc029b9e0dbaa14f338e8b9e125477bebfa02"⟩,
    ⟨"src/prime_regular_pattern.c", "b8bce60106249fcc63bc5323a6d210c95707d8f36a188b91cfaacfa5deec2135"⟩,
    ⟨"src/prime_regular_kernel.c", "e444ec9d1c0b01e31e036609aee4fe5bc4ea21a78c109ff3781ba3f77afdd581"⟩,
    ⟨"src/prime_semantics.c", "037466ef054adc6791033cf0560dfd72702cdce01380e22240e6e5f59b85e52b"⟩]

def experimentalSource : InspectedSourceSnapshot where
  date := "2026-09-10"
  repositoryRevision := "681ac7ea9e259c5ecd35755e87449c62ced56039"
  files := [
    ⟨"src/prime_scoped_judgments.c", "e66ac4b352a961c331a7e7d43a965fa20b17e90b00a39da3fa2938422638c1c7"⟩,
    ⟨"src/eval.c", "3abbb958f5ca34fecb80a9e1d8f7cac2e5aab54ebfe72b8b2d7c11636b631f4f"⟩,
    ⟨"src/prime_regular_pattern.c", "b8bce60106249fcc63bc5323a6d210c95707d8f36a188b91cfaacfa5deec2135"⟩,
    ⟨"src/prime_regular_kernel.c", "e444ec9d1c0b01e31e036609aee4fe5bc4ea21a78c109ff3781ba3f77afdd581"⟩,
    ⟨"src/prime_semantics.c", "037466ef054adc6791033cf0560dfd72702cdce01380e22240e6e5f59b85e52b"⟩]

/-! ## Inspected source surfaces -/

def publicationSource : SourceObservation experimentalSource where
  source := ⟨"src/prime_scoped_judgments.c",
    "e66ac4b352a961c331a7e7d43a965fa20b17e90b00a39da3fa2938422638c1c7"⟩
  sourceInSnapshot := by decide
  symbols := ["sj_known_proposition", "sj_set_proves", "set:axiom", "set:theorem"]
  observation := "Both publication branches return SetPublish with a name and proposition. The theorem branch checks its submitted proof first. Known-proposition lookup reads user-space set:known entries before the seeded entries. The evaluator publishes the same set:known shape for both origins."
  limitation := "Current-space lookup does not retain the theorem's proof, assumptions, origin or checking revision. Treating every known entry as a fresh axiom is different from checked theorem reuse; this inspection is not a consistency or authorization theorem."

def publicationDispatchSource : SourceObservation experimentalSource where
  source := ⟨"src/eval.c", "3abbb958f5ca34fecb80a9e1d8f7cac2e5aab54ebfe72b8b2d7c11636b631f4f"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_public_eval_scoped_judgment", "SetPublish", "set:known"]
  observation := "The scoped-judgment evaluator turns SetPublish into a three-field set:known atom in the selected space. It does not publish the submitted derivation or its dependencies in that atom."
  limitation := "The common stored shape cannot by itself distinguish explicit assumptions from theorems relative to a retained theory. A receipt hash without the corresponding meaning and dependency contract would not establish reuse."

def conversionSource : SourceObservation optBaseSource where
  source := ⟨"src/prime_regular_pattern.c",
    "b8bce60106249fcc63bc5323a6d210c95707d8f36a188b91cfaacfa5deec2135"⟩
  sourceInSnapshot := by decide
  symbols := ["regular_term_lower_lambda", "typed-lambda-awaits-typed-pattern-authority"]
  observation := "The declared surface elaborator classifies annotation-bearing lambda binders as out of class. An unannotated lambda can be checked against a supplied domain but cannot always synthesize that domain. The same file digest occurs in the experimental snapshot."
  limitation := "A False from another equality fallback on this unsupported spelling does not demonstrate that beta is absent from the native conversion service. Ownership, admitted syntax and fallback must be qualified separately."

def conversionKernelSource : SourceObservation optBaseSource where
  source := ⟨"src/prime_regular_kernel.c",
    "e444ec9d1c0b01e31e036609aee4fe5bc4ea21a78c109ff3781ba3f77afdd581"⟩
  sourceInSnapshot := by decide
  symbols := ["regular_normalize", "beta-substitution-failed", "eta-lowering-failed"]
  observation := "The regular normalizer contains beta substitution and eta lowering. The reviewed intrinsic and scoped public spellings have successful beta/eta controls on both binaries. The kernel source digest is shared by these two inspected snapshots."
  limitation := "These source branches and recorded examples neither prove all-input conversion correctness nor identify the conversion profiles of every hosted theory. Definitions and qualified delta remain separate obligations."

def conversionRoutingSource : SourceObservation optBaseSource where
  source := ⟨"src/prime_semantics.c",
    "037466ef054adc6791033cf0560dfd72702cdce01380e22240e6e5f59b85e52b"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_convert", "prime_convert_declared_regular"]
  observation := "Public conversion can continue after the declared elaboration fails to own an operand, reaching the legacy comparison path. The annotated surface probe and its reverse return False on both reviewed binaries, while supported native beta/eta spellings return True."
  limitation := "This is an ownership/fallback observation, not a proof that the unsupported surface term has been admitted and refuted by the intended candidate conversion. Adding another beta reducer would not alone qualify this boundary."

def roundtripSource : SourceObservation optBaseSource where
  source := ⟨"src/prime_regular_pattern.c",
    "b8bce60106249fcc63bc5323a6d210c95707d8f36a188b91cfaacfa5deec2135"⟩
  sourceInSnapshot := by decide
  symbols := ["regular_term_lower_arrow_rec", "regular_term_quote_intrinsic_rec"]
  observation := "Anonymous arrow binders retain dependency through idx. The recorded type:of result forms, checks the original all declaration and compares equal to the named telescope; feeding the actual result back through let also forms and checks on both binaries."
  limitation := "The example is a concrete level instance, not recovery of the complete polymorphic schema or a general codec theorem. The printed index is an ergonomic issue, not demonstrated loss of this dependency."

def prefixSource : SourceObservation experimentalSource where
  source := ⟨"src/prime_scoped_judgments.c",
    "e66ac4b352a961c331a7e7d43a965fa20b17e90b00a39da3fa2938422638c1c7"⟩
  sourceInSnapshot := by decide
  symbols := ["prime_scoped_judgment_is_head", "prime_scoped_judgment_judge"]
  observation := "The ownership test claims every set: or lang: prefix before ordinary evaluation, not only the listed judgment names. The draft leaves user-defined prefixed calls inert where opt-base rewrites them; an unprefixed control rewrites on both."
  limitation := "Prefix interception is a concrete extensibility policy, not a necessity of scoped mathematical judgments. Neither unconditional fallback nor accidental reservation of an entire prefix is a proved ownership contract."

def higherOrderSource : SourceObservation experimentalSource where
  source := ⟨"src/prime_scoped_judgments.c",
    "e66ac4b352a961c331a7e7d43a965fa20b17e90b00a39da3fa2938422638c1c7"⟩
  sourceInSnapshot := by decide
  symbols := ["sj_check", "sj_synth", "sj_elaborate_closed", "pf:all-intro", "pf:all-elim"]
  observation := "Universal proof introduction/elimination recognizes all_set rather than all_prop. Elimination elaborates its submitted witness as a closed set term. The recorded all_prop proposition checks but its introduction proof is rejected; reconstructing PowerI with the surrounding bound witness remains inert."
  limitation := "False rejects that submitted proof under this implemented grammar, not its proposition. The syntactic simple-fragment recognizer also accepts an ordinary arrow but declines a named constant-family binder; this is not complete semantic descent. No stronger universe, impredicative Prop, K or host selection follows."

def experimentalObservations : List (SourceObservation experimentalSource) :=
  [publicationSource, publicationDispatchSource, prefixSource, higherOrderSource]

def optBaseObservations : List (SourceObservation optBaseSource) :=
  [conversionSource, conversionKernelSource, conversionRoutingSource, roundtripSource]

/-! ## Literal recorded runs, without an execution-correctness field -/

/-- Artifact names are review-local identifiers. Digests identify the original
files; commands below are one expression per output, not a byte-for-byte copy
of their whitespace/comments. An absent executable digest is explicit missing
historical provenance, never inferred from a source revision. -/
structure RecordedRun where
  profile : String
  sourceSnapshot : InspectedSourceSnapshot
  executable : Option SourceDigest
  input : SourceDigest
  transcript : SourceDigest
  setup : List String
  commands : List String
  outputs : List String

def draftExecutable : SourceDigest :=
  ⟨"cetta", "acdb8aabde1d599205d8dd0f9cc6321c96c1910eefb9124735d9b54f2745bc95"⟩

def proofCommands : List String := [
  "!(set:formed (-> set set))",
  "!(set:formed (-> (x : set) set))",
  "!(set:check (all_prop (lam p (imp p p))) prop)",
  "!(set:proves (pf:all-intro (pf:imp-intro (pf:hyp 0))) (all_prop (lam p (imp p p))))",
  "!(set:proves (pf:known PowerI) (all_set (lam x (In x (Power x)))))",
  "!(set:proves (pf:all-intro (pf:all-elim (pf:known PowerI) (idx 0))) (all_set (lam x (In x (Power x)))))",
  "!(bind! &review (new-space))",
  "!(set:axiom &review premise (In Empty Empty))",
  "!(set:theorem &review derived (In Empty Empty) (pf:known premise))",
  "!(match &review (set:known derived $p) $p)",
  "!(remove-atom &review (set:known premise (In Empty Empty)))",
  "!(set:proves &review (pf:known premise) (In Empty Empty))",
  "!(set:proves &review (pf:known derived) (In Empty Empty))",
  "!(bind! &raw (new-space))",
  "!(add-atom &raw (set:known directly-inserted Falsum))",
  "!(set:proves &raw (pf:known directly-inserted) Falsum)",
  "!(bind! &shadow (new-space))",
  "!(set:axiom &shadow PowerI Falsum)",
  "!(set:proves &shadow (pf:known PowerI) Falsum)",
  "!(set:proves &shadow (pf:known PowerI) (all_set (lam x (In x (Power x)))))"]

def draftProofRun : RecordedRun where
  profile := experimentalProfile
  sourceSnapshot := experimentalSource
  executable := some draftExecutable
  input := ⟨"prime-draft-review-20260910.metta",
    "62e805ed9df4e79ee017fd0085e960f227982cea44e8dcd74e9fba2f3551bce1"⟩
  transcript := ⟨"prime-draft-review-20260910-draft-proof.out",
    "c55af675143ede4320529847f1330e838a3e1c680e4bb123d1613bd559871a6f"⟩
  setup := []
  commands := proofCommands
  outputs := ["[True]", "[(set:formed (-> (x : set) set))]", "[True]", "[False]", "[True]",
    "[(set:proves (pf:all-intro (pf:all-elim (pf:known PowerI) (idx 0))) (all_set (lam x (In x (Power x)))))]",
    "[()]", "[premise]", "[derived]", "[(In Empty Empty)]", "[()]",
    "[(set:proves &review (pf:known premise) (In Empty Empty))]", "[True]",
    "[()]", "[()]", "[True]", "[()]", "[PowerI]", "[True]", "[False]"]

def conversionCommands : List String := [
  "!(type:eq (App (Lam (Pi U0 U0) (idx 0)) (Lam U0 (idx 0))) (Lam U0 (idx 0)))",
  "!(type:eq (Lam (Pi U0 U0) (Lam U0 (App (idx 1) (idx 0)))) (Lam (Pi U0 U0) (idx 0)))",
  "!(type:eq U0 (Pi U0 U0))",
  "!(type:eq (PrimeScoped (PrimeCtxCons U0 PrimeCtxNil) (App (Lam U0 (idx 0)) (idx 0))) (PrimeScoped (PrimeCtxCons U0 PrimeCtxNil) (idx 0)))",
  "!(type:eq (PrimeScoped (PrimeCtxCons (Pi U0 U0) PrimeCtxNil) (Lam U0 (App (idx 1) (idx 0)))) (PrimeScoped (PrimeCtxCons (Pi U0 U0) PrimeCtxNil) (idx 0)))",
  "!(bind! &review (new-space))",
  "!(add-atom &review (: set (u 0)))",
  "!(add-atom &review (: Empty set))",
  "!(add-atom &review (: Power (-> set set)))",
  "!(type:eq &review ((lam (x : set) (Power x)) Empty) (Power Empty))",
  "!(type:eq &review (Power Empty) ((lam (x : set) (Power x)) Empty))",
  "!(type:check &review (lam x (Power x)) (-> set set))",
  "!(type:check &review (lam (x : set) (Power x)) (-> set set))",
  "!(type:eq &review ((lam x (Power x)) Empty) (Power Empty))"]

def conversionOutputs : List String := [
  "[True]", "[True]", "[False]", "[True]", "[True]",
  "[()]", "[()]", "[()]", "[()]", "[False]", "[False]", "[True]",
  "[(type:check &review (lam (x : set) (Power x)) (-> set set))]",
  "[(type:eq &review ((lam x (Power x)) Empty) (Power Empty))]"]

def draftConversionRun : RecordedRun where
  profile := experimentalProfile
  sourceSnapshot := experimentalSource
  executable := some draftExecutable
  input := ⟨"prime-draft-conversion-review-20260910.metta",
    "d94f520305fc1a54c988b4a12c931c521a237c955a7ec426f317f2653d3e143f"⟩
  transcript := ⟨"prime-draft-review-20260910-draft-conversion.out",
    "55d55fe3a2547e12340a4b426ebe7feb6bbedfaf78404e7a56baf26bbec2fe79"⟩
  setup := []
  commands := conversionCommands
  outputs := conversionOutputs

/-- The original review did not pin the opt-base executable digest. Its
literal transcript remains recorded, with that limitation visible. -/
def optBaseConversionRun : RecordedRun where
  profile := optBaseProfile
  sourceSnapshot := optBaseSource
  executable := none
  input := ⟨"prime-draft-conversion-review-20260910.metta",
    "d94f520305fc1a54c988b4a12c931c521a237c955a7ec426f317f2653d3e143f"⟩
  transcript := ⟨"prime-draft-review-20260910-base-conversion.out",
    "55d55fe3a2547e12340a4b426ebe7feb6bbedfaf78404e7a56baf26bbec2fe79"⟩
  setup := []
  commands := conversionCommands
  outputs := conversionOutputs

/-- The first three definitions precede the evaluated expressions. Retaining
this setup is essential to interpreting the prefix-interception control. -/
def interfaceDefinitions : List String := [
  "(= (ordinary-operation $x) (Wrapped $x))",
  "(= (set:review-operation $x) (Wrapped $x))",
  "(= (lang:review-operation $x) (Wrapped $x))"]

def interfaceCommands : List String := [
  "!(ordinary-operation A)", "!(set:review-operation A)", "!(lang:review-operation A)",
  "!(bind! &poly (new-space))",
  "!(add-atom &poly (: set (u 0)))",
  "!(add-atom &poly (: prop (u 0)))",
  "!(add-atom &poly (: all (-> (A : (u $l)) (-> (-> A prop) prop))))",
  "!(type:of &poly all)",
  "!(type:formed &poly (-> (u 0) (-> (-> (idx 0) prop) prop)))",
  "!(type:check &poly all (-> (u 0) (-> (-> (idx 0) prop) prop)))",
  "!(type:eq &poly (-> (u 0) (-> (-> (idx 0) prop) prop)) (-> (A : (u 0)) (-> (-> A prop) prop)))",
  "!(let $ty (type:of &poly all) (type:formed &poly $ty))",
  "!(let $ty (type:of &poly all) (type:check &poly all $ty))"]

def roundtripOutputs : List String := [
  "[()]", "[()]", "[()]", "[()]",
  "[(-> (u 0) (-> (-> (idx 0) prop) prop))]",
  "[True]", "[True]", "[True]", "[True]", "[True]"]

def draftInterfaceRun : RecordedRun where
  profile := experimentalProfile
  sourceSnapshot := experimentalSource
  executable := some draftExecutable
  input := ⟨"prime-draft-interface-review-20260910.metta",
    "62204ab1b346431e97af02f49b0081891a92a7de93355e444bd9821b9c996af2"⟩
  transcript := ⟨"prime-draft-review-20260910-draft-interface.out",
    "350e2324238b4cb33c9eea7c3fa343623dcb552bbfa38fda8b4f811709117de7"⟩
  setup := interfaceDefinitions
  commands := interfaceCommands
  outputs := ["[(Wrapped A)]", "[(set:review-operation A)]", "[(lang:review-operation A)]"] ++
    roundtripOutputs

def optBaseInterfaceRun : RecordedRun where
  profile := optBaseProfile
  sourceSnapshot := optBaseSource
  executable := none
  input := ⟨"prime-draft-interface-review-20260910.metta",
    "62204ab1b346431e97af02f49b0081891a92a7de93355e444bd9821b9c996af2"⟩
  transcript := ⟨"prime-draft-review-20260910-base-interface.out",
    "ceabe4207fc553820f45099b353c15cd3681437d30b58c96ea313280c4cc44a3"⟩
  setup := interfaceDefinitions
  commands := interfaceCommands
  outputs := ["[(Wrapped A)]", "[(Wrapped A)]", "[(Wrapped A)]"] ++ roundtripOutputs

def recordedRuns : List RecordedRun :=
  [draftProofRun, draftConversionRun, optBaseConversionRun, draftInterfaceRun, optBaseInterfaceRun]

/-! ## Five review topics for the existing comparison layer -/

/-- This groups inspected prose, recorded runs and open contract questions.
There is no qualification, selection or completion field. -/
structure ReviewedProbe where
  title : String
  sources : List ((snapshot : InspectedSourceSnapshot) × SourceObservation snapshot)
  runs : List RecordedRun
  requirementIds : List String
  contractQuestion : String

def publication : ReviewedProbe where
  title := "Publication retains a conclusion but loses its justification"
  sources := [⟨experimentalSource, publicationSource⟩, ⟨experimentalSource, publicationDispatchSource⟩]
  runs := [draftProofRun]
  requirementIds := ["INV-TT-002", "INV-TT-003", "REQ-VIEWS-001", "REQ-NIK-001", "KG2", "KG6", "KG7", "KG9"]
  contractQuestion := "Which artifact distinguishes an explicit assumption from a theorem of a retained theory, and which dependencies authorize live reuse? Test removed used premises, direct known-atom insertion and changed seeded-name lookup. Retain proof syntax for learning without requiring every application view to print it; historical validity is not automatic current authorization."

def conversionRouting : ReviewedProbe where
  title := "Supported beta/eta versus unsupported surface fallback"
  sources := [⟨optBaseSource, conversionSource⟩, ⟨optBaseSource, conversionKernelSource⟩,
    ⟨optBaseSource, conversionRoutingSource⟩]
  runs := [draftConversionRun, optBaseConversionRun]
  requirementIds := ["INV-TT-002", "INV-TT-003", "INV-TT-004", "KG4", "KG7"]
  contractQuestion := "Which service owns each input spelling, and when may another service answer after elaboration declines? Preserve supported beta/eta and distinct-form controls while making unsupported syntax, evidence rejection and resource exhaustion explicit. Share conversion only through a declared profile and correspondence, not one forced global relation."

def dependentRoundtrip : ReviewedProbe where
  title := "The quoted dependent instance successfully returns through checking"
  sources := [⟨optBaseSource, roundtripSource⟩]
  runs := [draftInterfaceRun, optBaseInterfaceRun]
  requirementIds := ["INV-TT-001", "INV-TT-004", "INV-TT-006", "REQ-UNIFORM-001", "KG1", "KG9"]
  contractQuestion := "Which scope-indexed quotation/elaboration laws retain the actual type, environment and complete polymorphic schema? Preserve this successful anonymous-index round trip. One checked level instance is neither general schema recovery nor an argument that dependency was erased."

def prefixOwnership : ReviewedProbe where
  title := "Experimental prefix interception changes ordinary user definitions"
  sources := [⟨experimentalSource, prefixSource⟩]
  runs := [draftInterfaceRun, optBaseInterfaceRun]
  requirementIds := ["INV-TT-002", "INV-TT-004", "KG3", "KG7", "KG8", "KG9"]
  contractQuestion := "Is ownership declared per registered operation, per admitted environment, or by an explicitly reserved namespace? Specify fallback for unowned names without reinterpreting failed owned judgments. The tested overlay/prefix convention is an experimental policy, not a foundation selected by the namespace."

def higherOrderBinding : ReviewedProbe where
  title := "Proposition formation, submitted proof rules and open witnesses differ"
  sources := [⟨experimentalSource, higherOrderSource⟩]
  runs := [draftProofRun]
  requirementIds := ["INV-TT-002", "INV-TT-003", "REQ-UNIFORM-001", "REQ-NIK-001", "KG1", "KG3", "KG8", "KG9"]
  contractQuestion := "Which universal introduction/elimination rules and open native witnesses are admitted by this exact proof grammar? Distinguish rejected evidence from a false proposition and a syntactic fragment test from semantic descent. Compare qualified proof-family, guest-proof and proposition-profile interpretations without selecting an impredicative sort, K/UIP or Megalodon from these implementation limits."

def reviewedProbes : List ReviewedProbe :=
  [publication, conversionRouting, dependentRoundtrip, prefixOwnership, higherOrderBinding]

/-! ## Bookkeeping checks only, not proofs of C behavior -/

theorem five_review_topics : reviewedProbes.length = 5 := by decide

theorem recorded_run_lengths :
    recordedRuns.map (fun run => (run.commands.length, run.outputs.length)) =
      [(20, 20), (14, 14), (14, 14), (13, 13), (13, 13)] := by decide

theorem recorded_conversion_controls :
    draftConversionRun.outputs.take 5 = ["[True]", "[True]", "[False]", "[True]", "[True]"] ∧
    optBaseConversionRun.outputs = draftConversionRun.outputs ∧
    (draftConversionRun.outputs.drop 9).take 3 = ["[False]", "[False]", "[True]"] := by decide

theorem recorded_roundtrip_controls :
    draftInterfaceRun.outputs.drop 8 = ["[True]", "[True]", "[True]", "[True]", "[True]"] ∧
    optBaseInterfaceRun.outputs.drop 3 = draftInterfaceRun.outputs.drop 3 := by decide

theorem recorded_prefix_difference :
    optBaseInterfaceRun.outputs.take 3 = ["[(Wrapped A)]", "[(Wrapped A)]", "[(Wrapped A)]"] ∧
    draftInterfaceRun.outputs.take 3 =
      ["[(Wrapped A)]", "[(set:review-operation A)]", "[(lang:review-operation A)]"] := by decide

theorem recorded_publication_controls :
    (draftProofRun.outputs.drop 11).take 2 =
      ["[(set:proves &review (pf:known premise) (In Empty Empty))]", "[True]"] ∧
    draftProofRun.outputs[15]? = some "[True]" ∧
    draftProofRun.outputs.drop 18 = ["[True]", "[False]"] := by decide

theorem recorded_proof_boundary :
    (draftProofRun.outputs.drop 2).take 3 = ["[True]", "[False]", "[True]"] ∧
    draftProofRun.outputs[5]? = some
      "[(set:proves (pf:all-intro (pf:all-elim (pf:known PowerI) (idx 0))) (all_set (lam x (In x (Power x)))))]" := by decide

theorem profiles_remain_distinct : experimentalProfile ≠ optBaseProfile := by decide

#print axioms recorded_run_lengths
#print axioms recorded_conversion_controls
#print axioms recorded_publication_controls
#print axioms recorded_proof_boundary

end Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraft
