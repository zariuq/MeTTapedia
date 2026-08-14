import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.GSLT.LanguageDef.InferenceRelationalMeTTaRender
import Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

/-!
# Exporter: PeTTa typecheck-v2 core presentation → generated artifacts

Script (`lake env lean --run <this file> <executable.metta> <audit.metta>
[<presentation.metta>]`) emitting projections of the admitted PeTTa
typecheck-v2 GSLT root:

- the EXECUTABLE artifact — the relational clause program the sealed
  checker space loads (`lib/petta/lib_typecheck_petta_generated_v0.metta`
  in the CeTTa tree); and
- the AUDIT file — the presentation as data plus the receipt-checked
  sample derivations, replayed by the operational generic inference
  checker (`generic_inference_checker_v0`).  Replay agreement is the
  J2-soundness sample check; it does not by itself establish the full
  specialized↔LanguageDef correspondence; and
- the optional FINITE-HORN GSLT source — a proper `gslt-presentation-v1`
  consumed by CeTTa's build-time langdef tooling.  It contains the authored
  constructors, judgments, and rules, but no runtime harness or fixture rules.

Byte-identity between committed artifacts and fresh regeneration is the
gate (`cmp -s`), per the Metamath export contract.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTMeTTaExport

open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.GSLT.LanguageDef.InferenceRelationalMeTTaRender

private def executableHeader : String :=
  "; Generated from the admitted PeTTa typecheck-v2 GSLT root.\n" ++
  "; Edit the Lean source (Languages/MeTTa/PeTTa/TypeSystemGSLT.lean)\n" ++
  "; and regenerate this artifact.\n\n"

/-- Guard-consult fuel: matches the depth cutoff of the runtime
realization this artifact replaces. -/
private def fuelLiteral : String := Nat.fold 64 (fun _ _ acc => s!"(FS {acc})") "FZ"

/-- Environment bindings: the LexD-analog section.  `EnvDeclared` and
`EnvDeclaredList` read the USER space's `(: subject type)` atoms through
the ordinary `match` form (the machine resolves `&self` to the user space
during sealed-clause evaluation) and reify through the generated reifier.
Logic-free by construction: a `match`, a walker call, a unification. -/
private def envBindings : String :=
  "(= (EnvDeclared $n $rd)\n" ++
  "   (let $sd (match &self (: $n $s) $s)\n" ++
  "     (let $rd (ptg-reify-type $sd) ptg-true)))\n" ++
  "(= (EnvDeclaredList $n $rds)\n" ++
  "   (let $sds (collapse (match &self (: $n $s) $s))\n" ++
  "     (let $rds (ptg-reify-decls $n $sds) ptg-true)))\n" ++
  "(= (ptg-reify-decls $n $sds)\n" ++
  "   (if (ptg-is-empty-expr $sds) DNil\n" ++
  "       (let $sd (car-atom $sds)\n" ++
  "         (let $rest (cdr-atom $sds)\n" ++
  "           (let $rd (ptg-reify-type $sd)\n" ++
  "             (let $rrest (ptg-reify-decls $n $rest)\n" ++
  "               (DCons (Decl $n $rd) $rrest)))))))\n"

/-- The reifier, generated from the root's interface tables as DETERMINISTIC
single-clause dispatchers (clause choice enumerates every matching clause,
so a fallback clause may never overlap a table clause: each relation is
one `if`-chain).  Base names from `syntaxBaseTypeTable`, arrows from
`syntaxModeTable`, variadic union/list walkers, `TNominal` symbol
fallback, `TCtor` constructor-shape fallback. -/
private def reifier : String :=
  "(= (ptg-reify-type $t)\n" ++
  String.join (syntaxBaseTypeTable.map fun entry =>
    s!"   (if (== $t {entry.1}) {entry.2}\n") ++
  "   (if (is-expr $t)\n" ++
  "       (if (ptg-is-empty-expr $t) (TCtor ptg-empty FZ)\n" ++
  "           (ptg-reify-expr-type (car-atom $t) $t))\n" ++
  "       (TNominal $t))" ++
  String.join (syntaxBaseTypeTable.map fun _ => ")") ++ ")\n" ++
  "(= (ptg-reify-list $ts)\n" ++
  "   (if (ptg-is-empty-expr $ts) TTNil\n" ++
  "       (let $t (car-atom $ts)\n" ++
  "         (let $rest (cdr-atom $ts)\n" ++
  "           (let $rt (ptg-reify-type $t)\n" ++
  "             (let $rrest (ptg-reify-list $rest)\n" ++
  "               (TTCons $rt $rrest)))))))\n" ++
  "(= (ptg-arity $es)\n" ++
  "   (if (ptg-is-empty-expr $es) FZ\n" ++
  "       (let $rest (cdr-atom $es)\n" ++
  "         (let $k (ptg-arity $rest) (FS $k)))))\n" ++
  "(= (ptg-reify-expr-type $h $t)\n" ++
  "   (if (== $h |)\n" ++
  "       (let $ms (cdr-atom $t)\n" ++
  "         (let $rms (ptg-reify-list $ms) (TUnion $rms)))\n" ++
  "   (if (== $h List)\n" ++
  "       (let $elems (cdr-atom $t)\n" ++
  "         (let $e (car-atom $elems)\n" ++
  "           (let $rt (ptg-reify-type $e) (TList $rt))))\n" ++
  String.join (syntaxModeTable.map fun entry =>
    s!"   (if (== $h {entry.1})\n" ++
    "       (let $body (cdr-atom $t)\n" ++
    "         (let $ret (ptg-last-atom $body)\n" ++
    "           (let $args (ptg-init-atoms $body)\n" ++
    "             (let $rargs (ptg-reify-list $args)\n" ++
    "               (let $rret (ptg-reify-type $ret)\n" ++
    s!"                 (TArrow {entry.2} $rargs $rret))))))\n") ++
  "   (let $rest (cdr-atom $t)\n" ++
  "     (let $k (ptg-arity $rest) (TCtor $h $k)))" ++
  String.join (syntaxModeTable.map fun _ => ")") ++ ")))\n" ++
  "(= (ptg-last-atom $es)\n" ++
  "   (let $rest (cdr-atom $es)\n" ++
  "     (if (ptg-is-empty-expr $rest) (car-atom $es) (ptg-last-atom $rest))))\n" ++
  "(= (ptg-init-atoms $es)\n" ++
  "   (let $rest (cdr-atom $es)\n" ++
  "     (if (ptg-is-empty-expr $rest) ()\n" ++
  "         (let $h (car-atom $es)\n" ++
  "           (let $ri (ptg-init-atoms $rest) (cons-atom $h $ri))))))\n" ++
  "(= (ptg-reify-value $v)\n" ++
  "   (let $sort (ptg-literal-sort $v)\n" ++
  "     (if (== $sort ())\n" ++
  "         (if (is-expr $v) (ptg-reify-value-list $v) (VSym $v))\n" ++
  "         $sort)))\n" ++
  "(= (ptg-reify-value-list $vs)\n" ++
  "   (if (ptg-is-empty-expr $vs) VNil\n" ++
  "       (let $v (car-atom $vs)\n" ++
  "         (let $rest (cdr-atom $vs)\n" ++
  "           (let $rv (ptg-reify-value $v)\n" ++
  "             (let $rrest (ptg-reify-value-list $rest)\n" ++
  "               (VCons $rv $rrest)))))))\n" ++
  "(= (ptg-reify-value-app $v)\n" ++
  "   (if (ptg-is-empty-expr $v) (VSym ptg-empty)\n" ++
  "   (if (is-expr $v)\n" ++
  "       (let $h (car-atom $v)\n" ++
  "         (let $rest (cdr-atom $v)\n" ++
  "           (let $k (ptg-arity $rest) (VApp $h $k))))\n" ++
  "       (VSym $v))))\n"

/-- The deterministic verdict harness.  Both value reifications are
consulted (list-view and applied-head-view expose different provable
conflicts); refuted wins, then established, else undetermined.  Evidence
carries the diagnostic-class tag; the C trip plumbing assembles the
pinned message text.  Runtime derivation-evidence emission (GIC-replayable
per verdict) is a declared gap of this version. -/
private def verdictHarness : String :=
  "(= (ptg-reify-mode $m)\n" ++
  String.join (syntaxModeTable.map fun entry =>
    s!"   (if (== $m {entry.1}) {entry.2}\n") ++
  "   MPlain" ++
  String.join (syntaxModeTable.map fun _ => ")") ++ ")\n" ++
  "(= (petta-type-guard $env $v $t $mode)\n" ++
  "   (let $rt (ptg-reify-type $t)\n" ++
  "     (if (is-var $v)\n" ++
  "         (let $rm (ptg-reify-mode $mode)\n" ++
  "           (if (== (collapse (BoundnessRefuted $rm $rt)) ())\n" ++
  "               (ptg-verdict undetermined ())\n" ++
  "               (ptg-verdict refuted (ptg-unbound))))\n" ++
  "         (let $rv (ptg-reify-value $v)\n" ++
  "           (let $ra (ptg-reify-value-app $v)\n" ++
  s!"             (if (not (== (collapse (DefiniteMismatch {fuelLiteral} $rv $rt)) ()))\n" ++
  "                 (ptg-verdict refuted (ptg-mismatch))\n" ++
  s!"                 (if (not (== (collapse (DefiniteMismatch {fuelLiteral} $ra $rt)) ()))\n" ++
  "                     (ptg-verdict refuted (ptg-mismatch))\n" ++
  "                     (if (not (== (collapse (ValueHasType $rv $rt)) ()))\n" ++
  "                         (ptg-verdict established ())\n" ++
  "                         (ptg-verdict undetermined ())))))))))\n" ++
  "!(tabled (DefiniteMismatch $f $v $t))\n" ++
  "!(tabled (ValueHasType $v $t))\n"

def executable? : Option String := do
  let program ← renderProgram? guardPresentation
  some (executableHeader ++ program ++ "\n" ++ envBindings ++ "\n" ++
        reifier ++ "\n" ++ verdictHarness)

/-- Semantic-source projection for the build-time langdef pipeline.  The
guard presentation deliberately excludes the receipt-only environment
fixtures and the nonmonotone four-way runtime harness. -/
def finiteHornPresentation? : Option String :=
  Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender.renderPresentation?
    guardPresentation

/-- Fail-closed totality, structural side: every core rule satisfies
exactly the conditions under which `renderClause?` renders.  A rule
drifting outside the fragment fails the build here; the exporter's
runtime Option handling remains the last-resort refusal. -/
theorem guard_rules_all_projectable :
    guardPresentation.rules.all
      Mettapedia.GSLT.LanguageDef.InferenceRelationalMeTTaRender.projectable
      = true := by decide

def audit : String :=
  "; Generated audit projection of the PeTTa typecheck-v2 GSLT root.\n" ++
  "; Replayed by the operational generic inference checker; the sample\n" ++
  "; derivations are the same objects the Lean checkRaw receipts accept\n" ++
  "; and reject.\n\n" ++
  "!(import! &self generic_inference_checker_v0)\n\n" ++
  s!"(= (petta-core-presentation) {renderPresentation corePresentation})\n" ++
  s!"(= (petta-core-accept-goal) {renderPattern sampleAcceptGoal})\n" ++
  s!"(= (petta-core-accept-proof) {renderRawProof sampleAcceptProof})\n" ++
  s!"(= (petta-core-union-goal) {renderPattern sampleUnionGoal})\n" ++
  s!"(= (petta-core-union-proof) {renderRawProof sampleUnionProof})\n" ++
  s!"(= (petta-core-value-goal) {renderPattern sampleValueGoal})\n" ++
  s!"(= (petta-core-value-proof) {renderRawProof sampleValueProof})\n" ++
  s!"(= (petta-core-reject-goal) {renderPattern sampleRejectGoal})\n" ++
  s!"(= (petta-core-reject-proof) {renderRawProof sampleRejectProof})\n" ++
  s!"(= (petta-core-brand-goal) {renderPattern sampleBrandRejectGoal})\n" ++
  s!"(= (petta-core-brand-proof) {renderRawProof sampleBrandRejectProof})\n\n" ++
  "!(assertEqual (gic-presentation-valid (petta-core-presentation)) True)\n" ++
  "!(assertEqual (gic-check (petta-core-presentation) " ++
    "(petta-core-accept-goal) (petta-core-accept-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-core-presentation) " ++
    "(petta-core-union-goal) (petta-core-union-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-core-presentation) " ++
    "(petta-core-value-goal) (petta-core-value-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-core-presentation) " ++
    "(petta-core-reject-goal) (petta-core-reject-proof)) False)\n" ++
  "!(assertEqual (gic-check (petta-core-presentation) " ++
    "(petta-core-brand-goal) (petta-core-brand-proof)) False)\n\n" ++
  "!(PettaTypecheckCoreGICSummary 25 5 21 3 2)\n\n" ++
  "; Guard-level projection: the RECEIPT presentation (export rules plus\n" ++
  "; the three environment fixtures; the delta is theorem-pinned by\n" ++
  "; export_rules_are_receipt_prefix).  Samples are the guard module's own\n" ++
  "; checkRaw receipts: three accepted derivations (base-sort mismatch,\n" ++
  "; boundness proviso, newtype resolution through the environment) and\n" ++
  "; two rejected candidates (unplaceable-declaration veto, same-base).\n" ++
  s!"(= (petta-guard-presentation) {renderPresentation auditPresentation})\n" ++
  s!"(= (petta-guard-mismatch-goal) {renderPattern auditSampleMismatchGoal})\n" ++
  s!"(= (petta-guard-mismatch-proof) {renderRawProof auditSampleMismatchProof})\n" ++
  s!"(= (petta-guard-boundness-goal) {renderPattern auditSampleBoundnessGoal})\n" ++
  s!"(= (petta-guard-boundness-proof) {renderRawProof auditSampleBoundnessProof})\n" ++
  s!"(= (petta-guard-newtype-goal) {renderPattern auditSampleNewtypeGoal})\n" ++
  s!"(= (petta-guard-newtype-proof) {renderRawProof auditSampleNewtypeProof})\n" ++
  s!"(= (petta-guard-veto-goal) {renderPattern auditSampleVetoGoal})\n" ++
  s!"(= (petta-guard-veto-proof) {renderRawProof auditSampleVetoProof})\n" ++
  s!"(= (petta-guard-samebase-goal) {renderPattern auditSampleSameBaseGoal})\n" ++
  s!"(= (petta-guard-samebase-proof) {renderRawProof auditSampleSameBaseProof})\n\n" ++
  "!(assertEqual (gic-presentation-valid (petta-guard-presentation)) True)\n" ++
  "!(assertEqual (gic-check (petta-guard-presentation) " ++
    "(petta-guard-mismatch-goal) (petta-guard-mismatch-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-guard-presentation) " ++
    "(petta-guard-boundness-goal) (petta-guard-boundness-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-guard-presentation) " ++
    "(petta-guard-newtype-goal) (petta-guard-newtype-proof)) True)\n" ++
  "!(assertEqual (gic-check (petta-guard-presentation) " ++
    "(petta-guard-veto-goal) (petta-guard-veto-proof)) False)\n" ++
  "!(assertEqual (gic-check (petta-guard-presentation) " ++
    "(petta-guard-samebase-goal) (petta-guard-samebase-proof)) False)\n\n" ++
  "!(PettaTypecheckGuardGICSummary 43 20 75 3 2)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [executablePath, auditPath] =>
      match executable? with
      | none =>
          IO.eprintln "PeTTa typecheck core rule outside the relational fragment"
          pure 1
      | some rendered => do
          IO.FS.writeFile executablePath rendered
          IO.FS.writeFile auditPath audit
          IO.println s!"wrote {rendered.toUTF8.size} bytes to {executablePath}"
          IO.println s!"wrote {audit.toUTF8.size} bytes to {auditPath}"
          pure 0
  | [executablePath, auditPath, presentationPath] =>
      match executable?, finiteHornPresentation? with
      | none, _ =>
          IO.eprintln "PeTTa typecheck core rule outside the relational fragment"
          pure 1
      | _, none =>
          IO.eprintln "PeTTa typecheck rule outside the finite-Horn GSLT fragment"
          pure 1
      | some rendered, some presentation => do
          IO.FS.writeFile executablePath rendered
          IO.FS.writeFile auditPath audit
          IO.FS.writeFile presentationPath presentation
          IO.println s!"wrote {rendered.toUTF8.size} bytes to {executablePath}"
          IO.println s!"wrote {audit.toUTF8.size} bytes to {auditPath}"
          IO.println s!"wrote {presentation.toUTF8.size} bytes to {presentationPath}"
          pure 0
  | _ => do
      IO.eprintln
        "usage: <executable-output.metta> <audit-output.metta> [<presentation-output.metta>]"
      pure 2

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTMeTTaExport.main arguments
