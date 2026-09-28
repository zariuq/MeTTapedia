import Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceAdmission

/-!
# Selected source-to-generated PeTTa syntax

This executable structural fold covers the ordinary, functional-mode branch
used by the authored trie, reversal and declaration collector. It computes
actual dollar-variable templates, worker calls, result tuples, nested `let`
and `quote` forms on the existing S-expression carrier.

The selected input/output modes are explicit source contracts, not inferred
NativeTypes. The finite artifact correspondence below checks this branch
against independently generated equations. It does not prove the native mode
analysis, arbitrary C emission, byte reading, or PeTTa execution.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Source Rewrite)
open PlainBnfCollectorSourceExecution (mode?)
open PlainBnfCollectorSourceAdmission (indexSource discoverySource)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-- The selected native emitter maps source schema `?name` to `$name`.
The isolated `?` remains an ordinary atom; `?_` becomes the target wildcard. -/
def variableToken (token : String) : String :=
  match token.toList with
  | '?' :: next :: rest => String.ofList ('$' :: next :: rest)
  | _ => token

mutual
  /-- Render source templates structurally. This does not visit substituted
  runtime values, so it is not an evaluator or a payload translation. -/
  def sourceTerm? : SExpr → Option SExpr
    | .atom token => some (.atom (variableToken token))
    | .list [.atom "metta-nullary", .atom token] =>
        some (.list [.atom (variableToken token)])
    | .list [] => none
    | .list terms => SExpr.list <$> sourceTerms? terms

  def sourceTerms? : List SExpr → Option (List SExpr)
    | [] => some []
    | term :: terms => do
        return (← sourceTerm? term) :: (← sourceTerms? terms)
end

def modeBits (inputs outputs : Nat) : String :=
  String.ofList (List.replicate inputs '1' ++ List.replicate outputs '0')

def workerName (relation : String) (inputs outputs : Nat) : String :=
  "gslt:fn:" ++ relation ++ ":" ++ modeBits inputs outputs

def resultTag (relation : String) (inputs outputs : Nat) : String :=
  "gslt:result:" ++ relation ++ ":" ++ modeBits inputs outputs

/-- Exact arity checks prevent truncating a malformed relation application. -/
def workerCall? : SExpr → Option SExpr
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length != inputs + outputs then none else do
        let rendered ← sourceTerms? (arguments.take inputs)
        return .list (.atom (workerName relation inputs outputs) :: rendered)
  | _ => none

def resultTuple? : SExpr → Option SExpr
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length != inputs + outputs then none else do
        let rendered ← sourceTerms? (arguments.drop inputs)
        if outputs = 0 then return .atom (resultTag relation inputs outputs)
        else return .list (.atom (resultTag relation inputs outputs) :: rendered)
  | _ => none

def quote (value : SExpr) : SExpr := .list [.atom "quote", value]

def letTerm (pattern value continuation : SExpr) : SExpr :=
  .list [.atom "let", pattern, value, continuation]

/-- The sole unprojected premise in this selected family is the actual
two-argument `different` provider call; unknown relations fail closed. -/
def premise? (source continuation : SExpr) : Option SExpr :=
  match source with
  | .list [.atom "different", _, _] => do
      let rendered ← sourceTerm? source
      return letTerm (.atom "$_") (.list [.atom "gslt:different", rendered]) continuation
  | _ => do
      let result ← resultTuple? source
      let call ← workerCall? source
      return letTerm result call continuation

/-- Ordered source premises become outer-to-inner target `let` forms. -/
def lets? : List SExpr → SExpr → Option SExpr
  | [], continuation => some continuation
  | premise :: premises, final => do
      let continuation ← lets? premises final
      premise? premise continuation

def body? (premises : List SExpr) (result : SExpr) : Option SExpr :=
  lets? premises (quote result)

/-- This is the ordinary-head/functional-mode emission branch, not a claim
that arbitrary source patterns can occur in PeTTa evaluation-position heads. -/
def generatedEquation? (source : Rewrite) : Option SExpr := do
  let head ← workerCall? source.head
  let result ← resultTuple? source.head
  let body ← body? source.body result
  return .list [.atom "=", head, body]

def generatedEquations? : List Rewrite → Option (List SExpr)
  | [] => some []
  | row :: rows => do
      return (← generatedEquation? row) :: (← generatedEquations? rows)

@[simp] theorem sourceTerm_atom (token : String) :
    sourceTerm? (.atom token) = some (.atom (variableToken token)) := rfl

@[simp] theorem sourceTerm_nullary (token : String) :
    sourceTerm? (.list [.atom "metta-nullary", .atom token]) =
      some (.list [.atom (variableToken token)]) := rfl

@[simp] theorem body_nil (result : SExpr) :
    body? [] result = some (quote result) := rfl

theorem body_cons (premise : SExpr) (premises : List SExpr) (result : SExpr) :
    body? (premise :: premises) result =
      (body? premises result).bind (premise? premise) := rfl

/-- Splitting a source premise list only splits the structural fold; it does
not reverse its order or discard a failed translation. -/
theorem lets_append (left right : List SExpr) (continuation : SExpr) :
    lets? (left ++ right) continuation =
      (lets? right continuation).bind (lets? left) := by
  induction left with
  | nil => simp [lets?]
  | cons premise premises ih =>
      simp only [List.cons_append, lets?, ih]
      cases rest : lets? right continuation <;> rfl

theorem generatedEquations_append (left right : List Rewrite) :
    generatedEquations? (left ++ right) =
      (do return (← generatedEquations? left) ++ (← generatedEquations? right)) := by
  induction left with
  | nil => simp [generatedEquations?]
  | cons row rows ih =>
      cases first : generatedEquation? row <;> simp [generatedEquations?, first, ih]
      cases rest : generatedEquations? rows <;> cases last : generatedEquations? right <;> simp

/-- Syntax emission preserves repeated source occurrences, even when their
generated equations are equal. Semideterminism is a separate obligation. -/
theorem repeated_generatedEquation {row : Rewrite} {generated : SExpr}
    (emitted : generatedEquation? row = some generated) :
    generatedEquations? [row, row] = some [generated, generated] := by
  simp [generatedEquations?, emitted]

theorem generatedEquations_length {rows : List Rewrite} {generated : List SExpr}
    (emitted : generatedEquations? rows = some generated) : generated.length = rows.length := by
  induction rows generalizing generated with
  | nil => simpa [generatedEquations?] using emitted.symm
  | cons row rows ih =>
      cases first : generatedEquation? row with
      | none => simp [generatedEquations?, first] at emitted
      | some head =>
          cases rest : generatedEquations? rows with
          | none => simp [generatedEquations?, first, rest] at emitted
          | some tail =>
              have same : head :: tail = generated := by
                simpa [generatedEquations?, first, rest] using emitted
              subst generated
              simp [ih rest]

theorem generatedEquations_getElem? {rows : List Rewrite} {generated : List SExpr}
    (emitted : generatedEquations? rows = some generated) (index : Nat) :
    generated[index]? = rows[index]?.bind generatedEquation? := by
  induction rows generalizing generated index with
  | nil =>
      have same : generated = [] := by simpa [generatedEquations?] using emitted.symm
      subst generated
      simp
  | cons row rows ih =>
      cases first : generatedEquation? row with
      | none => simp [generatedEquations?, first] at emitted
      | some head =>
          cases rest : generatedEquations? rows with
          | none => simp [generatedEquations?, first, rest] at emitted
          | some tail =>
              have same : head :: tail = generated := by
                simpa [generatedEquations?, first, rest] using emitted
              subst generated
              cases index with
              | zero => simpa using first.symm
              | succ index => simpa using ih rest index

/-- The whole independent native compiler output, including declarations,
providers and entry wrappers. The reader preserves its physical row starts. -/
def generatedProgram : List (Nat × SExpr) :=
  metta_sexpr_program_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/tests/langdef/bnf/generated/plain_bnf_components_v1.metta"

def isWorkerEquation : SExpr → Bool
  | .list [.atom "=", .list (.atom head :: _), _] =>
      match head.toList with
      | 'g' :: 's' :: 'l' :: 't' :: ':' :: 'f' :: 'n' :: ':' :: _ => true
      | _ => false
  | _ => false

/-- Select all ordinary functional worker equations, not merely a fixed
slice or a whitelist that could silently ignore an extra worker occurrence. -/
def generatedWorkers : List (Nat × SExpr) :=
  generatedProgram.filter (fun row => isWorkerEquation row.2)

/-- A syntactic noninterference check: every emitted equation has a literal
application head, not a target variable capable of matching arbitrary calls.
This does not constrain equations installed later by a caller. -/
def hasLiteralEquationHead : SExpr → Bool
  | .list (.atom "=" :: rest) =>
      match rest with
      | [.list (.atom head :: _), _] =>
          match head.toList with
          | [] | '$' :: _ => false
          | _ => true
      | _ => false
  | _ => true

theorem generated_equations_have_literal_heads :
    generatedProgram.all (fun row => hasLiteralEquationHead row.2) = true := by
  have first : (generatedProgram.take 80).all (fun row => hasLiteralEquationHead row.2) = true := by
    rfl
  have rest : (generatedProgram.drop 80).all (fun row => hasLiteralEquationHead row.2) = true := by
    rfl
  have partition := List.take_append_drop 80 generatedProgram
  rw [← partition, List.all_append, first, rest]
  rfl

/-- Mode grouping puts reversal before its collector caller. Within each
relation the authored occurrence order is retained. These are actual admitted
source rows, including their complete heads and ordered premises. -/
def selectedSourceRows : List Rewrite :=
  indexSource.rewrites.take 14 ++
  (discoverySource.rewrites.drop 47).take 2 ++
  (discoverySource.rewrites.drop 40).take 7

/-- The same rows with local source occurrence identities. Spans in the
source terms themselves are untouched by this administrative annotation. -/
def selectedSourceOccurrences : List ((String × Nat) × Rewrite) :=
  ((indexSource.rewrites.take 14).zipIdx.map fun (row, occurrence) =>
    ((indexSource.name, occurrence), row)) ++
  (((discoverySource.rewrites.drop 47).take 2).zipIdx 47 |>.map fun (row, occurrence) =>
    ((discoverySource.name, occurrence), row)) ++
  (((discoverySource.rewrites.drop 40).take 7).zipIdx 40 |>.map fun (row, occurrence) =>
    ((discoverySource.name, occurrence), row))

theorem selected_occurrence_rows :
    selectedSourceOccurrences.map Prod.snd = selectedSourceRows := by
  simp only [selectedSourceOccurrences, selectedSourceRows, List.map_append,
    List.map_map, Function.comp_def]
  simp only [List.zipIdx_map_fst]

/-- Grouping changes only cross-relation order, not the exact multiset of
admitted selected source occurrences. The imported family theorem excludes
all other source heads, not just a list of expected names. -/
theorem selected_source_family_complete :
    selectedSourceRows.Perm
      ((PlainBnfCollectorSourceAdmission.family indexSource).map Prod.fst ++
       (PlainBnfCollectorSourceAdmission.family discoverySource).map Prod.fst) := by
  rw [PlainBnfCollectorSourceAdmission.index_family_exact,
      PlainBnfCollectorSourceAdmission.discovery_family_exact]
  simp only [List.zipIdx_map_fst]
  have partition : (discoverySource.rewrites.drop 40).take 9 =
      (discoverySource.rewrites.drop 40).take 7 ++
      (discoverySource.rewrites.drop 47).take 2 := by rfl
  rw [partition, selectedSourceRows, List.append_assoc]
  exact List.perm_append_comm.append_left _


/-- Exact finite correspondence to independently emitted syntax. This is not
an equality between two names for the same construction. -/
theorem generated_worker_equations :
    generatedEquations? selectedSourceRows = some (generatedWorkers.map Prod.snd) := by
  rfl

theorem generated_worker_count : generatedWorkers.length = 23 := by rfl

theorem generated_worker_at (index : Nat) :
    (generatedWorkers.map Prod.snd)[index]? =
      selectedSourceRows[index]?.bind generatedEquation? :=
  generatedEquations_getElem? generated_worker_equations index

theorem generated_with_occurrence_identity :
    generatedEquations? (selectedSourceOccurrences.map Prod.snd) =
      some (generatedWorkers.map Prod.snd) := by
  rw [selected_occurrence_rows]
  exact generated_worker_equations

/-- Dropping an equation cannot pass the exact finite correspondence check. -/
theorem missing_worker_detected :
    generatedEquations? selectedSourceRows ≠ some ((generatedWorkers.drop 1).map Prod.snd) := by
  intro missing
  have same := Option.some.inj (generated_worker_equations.symm.trans missing)
  have lengths := congrArg List.length same
  simp [generated_worker_count] at lengths

/-- Nor can an additional equal equation occurrence be hidden by set equality. -/
theorem extra_worker_detected (extra : SExpr) :
    generatedEquations? selectedSourceRows ≠ some (generatedWorkers.map Prod.snd ++ [extra]) := by
  intro added
  have same := Option.some.inj (generated_worker_equations.symm.trans added)
  have lengths := congrArg List.length same
  simp at lengths

/-- A source edit introducing an unsupported premise is rejected by the
fold, rather than accepted because the old generated artifact still exists. -/
theorem unknown_premise_refused (row : Rewrite) :
    generatedEquation? {row with body := [.list [.atom "OutsideCollectorFamily"]]} = none := by
  change (do
    let head ← workerCall? row.head
    let result ← resultTuple? row.head
    let body ← body? [.list [.atom "OutsideCollectorFamily"]] result
    some (.list [.atom "=", head, body])) = none
  cases workerCall? row.head <;> cases resultTuple? row.head <;> rfl

example : variableToken "?" = "?" := by decide
example : variableToken "?_" = "$_" := by decide
example : variableToken "?x" = variableToken "$x" := by decide
example : sourceTerm? (.list []) = none := rfl
example : sourceTerm? (.atom "x") ≠ sourceTerm? (.list [.atom "metta-nullary", .atom "x"]) := by
  simp [sourceTerm?]
example : workerCall? (.list [.atom "BNFGraphTrieLookupV1", .atom "missing-arguments"]) = none := by
  decide
example : premise? (.list [.atom "unknown", .atom "x"]) (.atom "next") = none := by
  decide

#print axioms generated_worker_equations
#print axioms selected_source_family_complete
#print axioms generated_with_occurrence_identity
#print axioms generatedEquations_getElem?
#print axioms lets_append
#print axioms missing_worker_detected
#print axioms extra_worker_detected

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaSyntax
