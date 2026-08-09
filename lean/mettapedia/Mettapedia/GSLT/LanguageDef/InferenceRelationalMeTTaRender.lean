import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Relational MeTTa projection of LanguageDef inference rules

Renders the inference rules of a constructor-only `LanguageDef`
presentation as an EXECUTABLE MeTTa relational program: one ordered clause
per rule, judgment applications as ordinary applications, metavariables as
MeTTa variables, and premises as a `let`-chain over the private derivation
token `ptg-true`.  Clause backtracking then realizes derivation search.

This is the executable sibling of `InferenceMeTTaRender` (which serializes
the same presentation as DATA for the operational generic checker): two
projections of one authored root, kept in the authored rule order.

Fail-closed contract: rules with side conditions, binder-arity
metavariables, or patterns outside the source fragment (bound variables,
lambdas, substitutions, collections) do not render — the projection
refuses rather than approximates.  Quoting is plain interpolation; no
`Repr`-derived output enters the artifact.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceRelationalMeTTaRender

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- The derivation token: a premise holds when its relational evaluation
yields this atom.  Private vocabulary of the sealed checker space. -/
def derivationToken : String := "ptg-true"

mutual

/-- Render a source-fragment pattern as MeTTa source text. -/
def renderTerm? : Pattern → Option String
  | .fvar name => some s!"${name}"
  | .apply head [] => some head
  | .apply head arguments => do
      let rendered ← renderTerms? arguments
      some s!"({head} {String.intercalate " " rendered})"
  | _ => none
termination_by pattern => 2 * sizeOf pattern

def renderTerms? : List Pattern → Option (List String)
  | [] => some []
  | pattern :: patterns => do
      let head ← renderTerm? pattern
      let tail ← renderTerms? patterns
      some (head :: tail)
termination_by patterns => 2 * sizeOf patterns + 1

end

/-- Premises chain through `let` on the derivation token: each premise must
evaluate to `ptg-true`, with clause choice supplying backtracking across
alternative derivations. -/
def renderPremiseChain : List String → String
  | [] => derivationToken
  | premise :: premises =>
      s!"(let {derivationToken} {premise} {renderPremiseChain premises})"

/-- One executable clause per rule, in authored order. -/
def renderClause? (rule : RuleSchema) : Option String := do
  if !rule.sideConditions.isEmpty then
    none
  else if !(rule.metavariables.all fun formal => formal.2 == 0) then
    none
  else
    let conclusion ← renderTerm? rule.conclusion
    let premises ← renderTerms? rule.premises
    some s!"(= {conclusion} {renderPremiseChain premises})"

def renderClauses? (rules : List RuleSchema) : Option (List String) :=
  match rules with
  | [] => some []
  | rule :: rest => do
      let head ← renderClause? rule
      let tail ← renderClauses? rest
      some (head :: tail)

mutual

/-- Structural image of `renderTerm?`'s domain: the source fragment.
Structurally recursive (no well-founded wrapper) so `decide` can evaluate
it in the kernel. -/
def sourceSyntaxOk : Pattern → Bool
  | .fvar _ => true
  | .apply _ arguments => sourceSyntaxOkList arguments
  | _ => false

def sourceSyntaxOkList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => sourceSyntaxOk pattern && sourceSyntaxOkList patterns

end

/-- Decidable structural totality: exactly the fail-closed conditions of
`renderClause?`.  The exporter still refuses at runtime on any rule this
predicate would reject; proving `rules.all projectable` by `decide` moves
that refusal to build time without kernel-evaluating string construction. -/
def projectable (rule : RuleSchema) : Bool :=
  rule.sideConditions.isEmpty &&
  rule.metavariables.all (fun formal => formal.2 == 0) &&
  sourceSyntaxOk rule.conclusion &&
  rule.premises.all sourceSyntaxOk

/-- The full relational program for a presentation's rules, or `none` if
any rule falls outside the projectable fragment. -/
def renderProgram? (presentation : Presentation) : Option String := do
  let clauses ← renderClauses? presentation.rules
  some (String.intercalate "\n" clauses ++ "\n")

end Mettapedia.GSLT.LanguageDef.InferenceRelationalMeTTaRender
