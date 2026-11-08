import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput

/-!
# Corrected stable intrinsic-query boundary

This boundary reuses the existing ordered argument, structural-product,
declaration and first-order matching operations. It distinguishes a fresh
output variable from a structured incoming requirement. Undefined fallback
requires absence of every intrinsic candidate; rejection of one requested
type is not that absence. Literal unchecked domains are selected before any
codomain or argument refinement.

The older `IndependentTypeOutput.run` remains its own query-policy model.
This module does not identify that model with the corrected boundary, and
does not replace the language's body evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration named undefinedType)
open IndependentTypeOutput (Path Supply Result Query collect row elements literal isVariable
  declarations callParts matched select arguments freshRows structural allowsRow)

def unchecked (formal : TypeTerm) : Bool :=
  match formal with
  | .const (.symbol name) => name == "%Undefined%" || name == "_"
  | _ => false

def isUndefined : TypeTerm → Bool
  | .const (.symbol name) => name == "%Undefined%"
  | _ => false

def checkedArguments (actuals domains : List TypeTerm) : List (TypeTerm × TypeTerm) :=
  (actuals.zip domains).filter fun pair => !unchecked pair.2

/-- A function row's literal demand is fixed before its result match.
The reused argument owner subsequently reads every subject in its reached
substitution before making the next recursive query. -/
def functions (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (items : List TypeTerm) (required : Option TypeTerm) : Result :=
  match items with
  | [] => some []
  | head :: actuals =>
    collect (declarations library supply path head) fun scheme =>
      match callParts actuals.length scheme with
      | none => some []
      | some (domains, result) =>
        let pending := checkedArguments actuals domains
        match required with
        | none => arguments query path 0 pending result (Subst.id signature)
        | some target =>
          match unifyTotal [(result, target)] with
          | none => some []
          | some initial => arguments query path 0 pending result initial

/-- Candidate enumeration has no implicit Undefined fallback of its own. -/
def candidates (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) : Result :=
  if isVariable subject then some [required.getD (.var (supply (5 :: path) 0))]
  else
    match literal subject with
    | some primitive => some (select required [primitive])
    | none =>
      match elements subject with
      | none => some (select required (declarations library supply path subject))
      | some items => do
        let functionAnswers ← functions library supply query path items required
        let allFunctions ← (match required with
          | none => some functionAnswers
          | some _ => if allowsRow required && functionAnswers.isEmpty then
              functions library supply query path items none else some functionAnswers)
        let rowAnswers ← (if allowsRow required && allFunctions.isEmpty then
            structural supply query path items required else some [])
        pure (functionAnswers ++ rowAnswers)

/-- A root output variable is genuinely fresh inference. A nonvariable
requirement is supplied to recursive queries, where its aliases can refine
later subject reads. Only explicit Undefined asks the global absence test. -/
def step (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (subject : TypeTerm) (required : Option TypeTerm) : Result :=
  match required with
  | none => do
    let answers ← candidates library supply query path subject none
    pure (if answers.isEmpty then [undefinedType] else answers)
  | some (.var _) => do
    let answers ← candidates library supply query path subject none
    pure (if answers.isEmpty then [undefinedType] else answers)
  | some target => do
    let answers ← candidates library supply query path subject (some target)
    if isUndefined target && answers.isEmpty then
      let all ← candidates library supply query path subject none
      pure (if all.isEmpty then [undefinedType] else [])
    else pure answers

def run (library : List Declaration) (supply : Supply) : Nat → Query
  | 0 => fun _ _ _ => none
  | fuel + 1 => step library supply (run library supply fuel)

theorem root_variable_is_fresh (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (subject : TypeTerm) (name : Nat) :
    step library supply query path subject (some (.var name)) =
      step library supply query path subject none := rfl

theorem missing_fresh_query_not_empty (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (subject : TypeTerm)
    (missing : candidates library supply query path subject none = none) :
    step library supply query path subject none = none := by simp [step, missing]

theorem completed_fresh_empty_has_undefined (library : List Declaration) (supply : Supply)
    (query : Query) (path : Path) (subject : TypeTerm)
    (empty : candidates library supply query path subject none = some []) :
    step library supply query path subject none = some [undefinedType] := by simp [step, empty]

theorem literal_unchecked_selected_before_refinement (subject : TypeTerm) :
    checkedArguments [subject] [undefinedType] = [] ∧
      checkedArguments [subject] [.var 0] = [(subject, .var 0)] := by
  simp [checkedArguments, unchecked, undefinedType, named]

end Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery
