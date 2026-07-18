import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Generic Pattern Matching for MeTTaIL (Locally Nameless)

Pattern matching engine that matches concrete terms against rule LHS patterns,
producing variable bindings. Bound occurrences use a locally nameless
representation, while authored binder names remain display metadata.

## Key Design Decisions

- **Non-deterministic**: Bag matching returns a `List Bindings` (all possible matches),
  since multiset matching can have multiple solutions.
- **Binder metadata**: Direct lambda matching ignores authored display names and
  compares locally nameless bodies. Repeated metavariable bindings remain
  structurally consistent, including metadata, until a canonical-metadata
  profile is admitted.
- **Rest variables**: Collection patterns with `some restVar` capture remaining unmatched
  elements as a collection bound to `restVar`.

## References

- mettail-rust: `macros/src/logic/rules.rs` (Ascent Datalog pattern matching)
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.OSLF.MeTTaIL.Match

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Bindings -/

/-- Variable bindings: maps pattern variable names to concrete terms. -/
abbrev Bindings := List (String × Pattern)

/-- Look up a variable in bindings. -/
def Bindings.lookup (b : Bindings) (name : String) : Option Pattern :=
  b.find? (·.1 == name) |>.map (·.2)

/-- Strict binding maps have one entry per metavariable.  Duplicate keys are
rejected even when their values agree, so certificate decoding has one
canonical interpretation. -/
def Bindings.hasUniqueNames (b : Bindings) : Bool :=
  let names := b.map (·.1)
  names.eraseDups.length == names.length

/-- Every binding value is closed executable data at top level.  This is a
conservative boundary for explicit checker arguments: depth-relative values
produced by matching under binders are rejected until bindings record their
source binder depth. -/
def Bindings.valuesGround : Bindings → Bool
  | [] => true
  | (_, value) :: rest => value.isGround && valuesGround rest

/-- Merge two binding sets. Fails (returns `none`) if they assign
    different values to the same variable. -/
def mergeBindings (b1 b2 : Bindings) : Option Bindings :=
  b2.foldlM (init := b1) fun acc (name, val) =>
    match acc.find? (·.1 == name) with
    | none => some ((name, val) :: acc)
    | some (_, existing) => if existing == val then some acc else none

section AlphaBindingFixtures

private def namedIdentity (name : String) : Pattern :=
  .lambda (some name) (.bvar 0)

-- Direct lambda matching ignores display metadata, but repeated metavariable
-- consistency is deliberately structural so `applyBindings` reconstruction
-- remains exact. The proof checker does not use this search matcher.
#guard decide (namedIdentity "x" ≠ namedIdentity "y")
#guard (mergeBindings [("f", namedIdentity "x")]
    [("f", namedIdentity "y")]).isNone
#guard (mergeBindings [("f", namedIdentity "x")]
    [("f", namedIdentity "x")]).isSome

end AlphaBindingFixtures

/-! ## Pattern Matching

The three mutually-dependent functions: matchPattern (single term),
matchArgs (argument list), matchBag (multiset).

In locally nameless, lambda matching is purely structural — no renaming
needed. FVars (metavariables) match anything and produce bindings.
BVars must match structurally (same index). -/

mutual
/-- Match argument lists pairwise, merging bindings. -/
def matchArgs : List Pattern → List Pattern → List Bindings
  | [], [] => [[]]
  | p :: ps, t :: ts =>
    (matchPattern p t).flatMap fun hb =>
      (matchArgs ps ts).filterMap fun tb =>
        mergeBindings hb tb
  | _, _ => []
termination_by pats => sizeOf pats

/-- Multiset matching: find all ways to match pattern elements against term elements.
    If `restVar` is `some v`, unmatched term elements are bound to `v` as a collection.
    This generalizes `findAllComm` from `RhoCalculus/Engine.lean`. -/
def matchBag : List Pattern → Option String → CollType → List Pattern → List Bindings
  | [], restVar, ct, termElems =>
    match restVar with
    | none => if termElems.isEmpty then [[]] else []
    | some rv => [[(rv, .collection ct termElems none)]]
  | ppat :: prest, restVar, ct, termElems =>
    termElems.zipIdx.flatMap fun (telem, i) =>
      (matchPattern ppat telem).flatMap fun hb =>
        let remaining := termElems.eraseIdx i
        (matchBag prest restVar ct remaining).filterMap fun restB =>
          mergeBindings hb restB
termination_by ppats => sizeOf ppats

/-- Match a concrete term against a pattern, producing all valid binding sets.

    Returns `[]` if the match fails, or a list of possible bindings (usually
    singleton for non-collection patterns, multiple for bag matching).

    - `FVar x` (metavariable) matches any term, binding `x` to it.
    - `BVar n` matches only `BVar n` (structural).
    - `lambda bodyPat` matches `lambda bodyConcrete` by matching bodies.
      No alpha-renaming needed — locally nameless makes this structural. -/
def matchPattern (pat term : Pattern) : List Bindings :=
  match pat, term with
  | .fvar x, t => [[(x, t)]]
  | .bvar n, .bvar m => if n == m then [[]] else []
  | .apply c1 pargs, .apply c2 targs =>
    if c1 == c2 && pargs.length == targs.length then
      matchArgs pargs targs
    else []
  | .lambda _ bodyPat, .lambda _ bodyConcrete =>
    matchPattern bodyPat bodyConcrete
  | .multiLambda npat _ bodyPat, .multiLambda nconc _ bodyConcrete =>
    if npat == nconc then matchPattern bodyPat bodyConcrete
    else []
  | .collection ct1 pelems rest1, .collection ct2 telems _rest2 =>
    if ct1 == ct2 then matchBag pelems rest1 ct1 telems
    else []
  | .subst pbody prepl, .subst tbody trepl =>
    (matchPattern pbody tbody).flatMap fun b1 =>
      (matchPattern prepl trepl).filterMap fun b2 =>
        mergeBindings b1 b2
  | _, _ => []
termination_by sizeOf pat
end

/-! ## Matching with a declared binding equivalence

Some calculi identify concrete values by an equational theory rather than by
raw syntax.  Repeated metavariables must then be checked with that theory.
These functions expose only that policy point: constructor matching, binder
handling, and bag search remain the generic MeTTaIL algorithm above.

The existing `matchPattern` remains the structural matcher.  Supplying a
different equivalence is therefore explicit at the caller and does not change
the behavior of existing languages.
-/

/-- Merge binding sets using `equivalent` when both sets bind the same
metavariable. -/
def mergeBindingsWith (equivalent : Pattern → Pattern → Bool)
    (b1 b2 : Bindings) : Option Bindings :=
  b2.foldlM (init := b1) fun acc (name, val) =>
    match acc.find? (·.1 == name) with
    | none => some ((name, val) :: acc)
    | some (_, existing) => if equivalent existing val then some acc else none

mutual
  /-- Pairwise argument matching with a declared repeated-binding
  equivalence. -/
  def matchArgsWith (equivalent : Pattern → Pattern → Bool) :
      List Pattern → List Pattern → List Bindings
    | [], [] => [[]]
    | p :: ps, t :: ts =>
        (matchPatternWith equivalent p t).flatMap fun headBindings =>
          (matchArgsWith equivalent ps ts).filterMap fun tailBindings =>
            mergeBindingsWith equivalent headBindings tailBindings
    | _, _ => []
  termination_by patterns => sizeOf patterns

  /-- Multiset matching with a declared repeated-binding equivalence. -/
  def matchBagWith (equivalent : Pattern → Pattern → Bool) :
      List Pattern → Option String → CollType → List Pattern → List Bindings
    | [], restVariable, collectionType, termElements =>
        match restVariable with
        | none => if termElements.isEmpty then [[]] else []
        | some name => [[(name, .collection collectionType termElements none)]]
    | pattern :: patterns, restVariable, collectionType, termElements =>
        termElements.zipIdx.flatMap fun (termElement, index) =>
          (matchPatternWith equivalent pattern termElement).flatMap fun headBindings =>
            let remaining := termElements.eraseIdx index
            (matchBagWith equivalent patterns restVariable collectionType remaining).filterMap
              fun tailBindings =>
                mergeBindingsWith equivalent headBindings tailBindings
  termination_by patterns => sizeOf patterns

  /-- Match a concrete term while using `equivalent` only to validate values
  assigned to repeated metavariables. -/
  def matchPatternWith (equivalent : Pattern → Pattern → Bool)
      (pattern term : Pattern) : List Bindings :=
    match pattern, term with
    | .fvar name, value => [[(name, value)]]
    | .bvar left, .bvar right => if left == right then [[]] else []
    | .apply leftConstructor leftArguments, .apply rightConstructor rightArguments =>
        if leftConstructor == rightConstructor &&
            leftArguments.length == rightArguments.length then
          matchArgsWith equivalent leftArguments rightArguments
        else
          []
    | .lambda _ leftBody, .lambda _ rightBody =>
        matchPatternWith equivalent leftBody rightBody
    | .multiLambda leftArity _ leftBody, .multiLambda rightArity _ rightBody =>
        if leftArity == rightArity then
          matchPatternWith equivalent leftBody rightBody
        else
          []
    | .collection leftType leftElements leftRest,
        .collection rightType rightElements _ =>
        if leftType == rightType then
          matchBagWith equivalent leftElements leftRest leftType rightElements
        else
          []
    | .subst leftBody leftReplacement, .subst rightBody rightReplacement =>
        (matchPatternWith equivalent leftBody rightBody).flatMap fun bodyBindings =>
          (matchPatternWith equivalent leftReplacement rightReplacement).filterMap
            fun replacementBindings =>
              mergeBindingsWith equivalent bodyBindings replacementBindings
    | _, _ => []
  termination_by sizeOf pattern
end

/-! ## Applying Bindings to RHS -/

/-- Apply variable bindings to a pattern (the RHS of a rule).
    Replaces free variables (metavariables) with their bound values.
    Evaluates `subst` nodes by eliminating their explicit binder with
    `instantiateBVar`. -/
def applyBindings (bindings : Bindings) (rhs : Pattern) : Pattern :=
  match rhs with
  | .fvar x =>
    match bindings.find? (·.1 == x) with
    | some (_, val) => val
    | none => .fvar x
  | .bvar n => .bvar n
  | .apply c args =>
    .apply c (args.map (applyBindings bindings))
  | .lambda nm body =>
    .lambda nm (applyBindings bindings body)
  | .multiLambda n nms body =>
    .multiLambda n nms (applyBindings bindings body)
  | .subst body repl =>
    -- Apply bindings to both parts, then eliminate the explicit binder.
    let body' := applyBindings bindings body
    let repl' := applyBindings bindings repl
    instantiateBVar repl' body'
  | .collection ct elems rest =>
    let elems' := elems.map (applyBindings bindings)
    let (restElems, unresolvedRest) := match rest with
      | some rv =>
        match bindings.find? (·.1 == rv) with
        | some (_, .collection boundCt relems none) =>
            if boundCt == ct then (relems, none) else ([], some rv)
        | _ => ([], some rv)
      | none => ([], none)
    .collection ct (elems' ++ restElems) unresolvedRest
termination_by sizeOf rhs

/-! ## Checked binding application

The gradual operation above deliberately preserves unknown free variables and
unresolved collection rests.  Closed-output consumers need a fail-closed
operation instead: every output metavariable must have a binding, and a rest
binding must be a closed collection of the expected shape.  This remains
distinct from context-correct substitution under binders. -/

/-- Recursive worker for a binding map already known to have unique names. -/
private def applyBindingsCore? (bindings : Bindings) (rhs : Pattern) : Option Pattern :=
  match rhs with
  | .fvar x => bindings.lookup x
  | .bvar n => some (.bvar n)
  | .apply c args =>
      (args.mapM (applyBindingsCore? bindings)).map (.apply c)
  | .lambda nm body =>
      (applyBindingsCore? bindings body).map (.lambda nm)
  | .multiLambda n nms body =>
      (applyBindingsCore? bindings body).map (.multiLambda n nms)
  | .subst body repl => do
      let body' ← applyBindingsCore? bindings body
      let repl' ← applyBindingsCore? bindings repl
      some (instantiateBVar repl' body')
  | .collection ct elems rest => do
      let elems' ← elems.mapM (applyBindingsCore? bindings)
      match rest with
      | none => some (.collection ct elems' none)
      | some rv =>
          match bindings.lookup rv with
          | some (.collection boundCt restElems none) =>
              if boundCt == ct then
                some (.collection ct (elems' ++ restElems) none)
              else
                none
          | _ => none
termination_by sizeOf rhs

/-- Apply bindings to an output pattern, failing on duplicate binding names, an
unbound metavariable, or an unresolved/ill-shaped collection-rest binding.
This checks binding-map structure, not binder-depth provenance. -/
def applyBindings? (bindings : Bindings) (rhs : Pattern) : Option Pattern :=
  if bindings.hasUniqueNames then applyBindingsCore? bindings rhs else none

/-- Checked binding application for explicit top-level ground arguments.  All
binding values must already be ground, and the result is checked again after
application.  This conservative gate rejects depth-relative bindings produced
under binders; it is not a complete contextual-substitution operation. -/
def applyBindingsGround? (bindings : Bindings) (rhs : Pattern) : Option Pattern :=
  if bindings.valuesGround then do
    let result ← applyBindings? bindings rhs
    if result.isGround then some result else none
  else
    none

/-! ## Checked-application contracts -/

/-- Every member of a ground binding map has a top-level ground value. -/
theorem Bindings.value_isGround_of_valuesGround {bindings : Bindings}
    (hground : bindings.valuesGround = true) {name : String} {value : Pattern}
    (hmem : (name, value) ∈ bindings) : value.isGround = true := by
  induction bindings with
  | nil => cases hmem
  | cons head tail ih =>
      rcases head with ⟨headName, headValue⟩
      simp only [Bindings.valuesGround, Bool.and_eq_true] at hground
      cases List.mem_cons.mp hmem with
      | inl heq =>
          cases heq
          exact hground.1
      | inr htail => exact ih hground.2 htail

/-- Strict application success certifies that binding names were unique. -/
theorem applyBindings?_success_hasUniqueNames {bindings : Bindings}
    {rhs result : Pattern} (hsuccess : applyBindings? bindings rhs = some result) :
    bindings.hasUniqueNames = true := by
  simp only [applyBindings?] at hsuccess
  split at hsuccess
  · assumption
  · simp_all

/-- Exact success characterization for the conservative ground wrapper. -/
theorem applyBindingsGround?_eq_some_iff {bindings : Bindings}
    {rhs result : Pattern} :
    applyBindingsGround? bindings rhs = some result ↔
      bindings.valuesGround = true ∧
      applyBindings? bindings rhs = some result ∧
      result.isGround = true := by
  constructor
  · intro hsuccess
    by_cases hvalues : bindings.valuesGround = true
    · cases hstrict : applyBindings? bindings rhs with
      | none => simp [applyBindingsGround?, hvalues, hstrict] at hsuccess
      | some checked =>
          by_cases hresult : checked.isGround = true
          · have heq : checked = result := by
              simpa [applyBindingsGround?, hvalues, hstrict, hresult] using hsuccess
            subst result
            exact ⟨hvalues, rfl, hresult⟩
          · simp [applyBindingsGround?, hvalues, hstrict, hresult] at hsuccess
    · simp [applyBindingsGround?, hvalues] at hsuccess
  · rintro ⟨hvalues, hstrict, hresult⟩
    simp [applyBindingsGround?, hvalues, hstrict, hresult]

/-- Ground-wrapper success certifies that every supplied binding value was
already top-level ground. -/
theorem applyBindingsGround?_success_valuesGround {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    bindings.valuesGround = true :=
  (applyBindingsGround?_eq_some_iff.mp hsuccess).1

/-- Ground-wrapper success includes strict binding application success. -/
theorem applyBindingsGround?_success_applyBindings? {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    applyBindings? bindings rhs = some result :=
  (applyBindingsGround?_eq_some_iff.mp hsuccess).2.1

/-- Ground-wrapper success certifies canonical, duplicate-free binding names. -/
theorem applyBindingsGround?_success_hasUniqueNames {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    bindings.hasUniqueNames = true :=
  applyBindings?_success_hasUniqueNames
    (applyBindingsGround?_success_applyBindings? hsuccess)

/-- Ground-wrapper success certifies a ground output. -/
theorem applyBindingsGround?_success_isGround {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    result.isGround = true :=
  (applyBindingsGround?_eq_some_iff.mp hsuccess).2.2

/-- Ground-wrapper success certifies a locally closed output. -/
theorem applyBindingsGround?_success_isWellScoped {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    result.isWellScoped = true :=
  isWellScoped_of_isGround (applyBindingsGround?_success_isGround hsuccess)

private theorem mapM_applyBindingsCore?_success_eq_map_applyBindings
    {bindings : Bindings} {patterns results : List Pattern}
    (hpoint : ∀ pattern ∈ patterns, ∀ result,
      applyBindingsCore? bindings pattern = some result →
      applyBindings bindings pattern = result)
    (hsuccess : patterns.mapM (applyBindingsCore? bindings) = some results) :
    patterns.map (applyBindings bindings) = results := by
  induction patterns generalizing results with
  | nil =>
      simp at hsuccess
      subst results
      rfl
  | cons pattern patterns ih =>
      cases hhead : applyBindingsCore? bindings pattern with
      | none => simp [List.mapM_cons, hhead] at hsuccess
      | some headResult =>
          cases htail : patterns.mapM (applyBindingsCore? bindings) with
          | none => simp [List.mapM_cons, hhead, htail] at hsuccess
          | some tailResults =>
              have hresults : headResult :: tailResults = results := by
                simpa [List.mapM_cons, hhead, htail] using hsuccess
              subst results
              simp only [List.map_cons]
              congr 1
              · exact hpoint pattern (List.mem_cons.mpr (Or.inl rfl)) headResult hhead
              · exact ih
                  (fun argument hmem =>
                    hpoint argument (List.mem_cons.mpr (Or.inr hmem)))
                  htail

private theorem Bindings.find?_eq_some_of_lookup_eq_some {bindings : Bindings}
    {name : String} {value : Pattern}
    (hlookup : bindings.lookup name = some value) :
    ∃ foundName, bindings.find? (·.1 == name) = some (foundName, value) := by
  simp only [Bindings.lookup] at hlookup
  cases hfind : bindings.find? (·.1 == name) with
  | none => simp [hfind] at hlookup
  | some entry =>
      rcases entry with ⟨foundName, foundValue⟩
      have hvalue : foundValue = value := by simpa [hfind] using hlookup
      subst value
      exact ⟨foundName, rfl⟩

/-- Whenever the strict recursive worker succeeds, its result is exactly the
result of gradual application.  This is computational agreement only; it does
not establish binder-context correctness. -/
private theorem applyBindingsCore?_success_eq_applyBindings
    {bindings : Bindings} {rhs result : Pattern}
    (hsuccess : applyBindingsCore? bindings rhs = some result) :
    applyBindings bindings rhs = result := by
  induction rhs using Pattern.inductionOn generalizing result with
  | hbvar _ =>
      simpa only [applyBindingsCore?, applyBindings, Option.some.injEq] using hsuccess
  | hfvar name =>
      simp only [applyBindingsCore?, Bindings.lookup] at hsuccess
      cases hfind : bindings.find? (·.1 == name) with
      | none => simp [hfind] at hsuccess
      | some entry =>
          rcases entry with ⟨foundName, foundValue⟩
          have hvalue : foundValue = result := by simpa [hfind] using hsuccess
          simp only [applyBindings, hfind]
          exact hvalue
  | happly constructor args ih =>
      simp only [applyBindingsCore?] at hsuccess
      rcases Option.map_eq_some_iff.mp hsuccess with
        ⟨argResults, hargs, hresult⟩
      subst result
      simp only [applyBindings]
      congr 1
      exact mapM_applyBindingsCore?_success_eq_map_applyBindings
        (fun argument hmem argumentResult =>
          ih argument hmem (result := argumentResult)) hargs
  | hlambda name body ih =>
      simp only [applyBindingsCore?] at hsuccess
      rcases Option.map_eq_some_iff.mp hsuccess with
        ⟨bodyResult, hbody, hresult⟩
      subst result
      simp only [applyBindings]
      congr 1
      exact ih (result := bodyResult) hbody
  | hmultiLambda arity names body ih =>
      simp only [applyBindingsCore?] at hsuccess
      rcases Option.map_eq_some_iff.mp hsuccess with
        ⟨bodyResult, hbody, hresult⟩
      subst result
      simp only [applyBindings]
      congr 1
      exact ih (result := bodyResult) hbody
  | hsubst body replacement ihBody ihReplacement =>
      cases hbody : applyBindingsCore? bindings body with
      | none => simp [applyBindingsCore?, hbody] at hsuccess
      | some bodyResult =>
          cases hreplacement : applyBindingsCore? bindings replacement with
          | none => simp [applyBindingsCore?, hbody, hreplacement] at hsuccess
          | some replacementResult =>
              have hresult : instantiateBVar replacementResult bodyResult = result := by
                simpa [applyBindingsCore?, hbody, hreplacement] using hsuccess
              subst result
              simp only [applyBindings]
              rw [ihBody (result := bodyResult) hbody,
                ihReplacement (result := replacementResult) hreplacement]
  | hcollection collectionType elements rest ih =>
      cases helements : elements.mapM (applyBindingsCore? bindings) with
      | none => simp [applyBindingsCore?, helements] at hsuccess
      | some elementResults =>
          have helementResults : elements.map (applyBindings bindings) = elementResults :=
            mapM_applyBindingsCore?_success_eq_map_applyBindings
              (fun element hmem elementResult =>
                ih element hmem (result := elementResult)) helements
          cases rest with
          | none =>
              have hresult :
                  Pattern.collection collectionType elementResults none = result := by
                simpa [applyBindingsCore?, helements] using hsuccess
              subst result
              simp only [applyBindings]
              rw [helementResults]
              simp
          | some restName =>
              cases hlookup : bindings.lookup restName with
              | none => simp [applyBindingsCore?, helements, hlookup] at hsuccess
              | some restValue =>
                  cases restValue with
                  | bvar index =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | fvar name =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | apply constructor args =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | lambda name body =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | multiLambda arity names body =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | subst body replacement =>
                      simp [applyBindingsCore?, helements, hlookup] at hsuccess
                  | collection boundType restElements restTail =>
                      cases restTail with
                      | some tailName =>
                          simp [applyBindingsCore?, helements, hlookup] at hsuccess
                      | none =>
                          by_cases htype : boundType == collectionType
                          · have hresult :
                                Pattern.collection collectionType
                                  (elementResults ++ restElements) none = result := by
                              simpa [applyBindingsCore?, helements, hlookup, htype] using hsuccess
                            subst result
                            rcases Bindings.find?_eq_some_of_lookup_eq_some hlookup with
                              ⟨foundName, hfind⟩
                            simp only [applyBindings, hfind, htype, if_pos]
                            rw [helementResults]
                          · simp [applyBindingsCore?, helements, hlookup, htype] at hsuccess

/-- Strict application agrees with gradual application whenever it succeeds. -/
theorem applyBindings?_success_eq_applyBindings {bindings : Bindings}
    {rhs result : Pattern} (hsuccess : applyBindings? bindings rhs = some result) :
    applyBindings bindings rhs = result := by
  simp only [applyBindings?] at hsuccess
  split at hsuccess
  · exact applyBindingsCore?_success_eq_applyBindings hsuccess
  · simp_all

/-- The conservative ground wrapper also agrees with gradual application on
every accepted result. -/
theorem applyBindingsGround?_success_eq_applyBindings {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    applyBindings bindings rhs = result :=
  applyBindings?_success_eq_applyBindings
    (applyBindingsGround?_success_applyBindings? hsuccess)

/-- The two structural invariants exposed by any successful strict
application: canonical binding names and exact agreement with gradual
application.  This punctuation-free bundle is also convenient for checker
clients that do not need the intermediate worker API. -/
theorem checkedApplication_success_contract {bindings : Bindings}
    {rhs result : Pattern} (hsuccess : applyBindings? bindings rhs = some result) :
    bindings.hasUniqueNames = true ∧ applyBindings bindings rhs = result :=
  ⟨applyBindings?_success_hasUniqueNames hsuccess,
    applyBindings?_success_eq_applyBindings hsuccess⟩

/-- Successful conservative ground application exposes all of its boundary
facts together: ground input values, canonical names, a ground and locally
closed result, and agreement with gradual application. -/
theorem groundApplication_success_contract {bindings : Bindings}
    {rhs result : Pattern}
    (hsuccess : applyBindingsGround? bindings rhs = some result) :
    bindings.valuesGround = true ∧
      bindings.hasUniqueNames = true ∧
      result.isGround = true ∧
      result.isWellScoped = true ∧
      applyBindings bindings rhs = result :=
  ⟨applyBindingsGround?_success_valuesGround hsuccess,
    applyBindingsGround?_success_hasUniqueNames hsuccess,
    applyBindingsGround?_success_isGround hsuccess,
    applyBindingsGround?_success_isWellScoped hsuccess,
    applyBindingsGround?_success_eq_applyBindings hsuccess⟩

/-- Non-canonical duplicate binding names fail before strict application. -/
theorem applyBindings?_eq_none_of_hasUniqueNames_eq_false {bindings : Bindings}
    {rhs : Pattern} (hnames : bindings.hasUniqueNames = false) :
    applyBindings? bindings rhs = none := by
  simp [applyBindings?, hnames]

/-- A non-ground input binding map fails before conservative ground
application. -/
theorem applyBindingsGround?_eq_none_of_valuesGround_eq_false
    {bindings : Bindings} {rhs : Pattern}
    (hvalues : bindings.valuesGround = false) :
    applyBindingsGround? bindings rhs = none := by
  simp [applyBindingsGround?, hvalues]

/-- The two fail-closed prechecks exposed together: duplicate names reject
strict application, and a non-ground value rejects conservative ground
application before the RHS is traversed. -/
theorem checkedApplication_precheck_failure_contract
    {bindings : Bindings} {rhs : Pattern} :
    (bindings.hasUniqueNames = false → applyBindings? bindings rhs = none) ∧
      (bindings.valuesGround = false →
        applyBindingsGround? bindings rhs = none) :=
  ⟨applyBindings?_eq_none_of_hasUniqueNames_eq_false,
    applyBindingsGround?_eq_none_of_valuesGround_eq_false⟩

section ApplyBindingsFixtures

private def unresolvedRestPattern : Pattern :=
  .collection .hashBag [.apply "K" []] (some "rest")

-- Gradual application preserves unknown structure instead of erasing it.
#guard decide (applyBindings [] unresolvedRestPattern = unresolvedRestPattern)

-- The checked profile rejects that same unresolved output.
#guard (applyBindings? [] unresolvedRestPattern).isNone

theorem applyBindings?_rejects_unresolved_rest :
    applyBindings? []
      (.collection .hashBag [.apply "K" []] (some "rest")) = none := by
  rw [applyBindings?]
  rw [show Bindings.hasUniqueNames ([] : Bindings) = true by rfl]
  simp [applyBindingsCore?, Bindings.lookup]

-- A correctly shaped rest binding is spliced in by both profiles.
private def restBindings : Bindings :=
  [("rest", .collection .hashBag [.apply "V" []] none)]

private def resolvedRestPattern : Pattern :=
  .collection .hashBag [.apply "K" [], .apply "V" []] none

#guard decide (applyBindings restBindings unresolvedRestPattern = resolvedRestPattern)
#guard decide (applyBindings? restBindings unresolvedRestPattern = some resolvedRestPattern)

theorem applyBindings?_accepts_matching_closed_rest :
    applyBindings?
      [("rest", .collection .hashBag [.apply "V" []] none)]
      (.collection .hashBag [.apply "K" []] (some "rest")) =
        some (.collection .hashBag [.apply "K" [], .apply "V" []] none) := by
  rw [applyBindings?]
  rw [show
    Bindings.hasUniqueNames
      ([("rest", .collection .hashBag [.apply "V" []] none)] : Bindings) =
      true by rfl]
  simp [applyBindingsCore?, Bindings.lookup]

-- A binding of the wrong collection kind is never accepted as proof output.
#guard decide (applyBindings
    [("rest", .collection .vec [.apply "V" []] none)]
    unresolvedRestPattern = unresolvedRestPattern)
#guard (applyBindings?
    [("rest", .collection .vec [.apply "V" []] none)]
    unresolvedRestPattern).isNone

theorem applyBindings?_rejects_wrong_collection_kind :
    applyBindings?
      [("rest", .collection .vec [.apply "V" []] none)]
      (.collection .hashBag [.apply "K" []] (some "rest")) = none := by
  rw [applyBindings?]
  rw [show
    Bindings.hasUniqueNames
      ([("rest", .collection .vec [.apply "V" []] none)] : Bindings) =
      true by rfl]
  simp [applyBindingsCore?, Bindings.lookup]

-- Binding completeness and closed-data checking are distinct gates.
private def residualBinding : Bindings := [("x", .fvar "residual")]

#guard decide (applyBindings? residualBinding (.fvar "x") = some (.fvar "residual"))
#guard (applyBindingsGround? residualBinding (.fvar "x")).isNone
#guard decide
    (applyBindingsGround? [("x", .apply "V" [])] (.fvar "x") = some (.apply "V" []))

theorem applyBindingsGround?_rejects_nonground_binding_value :
    applyBindingsGround? [("x", .fvar "residual")] (.fvar "x") = none := by
  apply applyBindingsGround?_eq_none_of_valuesGround_eq_false
  rfl

theorem applyBindingsGround?_accepts_ground_binding_value :
    applyBindingsGround? [("x", .apply "V" [])] (.fvar "x") =
      some (.apply "V" []) := by
  apply applyBindingsGround?_eq_some_iff.mpr
  refine ⟨rfl, ?_, rfl⟩
  rw [applyBindings?]
  rw [show Bindings.hasUniqueNames ([("x", .apply "V" [])] : Bindings) = true by rfl]
  simp [applyBindingsCore?, Bindings.lookup]

-- Duplicate certificate bindings are ambiguous/non-canonical and fail closed.
#guard (applyBindings?
    [("x", .apply "V" []), ("x", .apply "V" [])] (.fvar "x")).isNone
#guard (applyBindings?
    [("x", .apply "V" []), ("x", .apply "W" [])] (.fvar "x")).isNone

theorem applyBindings?_rejects_duplicate_equal_values :
    applyBindings?
      [("x", .apply "V" []), ("x", .apply "V" [])] (.fvar "x") = none := by
  apply applyBindings?_eq_none_of_hasUniqueNames_eq_false
  rfl

theorem applyBindings?_rejects_duplicate_unequal_values :
    applyBindings?
      [("x", .apply "V" []), ("x", .apply "W" [])] (.fvar "x") = none := by
  apply applyBindings?_eq_none_of_hasUniqueNames_eq_false
  rfl

-- Executing an explicit substitution under an ambient binder removes its own
-- de Bruijn level; the former `openBVar 0` path left index 1 dangling here.
private def ambientExplicitSubst : Pattern :=
  .lambda none (.subst (.bvar 1) (.apply "K" []))

private def ambientExplicitSubstResult : Pattern :=
  .lambda none (.bvar 0)

#guard ambientExplicitSubst.isGround
#guard ambientExplicitSubstResult.isGround
#guard decide
    (applyBindingsGround? [] ambientExplicitSubst = some ambientExplicitSubstResult)

theorem applyBindingsGround?_executes_ambient_explicit_subst :
    applyBindingsGround? []
      (.lambda none (.subst (.bvar 1) (.apply "K" []))) =
        some (.lambda none (.bvar 0)) := by
  apply applyBindingsGround?_eq_some_iff.mpr
  refine ⟨rfl, ?_, rfl⟩
  rw [applyBindings?]
  rw [show Bindings.hasUniqueNames ([] : Bindings) = true by rfl]
  simp [applyBindingsCore?, instantiateBVar, instantiateBVarAt]

end ApplyBindingsFixtures

section BinderDepthCounterexample

private def depthRelativeMatchPattern : Pattern :=
  .lambda none (.fvar "x")

private def depthRelativeMatchTerm : Pattern :=
  .lambda none (.bvar 0)

private def deeperBindingUse : Pattern :=
  .lambda none (.lambda none (.fvar "x"))

private def depthBlindBindingResult : Pattern :=
  .lambda none (.lambda none (.bvar 0))

private def depthShiftedBindingResult : Pattern :=
  .lambda none (.lambda none (.bvar 1))

-- Matching under one binder records only `x ↦ #0`.  Strict application under
-- two binders therefore returns `#0`, not the depth-shifted `#1`.  The returned
-- term happens to be ground, so output groundness alone is not contextual
-- substitution correctness.
theorem applyBindings?_binder_depth_counterexample :
    matchPattern depthRelativeMatchPattern depthRelativeMatchTerm =
        [[("x", .bvar 0)]] ∧
      applyBindings? [("x", .bvar 0)] deeperBindingUse =
        some depthBlindBindingResult ∧
      depthBlindBindingResult.isGround = true ∧
      depthBlindBindingResult ≠ depthShiftedBindingResult := by
  constructor
  · simp only [depthRelativeMatchPattern, depthRelativeMatchTerm, matchPattern]
  constructor
  · simp only [deeperBindingUse, depthBlindBindingResult]
    rw [applyBindings?]
    rw [show Bindings.hasUniqueNames ([("x", .bvar 0)] : Bindings) = true by rfl]
    simp [applyBindingsCore?, Bindings.lookup]
  constructor
  · rfl
  · simp only [depthBlindBindingResult, depthShiftedBindingResult]
    decide

-- The conservative ground-input gate rejects that depth-relative binding.
theorem applyBindingsGround?_rejects_depth_relative_binding :
    applyBindingsGround? [("x", .bvar 0)] deeperBindingUse = none := by
  apply applyBindingsGround?_eq_none_of_valuesGround_eq_false
  rfl

/-- Concrete capture boundary for the current depth-blind matcher.  Matching
records a binder-relative value without its source depth; strict application
can therefore produce a different well-scoped term at a deeper use site,
whereas the conservative ground-input profile rejects the binding. -/
theorem binderDepth_conservative_boundary :
    matchPattern (.lambda none (.fvar "x")) (.lambda none (.bvar 0)) =
        [[("x", .bvar 0)]] ∧
      applyBindings? [("x", .bvar 0)]
          (.lambda none (.lambda none (.fvar "x"))) =
        some (.lambda none (.lambda none (.bvar 0))) ∧
      (Pattern.lambda none (.lambda none (.bvar 0))).isGround = true ∧
      (Pattern.lambda none (.lambda none (.bvar 0))) ≠
        (Pattern.lambda none (.lambda none (.bvar 1))) ∧
      applyBindingsGround? [("x", .bvar 0)]
          (.lambda none (.lambda none (.fvar "x"))) = none := by
  rcases applyBindings?_binder_depth_counterexample with
    ⟨hmatch, happly, hground, hdifferent⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [depthRelativeMatchPattern, depthRelativeMatchTerm] using hmatch
  · simpa only [deeperBindingUse, depthBlindBindingResult] using happly
  · simpa only [depthBlindBindingResult] using hground
  · simpa only [depthBlindBindingResult, depthShiftedBindingResult] using hdifferent
  · simpa only [deeperBindingUse] using
      applyBindingsGround?_rejects_depth_relative_binding

#guard decide
  (matchPattern depthRelativeMatchPattern depthRelativeMatchTerm =
    [[("x", .bvar 0)]])
#guard decide
  (applyBindings? [("x", .bvar 0)] deeperBindingUse =
    some depthBlindBindingResult)
#guard depthBlindBindingResult.isGround
#guard decide (depthBlindBindingResult ≠ depthShiftedBindingResult)
#guard (applyBindingsGround? [("x", .bvar 0)] deeperBindingUse).isNone

end BinderDepthCounterexample

/-! ## isMatchCorrect Fragment -/

mutual
def isMatchCorrectAux : Pattern → Bool
  | .fvar _           => true
  | .bvar _           => true
  | .apply _ args     => isMatchCorrectListAux args
  | .lambda _ _       => false  -- matchPattern ignores binder names; correctness breaks
  | .multiLambda _ _ _  => false  -- matchPattern ignores binder names; correctness breaks
  | .subst _ _        => false
  | .collection _ _ _ => false

def isMatchCorrectListAux : List Pattern → Bool
  | []      => true
  | p :: ps => isMatchCorrectAux p && isMatchCorrectListAux ps
end

/-- A pattern is "match-correct" if `applyBindings bs pat = t` holds for every
    `bs ∈ matchPattern pat t`. Excludes:
    - `.subst`: `applyBindings` eliminates the explicit binder, rather than
      preserving the matched syntax.
    - `.collection`: bag matching can pick elements out of order, so
      `applyBindings bs pat` may reorder elements vs. the target `t`. -/
def Pattern.isMatchCorrect (p : Pattern) : Bool := isMatchCorrectAux p

/-! ## Rule Application -/

/-- Apply a single rewrite rule to a term (top-level match only).
    Returns all possible reducts. Skips rules with premises (congruence
    premises require recursive reduction, handled by the full engine). -/
def applyRule (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).map fun b => applyBindings b rule.right
  else []

/-- No-premise operational helper with fail-closed output substitution.
This is a strict execution primitive, not the proof-calculus checker. -/
def applyRuleWithCheckedOutput (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).filterMap fun b => applyBindings? b rule.right
  else []

/-- No-premise operational helper whose accepted matcher bindings and outputs
are ground.  It conservatively rejects depth-relative matcher bindings, so it
is incomplete for legitimate contextual matches.  Input groundness and
proof-rule provenance remain separate checker obligations. -/
def applyRuleWithGroundOutput (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).filterMap fun b => applyBindingsGround? b rule.right
  else []

/-- Apply all rewrite rules from a LanguageDef to a term (top-level).
    Returns all possible reducts from all applicable rules. -/
def rewriteStep (lang : LanguageDef) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRule rule term

/-- Apply all no-premise rules while rejecting unresolved output bindings. -/
def rewriteStepWithCheckedOutput (lang : LanguageDef) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRuleWithCheckedOutput rule term

/-- Apply all no-premise rules while requiring ground outputs. -/
def rewriteStepWithGroundOutput (lang : LanguageDef) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRuleWithGroundOutput rule term

section CheckedOutputFixtures

private def unboundOutputRule : RewriteRule :=
  { name := "unbound-output"
    typeContext := []
    premises := []
    left := .apply "K" []
    right := .fvar "ghost" }

-- Gradual execution leaves the unknown output inert.
#guard decide
    (applyRule unboundOutputRule (.apply "K" []) = [.fvar "ghost"])

-- Strict output checking rejects the same malformed rule application.
#guard applyRuleWithCheckedOutput unboundOutputRule (.apply "K" []) |>.isEmpty

private def reboundOutputRule : RewriteRule :=
  { name := "rebound-output"
    typeContext := []
    premises := []
    left := .apply "Box" [.fvar "x"]
    right := .fvar "x" }

-- A complete binding may still contain unresolved matcher structure.
#guard decide
    (applyRuleWithCheckedOutput reboundOutputRule
      (.apply "Box" [.fvar "residual"]) = [.fvar "residual"])
#guard applyRuleWithGroundOutput reboundOutputRule
    (.apply "Box" [.fvar "residual"]) |>.isEmpty
#guard decide
    (applyRuleWithGroundOutput reboundOutputRule
      (.apply "Box" [.apply "V" []]) = [.apply "V" []])

end CheckedOutputFixtures

/-- Reduce to normal form (deterministic: pick first reduct, with fuel). -/
def rewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteStep lang term with
    | [] => term
    | q :: _ => rewriteToNormalForm lang q fuel

end Mettapedia.OSLF.MeTTaIL.Match
