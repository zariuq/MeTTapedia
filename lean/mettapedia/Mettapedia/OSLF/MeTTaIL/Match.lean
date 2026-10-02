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
  elements as a collection bound to `restVar`. Vectors match in order and bind
  only the suffix; bags and sets explore element permutations.

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
decreasing_by all_goals sizeOf_pattern_dec

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
decreasing_by all_goals sizeOf_pattern_dec

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
    if ct1 == ct2 then
      if ct1 == .vec then
        match rest1 with
        | none => matchArgs pelems telems
        | some rv =>
          (matchArgs pelems (telems.take pelems.length)).filterMap fun bindings =>
            mergeBindings bindings
              [(rv, .collection .vec (telems.drop pelems.length) none)]
      else matchBag pelems rest1 ct1 telems
    else []
  | .subst pbody prepl, .subst tbody trepl =>
    (matchPattern pbody tbody).flatMap fun b1 =>
      (matchPattern prepl trepl).filterMap fun b2 =>
        mergeBindings b1 b2
  | _, _ => []
termination_by sizeOf pat
decreasing_by all_goals sizeOf_pattern_dec
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
  decreasing_by all_goals sizeOf_pattern_dec

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
  decreasing_by all_goals sizeOf_pattern_dec

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
          if leftType == .vec then
            match leftRest with
            | none => matchArgsWith equivalent leftElements rightElements
            | some name =>
                (matchArgsWith equivalent leftElements
                  (rightElements.take leftElements.length)).filterMap fun bindings =>
                    mergeBindingsWith equivalent bindings
                      [(name, .collection .vec (rightElements.drop leftElements.length) none)]
          else matchBagWith equivalent leftElements leftRest leftType rightElements
        else
          []
    | .subst leftBody leftReplacement, .subst rightBody rightReplacement =>
        (matchPatternWith equivalent leftBody rightBody).flatMap fun bodyBindings =>
          (matchPatternWith equivalent leftReplacement rightReplacement).filterMap
            fun replacementBindings =>
              mergeBindingsWith equivalent bodyBindings replacementBindings
    | _, _ => []
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
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
decreasing_by all_goals sizeOf_pattern_dec

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
decreasing_by all_goals sizeOf_pattern_dec

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

/-! ## Rule Application

NOTE FOR OTHER LANES (2026-09-15): rule firing is now scope-correct.  A matched
value is shifted from the binder depth at which the rule's left-hand side
captured it to the depth at which its right-hand side uses it, so a rule that
moves a metavariable under a binder no longer changes which binder the value
refers to.  `applyBindings` itself is unchanged; the correction lives in
`applyBindingsScoped`, which `applyRule` now uses.  If a proof of yours asserted
the previous reduct, the new one is the corrected reduct and the old statement
was recording the defect.  `Substitution.liftBVars` was also made structural so
the kernel can reduce it; `liftBVarsList_eq_map` restores the previous
`List.map` shape for simp sets that need it. -/

/-! ## Scope-correct binding application

`applyBindings` inserts a matched value wherever its metavariable occurs in the
right-hand side, unchanged.  That is wrong whenever the two occurrences sit under
different numbers of binders: a value matched under one binder and inserted under
two keeps the index it had, and so names a different binder than the one it was
matched against.  On the rule `lam z. F ~> lam z. lam y. app(F, y)` applied to the
identity, it turns the identity into self-application.

The correction needs the depth at which the value was captured, and that is a
static property of the rule's left-hand side rather than data the matcher has to
carry: a metavariable occurs at one depth in the left-hand side, and the traversal
of the right-hand side knows its own depth, so the shift is the difference.  No
change to the binding type is required.

Outward motion -- a metavariable occurring deeper in the left-hand side than in
the right -- is not corrected, because the value would name binders that do not
exist at the target; such a rule is ill-formed and the truncated difference
leaves the value alone rather than inventing a scope for it. -/

mutual
/-- The binder depth at which a metavariable occurs in a pattern. -/
def captureDepth (name : String) : Nat → Pattern → Option Nat
  | d, .fvar x => if x == name then some d else none
  | _, .bvar _ => none
  | d, .apply _ args => captureDepthList name d args
  | d, .lambda _ body => captureDepth name (d + 1) body
  | d, .multiLambda n _ body => captureDepth name (d + n) body
  | d, .subst body repl =>
      match captureDepth name (d + 1) body with
      | some k => some k
      | none => captureDepth name d repl
  | d, .collection _ elems rest =>
      match captureDepthList name d elems with
      | some k => some k
      | none =>
          match rest with
          | some restVar => if restVar == name then some d else none
          | none => none

def captureDepthList (name : String) : Nat → List Pattern → Option Nat
  | _, [] => none
  | d, p :: ps =>
      match captureDepth name d p with
      | some k => some k
      | none => captureDepthList name d ps
end

/-- A zero shift leaves a list of spliced elements alone. -/
theorem map_liftBVars_zero (ps : List Pattern) :
    ps.map (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 0) = ps := by
  induction ps with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, ih]

/-- What a collection's rest variable contributes, and whether it survives
unresolved.  A rest variable is a metavariable of the left-hand side like any
other, so the elements it carries are shifted by the same difference of depths:
a bag matched `dc` binders deep and re-emitted `d` deep moves its elements by
`d - dc`.  Without that shift the matcher's choice of which element to place in
an element metavariable and which to leave to the rest would be observable,
since the two carriers would transport the same index differently. -/
def restSplice (lhs : Pattern) (bindings : Bindings) (d : Nat) (ct : CollType) :
    Option String → List Pattern × Option String
  | none => ([], none)
  | some rv =>
      match bindings.find? (·.1 == rv) with
      | some (_, .collection boundCt relems none) =>
          if boundCt == ct then
            ((match captureDepth rv 0 lhs with
              | some dc =>
                  relems.map (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 (d - dc))
              | none => relems), none)
          else ([], some rv)
      | _ => ([], some rv)

mutual
/-- Binding application that keeps a matched value pointing at the binder it was
matched against, by shifting it from the depth at which the rule's left-hand side
captured it to the depth at which the right-hand side uses it. -/
def applyBindingsScoped (lhs : Pattern) (bindings : Bindings) :
    Nat → Pattern → Pattern
  | d, .fvar x =>
    match bindings.find? (·.1 == x) with
    | some (_, val) =>
        match captureDepth x 0 lhs with
        | some dc => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 (d - dc) val
        | none => val
    | none => .fvar x
  | _, .bvar n => .bvar n
  | d, .apply c args => .apply c (applyBindingsScopedList lhs bindings d args)
  | d, .lambda nm body =>
    .lambda nm (applyBindingsScoped lhs bindings (d + 1) body)
  | d, .multiLambda n nms body =>
    .multiLambda n nms (applyBindingsScoped lhs bindings (d + n) body)
  | d, .subst body repl =>
    instantiateBVar (applyBindingsScoped lhs bindings d repl)
      (applyBindingsScoped lhs bindings (d + 1) body)
  | d, .collection ct elems rest =>
    .collection ct
      (applyBindingsScopedList lhs bindings d elems ++ (restSplice lhs bindings d ct rest).1)
      (restSplice lhs bindings d ct rest).2

def applyBindingsScopedList (lhs : Pattern) (bindings : Bindings) :
    Nat → List Pattern → List Pattern
  | _, [] => []
  | d, p :: ps =>
      applyBindingsScoped lhs bindings d p :: applyBindingsScopedList lhs bindings d ps
end

/-- The explicit traversal is the map, so proofs written against `List.map`
shapes are unaffected. -/
@[simp] theorem applyBindingsScopedList_eq_map (lhs : Pattern) (bindings : Bindings)
    (d : Nat) : ∀ (ps : List Pattern),
    applyBindingsScopedList lhs bindings d ps
      = ps.map (applyBindingsScoped lhs bindings d)
  | [] => rfl
  | p :: ps => by
      simp only [applyBindingsScopedList, List.map_cons,
        applyBindingsScopedList_eq_map lhs bindings d ps]

/-- The scoped applier passes through an application unchanged in depth. -/
@[simp] theorem applyBindingsScoped_apply (lhs : Pattern) (bindings : Bindings)
    (d : Nat) (c : String) (args : List Pattern) :
    applyBindingsScoped lhs bindings d (.apply c args)
      = .apply c (args.map (applyBindingsScoped lhs bindings d)) := by
  simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]

/-- And leaves a bound variable alone. -/
@[simp] theorem applyBindingsScoped_bvar (lhs : Pattern) (bindings : Bindings)
    (d n : Nat) :
    applyBindingsScoped lhs bindings d (.bvar n) = .bvar n := by
  simp only [applyBindingsScoped]

/-- **At the outermost depth the shift is zero**, so the scoped applier agrees
with the plain one on a metavariable.  A rule whose right-hand side binds
nothing above an occurrence therefore behaves exactly as before, and this is the
form that lets `simp` see it. -/
@[simp] theorem applyBindingsScoped_fvar_zero (lhs : Pattern) (bindings : Bindings)
    (x : String) :
    applyBindingsScoped lhs bindings 0 (.fvar x) = applyBindings bindings (.fvar x) := by
  simp only [applyBindingsScoped, applyBindings]
  cases bindings.find? (fun entry => entry.1 == x) with
  | none => rfl
  | some entry =>
      cases captureDepth x 0 lhs with
      | none => rfl
      | some dc =>
          simp only [Nat.zero_sub,
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- Apply a rule's right-hand side to a matcher result, scope-correctly. -/
def applyRuleBindings (rule : RewriteRule) (bindings : Bindings) : Pattern :=
  applyBindingsScoped rule.left bindings 0 rule.right

/-! ### Which rules the correction changes, and which it leaves alone

The shift a matched value receives is the difference between the depth at which
the rule's left-hand side captured it and the depth at which the right-hand side
uses it.  When those agree the shift is zero, so the corrected applier and the
plain one compute the same reduct, character for character.

That is the audit a change of executable semantics owes, and it is stated as a
theorem rather than performed as a survey: a rule is unaffected exactly when it
never moves a metavariable across a binder, which is exactly the class on which
the plain applier was already right.  The condition is decidable, so checking a
language definition against it is a computation. -/

mutual
/-- Every metavariable of the right-hand side sits at the depth its left-hand
side occurrence sits at. -/
def depthAligned (lhs : Pattern) : Nat → Pattern → Bool
  | d, .fvar x =>
      match captureDepth x 0 lhs with
      | some dx => dx == d
      | none => true
  | _, .bvar _ => true
  | d, .apply _ args => depthAlignedList lhs d args
  | d, .lambda _ body => depthAligned lhs (d + 1) body
  | d, .multiLambda n _ body => depthAligned lhs (d + n) body
  | d, .subst body repl => depthAligned lhs (d + 1) body && depthAligned lhs d repl
  | d, .collection _ elems rest =>
      depthAlignedList lhs d elems &&
        (match rest with
          | some rv =>
              match captureDepth rv 0 lhs with
              | some dx => dx == d
              | none => true
          | none => true)

def depthAlignedList (lhs : Pattern) : Nat → List Pattern → Bool
  | _, [] => true
  | d, p :: ps => depthAligned lhs d p && depthAlignedList lhs d ps
end

mutual
/-- **The correction is conservative where the rule does not cross a binder.** -/
theorem applyBindingsScoped_eq_applyBindings (lhs : Pattern) (bindings : Bindings) :
    ∀ (d : Nat) (rhs : Pattern), depthAligned lhs d rhs = true →
      applyBindingsScoped lhs bindings d rhs = applyBindings bindings rhs
  | d, .fvar x, h => by
      simp only [applyBindingsScoped, applyBindings]
      cases found : bindings.find? (fun entry => entry.1 == x) with
      | none => rfl
      | some entry =>
          cases captured : captureDepth x 0 lhs with
          | none => rfl
          | some dx =>
              simp only [depthAligned, captured, beq_iff_eq] at h
              subst h
              simp only [Nat.sub_self,
                Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  | _, .bvar _, _ => by simp only [applyBindingsScoped, applyBindings]
  | d, .apply c args, h => by
      simp only [depthAligned] at h
      simp only [applyBindingsScoped, applyBindings,
        applyBindingsScopedList_eq_applyBindingsMap lhs bindings d args h]
  | d, .lambda _ body, h => by
      simp only [depthAligned] at h
      simp only [applyBindingsScoped, applyBindings,
        applyBindingsScoped_eq_applyBindings lhs bindings (d + 1) body h]
  | d, .multiLambda n _ body, h => by
      simp only [depthAligned] at h
      simp only [applyBindingsScoped, applyBindings,
        applyBindingsScoped_eq_applyBindings lhs bindings (d + n) body h]
  | d, .subst body repl, h => by
      simp only [depthAligned, Bool.and_eq_true] at h
      simp only [applyBindingsScoped, applyBindings,
        applyBindingsScoped_eq_applyBindings lhs bindings (d + 1) body h.1,
        applyBindingsScoped_eq_applyBindings lhs bindings d repl h.2]
  | d, .collection ct elems rest, h => by
      simp only [depthAligned, Bool.and_eq_true] at h
      rw [applyBindings.eq_def]
      simp only [applyBindingsScoped,
        applyBindingsScopedList_eq_applyBindingsMap lhs bindings d elems h.1]
      cases rest with
      | none => simp [restSplice]
      | some rv =>
          simp only [restSplice]
          cases found : bindings.find? (fun entry => entry.1 == rv) with
          | none => simp
          | some entry =>
              obtain ⟨entryName, entryValue⟩ := entry
              cases entryValue with
              | collection boundCt relems boundRest =>
                  cases boundRest with
                  | some _ => simp
                  | none =>
                      by_cases sameKind : boundCt = ct
                      · subst sameKind
                        cases hdc : captureDepth rv 0 lhs with
                        | none => simp
                        | some dc =>
                            have hdd : dc = d := by
                              simp only [hdc, beq_iff_eq] at h
                              exact h.2
                            subst hdd
                            simp [map_liftBVars_zero]
                      · simp [sameKind]
              | _ => simp

theorem applyBindingsScopedList_eq_applyBindingsMap (lhs : Pattern)
    (bindings : Bindings) :
    ∀ (d : Nat) (ps : List Pattern), depthAlignedList lhs d ps = true →
      applyBindingsScopedList lhs bindings d ps = ps.map (applyBindings bindings)
  | _, [], _ => rfl
  | d, p :: ps, h => by
      simp only [depthAlignedList, Bool.and_eq_true] at h
      simp only [applyBindingsScopedList, List.map_cons,
        applyBindingsScoped_eq_applyBindings lhs bindings d p h.1,
        applyBindingsScopedList_eq_applyBindingsMap lhs bindings d ps h.2]
end

mutual
/-- A pattern with no binding former anywhere in it. -/
def binderFree : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ args => binderFreeList args
  | .lambda _ _ => false
  | .multiLambda _ _ _ => false
  | .subst _ _ => false
  | .collection _ elems _ => binderFreeList elems

def binderFreeList : List Pattern → Bool
  | [] => true
  | p :: ps => binderFree p && binderFreeList ps
end

mutual
/-- In a binder-free pattern every metavariable sits at the ambient depth. -/
theorem captureDepth_of_binderFree : ∀ (name : String) (d : Nat) (p : Pattern),
    binderFree p = true → ∀ k, captureDepth name d p = some k → k = d
  | _, _, .bvar _, _, _, h => by simp [captureDepth] at h
  | name, d, .fvar x, _, k, h => by
      simp only [captureDepth] at h
      split at h
      · injection h with h'; exact h'.symm
      · simp at h
  | name, d, .apply _ args, hp, k, h => by
      simp only [binderFree] at hp
      simp only [captureDepth] at h
      exact captureDepthList_of_binderFree name d args hp k h
  | _, _, .lambda _ _, hp, _, _ => by simp [binderFree] at hp
  | _, _, .multiLambda _ _ _, hp, _, _ => by simp [binderFree] at hp
  | _, _, .subst _ _, hp, _, _ => by simp [binderFree] at hp
  | name, d, .collection _ elems rest, hp, k, h => by
      simp only [binderFree] at hp
      simp only [captureDepth] at h
      cases hlist : captureDepthList name d elems with
      | some k' =>
          rw [hlist] at h
          injection h with h'
          exact h' ▸ captureDepthList_of_binderFree name d elems hp k' hlist
      | none =>
          rw [hlist] at h
          cases rest with
          | none => simp at h
          | some restVar =>
              by_cases same : restVar = name
              · simp only [same, beq_self_eq_true] at h
                injection h with h'
                exact h'.symm
              · simp only [beq_iff_eq, if_neg same] at h
                exact absurd h (by simp)

theorem captureDepthList_of_binderFree : ∀ (name : String) (d : Nat) (ps : List Pattern),
    binderFreeList ps = true → ∀ k, captureDepthList name d ps = some k → k = d
  | _, _, [], _, _, h => by simp [captureDepthList] at h
  | name, d, p :: ps, hp, k, h => by
      simp only [binderFreeList, Bool.and_eq_true] at hp
      simp only [captureDepthList] at h
      split at h
      · rename_i heq
        injection h with h'
        exact captureDepth_of_binderFree name d p hp.1 _ (h' ▸ heq)
      · exact captureDepthList_of_binderFree name d ps hp.2 k h
end

mutual
/-- **A rule between binder-free patterns is depth-aligned**, so the whole class
of languages that never bind is untouched by the correction without any of them
being checked one at a time. -/
theorem depthAligned_of_binderFree_aux : ∀ (lhs : Pattern) (d : Nat) (rhs : Pattern),
    (∀ x k, captureDepth x 0 lhs = some k → k = d) → binderFree rhs = true →
    depthAligned lhs d rhs = true
  | _, _, .bvar _, _, _ => rfl
  | lhs, d, .fvar x, hl, _ => by
      simp only [depthAligned]
      split
      · rename_i k heq
        simp only [beq_iff_eq]
        exact hl x k heq
      · rfl
  | lhs, d, .apply _ args, hl, hr => by
      simp only [binderFree] at hr
      simp only [depthAligned]
      exact depthAlignedList_of_binderFree_aux lhs d args hl hr
  | _, _, .lambda _ _, _, hr => by simp [binderFree] at hr
  | _, _, .multiLambda _ _ _, _, hr => by simp [binderFree] at hr
  | _, _, .subst _ _, _, hr => by simp [binderFree] at hr
  | lhs, d, .collection _ elems rest, hl, hr => by
      simp only [binderFree] at hr
      simp only [depthAligned, Bool.and_eq_true]
      refine ⟨depthAlignedList_of_binderFree_aux lhs d elems hl hr, ?_⟩
      cases rest with
      | none => rfl
      | some rv =>
          cases hdc : captureDepth rv 0 lhs with
          | none => simp [hdc]
          | some dc => simp [hdc, hl rv dc hdc]

theorem depthAlignedList_of_binderFree_aux : ∀ (lhs : Pattern) (d : Nat)
    (ps : List Pattern), (∀ x k, captureDepth x 0 lhs = some k → k = d) →
    binderFreeList ps = true → depthAlignedList lhs d ps = true
  | _, _, [], _, _ => rfl
  | lhs, d, p :: ps, hl, hr => by
      simp only [binderFreeList, Bool.and_eq_true] at hr
      simp only [depthAlignedList, Bool.and_eq_true]
      exact ⟨depthAligned_of_binderFree_aux lhs d p hl hr.1,
        depthAlignedList_of_binderFree_aux lhs d ps hl hr.2⟩
end

mutual
/-- **A right-hand side that binds nothing is applied exactly as before.**  The
traversal never leaves depth zero, and at depth zero the shift is zero whatever
the left-hand side did, so the two appliers agree outright.  This is the form
that keeps existing proofs about binder-free languages working unchanged. -/
theorem applyBindingsScoped_zero_of_binderFree (lhs : Pattern)
    (bindings : Bindings) : ∀ (rhs : Pattern), binderFree rhs = true →
      applyBindingsScoped lhs bindings 0 rhs = applyBindings bindings rhs
  | .fvar x, _ => applyBindingsScoped_fvar_zero lhs bindings x
  | .bvar _, _ => by simp only [applyBindingsScoped, applyBindings]
  | .apply c args, h => by
      simp only [binderFree] at h
      rw [applyBindings]
      simp only [applyBindingsScoped, applyBindingsScopedList_eq_map,
        applyBindingsScopedList_zero_of_binderFreeList lhs bindings args h]
  | .lambda _ _, h => by simp [binderFree] at h
  | .multiLambda _ _ _, h => by simp [binderFree] at h
  | .subst _ _, h => by simp [binderFree] at h
  | .collection ct elems rest, h => by
      simp only [binderFree] at h
      rw [applyBindings.eq_def]
      simp only [applyBindingsScoped, applyBindingsScopedList_eq_map,
        applyBindingsScopedList_zero_of_binderFreeList lhs bindings elems h]
      cases rest with
      | none => simp [restSplice]
      | some rv =>
          simp only [restSplice]
          cases found : bindings.find? (fun entry => entry.1 == rv) with
          | none => simp
          | some entry =>
              obtain ⟨entryName, entryValue⟩ := entry
              cases entryValue with
              | collection boundCt relems boundRest =>
                  cases boundRest with
                  | some _ => simp
                  | none =>
                      cases hdc : captureDepth rv 0 lhs with
                      | none => simp
                      | some dc => simp [map_liftBVars_zero]
              | _ => simp

theorem applyBindingsScopedList_zero_of_binderFreeList (lhs : Pattern)
    (bindings : Bindings) : ∀ (ps : List Pattern), binderFreeList ps = true →
      ps.map (applyBindingsScoped lhs bindings 0) = ps.map (applyBindings bindings)
  | [], _ => rfl
  | p :: ps, h => by
      simp only [binderFreeList, Bool.and_eq_true] at h
      simp only [List.map_cons,
        applyBindingsScoped_zero_of_binderFree lhs bindings p h.1,
        applyBindingsScopedList_zero_of_binderFreeList lhs bindings ps h.2]
end

attribute [simp] applyBindingsScoped_zero_of_binderFree

mutual
/-- Match-correctness is stronger than binder-freeness: it rejects the two
binder formers, explicit substitution and collections, while binder-freeness
rejects only the first three.  So every match-correct pattern is binder-free,
and a rule between match-correct patterns fires exactly as it did before the
scope correction. -/
theorem binderFree_of_isMatchCorrectAux : ∀ p : Pattern,
    isMatchCorrectAux p = true → binderFree p = true
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ args, h => by
      simp only [isMatchCorrectAux] at h
      simpa only [binderFree] using binderFreeList_of_isMatchCorrectListAux args h
  | .lambda _ _, h => by simp [isMatchCorrectAux] at h
  | .multiLambda _ _ _, h => by simp [isMatchCorrectAux] at h
  | .subst _ _, h => by simp [isMatchCorrectAux] at h
  | .collection _ _ _, h => by simp [isMatchCorrectAux] at h

/-- Ordered-list companion to `binderFree_of_isMatchCorrectAux`. -/
theorem binderFreeList_of_isMatchCorrectListAux : ∀ ps : List Pattern,
    isMatchCorrectListAux ps = true → binderFreeList ps = true
  | [], _ => rfl
  | p :: ps, h => by
      simp only [isMatchCorrectListAux, Bool.and_eq_true] at h
      simp only [binderFreeList, Bool.and_eq_true]
      exact ⟨binderFree_of_isMatchCorrectAux p h.1,
        binderFreeList_of_isMatchCorrectListAux ps h.2⟩
end

/-- A rule none of whose metavariables crosses a binder. -/
def ruleDepthAligned (rule : RewriteRule) : Bool :=
  depthAligned rule.left 0 rule.right

/-- **A rule between binder-free patterns is depth-aligned.**  Every language
whose rules never bind is therefore untouched by the correction, with no
per-language check. -/
theorem ruleDepthAligned_of_binderFree (rule : RewriteRule)
    (hl : binderFree rule.left = true) (hr : binderFree rule.right = true) :
    ruleDepthAligned rule = true :=
  depthAligned_of_binderFree_aux rule.left 0 rule.right
    (fun x k heq => captureDepth_of_binderFree x 0 rule.left hl k heq) hr

/-- **Such a rule fires exactly as it did before the correction.** -/
theorem applyRuleBindings_eq_applyBindings (rule : RewriteRule) (bindings : Bindings)
    (aligned : ruleDepthAligned rule = true) :
    applyRuleBindings rule bindings = applyBindings bindings rule.right :=
  applyBindingsScoped_eq_applyBindings rule.left bindings 0 rule.right aligned

/-- Apply a single rewrite rule to a term (top-level match only).
    Returns all possible reducts. Skips rules with premises (congruence
    premises require recursive reduction, handled by the full engine). -/
def applyRule (rule : RewriteRule) (term : Pattern) : List Pattern :=
  if rule.premises.isEmpty then
    (matchPattern rule.left term).map fun b => applyRuleBindings rule b
  else []

/-- **So its whole step relation is unchanged.**  A language definition all of
whose rules are depth-aligned computes the same reducts it computed before, and
the condition is decidable, so that is checkable per language rather than
argued. -/
theorem applyRule_eq_old (rule : RewriteRule) (term : Pattern)
    (aligned : ruleDepthAligned rule = true) :
    applyRule rule term
      = (if rule.premises.isEmpty then
          (matchPattern rule.left term).map (fun b => applyBindings b rule.right)
        else []) := by
  simp only [applyRule]
  by_cases premiseFree : rule.premises.isEmpty
  · simp only [premiseFree, if_true]
    exact List.map_congr_left fun b _ =>
      applyRuleBindings_eq_applyBindings rule b aligned
  · simp [premiseFree]


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
