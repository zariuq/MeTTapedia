import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Generic derivation search over an authored presentation

The repair of the banked union disagreement: search compiled FROM the
presentation's own `RuleSchema` data, not from a hand mirror.  For a
ground goal the search enumerates EVERY rule in authored order, matches
the goal against each rule's conclusion by one-sided matching (nonlinear
metavariables checked by structural equality), instantiates premises
through the checker's own `instantiateRule?` — never a second
instantiation semantics — and recurses under an explicit fuel bound.

Every candidate proof is validated with `checkRaw` before it is
returned, so the single soundness theorem that matters —

    found proof  →  checkRaw presentation goal proof = true

— holds BY CONSTRUCTION: the authored checker is the only judge, and the
search is merely its client.  Fuel exhaustion is a distinct outcome from
a closed (fully traversed) search, so the four-valued verdict discipline
above this searcher never mistakes a resource bound for semantic
absence.

Environments enter as presentation EXTENSIONS (runtime declarations are
zero-premise rules added through the validated-extension calculus), so
this one searcher serves every layer of a presentation tower.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceSearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## One-sided matching (goal against a rule conclusion)

Metavariables are the rule's arity-0 formals (`.fvar name`); the goal is
ground.  A repeated metavariable must match structurally equal subterms.
Only the constructor fragment (`.fvar`/`.apply`) participates — the same
projectable fragment the relational renderer admits. -/

abbrev Assignment := List (String × Pattern)

def Assignment.lookup (assignment : Assignment) (name : String) :
    Option Pattern :=
  match assignment with
  | [] => none
  | (key, value) :: rest =>
      if key = name then some value else Assignment.lookup rest name

mutual

/-- Match a schema pattern against a ground goal, extending the
assignment; nonlinear occurrences must agree by structural equality. -/
def matchPattern (schema goal : Pattern) (assignment : Assignment) :
    Option Assignment :=
  match schema with
  | .fvar name =>
      match assignment.lookup name with
      | some bound => if bound = goal then some assignment else none
      | none => some ((name, goal) :: assignment)
  | .apply head arguments =>
      match goal with
      | .apply goalHead goalArguments =>
          if head = goalHead then
            matchPatterns arguments goalArguments assignment
          else none
      | _ => none
  | _ => none

def matchPatterns (schemas goals : List Pattern)
    (assignment : Assignment) : Option Assignment :=
  match schemas, goals with
  | [], [] => some assignment
  | schema :: restSchemas, goal :: restGoals =>
      match matchPattern schema goal assignment with
      | some extended => matchPatterns restSchemas restGoals extended
      | none => none
  | _, _ => none

end

/-- Arguments in the rule's declared metavariable order (total exactly
when the match bound every metavariable). -/
def argumentsFor (rule : RuleSchema) (assignment : Assignment) :
    Option (List Pattern) :=
  rule.metavariables.foldr
    (fun formal acc => do
      let arguments ← acc
      let value ← assignment.lookup formal.1
      pure (value :: arguments))
    (some [])

/-! ## Search outcomes -/

inductive SearchOutcome where
  /-- A proof that the AUTHORED checker has already accepted. -/
  | found (proof : RawProof)
  /-- The bounded search space was fully traversed without a proof. -/
  | closed
  /-- The fuel bound interrupted the traversal: NOT semantic absence. -/
  | exhausted
deriving Repr

/-- Combine sibling outcomes: a proof wins; an exhaustion taints a
closed traversal (we cannot claim the space was covered). -/
def SearchOutcome.orElse (first : SearchOutcome)
    (second : Unit → SearchOutcome) : SearchOutcome :=
  match first with
  | .found proof => .found proof
  | .closed => second ()
  | .exhausted =>
      match second () with
      | .found proof => .found proof
      | _ => .exhausted

inductive PremiseOutcome where
  | proved (proofs : List RawProof)
  | failed
  | exhausted

mutual

/-- Fair backward search: every rule of the presentation is tried in
authored order. -/
def searchGoal (presentation : ValidatedPresentation) (fuel : Nat)
    (goal : Pattern) : SearchOutcome :=
  match fuel with
  | 0 => .exhausted
  | fuel + 1 => searchRules presentation fuel presentation.1.rules goal

def searchRules (presentation : ValidatedPresentation) (fuel : Nat)
    (rules : List RuleSchema) (goal : Pattern) : SearchOutcome :=
  match rules with
  | [] => .closed
  | rule :: rest =>
      (searchViaRule presentation fuel rule goal).orElse fun () =>
        searchRules presentation fuel rest goal

def searchViaRule (presentation : ValidatedPresentation) (fuel : Nat)
    (rule : RuleSchema) (goal : Pattern) : SearchOutcome :=
  match matchPattern rule.conclusion goal [] with
  | none => .closed
  | some assignment =>
      match argumentsFor rule assignment with
      | none => .closed
      | some arguments =>
          match instantiateRule? presentation
              { ruleId := rule.id, arguments } with
          | none => .closed
          | some instantiated =>
              match searchPremises presentation fuel
                  instantiated.1 with
              | .failed => .closed
              | .exhausted => .exhausted
              | .proved childProofs =>
                  /- The authored checker is the only judge: an
                  unverified candidate is never returned. -/
                  if checkRaw presentation goal
                      (.node { ruleId := rule.id, arguments }
                        childProofs) then
                    .found
                      (.node { ruleId := rule.id, arguments }
                        childProofs)
                  else .closed

def searchPremises (presentation : ValidatedPresentation) (fuel : Nat)
    (premises : List Pattern) : PremiseOutcome :=
  match premises with
  | [] => .proved []
  | premise :: rest =>
      match searchGoal presentation fuel premise with
      | .exhausted => .exhausted
      | .closed => .failed
      | .found proof =>
          match searchPremises presentation fuel rest with
          | .proved proofs => .proved (proof :: proofs)
          | .failed => .failed
          | .exhausted => .exhausted

end

/-! ## Soundness, by construction -/

theorem searchViaRule_found_checkRaw
    {presentation fuel rule goal proof}
    (h : searchViaRule presentation fuel rule goal = .found proof) :
    checkRaw presentation goal proof = true := by
  unfold searchViaRule at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · split at h
          · rename_i hcheck
            cases h
            exact hcheck
          · cases h

theorem searchRules_found_checkRaw
    {presentation fuel goal proof} :
    ∀ {rules}, searchRules presentation fuel rules goal = .found proof →
      checkRaw presentation goal proof = true := by
  intro rules
  induction rules with
  | nil => intro h; simp [searchRules] at h
  | cons rule rest ih =>
      intro h
      unfold searchRules at h
      unfold SearchOutcome.orElse at h
      split at h
      · rename_i hvia
        cases h
        exact searchViaRule_found_checkRaw hvia
      · exact ih h
      · split at h
        · rename_i hrest
          cases h
          exact ih hrest
        · cases h

/-- THE soundness theorem: whatever this searcher returns, the authored
checker has already accepted.  Every verdict layer and every specialized
executor built over this search inherits it. -/
theorem searchGoal_found_checkRaw
    {presentation fuel goal proof}
    (h : searchGoal presentation fuel goal = .found proof) :
    checkRaw presentation goal proof = true := by
  unfold searchGoal at h
  split at h
  · cases h
  · exact searchRules_found_checkRaw h

end Mettapedia.GSLT.LanguageDef.InferenceSearch
