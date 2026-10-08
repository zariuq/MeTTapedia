import Mettapedia.Logic.LP.RigidUnificationComposition
import Mettapedia.Logic.LP.Narrowing

/-!
# Joint matching of open first-order terms

The subjects may contain variables. Every identity present in any subject is
fixed throughout the batch, including identities also present in patterns.
Successful answers instantiate patterns without instantiating subjects.
-/

namespace Mettapedia.Logic.LP.DirectionalMatching

universe u v
variable {σ : LPSignature.{u, u, v, u}} [DecidableEq σ.vars]

def subjectVars : List (Term σ × Term σ) → Finset σ.vars
  | [] => ∅
  | pair :: rest => pair.2.freeVars ∪ subjectVars rest

@[simp] theorem mem_subjectVars (equations : List (Term σ × Term σ)) (name : σ.vars) :
    name ∈ subjectVars equations ↔ ∃ pair ∈ equations, name ∈ pair.2.freeVars := by
  induction equations with
  | nil => simp [subjectVars]
  | cons pair rest ih => simp [subjectVars, ih]

def Matches (answer : Subst σ) (equations : List (Term σ × Term σ)) : Prop :=
  ∀ pair ∈ equations, answer.applyTerm pair.1 = pair.2

def matchMany [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  RigidUnification.solve (fun name => name ∈ subjectVars equations) equations

theorem fixes_subject {equations : List (Term σ × Term σ)} {answer : Subst σ}
    (fixed : RigidUnification.Fixes (fun name => name ∈ subjectVars equations) answer)
    {pair : Term σ × Term σ} (member : pair ∈ equations) :
    answer.applyTerm pair.2 = pair.2 := by
  apply Subst.applyTerm_eq_self
  intro name present
  exact fixed name ((mem_subjectVars equations name).mpr ⟨pair, member, present⟩)

theorem matchMany_sound [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (answer : Subst σ)
    (accepted : matchMany equations = some answer) :
    RigidUnification.Fixes (fun name => name ∈ subjectVars equations) answer ∧
      Matches answer equations := by
  obtain ⟨fixed, solves⟩ := RigidUnification.solve_sound _ equations answer accepted
  refine ⟨fixed, fun pair member => ?_⟩
  exact (solves pair member).trans (fixes_subject fixed member)

theorem matchMany_complete [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun name => name ∈ subjectVars equations) answer)
    (matched : Matches answer equations) :
    ∃ result, matchMany equations = some result := by
  apply RigidUnification.solve_complete
  refine ⟨answer, fixed, fun pair member => ?_⟩
  exact (matched pair member).trans (fixes_subject fixed member).symm

theorem matchMany_none_iff [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) :
    matchMany equations = none ↔
      ¬∃ answer, RigidUnification.Fixes (fun name => name ∈ subjectVars equations) answer ∧
        Matches answer equations := by
  constructor
  · intro rejected solvable
    obtain ⟨answer, fixed, matched⟩ := solvable
    obtain ⟨result, accepted⟩ := matchMany_complete equations answer fixed matched
    simp [rejected] at accepted
  · intro impossible
    cases h : matchMany equations with
    | none => rfl
    | some answer => exact False.elim (impossible ⟨answer, matchMany_sound equations answer h⟩)

omit [DecidableEq σ.vars] in
/-- Duplicate uses of a pattern must produce the same subject, even when
    the uses occur in different constraints. -/
theorem repeated_pattern_consistent {equations : List (Term σ × Term σ)}
    {answer : Subst σ} (matched : Matches answer equations)
    {pattern left right : Term σ}
    (hl : (pattern, left) ∈ equations) (hr : (pattern, right) ∈ equations) :
    left = right := (matched _ hl).symm.trans (matched _ hr)

/-- Equality of a whole instantiated term determines the images of all its
    variables. This is stronger than agreement on printed variable names. -/
theorem images_equal_of_term_equal {left right : Subst σ} {term : Term σ}
    (same : left.applyTerm term = right.applyTerm term) :
    ∀ name ∈ term.freeVars, left name = right name := by
  induction term with
  | var name =>
    intro other member
    have equal : other = name := by simpa [Term.freeVars] using member
    subst other
    exact same
  | const c => simp [Term.freeVars]
  | app f args ih =>
    simp only [Subst.applyTerm_app, Term.app.injEq, heq_eq_eq, true_and] at same
    intro name member
    obtain ⟨i, present⟩ := Term.mem_freeVars_app.mp member
    exact ih i (congrFun same i) name present

/-- Matching has a unique image for every observed pattern variable. -/
theorem matching_images_unique {equations : List (Term σ × Term σ)}
    {left right : Subst σ} (hl : Matches left equations) (hr : Matches right equations)
    {pair : Term σ × Term σ} (member : pair ∈ equations) :
    ∀ name ∈ pair.1.freeVars, left name = right name :=
  images_equal_of_term_equal ((hl pair member).trans (hr pair member).symm)

def reversePairs (equations : List (Term σ × Term σ)) : List (Term σ × Term σ) :=
  equations.map Prod.swap

omit [DecidableEq σ.vars] in
@[simp] theorem reversePairs_twice (equations : List (Term σ × Term σ)) :
    reversePairs (reversePairs equations) = equations := by
  simp [reversePairs, List.map_map, Function.comp_def]

omit [DecidableEq σ.vars] in
/-- Converse matching substitutes the original subjects, not the queries. -/
theorem converse_matches (equations : List (Term σ × Term σ)) (answer : Subst σ) :
    Matches answer (reversePairs equations) ↔
      ∀ pair ∈ equations, answer.applyTerm pair.2 = pair.1 := by
  constructor
  · intro matched pair member
    exact matched pair.swap (List.mem_map.mpr ⟨pair, member, rfl⟩)
  · intro matched pair member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact matched original present

/-- The native rule-head contract yields a genuine rewriting step. This
    theorem concerns head application, not evaluation or effects of the body. -/
theorem rule_match_rewrites [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (rules : Set (FirstOrderRewriting.Equation σ))
    (rule : FirstOrderRewriting.Equation σ) (member : rule ∈ rules)
    (call : Term σ) (answer : Subst σ)
    (accepted : matchMany [(rule.left, call)] = some answer) :
    FirstOrderRewriting.Rewrite rules call (answer.applyTerm rule.right) := by
  have matched := (matchMany_sound [(rule.left, call)] answer accepted).2
  have head := matched (rule.left, call) (by simp)
  have step := FirstOrderRewriting.Rewrite.rule rule member answer
    (FirstOrderRewriting.Context.hole : FirstOrderRewriting.Context σ)
  simpa only [FirstOrderRewriting.Context.fill, head] using step

end Mettapedia.Logic.LP.DirectionalMatching
