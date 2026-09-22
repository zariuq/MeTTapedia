import Mathlib.Data.List.Basic

/-!
# Requirements, compatibility, and determination

Exhibiting an admissible candidate does not prove that requirements force its
features. `Determined` includes an inhabited admissible class, excluding a
vacuous implication from inconsistent requirements. Its property is an actual
predicate, not a status label or a string naming a theorem.

The finite expression language below is a countermodel to one particular
inference: preserving unevaluated quoted syntax does not force non-strict
evaluation of ordinary arguments. It makes no claim about stronger modal
axioms, general recursion, effects beyond the recorded tick, or full languages.
-/

namespace Mettapedia.TypeTheory.DesignDetermination

universe u

structure Determined {Candidate : Type u}
    (admissible property : Candidate → Prop) : Prop where
  inhabited : ∃ candidate, admissible candidate
  entails : ∀ candidate, admissible candidate → property candidate

theorem counterexample_excludes_determination {Candidate : Type u}
    {admissible property : Candidate → Prop} {candidate : Candidate}
    (accepted : admissible candidate) (fails : ¬ property candidate) :
    ¬ Determined admissible property := by
  intro determination
  exact fails (determination.entails candidate accepted)

theorem incompatible_requirements_determine_nothing {Candidate : Type u}
    {admissible property : Candidate → Prop}
    (impossible : ¬ ∃ candidate, admissible candidate) :
    ¬ Determined admissible property := by
  intro determination
  exact impossible determination.inhabited

namespace QuotationCountermodel

inductive Expr where
  | literal (value : Nat)
  | tick
  | quote (body : Expr)
  | discard (argument body : Expr)
  deriving DecidableEq, Repr

inductive Value where
  | number (value : Nat)
  | syntax (body : Expr)
  deriving DecidableEq, Repr

inductive Strategy where
  | eager
  | byName
  deriving DecidableEq, Repr

/-- The second component records executed ticks. Quotation retains syntax;
ordinary discarded arguments are evaluated only by the eager strategy. -/
def evaluate (strategy : Strategy) : Expr → Value × Nat
  | .literal n => (.number n, 0)
  | .tick => (.number 0, 1)
  | .quote body => (.syntax body, 0)
  | .discard argument body =>
      let result := evaluate strategy body
      match strategy with
      | .eager => (result.1, (evaluate strategy argument).2 + result.2)
      | .byName => result

def QuotesWithoutExecution (strategy : Strategy) : Prop :=
  ∀ body, evaluate strategy (.quote body) = (.syntax body, 0)

def SkipsDiscardedTick (strategy : Strategy) : Prop :=
  evaluate strategy (.discard .tick (.literal 7)) = (.number 7, 0)

theorem eager_quotes_without_execution : QuotesWithoutExecution .eager := by
  intro body
  rfl

theorem byName_quotes_without_execution : QuotesWithoutExecution .byName := by
  intro body
  rfl

theorem eager_executes_discarded_tick :
    evaluate .eager (.discard .tick (.literal 7)) = (.number 7, 1) := rfl

theorem byName_skips_discarded_tick : SkipsDiscardedTick .byName := rfl

theorem quotation_does_not_determine_non_strictness :
    ¬ Determined QuotesWithoutExecution SkipsDiscardedTick := by
  apply counterexample_excludes_determination eager_quotes_without_execution
  simp [SkipsDiscardedTick, evaluate]

/-- Within this explicit two-strategy comparison, the extra demand property
does distinguish the alternatives. This does not rank all possible machines. -/
theorem demand_property_determines_byName :
    Determined (fun strategy => QuotesWithoutExecution strategy ∧
      SkipsDiscardedTick strategy) (fun strategy => strategy = .byName) := by
  refine ⟨⟨.byName, byName_quotes_without_execution, byName_skips_discarded_tick⟩, ?_⟩
  intro strategy properties
  cases strategy with
  | eager => exact False.elim (by simpa [SkipsDiscardedTick, evaluate] using properties.2)
  | byName => rfl

end QuotationCountermodel

#print axioms QuotationCountermodel.quotation_does_not_determine_non_strictness
#print axioms QuotationCountermodel.demand_property_determines_byName

end Mettapedia.TypeTheory.DesignDetermination
