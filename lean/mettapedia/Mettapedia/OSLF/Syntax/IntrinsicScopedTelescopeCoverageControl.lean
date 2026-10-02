import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPolynomial
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# An unused global parameter can obstruct a real firing

The live sort has a closed token; the other sort has no closed terms.
The constant token rule uses no metavariables. Requiring an assignment to
an unrelated global declaration nevertheless prevents its closed firing.
The same rule with its actual empty telescope has a firing tree.

Thus restricting global assignments to a local support does not itself
prove coverage: extending the local assignment requires genuine values
for every discarded declaration.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedTelescopeCoverageControl

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

inductive Srt where
  | live
  | unused

inductive Op : Srt → Type where
  | token : Op .live

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun _ => []

def token {Γ : Ctx sig} : Term sig Γ Srt.live := .op Op.token .nil

/-- There is no closed value with which to fill the unused declaration. -/
theorem no_closed_unused (term : Term sig [] Srt.unused) : False := by
  cases term with
  | var v => nomatch v
  | op operator arguments => nomatch operator

abbrev globalMetas : List (MetaArity sig) := [([], Srt.unused)]

/-- This authored rule does not refer to any member of its declared telescope. -/
def tokenRule (M : List (MetaArity sig)) :
    IntrinsicScopedConditionalPolynomial.Rule sig M where
  conclusion :=
    let source : Term (withMetas sig M) [] Srt.live := .op (Sum.inl Op.token) .nil
    ⟨[], Srt.live, source, source, rootPosition source⟩
  premises := []

abbrev algebra := BindingCloneAlgebra.terms sig

/-- A global assignment cannot be completed at the empty ordinary scope. -/
theorem no_global_closed_occurrence
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance
      [tokenRule globalMetas] algebra) (closed : occurrence.ambient = []) : False := by
  have value := occurrence.valuation (⟨0, by decide⟩ : Fin globalMetas.length)
  change Term sig occurrence.ambient Srt.unused at value
  rw [closed] at value
  exact no_closed_unused value

/-- In particular the shared presentation admits no firing at this judgment. -/
theorem no_global_closed_tree
    (tree : IntrinsicScopedConditionalSubstitution.Tree [tokenRule globalMetas] algebra
      (⟨[], Srt.live, token, token⟩ : Judgment algebra)) : False := by
  obtain ⟨shape, children⟩ := IndexedPolynomial.Fix.out _ tree
  have ambient : shape.1.ambient = [] := congrArg Sigma.fst shape.2
  exact no_global_closed_occurrence shape.1 ambient

abbrev localRules : List (IntrinsicScopedLocalPolynomial.LocalRule sig) :=
  [⟨[], tokenRule []⟩]

/-- Removing the unrelated declaration needs no invented value at its sort. -/
def localOccurrence : IntrinsicScopedLocalPolynomial.Instance localRules algebra where
  index := ⟨0, by decide⟩
  ambient := []
  valuation := fun index => Fin.elim0 index
  close := fun _ v => nomatch v

theorem local_conclusion :
    IntrinsicScopedLocalPolynomial.conclusionJudgment localRules algebra localOccurrence =
      (⟨[], Srt.live, token, token⟩ : Judgment algebra) := rfl

/-- The rule-local presentation has an actual closed constructor tree. -/
def localTree : IntrinsicScopedLocalPolynomial.Tree localRules algebra
    (⟨[], Srt.live, token, token⟩ : Judgment algebra) :=
  .roll ⟨localOccurrence, local_conclusion⟩ (fun position => Fin.elim0 position)

/-- Closed-firing coverage cannot be inferred from pruning alone. -/
theorem local_firing_without_global_extension :
    Nonempty (IntrinsicScopedLocalPolynomial.Tree localRules algebra
      (⟨[], Srt.live, token, token⟩ : Judgment algebra)) ∧
    ¬ Nonempty (IntrinsicScopedConditionalSubstitution.Tree [tokenRule globalMetas] algebra
      (⟨[], Srt.live, token, token⟩ : Judgment algebra)) :=
  ⟨⟨localTree⟩, fun ⟨tree⟩ => no_global_closed_tree tree⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedTelescopeCoverageControl
