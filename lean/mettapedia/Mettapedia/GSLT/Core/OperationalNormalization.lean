import Mettapedia.GSLT.Core.OperationalReadback
import Mathlib.Order.WellFounded

/-!
# Normalization reflected by positive implementation blocks

Finite operational correspondence alone permits a source transition to be
implemented by an empty path. A positive implementation block instead gives
a strict descent in the target's transitive reduction relation. Target
accessibility then implies source accessibility, independently of any bound
on administrative execution. Such a bound is needed for the converse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

universe uSource uTarget

namespace ExecutionPath

variable {target : GSLT.{uTarget}}

/-- An actual finite execution is either empty at its endpoints or a
strict descent for the backwards-oriented target reduction relation. -/
theorem endpoint_eq_or_transGen {current final : target.Term}
    (path : ExecutionPath target current final) :
    current = final ∨ Relation.TransGen (fun next state => target.Step state next) final current := by
  induction path with
  | refl state => exact .inl rfl
  | cons first rest ih =>
      rcases ih with same | descended
      · subst same
        exact .inr (.single first.down)
      · exact .inr (.tail descended first.down)

/-- Positive length rules out using an empty implementation as a descent. -/
theorem transGen_of_positive {current final : target.Term}
    (path : ExecutionPath target current final) (positive : 0 < path.length) :
    Relation.TransGen (fun next state => target.Step state next) final current := by
  cases path with
  | refl state =>
      change 0 < 0 at positive
      exact False.elim (Nat.lt_irrefl 0 positive)
  | cons first rest =>
      rcases endpoint_eq_or_transGen rest with same | descended
      · subst same
        exact .single first.down
      · exact .tail descended first.down

end ExecutionPath

namespace OperationalCorrespondence

variable {source : GSLT.{uSource}} {target : GSLT.{uTarget}}

/-- Every actual source step must have a positive target implementation
from every related phase. The descent proof uses those supplied blocks. -/
theorem normalization_reflected (comparison : OperationalCorrespondence source target)
    (positiveForward : ∀ {origin after : source.Term} {current : target.Term},
      comparison.related origin current → source.Step origin after →
      ∃ final, ∃ path : ExecutionPath target current final,
        0 < path.length ∧ comparison.related after final)
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (normalizing : Acc (fun next state => target.Step state next) current) :
    Acc (fun after before => source.Step before after) origin := by
  have strict := normalizing.transGen
  clear normalizing
  induction strict generalizing origin with
  | intro current _ ih =>
      apply Acc.intro origin
      intro after firing
      obtain ⟨final, path, positive, preserved⟩ := positiveForward related firing
      exact ih final (ExecutionPath.transGen_of_positive path positive) preserved

/-- A genuine infinite source execution cannot be hidden by a
correspondence whose implementation blocks are all positive. -/
theorem infinite_execution_preserved (comparison : OperationalCorrespondence source target)
    (positiveForward : ∀ {origin after : source.Term} {current : target.Term},
      comparison.related origin current → source.Step origin after →
      ∃ final, ∃ path : ExecutionPath target current final,
        0 < path.length ∧ comparison.related after final)
    {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (execution : Nat → source.Term) (starts : execution 0 = origin)
    (firings : ∀ index, source.Step (execution index) (execution (index + 1))) :
    ∃ runtime : Nat → target.Term, runtime 0 = current ∧
      ∀ index, target.Step (runtime index) (runtime (index + 1)) := by
  have divergent : ¬ Acc (fun after before => source.Step before after) origin :=
    not_acc_iff_exists_descending_chain.mpr ⟨execution, starts, firings⟩
  have targetDivergent : ¬ Acc (fun next state => target.Step state next) current :=
    fun normalizing => divergent (comparison.normalization_reflected positiveForward related normalizing)
  exact not_acc_iff_exists_descending_chain.mp targetDivergent

end OperationalCorrespondence

end Mettapedia.GSLT.IndexedOperational
