import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.GSLT.Core.OperationalRealizationAccounts

/-!
# Accounting for arbitrary implementation prefixes

An implementation phase has a natural-number potential. An administrative
step spends one unit of that potential; a source transition replenishes it
by the transition's existing run account. This local law bounds every
supplied target execution, including unfinished and interleaved phases.
It accounts for actual transitions rather than only a selected forward
implementation. The potential may depend on the related source state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Effects

universe uSource uTarget

namespace OperationalReadback

variable {source : GSLT.{uSource}} {target : GSLT.{uTarget}}

/-- A strengthened readback law with an independently specified source
account. Its allowance includes the implementation step that exposes the
source transition. -/
structure Account (comparison : OperationalReadback source target) where
  sourceAccount : RunAccount (ExecutionObject source) (Multiplicative Nat)
  potential : source.Term → target.Term → Nat
  readStep : ∀ {origin : source.Term} {current next : target.Term},
    comparison.related origin current → target.Step current next →
      (comparison.related origin next ∧ potential origin next + 1 ≤ potential origin current) ∨
      ∃ (after : source.Term) (step : source.Step origin after),
        comparison.related after next ∧
          potential after next + 1 ≤ potential origin current +
            Multiplicative.toAdd (sourceAccount.of (.cons ⟨step⟩ (.refl after)))

namespace Account

/-- Retained source paths use the already defined account of their runs. -/
theorem charge_cons (account : RunAccount (ExecutionObject source) (Multiplicative Nat))
    {first middle last : source.Term} (step : source.Step first middle)
    (rest : ExecutionPath source middle last) :
    Multiplicative.toAdd (account.of (.cons ⟨step⟩ rest)) =
      Multiplicative.toAdd (account.of (.cons ⟨step⟩ (.refl middle))) +
        Multiplicative.toAdd (account.of rest) := by
  have concatenation := account.of_comp (.cons ⟨step⟩ (.refl middle)) rest
  exact congrArg Multiplicative.toAdd concatenation

/-- Every actual prefix reflects with an amortized bound and the literal
supplied endpoint. The retained source path has no more transitions than
the target path. -/
theorem reflectPath {comparison : OperationalReadback source target}
    (account : comparison.Account)
    {origin : source.Term} {current final : target.Term}
    (related : comparison.related origin current)
    (path : ExecutionPath target current final) :
    ∃ after, ∃ sourcePath : ExecutionPath source origin after,
      comparison.related after final ∧ sourcePath.length ≤ path.length ∧
        path.length + account.potential after final ≤
          account.potential origin current +
            Multiplicative.toAdd (account.sourceAccount.of sourcePath) := by
  induction path generalizing origin with
  | refl state =>
      refine ⟨origin, .refl origin, related, le_rfl, ?_⟩
      simpa only [Route.length, Nat.zero_add] using
        Nat.le_add_right (account.potential origin state)
          (Multiplicative.toAdd (account.sourceAccount.of (.refl origin)))
  | cons first rest ih =>
      rcases account.readStep related first.down with unchanged | advanced
      · obtain ⟨nextRelated, spent⟩ := unchanged
        obtain ⟨after, sourcePath, finalRelated, lengthBound, chargeBound⟩ := ih nextRelated
        refine ⟨after, sourcePath, finalRelated, ?_, ?_⟩
        · change sourcePath.length ≤ rest.length + 1
          omega
        · change rest.length + 1 + account.potential after _ ≤ _
          omega
      · obtain ⟨next, step, nextRelated, replenished⟩ := advanced
        obtain ⟨after, sourcePath, finalRelated, lengthBound, chargeBound⟩ := ih nextRelated
        refine ⟨after, .cons ⟨step⟩ sourcePath, finalRelated, ?_, ?_⟩
        · change sourcePath.length + 1 ≤ rest.length + 1
          omega
        · change rest.length + 1 + account.potential after _ ≤
            account.potential origin _ +
              Multiplicative.toAdd (account.sourceAccount.of (.cons ⟨step⟩ sourcePath))
          have charged := charge_cons account.sourceAccount step sourcePath
          omega

/-- Forgetting the remaining potential gives an upper bound on all target
instructions, rather than on one scheduler's selected implementation. -/
theorem reflectPath_length_bound {comparison : OperationalReadback source target}
    (account : comparison.Account)
    {origin : source.Term} {current final : target.Term}
    (related : comparison.related origin current)
    (path : ExecutionPath target current final) :
    ∃ after, ∃ sourcePath : ExecutionPath source origin after,
      comparison.related after final ∧ sourcePath.length ≤ path.length ∧
        path.length ≤ account.potential origin current +
          Multiplicative.toAdd (account.sourceAccount.of sourcePath) := by
  obtain ⟨after, sourcePath, finalRelated, lengthBound, bound⟩ := account.reflectPath related path
  exact ⟨after, sourcePath, finalRelated, lengthBound, by omega⟩

/-- Once the source is terminal, every remaining target instruction is
administrative and is bounded by the current phase potential. -/
theorem terminal_path_bound {comparison : OperationalReadback source target}
    (account : comparison.Account) {origin : source.Term} {current final : target.Term}
    (related : comparison.related origin current)
    (terminal : ∀ after, ¬ source.Step origin after)
    (path : ExecutionPath target current final) :
    path.length ≤ account.potential origin current := by
  obtain ⟨after, reflected, _, _, bounded⟩ := account.reflectPath related path
  cases reflected with
  | refl =>
      have identity := account.sourceAccount.of_id (origin : ExecutionObject source)
      change account.sourceAccount.of (.refl origin) = 1 at identity
      have zeroCharge : Multiplicative.toAdd (account.sourceAccount.of (.refl origin)) = 0 :=
        congrArg Multiplicative.toAdd identity
      omega
  | cons first rest => exact False.elim (terminal _ first.down)

/-- A source-terminal phase cannot contain an unbounded target-only run.
This is stronger than merely preserving successful finite executions. -/
theorem no_infinite_terminal_run {comparison : OperationalReadback source target}
    (account : comparison.Account) {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (terminal : ∀ after, ¬ source.Step origin after) :
    ¬ ∃ states : Nat → target.Term, states 0 = current ∧
      ∀ index, target.Step (states index) (states (index + 1)) := by
  rintro ⟨states, starts, steps⟩
  have countedPaths : ∀ count, ∃ path : ExecutionPath target (states 0) (states count),
      path.length = count := by
    intro count
    induction count with
    | zero => exact ⟨.refl _, rfl⟩
    | succ count ih =>
        obtain ⟨path, length⟩ := ih
        refine ⟨path.append (.cons ⟨steps count⟩ (.refl _)), ?_⟩
        simp only [Route.length_append, Route.length, Nat.zero_add, length]
  obtain ⟨path, length⟩ := countedPaths (account.potential origin current + 1)
  have firstRelated : comparison.related origin (states 0) := starts ▸ related
  have bounded := account.terminal_path_bound firstRelated terminal path
  rw [length, starts] at bounded
  omega

/-- An invisible target self-loop cannot satisfy an administrative account
at a terminal source state. It cannot be hidden as cost-free stuttering. -/
theorem excludes_terminal_self_loop {comparison : OperationalReadback source target}
    (account : comparison.Account) {origin : source.Term} {current : target.Term}
    (related : comparison.related origin current)
    (terminal : ∀ after, ¬ source.Step origin after) :
    ¬ target.Step current current := by
  intro loop
  rcases account.readStep related loop with administrative | advanced
  · have bound := administrative.2
    omega
  · obtain ⟨after, step, _⟩ := advanced
    exact terminal after step

end Account
end OperationalReadback

end Mettapedia.GSLT.IndexedOperational
