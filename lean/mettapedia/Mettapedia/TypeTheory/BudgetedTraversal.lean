import Mathlib.Data.Option.Basic
import Lean.Elab.Tactic.Omega

/-!
# Evidence-retaining traversal with one allowance

A checker returns evidence and the allowance it did not use. A finite batch
passes that allowance to the next check. Successful batches retain evidence
at each source position, including repeated queries. They do not restart the
producer bound or replay checks to obtain a resource account.

The generic composition laws require the individual checker to conserve its
allowance. They do not assert soundness of an arbitrary checker, interpret
failure as refutation, or identify checking work with execution cost.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BudgetedTraversal

universe u v

variable {Query : Type u} {Evidence : Query → Type v}

/-- Proof-relevant evidence at every occurrence of a finite query list. -/
inductive EvidenceList (Evidence : Query → Type v) : List Query → Type (max u v) where
  | nil : EvidenceList Evidence []
  | cons {query : Query} {queries : List Query} :
      Evidence query → EvidenceList Evidence queries → EvidenceList Evidence (query :: queries)

/-- A dependent consumer retrieves the receipt of an exact source occurrence,
not merely some receipt for an equal query. -/
def EvidenceList.get {queries : List Query} (evidence : EvidenceList Evidence queries) :
    (position : Fin queries.length) → Evidence queries[position] :=
  match evidence with
  | .nil => fun position => Fin.elim0 position
  | .cons head tail => Fin.cases head (fun position => tail.get position)

def EvidenceList.append {first second : List Query}
    (left : EvidenceList Evidence first) (right : EvidenceList Evidence second) :
    EvidenceList Evidence (first ++ second) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (tail.append right)

abbrev Checker (Query : Type u) (Evidence : Query → Type v) :=
  Nat → (query : Query) → Option (Evidence query × Nat)

/-- A successful subcheck's residual allowance is the next subcheck's input. -/
def traverseWithin (check : Checker Query Evidence) :
    Nat → (queries : List Query) → Option (EvidenceList Evidence queries × Nat)
  | fuel, [] => some (.nil, fuel)
  | fuel, query :: queries =>
      (check fuel query).bind fun head =>
        (traverseWithin check head.2 queries).map fun tail =>
          (.cons head.1 tail.1, tail.2)

/-- Concatenating inventories is exactly sequential composition, retaining
both inventories' occurrence-indexed evidence. -/
theorem traverseWithin_append (check : Checker Query Evidence)
    (fuel : Nat) (first second : List Query) :
    traverseWithin check fuel (first ++ second) =
      (traverseWithin check fuel first).bind fun left =>
        (traverseWithin check left.2 second).map fun right =>
          (left.1.append right.1, right.2) := by
  induction first generalizing fuel with
  | nil =>
      simp only [List.nil_append, traverseWithin, Option.bind_some, EvidenceList.append]
      cases traverseWithin check fuel second <;> rfl
  | cons query queries ih =>
      simp only [List.cons_append, traverseWithin]
      cases chosen : check fuel query with
      | none => rfl
      | some head =>
          simp only [Option.bind_some, ih]
          cases tail : traverseWithin check head.2 queries with
          | none => rfl
          | some left =>
              simp only [Option.bind_some, Option.map_some]
              cases traverseWithin check left.2 second <;> rfl

theorem traverseWithin_remaining_le (check : Checker Query Evidence)
    (conserves : ∀ fuel query evidence remaining,
      check fuel query = some (evidence, remaining) → remaining ≤ fuel)
    {fuel remaining : Nat} {queries : List Query}
    {evidence : EvidenceList Evidence queries}
    (completed : traverseWithin check fuel queries = some (evidence, remaining)) :
    remaining ≤ fuel := by
  induction queries generalizing fuel remaining with
  | nil =>
      have equal : fuel = remaining := by
        simpa [traverseWithin] using congrArg (fun x => x.map Prod.snd) completed
      omega
  | cons query queries ih =>
      simp only [traverseWithin] at completed
      obtain ⟨⟨head, afterHead⟩, chosen, rest⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨⟨tail, afterTail⟩, ran, equal⟩ := Option.map_eq_some_iff.mp rest
      have boundHead := conserves fuel query head afterHead chosen
      have boundTail := ih ran
      have sameRemaining := congrArg Prod.snd equal
      simp only at sameRemaining
      omega

/-- The work of two actual completed batches telescopes to their total work.
No independence or additivity assumption about machine costs is needed. -/
theorem completed_batches_spent_add (check : Checker Query Evidence)
    (conserves : ∀ fuel query evidence remaining,
      check fuel query = some (evidence, remaining) → remaining ≤ fuel)
    {fuel middle remaining : Nat} {first second : List Query}
    {left : EvidenceList Evidence first} {right : EvidenceList Evidence second}
    (leftRan : traverseWithin check fuel first = some (left, middle))
    (rightRan : traverseWithin check middle second = some (right, remaining)) :
    (fuel - middle) + (middle - remaining) = fuel - remaining ∧
      traverseWithin check fuel (first ++ second) =
        some (left.append right, remaining) := by
  have leftBound := traverseWithin_remaining_le check conserves leftRan
  have rightBound := traverseWithin_remaining_le check conserves rightRan
  constructor
  · omega
  · rw [traverseWithin_append, leftRan, Option.bind_some, rightRan, Option.map_some]

/-- When an individual checker retains a completed result under extra
allowance, the entire batch does too, with the same evidence at every index. -/
theorem traverseWithin_add (check : Checker Query Evidence)
    (stable : ∀ fuel query evidence remaining,
      check fuel query = some (evidence, remaining) → ∀ extra,
        check (fuel + extra) query = some (evidence, remaining + extra))
    {fuel remaining : Nat} {queries : List Query}
    {evidence : EvidenceList Evidence queries}
    (completed : traverseWithin check fuel queries = some (evidence, remaining))
    (extra : Nat) :
    traverseWithin check (fuel + extra) queries = some (evidence, remaining + extra) := by
  induction queries generalizing fuel remaining with
  | nil =>
      simpa [traverseWithin] using congrArg
        (fun x => x.map (fun pair => (pair.1, pair.2 + extra))) completed
  | cons query queries ih =>
      simp only [traverseWithin] at completed
      obtain ⟨⟨head, afterHead⟩, chosen, rest⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨⟨tail, afterTail⟩, ran, equal⟩ := Option.map_eq_some_iff.mp rest
      rw [traverseWithin, stable fuel query head afterHead chosen extra,
        Option.bind_some, ih ran, Option.map_some]
      exact congrArg some
        (congrArg (fun pair => (pair.1, pair.2 + extra)) equal)

/-- A finite batch eventually completes if each check eventually completes
and extra allowance retains established results. This does not assert that
arbitrary dependent conversion or proof search terminates. -/
theorem traverseWithin_eventually (check : Checker Query Evidence)
    (stable : ∀ fuel query evidence remaining,
      check fuel query = some (evidence, remaining) → ∀ extra,
        check (fuel + extra) query = some (evidence, remaining + extra))
    (terminates : ∀ query, ∃ fuel evidence remaining,
      check fuel query = some (evidence, remaining)) (queries : List Query) :
    ∃ fuel evidence remaining,
      traverseWithin check fuel queries = some (evidence, remaining) := by
  induction queries with
  | nil => exact ⟨0, .nil, 0, rfl⟩
  | cons query queries ih =>
      obtain ⟨headFuel, head, afterHead, headRan⟩ := terminates query
      obtain ⟨tailFuel, tail, afterTail, tailRan⟩ := ih
      have headExtended := stable headFuel query head afterHead headRan tailFuel
      have tailExtended := traverseWithin_add check stable tailRan afterHead
      rw [Nat.add_comm tailFuel afterHead] at tailExtended
      refine ⟨headFuel + tailFuel, .cons head tail, afterTail + afterHead, ?_⟩
      simp only [traverseWithin, headExtended, Option.bind_some,
        tailExtended, Option.map_some]

end Mettapedia.TypeTheory.BudgetedTraversal
