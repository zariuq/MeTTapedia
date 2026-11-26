import Mathlib.Data.Multiset.Basic

/-! How much a completed occurrence observation determines. A timed trace
records the batch published at each tick, including silent ticks, so an
observer may also stop at any fuel limit. Only a completed search reports absence. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Contracts.OccurrenceObservers

inductive Demand where
  | timed | ordered | bag | count | first | presence | absence
  deriving DecidableEq, Repr

abbrev Trace (A : Type*) := List (List A)

def atFuel {A : Type*} (n : Nat) (x : Trace A) : List A := (x.take n).flatten

/-- Exactly what a timed observer sees: the completion time and every
prefix of answers. Equality only of final fuel and final answers is weaker. -/
theorem timed_iff_all_budgets {A : Type*} (x y : Trace A) :
    x = y ↔ x.length = y.length ∧ ∀ n, atFuel n x = atFuel n y := by
  constructor
  · rintro rfl; exact ⟨rfl, fun _ => rfl⟩
  · induction x generalizing y with
    | nil => rintro ⟨length, _⟩; simpa using length.symm
    | cons a xs ih =>
      rintro ⟨length, samples⟩
      cases y with
      | nil => simp at length
      | cons b ys =>
        have first : a = b := by simpa [atFuel] using samples 1
        subst b
        congr 1
        apply ih
        refine ⟨by simpa using length, fun n => ?_⟩
        simpa [atFuel] using samples (n+1)

def Result (A : Type) : Demand → Type
  | .timed => Trace A
  | .ordered => List A
  | .bag => Multiset A
  | .count => Nat
  | .first => Option A
  | .presence | .absence => Bool

instance {A : Type} [DecidableEq A] (d : Demand) : DecidableEq (Result A d) := by
  cases d <;> dsimp [Result] <;> infer_instance

def observe {A : Type} (d : Demand) (x : Trace A) : Result A d :=
  match d with
  | .timed => x
  | .ordered => x.flatten
  | .bag => (x.flatten : Multiset A)
  | .count => x.flatten.length
  | .first => x.flatten.head?
  | .presence => !x.flatten.isEmpty
  | .absence => x.flatten.isEmpty

/-- Information implication uniformly in the type of occurrences. -/
def Determines (a b : Demand) : Prop :=
  ∀ {T : Type} (x y : Trace T), observe a x = observe a y → observe b x = observe b y

def covers : Demand → Demand → Bool
  | .timed, _ => true
  | .ordered, .timed => false
  | .ordered, _ => true
  | .bag, .bag | .bag, .count | .count, .count | .first, .first => true
  | _, .presence | _, .absence => true
  | _, _ => false

private theorem fromOrdered {T : Type} (x y : Trace T) (same : x.flatten = y.flatten)
    (d : Demand) (h : d ≠ .timed) : observe d x = observe d y := by
  cases d <;> simp_all [observe] <;> rfl

private theorem nonempty_count {T : Type} (x y : List T) (h : x.length = y.length) :
    x.isEmpty = y.isEmpty := by cases x <;> cases y <;> simp_all

private theorem nonempty_first {T : Type} (x y : List T) (h : x.head? = y.head?) :
    x.isEmpty = y.isEmpty := by cases x <;> cases y <;> simp_all

private theorem sound {a b : Demand} (yes : covers a b = true) : Determines a b := by
  intro T x y h
  cases a with
  | timed => exact congrArg (observe b) h
  | ordered => exact fromOrdered x y h b (by rintro rfl; cases yes)
  | bag =>
    have size : x.flatten.length = y.flatten.length := congrArg Multiset.card h
    have empty := nonempty_count _ _ size
    cases b <;> first | exact h | exact size | exact empty | exact congrArg Bool.not empty | cases yes
  | count =>
    have empty := nonempty_count _ _ h
    cases b <;> first | exact h | exact empty | exact congrArg Bool.not empty | cases yes
  | first =>
    have empty := nonempty_first _ _ h
    cases b <;> first | exact h | exact empty | exact congrArg Bool.not empty | cases yes
  | presence =>
    have empty : x.flatten.isEmpty = y.flatten.isEmpty := by simpa [observe] using congrArg Bool.not h
    cases b <;> first | exact h | exact empty | cases yes
  | absence =>
    cases b <;> first | exact h | exact congrArg Bool.not h | cases yes

private abbrev Pair := Trace Bool × Trace Bool
private def differentFuel : Pair := ([], [[]])
private def swapped : Pair := ([[false, true]], [[true, false]])
private def replaced : Pair := ([[false]], [[true]])
private def repeated : Pair := ([[false]], [[false, false]])

theorem same_total_different_prefix :
    let x : Trace Bool := [[true], []]
    let y : Trace Bool := [[], [true]]
    x.length = y.length ∧ observe .ordered x = observe .ordered y ∧
      atFuel 1 x ≠ atFuel 1 y := by decide

private theorem refutes {a b : Demand} (p : Pair)
    (same : observe a p.1 = observe a p.2) (diff : observe b p.1 ≠ observe b p.2) :
    ¬ Determines a b := fun det => diff (det p.1 p.2 same)

/-- Complete classification, not just the arrows of a proposed hierarchy.
Four two-trace controls separate all the false implications. -/
theorem determines_iff (a b : Demand) : Determines a b ↔ covers a b = true := by
  refine ⟨fun h => ?_, sound⟩
  cases a <;> cases b <;> first
    | rfl
    | exact (refutes differentFuel (by decide) (by decide) h).elim
    | exact (refutes swapped (by decide) (by decide) h).elim
    | exact (refutes replaced (by decide) (by decide) h).elim
    | exact (refutes repeated (by decide) (by decide) h).elim

end Mettapedia.GSLT.Contracts.OccurrenceObservers
