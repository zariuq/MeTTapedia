import Mathlib.Data.List.Monad

/-!
# Relational zero, demand, and definitional replacement

This module isolates the algebra needed to distinguish a computation with no
outcomes from a computation returning an atom whose spelling is `Empty`.
The concrete carrier is an ordered occurrence sequence, so source order and
multiplicity remain available.  Computational zero is the empty sequence;
ordinary data is introduced as a singleton sequence.

Sequencing is list bind.  Consequently zero is a left annihilator for a
demanded continuation, while a discarded computation is not forced.  An
explicit zero observer handles the empty sequence at one declared boundary.

The final section models the positional rule that caused the motivating
counterexample: a distinguished atom is retained when written literally but
filtered when it crosses an equation-result boundary.  The rule cannot factor
through the atom's denotation and therefore violates definitional replacement.
-/

namespace Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence

universe u

/-- Concrete nondeterministic results, retaining order and multiplicity. -/
abbrev Occurrences (Atom : Type u) := List Atom

/-- No computational outcomes. -/
def zero {Atom : Type u} : Occurrences Atom := []

/-- One ordinary data outcome. -/
def pure {Atom : Type u} (atom : Atom) : Occurrences Atom := [atom]

/-- Demand every occurrence and concatenate each continuation result. -/
def bind {Atom Result : Type u} (source : Occurrences Atom)
    (continuation : Atom → Occurrences Result) : Occurrences Result :=
  source.flatMap continuation

@[simp] theorem bind_zero {Atom Result : Type u}
    (continuation : Atom → Occurrences Result) :
    bind zero continuation = zero :=
  rfl

@[simp] theorem bind_pure {Atom Result : Type u} (atom : Atom)
    (continuation : Atom → Occurrences Result) :
    bind (pure atom) continuation = continuation atom := by
  simp [bind, pure]

@[simp] theorem bind_to_pure {Atom : Type u}
    (source : Occurrences Atom) :
    bind source pure = source := by
  change source.flatMap (fun atom => [atom]) = source
  induction source with
  | nil => rfl
  | cons head tail induction => simp [induction]

theorem bind_append {Atom Result : Type u}
    (left right : Occurrences Atom)
    (continuation : Atom → Occurrences Result) :
    bind (left ++ right) continuation =
      bind left continuation ++ bind right continuation := by
  simp [bind, List.flatMap_append]

theorem bind_assoc {Atom Middle Result : Type u}
    (source : Occurrences Atom)
    (first : Atom → Occurrences Middle)
    (second : Middle → Occurrences Result) :
    bind (bind source first) second =
      bind source (fun atom => bind (first atom) second) := by
  simpa [bind] using (List.flatMap_assoc :
    (source.flatMap first).flatMap second =
      source.flatMap (fun atom => (first atom).flatMap second))

/-- Observe zero at an explicit boundary.  Nonempty occurrences retain their
order and multiplicity through the value continuation. -/
def observeZero {Atom Result : Type u} (source : Occurrences Atom)
    (onZero : Occurrences Result)
    (onValue : Atom → Occurrences Result) : Occurrences Result :=
  match source with
  | [] => onZero
  | _ :: _ => bind source onValue

@[simp] theorem observeZero_zero {Atom Result : Type u}
    (onZero : Occurrences Result)
    (onValue : Atom → Occurrences Result) :
    observeZero zero onZero onValue = onZero :=
  rfl

@[simp] theorem observeZero_pure {Atom Result : Type u} (atom : Atom)
    (onZero : Occurrences Result)
    (onValue : Atom → Occurrences Result) :
    observeZero (pure atom) onZero onValue = onValue atom := by
  simp [observeZero, pure, bind]

/-- A data atom, including one conventionally printed as `Empty`, is not
computational zero. -/
theorem pure_ne_zero {Atom : Type u} (atom : Atom) :
    pure atom ≠ (zero : Occurrences Atom) := by
  simp [pure, zero]

/-! ## Pure demand -/

/-- A small sequencing language.  `discardThen` represents an unused lazy
binding; `demandThen` represents a binding whose value is demanded before the
body can run. -/
inductive Expr (Atom : Type u) where
  | data (atom : Atom)
  | zero
  | call (body : Expr Atom)
  | choose (left right : Expr Atom)
  | discardThen (source body : Expr Atom)
  | demandThen (source body : Expr Atom)

/-- Demand semantics for the small language. -/
def eval {Atom : Type u} : Expr Atom → Occurrences Atom
  | .data atom => pure atom
  | .zero => zero
  | .call body => eval body
  | .choose left right => eval left ++ eval right
  | .discardThen _ body => eval body
  | .demandThen source body => bind (eval source) (fun _ => eval body)

@[simp] theorem eval_call {Atom : Type u} (body : Expr Atom) :
    eval (.call body) = eval body :=
  rfl

@[simp] theorem eval_discardThen {Atom : Type u}
    (source body : Expr Atom) :
    eval (.discardThen source body) = eval body :=
  rfl

@[simp] theorem eval_demandThen_zero {Atom : Type u}
    (body : Expr Atom) :
    eval (.demandThen .zero body) = zero :=
  rfl

/-- Contexts built from calls, pure-demand sequencing, and explicit zero
observation.  The hole always denotes an occurrence sequence. -/
inductive DemandContext (Atom : Type u) where
  | hole
  | call (context : DemandContext Atom)
  | discardedSource (context : DemandContext Atom)
      (body : Occurrences Atom)
  | demandedSource (context : DemandContext Atom)
      (continuation : Atom → Occurrences Atom)
  | observedSource (context : DemandContext Atom)
      (onZero : Occurrences Atom)
      (onValue : Atom → Occurrences Atom)

/-- Interpret a demand context extensionally over occurrence sequences. -/
def DemandContext.run {Atom : Type u} :
    DemandContext Atom → Occurrences Atom → Occurrences Atom
  | .hole, source => source
  | .call context, source => context.run source
  | .discardedSource _ body, _ => body
  | .demandedSource context continuation, source =>
      bind (context.run source) continuation
  | .observedSource context onZero onValue, source =>
      observeZero (context.run source) onZero onValue

/-- Every context in the demand fragment respects denotational equality. -/
theorem DemandContext.run_congr {Atom : Type u}
    (context : DemandContext Atom) {left right : Occurrences Atom}
    (equivalent : left = right) :
    context.run left = context.run right := by
  subst right
  rfl

/-- Replacing a call by its definition preserves every context in the demand
fragment. -/
theorem replace_call_by_definition {Atom : Type u}
    (context : DemandContext Atom) (body : Expr Atom) :
    context.run (eval (.call body)) = context.run (eval body) := by
  exact context.run_congr (eval_call body)

/-! ## Positional filtering is not denotational -/

/-- The two syntactic positions involved in the counterexample. -/
inductive Boundary where
  | literal
  | equationResult
  deriving DecidableEq

/-- A positional rule that treats one distinguished atom as data when literal
but removes it when it arrives as an equation result. -/
def positional {Atom : Type u} [DecidableEq Atom] (emptyAtom : Atom) :
    Boundary → Atom → Occurrences Atom
  | .literal, atom => pure atom
  | .equationResult, atom => if atom = emptyAtom then zero else pure atom

@[simp] theorem positional_literal {Atom : Type u} [DecidableEq Atom]
    (emptyAtom atom : Atom) :
    positional emptyAtom .literal atom = pure atom :=
  rfl

@[simp] theorem positional_equationResult_empty
    {Atom : Type u} [DecidableEq Atom] (emptyAtom : Atom) :
    positional emptyAtom .equationResult emptyAtom = zero := by
  simp [positional]

/-- The literal and call-result forms of the same atom receive different
denotations under positional filtering. -/
theorem positional_breaks_definitional_replacement
    {Atom : Type u} [DecidableEq Atom] (emptyAtom : Atom) :
    positional emptyAtom .literal emptyAtom ≠
      positional emptyAtom .equationResult emptyAtom := by
  simp [positional, pure, zero]

/-- Positional filtering cannot be implemented by any interpretation that
depends only on the atom being interpreted. -/
theorem positional_cannot_factor_through_atom
    {Atom : Type u} [DecidableEq Atom] (emptyAtom : Atom) :
    ¬ ∃ meaning : Atom → Occurrences Atom,
      positional emptyAtom .literal emptyAtom = meaning emptyAtom ∧
      positional emptyAtom .equationResult emptyAtom = meaning emptyAtom := by
  rintro ⟨meaning, literalMeaning, resultMeaning⟩
  apply positional_breaks_definitional_replacement emptyAtom
  exact literalMeaning.trans resultMeaning.symm

/-! ## Executable positive and negative canaries -/

private inductive DemoAtom where
  | emptySymbol
  | token
  | zeroObserved
  | valueObserved
  deriving DecidableEq

/-- Positive: a genuine zero selects the explicit zero observer. -/
example :
    observeZero (zero : Occurrences DemoAtom) [DemoAtom.zeroObserved]
      (fun _ => [DemoAtom.valueObserved]) = [DemoAtom.zeroObserved] :=
  rfl

/-- Negative control: an ordinary atom named as the empty symbol is a value,
not a zero-result computation. -/
example :
    observeZero (pure DemoAtom.emptySymbol) [DemoAtom.zeroObserved]
      (fun _ => [DemoAtom.valueObserved]) = [DemoAtom.valueObserved] := by
  simp

/-- Pure demand: an unused zero computation does not erase the body. -/
example :
    eval (.discardThen .zero (.data DemoAtom.token)) =
      [DemoAtom.token] :=
  rfl

/-- A demanded zero computation prevents the continuation from running. -/
example :
    eval (.demandThen .zero (.data DemoAtom.token)) =
      (zero : Occurrences DemoAtom) :=
  rfl

end Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence
