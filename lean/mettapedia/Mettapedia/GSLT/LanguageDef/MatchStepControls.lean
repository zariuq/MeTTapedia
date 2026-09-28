import Mettapedia.GSLT.LanguageDef.MatchStepMachine
import Mettapedia.GSLT.LanguageDef.HostCallControls

/-!
# Controls for match steps

Concrete runs of the machine with match steps (`matching`) and of the
output-first machine on the translated program (`withFacts`), over the
substitution store of `CompiledTwoSidedHeadProgram`, evaluated through
`substitutionStoreByFuel_eq` and checked by `decide`.  The constructors `p`,
`q`, `r` are unary, constants are strings, the query's slot is the query
variable `0`, and the fresh supply starts at `10`.  Answers are compared read
through their stores (`readAnswer`).

* Two facts, in order: over the space `(p a) (p b)`, `(match &self (p $x) (q $x))`
  delivers `(q a)` and then `(q b)` and has exhausted its frontier after 3 steps;
  the translated program delivers the same after 5 (`pq_runs`).  The prefix law
  against the output-at-return machine holds for this query (`pq_refines`).
* A caller-bound filter: with `$x` already bound to `b`, both machines deliver
  `(q b)` alone (`pqBound_runs`).
* Freshening is necessary: over the space `(p $y) (r $y)`, whose atoms use the
  same variable name, `(match &self (, (p a) (r b)) ok)`, lowered to nested
  match sites, delivers `ok`.  A candidate step that does not freshen
  (`unfreshened`: an atom's variables are the same store variables in every
  candidate) binds the shared variable to `a` at the first match and then finds
  `(r a)` where `(r b)` is asked for: it exhausts its frontier with no answer
  (`conj_runs`), so at no step count has it delivered the translated program's
  answers (`unfreshened_differs`).
* No candidates: `(= (f) (match &empty (p $x) (q $x)))` and `(= (f) Z)` over the
  empty space.  The match has no candidate, its alternative fails, and the second
  equation still delivers `Z`, in both machines (`empty_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchSteps.Controls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
  (substitutionStoreByFuel substitutionStoreByFuel_eq)
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Terms -/

/-- Unary constructors. -/
inductive Sym where
  | p
  | q
  | r
  deriving DecidableEq

/-- String constants, natural-number variables, unary `p`, `q`, `r`. -/
abbrev msig : LPSignature.{0, 0, 0, 0} where
  constants := String
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Sym
  functionArity _ := 1

instance : Inhabited (Term msig) := ⟨.const "Z"⟩

/-- Head patterns over `msig` as templates. -/
abbrev L : TemplateLanguage (Term msig) := headTemplates msig

/-- A constant, over any variables. -/
def sym {V : Type} (c : String) : Term { msig with vars := V } := .const c

/-- A unary constructor applied to a term, over any variables. -/
def app {V : Type} (f : Sym) (t : Term { msig with vars := V }) : Term { msig with vars := V } :=
  .app f fun _ => t

/-- What a term reads as, for comparing answers. -/
inductive Shape where
  | const (c : String)
  | unary (f : Sym) (c : String)
  | other
  deriving DecidableEq

def shape : Term msig → Shape
  | .const c => .const c
  | .app f ts =>
      match ts ⟨0, Nat.zero_lt_one⟩ with
      | .const c => .unary f c
      | _ => .other
  | .var _ => .other

/-- An answer read through its store. -/
def readAnswer (a : Unit × Answer (Term msig) (Subst msig × ℕ)) : Shape :=
  shape (a.2.2.1.applyTerm a.2.1)

/-! ## The store -/

/-- No primitives. -/
def noPrim : Empty → List (Term msig) → Subst msig × ℕ → Option (Term msig) := fun op => op.elim

/-- No tests. -/
def noTest : Empty → List (Term msig) → Subst msig × ℕ → Option Bool := fun op => op.elim

/-- The substitution store without primitives or tests. -/
abbrev store := substitutionStore (σ := msig) id noPrim noTest

/-- Its exact reading. -/
abbrev exact := substitutionExact (σ := msig) id noPrim noTest

/-- The store starts empty, with the fresh supply at `10`. -/
def start : Subst msig × ℕ := (Subst.id msig, 10)

theorem start_wellFormed : exact.WellFormed start := fun _ => rfl

/-- One space, listed once. -/
theorem once : ∀ s : Unit, [()].count s = 1 := fun s => by cases s; rfl

/-! ## Two facts, in order -/

/-- The space holding `(p a)` and then `(p b)`. -/
def pab : Unit → List (Atom L) := fun _ => [⟨0, app .p (sym "a")⟩, ⟨0, app .p (sym "b")⟩]

/-- `(match &self (p $x) (q $x))`, with `$x` the query's slot. -/
def pq : Code L (Empty ⊕ Unit) Empty 1 := matchSite L () (app .p (.var 0)) (.ret (app .q (.var 0)))

/-- The query's slot is the query variable `0`. -/
def xFrame : Fin 1 → Term msig := fun _ => .var 0

/-- **Both answers, in order.**  The match step delivers `(q a)` and then `(q b)`
and has exhausted its frontier after 3 steps; the translated program delivers
the same answers after 5, each fact returning into the continuation. -/
theorem pq_runs :
    (repeats (step (matching L store [] pab)) 3 (queryStateOut L pq xFrame start)).frontier = [] ∧
      (repeats (step (matching L store [] pab)) 3 (queryStateOut L pq xFrame start)).emitted.map
        readAnswer = [.unary .q "a", .unary .q "b"] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pab))) 5
        (queryStateOut L pq xFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pab))) 5
        (queryStateOut L pq xFrame start)).emitted.map readAnswer =
          [.unary .q "a", .unary .q "b"] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **The law, instantiated.**  The program has no tests or primitives, so after
any number of reference steps on the program with its facts, the machine with
match steps has delivered corresponding answers. -/
theorem pq_refines (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer exact)
      (repeats (step (compiled L store (withFacts L [] [()] pab))) n
        (queryState L pq xFrame start)).emitted
      (repeats (step (matching L store [] pab)) n' (queryStateOut L pq xFrame start)).emitted :=
  matching_refines L exact [()] pab once .nil
    (simulates_query exact (BindsAhead.refl pq) xFrame start start_wellFormed)
    (fun _ t _ => substitution_moded id noPrim noTest (fun op => op.elim) t) n

/-! ## A pattern bound by the caller -/

/-- `$x` bound to `b` before the same match site. -/
def pqBound : Code L (Empty ⊕ Unit) Empty 1 := .bind (.var 0) (sym "b") pq

/-- **The caller's binding filters the candidates.**  Only `(p b)` unifies with
`(p $x)` once `$x` is `b`: the match step delivers `(q b)` alone, as does the
translated program. -/
theorem pqBound_runs :
    (repeats (step (matching L store [] pab)) 2
        (queryStateOut L pqBound xFrame start)).frontier = [] ∧
      (repeats (step (matching L store [] pab)) 2
        (queryStateOut L pqBound xFrame start)).emitted.map readAnswer = [.unary .q "b"] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pab))) 3
        (queryStateOut L pqBound xFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pab))) 3
        (queryStateOut L pqBound xFrame start)).emitted.map readAnswer = [.unary .q "b"] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-! ## Freshening is necessary -/

/-- A candidate step that does not freshen: in every candidate, the atom's `i`-th
variable is the store variable `100 + i`, so atoms using the same variable name
alias. -/
def unfreshened (S : StoreAlgebra (Term msig) (Subst msig × ℕ) Empty) (A : Atom L)
    (p : Term msig) (σ : Subst msig × ℕ) : Option (Subst msig × ℕ) :=
  S.unify (L.inst A.2 fun i => .var (100 + i.val)) p σ

/-- The space holding `(p $y)` and then `(r $y)`: two atoms whose variables share
a name but not a meaning. -/
def pyry : Unit → List (Atom L) := fun _ => [⟨1, app .p (.var 0)⟩, ⟨1, app .r (.var 0)⟩]

/-- `(match &self (, (p a) (r b)) ok)`, lowered to nested match sites. -/
def conj : Code L (Empty ⊕ Unit) Empty 0 :=
  conjunctionSite L () (app .p (sym "a")) (app .r (sym "b")) (.ret (sym "ok"))

/-- The query has no slots. -/
def noFrame : Fin 0 → Term msig := fun i => i.elim0

/-- **With freshening, the conjunction holds.**  `(p a)` meets a fresh copy of
`(p $y)`, then `(r b)` meets another fresh copy of `(r $y)`: the match steps
deliver `ok` after 3 steps and the translated program after 5.  **Without**,
the first match binds the shared variable to `a`, the second finds `(r a)`
where it needs `(r b)`, and the run has exhausted its frontier after 2 steps
with no answer. -/
theorem conj_runs :
    (repeats (step (matching L store [] pyry)) 3 (queryStateOut L conj noFrame start)).frontier =
        [] ∧
      (repeats (step (matching L store [] pyry)) 3
        (queryStateOut L conj noFrame start)).emitted.map readAnswer = [.const "ok"] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pyry))) 5
        (queryStateOut L conj noFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L store (withFacts L [] [()] pyry))) 5
        (queryStateOut L conj noFrame start)).emitted.map readAnswer = [.const "ok"] ∧
      (∀ n < 2, (repeats (step (matchingBy L store (unfreshened store) [] pyry)) n
        (queryStateOut L conj noFrame start)).emitted = []) ∧
      (repeats (step (matchingBy L store (unfreshened store) [] pyry)) 2
        (queryStateOut L conj noFrame start)).frontier = [] ∧
      (repeats (step (matchingBy L store (unfreshened store) [] pyry)) 2
        (queryStateOut L conj noFrame start)).emitted = [] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **The step without freshening gives a different stream.**  At no step count
has it delivered the answers the translated program delivers. -/
theorem unfreshened_differs (n : ℕ) :
    (repeats (step (matchingBy L store (unfreshened store) [] pyry)) n
        (queryStateOut L conj noFrame start)).emitted ≠
      (repeats (step (outputFirst L store (withFacts L [] [()] pyry))) 5
        (queryStateOut L conj noFrame start)).emitted := by
  obtain ⟨-, -, -, delivered, early, done, silent⟩ := conj_runs
  have never : (repeats (step (matchingBy L store (unfreshened store) [] pyry)) n
      (queryStateOut L conj noFrame start)).emitted = [] := by
    by_cases below : n < 2
    · exact early n below
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
      rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add,
        HostCalls.Controls.repeats_exhausted _ _ done]
      exact silent
  rw [never]
  intro same
  rw [← same] at delivered
  simp at delivered

/-! ## No candidates -/

/-- The empty space. -/
def empty : Unit → List (Atom L) := fun _ => []

/-- `(= (f) (match &empty (p $x) (q $x)))` and `(= (f) Z)`. -/
def fProgram : EqProgram L (Unit ⊕ Unit) Empty :=
  [(.inl (), ⟨1, [], matchSite L () (app .p (.var 0)) (.ret (app .q (.var 0)))⟩),
   (.inl (), ⟨0, [], .ret (sym "Z")⟩)]

/-- The query `(f)`, reporting its answer in the query variable `0`. -/
def fQuery : Code L (Unit ⊕ Unit) Empty 1 := .letCall (.var 0) (.inl ()) [] (.ret (.var 0))

/-- **An exhausted match fails its alternative; the sibling answers.**  After 2
steps the first equation's match has found no candidate: its alternative is
gone, nothing is delivered, and the second equation's alternative remains.
After 4 steps `Z` is delivered and the frontier is exhausted, in both
machines. -/
theorem empty_runs :
    (repeats (step (matching L store fProgram empty)) 2
        (queryStateOut L fQuery xFrame start)).frontier.length = 1 ∧
      (repeats (step (matching L store fProgram empty)) 2
        (queryStateOut L fQuery xFrame start)).emitted = [] ∧
      (repeats (step (matching L store fProgram empty)) 4
        (queryStateOut L fQuery xFrame start)).frontier = [] ∧
      (repeats (step (matching L store fProgram empty)) 4
        (queryStateOut L fQuery xFrame start)).emitted.map readAnswer = [.const "Z"] ∧
      (repeats (step (outputFirst L store (withFacts L fProgram [()] empty))) 4
        (queryStateOut L fQuery xFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L store (withFacts L fProgram [()] empty))) 4
        (queryStateOut L fQuery xFrame start)).emitted.map readAnswer = [.const "Z"] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

end Mettapedia.GSLT.LanguageDef.MatchSteps.Controls

#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.pq_runs
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.pq_refines
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.pqBound_runs
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.conj_runs
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.unfreshened_differs
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.Controls.empty_runs
