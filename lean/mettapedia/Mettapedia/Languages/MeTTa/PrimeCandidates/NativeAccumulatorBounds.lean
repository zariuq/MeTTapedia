import Mettapedia.GSLT.Core.BoundedPublication
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-!
# Source-associated bounds for a unary accumulator fragment

The admitted source equations have a variable argument. A recursive body adds
a literal natural cost; a terminal body places that argument in a declared
constructor field. Activations retain the physical equation position and the
accumulator independently of the scheduler's heuristic key.

The authored equations are ordinary parsed Atom commands. Their matching law
uses the independently defined first-order matcher relation. The local lower
bound follows from nonnegative arithmetic and the terminal projection, rather
than from a priority supplied by the program. Constructor names must be inert
in the surrounding profile; this module does not admit arbitrary foreign
calls or prove a C-runtime refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeAccumulatorBounds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.BoundedPublication

inductive Literal where
  | symbol (name : String)
  | number (value : Int)
  | text (value : String)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

def Literal.atom : Literal → Atom
  | .symbol name => .symbol name
  | .number value => .grounded (.int value)
  | .text value => .grounded (.string value)
  | .boolean value => .grounded (.bool value)

inductive Body where
  | recurse (increment : Nat)
  | terminal (constructor : String) (before after : List Literal)
  deriving Repr, DecidableEq

structure Source where
  head : String
  argument : String
  equations : List Body
  deriving Repr, DecidableEq

def numeral (value : Nat) : Atom := .grounded (.int value)
def call (head : String) (value : Nat) : Atom := .expression [.symbol head, numeral value]
def lhs (source : Source) : Atom := .expression [.symbol source.head, .var source.argument]

def rhs (source : Source) : Body → Atom
  | .recurse increment =>
      .expression [.symbol source.head,
        .expression [.symbol "+", .var source.argument, numeral increment]]
  | .terminal constructor before after =>
      .expression (.symbol constructor ::
        before.map Literal.atom ++ [.var source.argument] ++ after.map Literal.atom)

def authored (source : Source) : Program Atom :=
  source.equations.mapIdx fun index body =>
    (index + 1, ProgramCommand.defineEq (lhs source) (rhs source body))

/-- Every source call really matches the authored variable pattern. Matching
does not force its body or confuse heuristic grades with substitution. -/
theorem lhs_matches (source : Source) (value : Nat) :
    MatchAtomRel [] (lhs source) (call source.head value)
      [(source.argument, numeral value)] := by
  apply MatchAtomRel.expr_cons MatchAtomRel.symbol
  apply MatchAtomRel.expr_cons
  · exact MatchAtomRel.var_fresh rfl
  · exact MatchAtomRel.expr_nil

theorem executable_lhs_matches (source : Source) (value : Nat) :
    matchAtom [] (lhs source) (call source.head value) =
      some [(source.argument, numeral value)] :=
  matchAtom_complete (lhs_matches source value)

def terminalValue (constructor : String) (before after : List Literal) (value : Nat) : Atom :=
  .expression (.symbol constructor ::
    before.map Literal.atom ++ [numeral value] ++ after.map Literal.atom)

/-- Independently stated evaluation of the admitted RHS primitives. -/
inductive RhsEvaluation (head argument : String) (value : Nat) : Atom → Atom → Prop where
  | arithmetic (increment : Nat) :
      RhsEvaluation head argument value
        (.expression [.symbol head,
          .expression [.symbol "+", .var argument, numeral increment]])
        (call head (value + increment))
  | constructor (name : String) (before after : List Literal) :
      RhsEvaluation head argument value
        (.expression (.symbol name ::
          before.map Literal.atom ++ [.var argument] ++ after.map Literal.atom))
        (terminalValue name before after value)

def bodyValue (source : Source) (value : Nat) : Body → Atom
  | .recurse increment => call source.head (value + increment)
  | .terminal constructor before after => terminalValue constructor before after value

theorem body_evaluates (source : Source) (value : Nat) (body : Body) :
    RhsEvaluation source.head source.argument value (rhs source body)
      (bodyValue source value body) := by
  cases body with
  | recurse increment => exact .arithmetic increment
  | terminal constructor before after => exact .constructor constructor before after

def SourceStep (source : Source) (start finish : Atom) : Prop :=
  ∃ value body, body ∈ source.equations ∧ start = call source.head value ∧
    MatchAtomRel [] (lhs source) start [(source.argument, numeral value)] ∧
    RhsEvaluation source.head source.argument value (rhs source body) finish

theorem source_step (source : Source) (value : Nat) (body : Body)
    (listed : body ∈ source.equations) :
    SourceStep source (call source.head value) (bodyValue source value body) :=
  ⟨value, body, listed, rfl, lhs_matches source value, body_evaluates source value body⟩

inductive Work (source : Source) where
  | call (value : Nat)
  | activate (equation : Fin source.equations.length) (value : Nat)
  | returned (equation : Fin source.equations.length) (value : Nat)
  deriving DecidableEq, Repr

structure Result where
  declaration : Nat
  value : Atom
  cost : Nat
  deriving DecidableEq, Repr

def system (source : Source) : BranchingSystem (Work source) Result where
  emit
    | .returned equation value =>
        some ⟨equation.val, bodyValue source value source.equations[equation], value⟩
    | _ => none
  successors
    | .call value => (List.finRange source.equations.length).map (.activate · value)
    | .activate equation value => match source.equations[equation] with
      | .recurse increment => [.call (value + increment)]
      | .terminal _ _ _ => [.returned equation value]
    | .returned _ _ => []

def lower (source : Source) : Work source → Nat
  | .call value | .activate _ value | .returned _ value => value

/-- The local certificate is proved from the authored arithmetic and terminal
field contract. A heuristic reordering is irrelevant to the proof. -/
theorem local_bounds (source : Source) :
    LocalBounds (system source) Result.cost (lower source) := by
  constructor
  · intro node answer emitted
    cases node with
    | call value => simp [system] at emitted
    | activate equation value => simp [system] at emitted
    | returned equation value =>
        have same : answer = ⟨equation.val,
            bodyValue source value source.equations[equation], value⟩ :=
          (Option.some.inj emitted).symm
        subst answer
        exact le_rfl
  · intro node child member
    cases node with
    | call value =>
        obtain ⟨equation, _, same⟩ := List.mem_map.mp member
        subst child
        exact le_rfl
    | activate equation value =>
        change child ∈ (match source.equations[equation] with
          | .recurse increment => [Work.call (value + increment)]
          | .terminal _ _ _ => [Work.returned equation value]) at member
        cases body : source.equations[equation] with
        | recurse increment =>
            have same : child = .call (value + increment) := by
              simpa only [body, List.mem_singleton] using member
            subst child
            exact Nat.le_add_right _ _
        | terminal constructor before after =>
            have same : child = .returned equation value := by
              simpa only [body, List.mem_singleton] using member
            subst child
            exact le_rfl
    | returned equation value => simp [system] at member

/-- A reached activation names an actual authored equation occurrence and
its computed body is an independently permitted source reduction. -/
theorem activation_source_step (source : Source) (equation : Fin source.equations.length)
    (value : Nat) :
    SourceStep source (call source.head value)
      (bodyValue source value source.equations[equation]) :=
  source_step source value source.equations[equation] (List.getElem_mem _)

namespace Controls

def routes : Source :=
  ⟨"walk", "cost", [.recurse 2, .terminal "Route" [] [.symbol "left"],
    .terminal "Route" [] [.symbol "right"]]⟩

example : ((system routes).successors (.call 0)).length = 3 := by decide
example : lower routes (.activate ⟨0, by decide⟩ 7) = 7 := rfl
example : (system routes).successors (.activate ⟨0, by decide⟩ 7) = [.call 9] := rfl
example : (system routes).emit (.returned ⟨1, by decide⟩ 7) ≠
    (system routes).emit (.returned ⟨2, by decide⟩ 7) := by decide

/-- A negative update would invalidate the local lower-bound condition. -/
example : ¬ (7 : Int) ≤ 7 + (-2) := by decide

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeAccumulatorBounds
