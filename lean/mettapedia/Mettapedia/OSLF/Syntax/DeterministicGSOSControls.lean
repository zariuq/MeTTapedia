import Mettapedia.OSLF.Syntax.DeterministicGSOSCounterexample
import Mettapedia.OSLF.Syntax.DeterministicGSOSOperational

/-!
# Deterministic rule controls

Priority composition keeps the unfired argument and the exact derivative
of the argument that fires. Independent controls separate a natural law
from state-equality tests, one-step rules from lookahead, and authored
occurrence histories from their deterministic target readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.Controls

open CategoryTheory Mettapedia.TypeTheory

inductive Operator where
  | stopped
  | prefix (label : Nat)
  | priority
  deriving DecidableEq

abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator
  Position := fun operator => match operator with
    | .stopped => Empty
    | .prefix _ => Unit
    | .priority => Fin 2
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

abbrev actions : signature.Srt → Type := fun _ => Nat
abbrev naturals : signature.Families := fun _ _ => Nat
abbrev booleans : signature.Families := fun _ _ => Bool
abbrev units : signature.Families := fun _ _ => Unit

abbrev left : Fin 2 := 0
abbrev right : Fin 2 := 1

noncomputable def pure {X : signature.Families} (value : X PUnit.unit ()) :
    signature.Term X () := IndexedPolynomial.Free.pure signature.polynomial value

noncomputable def priority {X : signature.Families}
    (first second : signature.Term X ()) : signature.Term X () :=
  IndexedPolynomial.Free.node signature.polynomial .priority
    (fun position => if position = left then first else second)

theorem rename_priority {X Y : signature.Families} (mapping : X ⟶ Y)
    (first second : signature.Term X ()) :
    signature.rename mapping (priority first second) =
      priority (signature.rename mapping first) (signature.rename mapping second) := by
  classical
  change IndexedPolynomial.Free.map signature.polynomial _ PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial Operator.priority _) = _
  rw [IndexedPolynomial.Free.map_node]
  apply congrArg (IndexedPolynomial.Free.node signature.polynomial Operator.priority)
  funext position
  by_cases same : position = left <;> simp [same]

/-- The left action has priority; every conclusion retains the other argument. -/
noncomputable def rules : GuardedSchemas actions := by
  classical
  exact fun _ operator guard action => match operator with
    | .stopped => none
    | .prefix label => if action = label then some (pure (.original ())) else none
    | .priority =>
        if enabled : guard ⟨left, action⟩ = true then
          some (priority (pure (.derivative ⟨left, action⟩ enabled)) (pure (.original right)))
        else if enabled : guard ⟨right, action⟩ = true then
          some (priority (pure (.original left)) (pure (.derivative ⟨right, action⟩ enabled)))
        else none

noncomputable def law : Law signature actions := toLaw actions rules

/-- Both independent inputs offer action seven, with distinct complete derivatives. -/
def offered : BehaviourArguments signature actions naturals (sort := ()) .priority :=
  fun position => if position = left then (10, fun action => if action = 7 then some 11 else none)
    else (20, fun action => if action = 7 then some 21 else none)

/-- The full priority conclusion retains the unfired original argument. -/
theorem left_priority_readout :
    law.app naturals PUnit.unit () ⟨Operator.priority, offered⟩ 7 =
      some (priority (pure 11) (pure 20)) := by
  have enabled : inputGuard actions offered ⟨left, 7⟩ = true := by decide
  change instantiate actions rules Operator.priority offered 7 = _
  simp only [instantiate, instantiateAt, rules, enabled, dif_pos, Option.map_some]
  rw [rename_priority]
  rfl

def rightOnly : BehaviourArguments signature actions naturals (sort := ()) .priority :=
  fun position => if position = left then (10, fun _ => none)
    else (20, fun action => if action = 7 then some 21 else none)

theorem right_fallback_readout :
    law.app naturals PUnit.unit () ⟨Operator.priority, rightOnly⟩ 7 =
      some (priority (pure 10) (pure 21)) := by
  have disabled : ¬ inputGuard actions rightOnly ⟨left, 7⟩ = true := by decide
  have enabled : inputGuard actions rightOnly ⟨right, 7⟩ = true := by decide
  change instantiate actions rules Operator.priority rightOnly 7 = _
  simp [instantiate, instantiateAt, rules, disabled, enabled]
  rw [rename_priority]
  rfl

/-- A genuinely noninjective variable map identifies all natural-number inputs. -/
def collapse : naturals ⟶ units := fun _ _ => ↾(fun _ => ())

theorem collapse_is_noninjective : ¬ Function.Injective (collapse PUnit.unit ()) := by
  intro injective
  have impossible : (0 : Nat) = 1 := injective rfl
  exact Nat.zero_ne_one impossible

/-- Real variable collisions preserve the independently checked whole conclusion. -/
theorem collision_readout :
    law.app units PUnit.unit ()
        ⟨Operator.priority, mapArguments actions collapse offered⟩ 7 =
      (some (priority (pure 11) (pure 20))).map (signature.rename collapse) := by
  have natural := congrArg (fun map => map PUnit.unit () ⟨Operator.priority, offered⟩ 7)
    (law.naturality collapse)
  change law.app units PUnit.unit ()
      ⟨Operator.priority, mapArguments actions collapse offered⟩ 7 =
    (law.app naturals PUnit.unit () ⟨Operator.priority, offered⟩ 7).map
      (signature.rename collapse) at natural
  exact natural.trans (congrArg (Option.map (signature.rename collapse)) left_priority_readout)

/-- A proposed equality test can distinguish source identities, unlike a natural law. -/
noncomputable def equalityProbe {X : signature.Families} [DecidableEq (X PUnit.unit ())]
    (arguments : BehaviourArguments signature actions X (sort := ()) .priority) : Bool :=
  decide ((arguments left).1 = (arguments right).1)

def unequal : BehaviourArguments signature actions booleans (sort := ()) .priority :=
  fun position => (position = left, fun _ => none)

def collapseBool : booleans ⟶ units := fun _ _ => ↾(fun _ => ())

/-- Source-equality inspection fails naturality under an actual variable collision. -/
theorem equality_test_not_natural :
    equalityProbe unequal ≠ equalityProbe (mapArguments actions collapseBool unequal) := by
  decide

/-- Two variable coalgebras agree at zero but differ at its immediate successor. -/
def firstSteps : VariableCoalgebra actions naturals :=
  fun _ _ => ↾(fun state action => if state = 0 ∧ action = 7 then some 1 else none)

def secondSteps : VariableCoalgebra actions naturals :=
  fun _ _ => ↾(fun state action =>
    if state = 0 ∧ action = 7 then some 1
    else if state = 1 ∧ action = 8 then some 2 else none)

theorem same_immediate_input : firstSteps PUnit.unit () 0 = secondSteps PUnit.unit () 0 := by
  funext action
  simp [firstSteps, secondSteps]
  rfl

theorem different_successor_input :
    firstSteps PUnit.unit () 1 8 ≠ secondSteps PUnit.unit () 1 8 := by
  decide

/-- A one-step law cannot tell apart these identical supplied immediate inputs. -/
theorem no_immediate_lookahead (candidate : Law signature actions) :
    candidate.app naturals PUnit.unit ()
        ⟨Operator.prefix 7, fun _ => (0, firstSteps PUnit.unit () 0)⟩ =
      candidate.app naturals PUnit.unit ()
        ⟨Operator.prefix 7, fun _ => (0, secondSteps PUnit.unit () 0)⟩ := by
  rw [same_immediate_input]

/-- Authored occurrence positions are retained independently of target readout. -/
structure Occurrence where
  position : Fin 2
  target : signature.Term naturals ()

noncomputable def firstOccurrence : Occurrence := ⟨0, priority (pure 11) (pure 20)⟩
noncomputable def secondOccurrence : Occurrence := ⟨1, priority (pure 11) (pure 20)⟩

theorem occurrence_histories_differ : firstOccurrence ≠ secondOccurrence := by
  intro same
  have positions := congrArg Occurrence.position same
  exact Fin.zero_ne_one positions

theorem occurrence_readouts_agree : firstOccurrence.target = secondOccurrence.target := rfl

/-- Add a second available label while retaining the exact same selected edge. -/
def extraSourceSteps : VariableCoalgebra actions naturals :=
  fun _ _ => ↾(fun state action =>
    if state = 0 ∧ action = 7 then some 1
    else if state = 0 ∧ action = 8 then some 2 else none)

theorem selected_edges_agree :
    firstSteps PUnit.unit () 0 7 = some 1 ∧
      extraSourceSteps PUnit.unit () 0 7 = some 1 := by decide

/-- A natural negative-premise rule fires exactly when label eight is absent. -/
noncomputable def absenceRules : GuardedSchemas actions := by
  classical
  exact fun _ operator guard action => match operator with
    | .stopped => none
    | .priority => none
    | .prefix _ =>
        if action = 0 ∧ guard ⟨(), 8⟩ = false then some (pure (.original ())) else none

noncomputable def absenceLaw : Law signature actions := toLaw actions absenceRules

theorem absent_other_action_returns :
    absenceLaw.app naturals PUnit.unit ()
      ⟨Operator.prefix 7, fun _ => (0, firstSteps PUnit.unit () 0)⟩ 0 = some (pure 0) := by
  have absent : inputGuard actions (sort := ()) (operator := Operator.prefix 7)
      (fun _ => (0, firstSteps PUnit.unit () 0)) ⟨(), 8⟩ = false := by decide
  change instantiate actions absenceRules (X := naturals) (sort := ()) (Operator.prefix 7)
    (fun _ => (0, firstSteps PUnit.unit () 0)) 0 = some (pure 0)
  simp [instantiate, instantiateAt, absenceRules, absent]
  rfl

theorem present_other_action_blocks :
    absenceLaw.app naturals PUnit.unit ()
      ⟨Operator.prefix 7, fun _ => (0, extraSourceSteps PUnit.unit () 0)⟩ 0 = none := by
  have present : inputGuard actions (sort := ()) (operator := Operator.prefix 7)
      (fun _ => (0, extraSourceSteps PUnit.unit () 0)) ⟨(), 8⟩ = true := by decide
  change instantiate actions absenceRules (X := naturals) (sort := ()) (Operator.prefix 7)
    (fun _ => (0, extraSourceSteps PUnit.unit () 0)) 0 = none
  simp [instantiate, instantiateAt, absenceRules, present]

/-- A selected edge with identical source, label and target cannot recover negative premises. -/
theorem selected_edge_information_insufficient :
    ¬ ∃ decode : Nat × Nat × Nat → Option (signature.Term naturals ()),
      decode (0, 7, 1) = absenceLaw.app naturals PUnit.unit ()
        ⟨Operator.prefix 7, fun _ => (0, firstSteps PUnit.unit () 0)⟩ 0 ∧
      decode (0, 7, 1) = absenceLaw.app naturals PUnit.unit ()
        ⟨Operator.prefix 7, fun _ => (0, extraSourceSteps PUnit.unit () 0)⟩ 0 := by
  rintro ⟨decode, first, second⟩
  rw [absent_other_action_returns] at first
  rw [present_other_action_blocks] at second
  have impossible := first.symm.trans second
  cases impossible

def noSteps : VariableCoalgebra actions naturals := fun _ _ => ↾(fun _ _ => none)

noncomputable def prefixed (label : Nat) (child : signature.Term naturals ()) :
    signature.Term naturals () :=
  IndexedPolynomial.Free.node signature.polynomial (.prefix label) (fun _ => child)

/-- The real operational constructor rule returns the actual supplied continuation. -/
theorem operational_prefix_readout :
    Operational.coalgebra law noSteps PUnit.unit () (prefixed 7 (pure 10)) 7 = some (pure 10) := by
  change (Operational.evaluate law noSteps PUnit.unit () (prefixed 7 (pure 10))).2 7 = _
  simp [Operational.evaluate, prefixed, IndexedPolynomial.Free.fold_node,
    IndexedPolynomial.Free.fold_pure, Operational.algebra, Operational.leaf,
    law, toLaw, instantiate, instantiateAt, rules, noSteps,
    pure, Signature.rename, assignmentAt, IndexedPolynomial.Free.map_pure]
  rfl

/-- The actual monad bind replaces this continuation by the supplied typed term. -/
theorem operational_bind_readout :
    Operational.coalgebra law noSteps PUnit.unit ()
      (IndexedPolynomial.Free.bind signature.polynomial
        (fun _ _ value => pure (value + 1)) PUnit.unit () (prefixed 7 (pure 10))) 7 =
      some (pure 11) := by
  have respects : ∀ base sort value,
      Operational.coalgebra law noSteps base sort (pure (value + 1)) =
        fun action => (noSteps base sort value action).map (fun value => pure (value + 1)) := by
    intro base sort value
    cases base
    cases sort
    funext action
    rfl
  have substitution := congrFun (Operational.coalgebra_bind law noSteps noSteps
    (fun _ _ value => pure (value + 1)) respects PUnit.unit () (prefixed 7 (pure 10))) 7
  rw [operational_prefix_readout] at substitution
  exact substitution

/-- Substitution compatibility requires the actual coalgebra premise. -/
theorem arbitrary_bind_is_not_coalgebra_preserving :
    Operational.coalgebra law noSteps PUnit.unit () (prefixed 7 (pure 10)) 7 ≠
      (noSteps PUnit.unit () 10 7).map (fun value => prefixed 7 (pure value)) := by
  rw [operational_prefix_readout]
  intro same
  cases same

end Mettapedia.OSLF.DeterministicGSOS.Controls
