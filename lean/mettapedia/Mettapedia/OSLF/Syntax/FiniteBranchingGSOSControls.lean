import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSOperational
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual stopped and binary-choice GSOS lifting

The natural law is independently specified on complete argument behaviors.
Choice takes successors from either child, including shared successors.
Naturality is proved for every family map, so variable identifications are
admitted. The actual lifted unit, map and multiplication retain complete
free terms. A many-to-one coalgebra map collapses distinct successors; the
resulting finite set cannot reconstruct their supplied origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.GSOSControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Classical
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

inductive Operator where
  | stopped
  | choose
  deriving DecidableEq

abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator
  Position := fun operator => match operator with
    | .stopped => Empty
    | .choose => Bool
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

abbrev actions : signature.Srt → Type := fun _ => Nat
abbrev naturals : signature.Families := fun _ _ => Nat
abbrev units : signature.Families := fun _ _ => Unit

def pure {X : signature.Families} (value : X PUnit.unit ()) : signature.Term X () :=
  IndexedPolynomial.Free.pure signature.polynomial value

def stopped {X : signature.Families} : signature.Term X () :=
  IndexedPolynomial.Free.node signature.polynomial Operator.stopped (fun position => position.elim)

def choose {X : signature.Families} (first second : signature.Term X ()) : signature.Term X () :=
  IndexedPolynomial.Free.node signature.polynomial Operator.choose
    (fun position => if position then second else first)

abbrev pureNat (value : Nat) : signature.Term naturals () := pure (X := naturals) value
abbrev pureUnit (value : Unit) : signature.Term units () := pure (X := units) value

/-- This is an independently specified complete GSOS law. Both child
successor sets contribute, and repeated targets are treated as set members. -/
def law : Law signature actions where
  app X := fun base sort => match base, sort with
    | PUnit.unit, () => ↾(fun layer => match layer with
      | ⟨.stopped, _⟩ => fun _ => ∅
      | ⟨.choose, children⟩ => fun action => FinitePowerset.map (pure (X := X))
          ((children false).2 action ∪ (children true).2 action))
  naturality {X Y} mapping := by
    classical
    funext base sort
    cases base
    cases sort
    apply ConcreteCategory.hom_ext
    intro layer
    cases layer with
    | mk operator children =>
      cases operator with
      | stopped =>
        funext action
        exact (FinitePowerset.map_empty _).symm
      | choose =>
        funext action
        change FinitePowerset.map (pure (X := Y))
            (FinitePowerset.map (mapping PUnit.unit ()) ((children false).2 action) ∪
              FinitePowerset.map (mapping PUnit.unit ()) ((children true).2 action)) =
          FinitePowerset.map (signature.termMonad.map mapping PUnit.unit ())
            (FinitePowerset.map (pure (X := X))
              ((children false).2 action ∪ (children true).2 action))
        simp only [FinitePowerset.map, Finset.image_union, Finset.image_image]
        rfl

abbrev Offered (X : signature.Families) :=
  (position : Bool) → X PUnit.unit () × Behaviour signature actions X PUnit.unit ()

theorem law_choice_readout (X : signature.Families) (arguments : Offered X) (action : Nat) :
    law.app X PUnit.unit () ⟨Operator.choose, arguments⟩ action =
      FinitePowerset.map (pure (X := X))
        ((arguments false).2 action ∪ (arguments true).2 action) := rfl

/-- The complete constructor equation follows from the independent law and
free multiplication, rather than defining the operational result by union. -/
theorem operational_choice {X : signature.Families}
    (steps : VariableCoalgebra signature actions X)
    (first second : signature.Term X ()) (action : Nat) :
    Operational.coalgebra law steps PUnit.unit () (choose first second) action =
      Operational.coalgebra law steps PUnit.unit () first action ∪
        Operational.coalgebra law steps PUnit.unit () second action := by
  change Operational.coalgebra law steps PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial Operator.choose _) action = _
  rw [Operational.coalgebra_node, law_choice_readout, FinitePowerset.map_compose]
  exact FinitePowerset.map_identity _

def offered : Offered naturals :=
  fun position => if position then
    (20, fun action => if action = 7 then {21, 31} else ∅)
  else (10, fun action => if action = 7 then {11, 31} else ∅)

theorem independently_authored_law_readout :
    law.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ 7 =
      {pureNat 11, pureNat 21, pureNat 31} := by
  classical
  ext term
  rw [law_choice_readout]
  simp [offered, FinitePowerset.map, pureNat, eq_comm, or_left_comm, or_comm]

def inputSteps : VariableCoalgebra signature actions naturals :=
  fun _ _ => ↾(fun state action => if action = 7 then {state + 1, 31} else ∅)

abbrev inputs : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str := inputSteps

abbrev unitInputs : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := units
  str := fun _ _ => ↾(fun _ action => if action = 7 then {()} else ∅)

def choiceTerm : signature.Term naturals () := choose (pureNat 10) (pureNat 20)

theorem actual_unit_retains_variable (value : Nat) :
    ((Operational.liftedMonad law).η.app inputs).f PUnit.unit () value = pure value := rfl

theorem actual_pure_successors (value : Nat) :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () (pureNat value) 7 =
      {pureNat (value + 1), pureNat 31} := by
  classical
  change FinitePowerset.map (pure (X := naturals)) {value + 1, 31} = _
  ext term
  simp [FinitePowerset.map]

theorem actual_unit_successors :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit ()
      (((Operational.liftedMonad law).η.app inputs).f PUnit.unit () (10 : Nat)) 7 =
        {pureNat 11, pureNat 31} := actual_pure_successors 10

theorem actual_stopped_successors (action : Nat) :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () stopped action = ∅ := by
  change Operational.coalgebra law inputSteps PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial Operator.stopped _) action = ∅
  rw [Operational.coalgebra_node]
  exact FinitePowerset.map_empty _

/-- The operational conclusion is the complete union of the actual child
successors, computed by the lifted monad's constructed coalgebra. -/
theorem actual_choice_successors :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 =
      {pureNat 11, pureNat 21, pureNat 31} := by
  classical
  rw [Operational.lifted_coalgebra_readout, show choiceTerm =
    choose (pureNat 10) (pureNat 20) from rfl, operational_choice]
  change (((Operational.liftedMonad law).obj inputs).str PUnit.unit () (pureNat 10) 7 ∪
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () (pureNat 20) 7) = _
  rw [actual_pure_successors, actual_pure_successors]
  ext term
  simp [or_left_comm]

theorem both_child_successors_retained :
    pureNat 11 ∈ ((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 ∧
    pureNat 21 ∈ ((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 := by
  classical
  rw [actual_choice_successors]
  simp

theorem shared_successor_retained :
    pureNat 31 ∈ ((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 := by
  classical
  rw [actual_choice_successors]
  simp

def collapse : inputs ⟶ unitInputs where
  f := fun _ _ => ↾(fun _ => ())
  h := by
    classical
    funext base sort
    apply ConcreteCategory.hom_ext
    intro state
    funext action
    by_cases enabled : action = 7
    · simp [inputSteps, behaviourFunctor, behaviourMap, FinitePowerset.map, enabled]
    · simp [inputSteps, behaviourFunctor, behaviourMap, FinitePowerset.map, enabled]

theorem collapse_noninjective : ¬ Function.Injective (collapse.f PUnit.unit ()) := by
  intro injective
  exact Nat.zero_ne_one (injective (a₁ := 0) (a₂ := 1) rfl)

/-- The actual lifted map preserves both constructor arguments even when
their distinct variables are identified. -/
theorem actual_map_retains_choice :
    ((Operational.liftedMonad law).map collapse).f PUnit.unit () choiceTerm =
      choose (pureUnit ()) (pureUnit ()) := by
  rw [Operational.lifted_map_readout]
  change IndexedPolynomial.Free.map signature.polynomial (fun base sort => collapse.f base sort) PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial Operator.choose _) = _
  rw [IndexedPolynomial.Free.map_node]
  apply congrArg (IndexedPolynomial.Free.node signature.polynomial Operator.choose)
  funext position
  cases position <;> rfl

theorem actual_map_pure (value : Nat) :
    ((Operational.liftedMonad law).map collapse).f PUnit.unit () (pureNat value) =
      pureUnit () := rfl

theorem actual_identified_successors :
    ((Operational.liftedMonad law).obj unitInputs).str PUnit.unit ()
      (((Operational.liftedMonad law).map collapse).f PUnit.unit () choiceTerm) 7 =
        {pureUnit ()} := by
  classical
  have square := congrArg (fun arrow => arrow PUnit.unit () choiceTerm 7)
    ((Operational.liftedMonad law).map collapse).h
  change FinitePowerset.map (((Operational.liftedMonad law).map collapse).f PUnit.unit ())
    (((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7) = _ at square
  rw [actual_choice_successors] at square
  symm
  calc
    {pureUnit ()} = FinitePowerset.map
        (((Operational.liftedMonad law).map collapse).f PUnit.unit ())
        {pureNat 11, pureNat 21, pureNat 31} := by
      ext term
      simp [FinitePowerset.map, actual_map_pure]
    _ = _ := square

theorem complete_actual_map_square (term : signature.Term naturals ()) (action : Nat) :
    FinitePowerset.map (((Operational.liftedMonad law).map collapse).f PUnit.unit ())
        (((Operational.liftedMonad law).obj inputs).str PUnit.unit () term action) =
      ((Operational.liftedMonad law).obj unitInputs).str PUnit.unit ()
        (((Operational.liftedMonad law).map collapse).f PUnit.unit () term) action :=
  congrArg (fun arrow => arrow PUnit.unit () term action)
    ((Operational.liftedMonad law).map collapse).h

def nestedChoice : signature.polynomial.Free (signature.polynomial.Free naturals) PUnit.unit () :=
  choose (pure choiceTerm) (pure stopped)

theorem actual_multiplication_term :
    ((Operational.liftedMonad law).μ.app inputs).f PUnit.unit () nestedChoice =
      choose choiceTerm stopped := by
  change IndexedPolynomial.Free.bind signature.polynomial (fun _ _ term => term)
    PUnit.unit () (IndexedPolynomial.Free.node signature.polynomial Operator.choose _) = _
  rw [IndexedPolynomial.Free.bind_node]
  apply congrArg (IndexedPolynomial.Free.node signature.polynomial Operator.choose)
  funext position
  cases position <;> rfl

theorem actual_multiplication_successors :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit ()
      (((Operational.liftedMonad law).μ.app inputs).f PUnit.unit () nestedChoice) 7 =
        {pureNat 11, pureNat 21, pureNat 31} := by
  classical
  rw [actual_multiplication_term]
  rw [Operational.lifted_coalgebra_readout, operational_choice]
  change (((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 ∪
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () stopped 7) = _
  rw [actual_choice_successors, actual_stopped_successors]
  exact Finset.union_empty _

theorem complete_actual_multiplication_square
    (term : signature.polynomial.Free (signature.polynomial.Free naturals) PUnit.unit ())
    (action : Nat) :
    FinitePowerset.map (((Operational.liftedMonad law).μ.app inputs).f PUnit.unit ())
        (((Operational.liftedMonad law).obj ((Operational.liftedMonad law).obj inputs)).str
          PUnit.unit () term action) =
      ((Operational.liftedMonad law).obj inputs).str PUnit.unit ()
        (((Operational.liftedMonad law).μ.app inputs).f PUnit.unit () term) action :=
  congrArg (fun arrow => arrow PUnit.unit () term action)
    ((Operational.liftedMonad law).μ.app inputs).h

/-- Numerical observation reads actual supplied leaves and actual choice
nodes. It also discriminates successors in the collision controls. -/
def valueReadout : signature.Term naturals () → Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ value => value)
    ⟨fun _ _ layer => match layer with
      | ⟨.stopped, _⟩ => 0
      | ⟨.choose, children⟩ => children false + children true⟩ PUnit.unit ()

theorem pure_injective : Function.Injective pureNat := by
  intro first second same
  exact congrArg valueReadout same

theorem actual_branch_counts :
    (((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7).card = 3 ∧
      (((Operational.liftedMonad law).obj unitInputs).str PUnit.unit ()
        (((Operational.liftedMonad law).map collapse).f PUnit.unit () choiceTerm) 7).card = 1 := by
  classical
  rw [actual_choice_successors, actual_identified_successors]
  simp [Finset.card_insert_of_notMem, pure_injective.eq_iff]

theorem distinct_supplied_successors : (pureNat 11 : signature.Term naturals ()) ≠ pureNat 21 := by
  intro same
  have reading := congrArg valueReadout same
  change (11 : Nat) = 21 at reading
  omega

theorem supplied_successors_identified :
    ((Operational.liftedMonad law).map collapse).f PUnit.unit () (pureNat 11) =
      ((Operational.liftedMonad law).map collapse).f PUnit.unit () (pureNat 21) := rfl

theorem no_supplied_successor_decoder :
    ¬ ∃ decode : signature.Term units () → signature.Term naturals (),
      ∀ term, decode (((Operational.liftedMonad law).map collapse).f PUnit.unit () term) = term := by
  rintro ⟨decode, recovers⟩
  exact distinct_supplied_successors ((recovers (pureNat 11)).symm.trans
    ((congrArg decode supplied_successors_identified).trans (recovers (pureNat 21))))

/-- Dropping one child changes a concrete successor, even when the other
child already supplies the common successor. -/
theorem first_child_alone_insufficient :
    ((Operational.liftedMonad law).obj inputs).str PUnit.unit () (pureNat 10) 7 ≠
      ((Operational.liftedMonad law).obj inputs).str PUnit.unit () choiceTerm 7 := by
  classical
  intro same
  have member := both_child_successors_retained.2
  rw [← same, actual_pure_successors] at member
  have alternatives : (pureNat 21 : signature.Term naturals ()) = pureNat 11 ∨ pureNat 21 = pureNat 31 :=
    by simpa using member
  rcases alternatives with left | right
  · have reading := congrArg valueReadout left
    change (21 : Nat) = 11 at reading
    omega
  · have reading := congrArg valueReadout right
    change (21 : Nat) = 31 at reading
    omega

/-- The fixed common successor makes an arbitrary translation fail the
variable-coalgebra square. Law naturality alone does not supply that square. -/
def incompatibleShift : naturals ⟶ naturals := fun _ _ => ↾(fun value => value + 1)

theorem incompatible_shift_has_no_coalgebra_map :
    ¬ ∃ mapping : inputs ⟶ inputs, mapping.f = incompatibleShift := by
  classical
  rintro ⟨mapping, same⟩
  have square := mapping.h
  rw [same] at square
  have reading := congrArg (fun arrow => arrow PUnit.unit () 0 7) square
  change FinitePowerset.map (fun value : Nat => value + 1) {1, 31} = {2, 31} at reading
  have supplied : (32 : Nat) ∈ FinitePowerset.map (fun value : Nat => value + 1) {1, 31} := by
    simp [FinitePowerset.map]
  rw [reading] at supplied
  simp at supplied

end Mettapedia.OSLF.FiniteBranching.GSOSControls
