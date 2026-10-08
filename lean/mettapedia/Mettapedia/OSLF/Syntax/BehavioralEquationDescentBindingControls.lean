import Mettapedia.OSLF.Syntax.BehavioralEquationDescentControls
import Mettapedia.OSLF.Syntax.BehavioralEquationDescentConstructors
import Mettapedia.OSLF.Syntax.BehavioralEquationDescentSubstitution

/-!
# Binding, substitution and complete quotient-clause controls

The active-scope law is checked under actual binder lifts. Replacing an
ambient variable by an inert term preserves its quotient operational edge
and leaves a newly bound variable untouched. An independently supplied
position-sensitive probe separates those retained witnesses in the same
equation quotient. Substitution of an enabled prefix for an inert variable
fails the unqualified operational substitution square.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BehavioralEquationDescentBindingControls

open FreeBindingTerms BindingEquationFamilyCongruence BehavioralEquationDescent
open BehavioralEquationDescentControls

theorem clauses : ClauseSubstitutionCompatible law
  | _, _, _environment, (), .stop, .nil => rfl
  | _, _, _environment, (), .tick, .cons _child .nil => rfl
  | _, _, environment, (), .scope, .cons child .nil => by
    funext action
    change ((child.2 action).map (bind (liftSub environment [()]))).map scope =
      ((child.2 action).map scope).map (bind environment)
    cases child.2 action <;> rfl

inductive Passive : {Γ : Ctx signature} → {sort : signature.Srt} →
    Term signature Γ sort → Prop where
  | isVariable {Γ : Ctx signature} {sort : signature.Srt} (position : Var Γ sort) :
    Passive (Γ := Γ) (sort := sort) (.var position)
  | stopped {Γ : Ctx signature} {sort : signature.Srt} :
    Passive (Γ := Γ) (sort := sort) (.op .stop .nil)

theorem passive_weaken {Γ : Ctx signature} {sort fresh : signature.Srt}
    {term : Term signature Γ sort} : Passive term → Passive (weaken (t := fresh) term)
  | .isVariable position => .isVariable (.succ position)
  | .stopped => .stopped

def passiveDomain : EnvironmentDomain signature :=
  fun environment => ∀ sort position, Passive (environment sort position)

theorem passive_lift_closed : LiftClosed passiveDomain := by
  intro Γ Δ environment admitted binders
  induction binders with
  | nil => exact admitted
  | cons fresh binders ih =>
    intro sort position
    cases position with
    | zero => exact .isVariable .zero
    | succ old => exact passive_weaken (ih sort old)

theorem passive_behavior : ∀ {Γ : Ctx signature} {sort : signature.Srt}
    {term : Term signature Γ sort}, Passive term → coalgebra law term = fun _ => none
  | _, _, _, .isVariable _ => rfl
  | _, _, _, .stopped => rfl

theorem passive_inputs : VariableSubstitutionCompatible law passiveDomain := by
  intro Γ Δ environment admitted sort position
  exact passive_behavior (admitted sort position)

def closeAmbient : Sub signature [()] [] := fun _ position => match position with
  | .zero => stop
  | .succ old => nomatch old

theorem closeAmbient_passive : passiveDomain closeAmbient := by
  intro sort position
  cases position with
  | zero => exact .stopped
  | succ old => nomatch old

/-- Actual capture avoidance: the old free position is replaced and the
new binder position survives the same substitution. -/
theorem closing_raw_readout :
    bind closeAmbient (scope (tick capturedBody)) = scope (tick stop) ∧
      bind closeAmbient (scope (tick boundBody)) = scope (tick (.var .zero)) :=
  ⟨rfl, rfl⟩

def closeClasses {sort : signature.Srt} : Classes family [()] sort → Classes family [] sort :=
  BindingTermCongruenceQuotient.bindQ (BindingEquationFamilyModel.congruence family) closeAmbient

theorem closing_descended_readout :
    descended (closeClasses (project family (scope (tick capturedBody)))) () =
      some (project family (scope stop)) := by
  have square := quotientCoalgebra_bindQ law constructors equations clauses passive_lift_closed passive_inputs
    closeAmbient closeAmbient_passive (project family (scope (tick capturedBody))) ()
  change descended (closeClasses (project family (scope (tick capturedBody)))) () =
    (descended (project family (scope (tick capturedBody))) ()).map closeClasses at square
  rw [actual_captured_binder_readout] at square
  exact square

/-- The complete class-level constructor clause is exercised independently
of the chosen representatives and of the source term's tree presentation. -/
theorem complete_scope_clause {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    quotientOperation family law .scope
      (.cons (project family (tick body), fun _ => some (project family body)) .nil) () =
        some (project family (scope body)) := by
  have square := quotientOperation_projection family law constructors (Γ := Γ) (sort := ()) .scope
    (.cons (tick body, fun _ => some body) .nil)
  exact congrArg (fun behavior => behavior ()) square

/-- The actual quotient clone obeys that complete constructor law, rather
than a second hand-defined quotient operator. -/
theorem actual_quotient_scope_clause {Γ : Ctx signature}
    (body : Term signature (() :: Γ) ()) :
    descended
      ((BindingEquationFamilyModel.algebra family).operation .scope
        (.cons (project family (tick body)) .nil)) () =
      some (project family (scope body)) := by
  have square := congrArg (fun behavior => behavior ())
    (quotientCoalgebra_operation family law constructors equations (Γ := Γ) (sort := ()) .scope
      (.cons (project family (tick body)) .nil))
  change descended _ () = quotientOperation family law .scope
    (.cons (project family (tick body), descended (project family (tick body))) .nil) () at square
  have input : descended (project family (tick body)) = fun _ => some (project family body) := by
    funext action
    change (coalgebra law (tick body) action).map (project family) = _
    rw [behavior_tick]
    rfl
  rw [input, complete_scope_clause] at square
  exact square

def probe : LocalLaw signature actions where
  onVariable := fun position _ => match position with
    | .zero => none
    | .succ old => some (.var (.succ old))
  operation := law.operation

theorem probe_tick {Γ : Ctx signature} (child : Term signature Γ ()) :
    coalgebra probe (tick child) = fun _ => some child := by
  rw [coalgebra_operation]
  rfl

theorem probe_scope {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    coalgebra probe (scope body) = fun action => (coalgebra probe body action).map scope := by
  rw [coalgebra_operation]
  rfl

theorem probe_equations : EquationCompatible probe family := by
  intro equation admitted Θ Γ bodies ambient ordinary action
  cases admitted
  change ((coalgebra probe (scope (tick _))) action).map (project family) =
    ((coalgebra probe (tick (scope _))) action).map (project family)
  rw [probe_scope, probe_tick, probe_tick, weakenSub_nil, weakenSub_nil]
  rfl

def probed {Γ : Ctx signature} :
    Classes family Γ () → Unit → Option (Classes family Γ ()) :=
  quotientCoalgebra probe constructors probe_equations

/-- The same admitted equations retain distinct bound/ambient witnesses.
This is proved on the actual classes by an independently formed probe. -/
theorem captured_and_bound_classes_distinct :
    project family (scope capturedBody) ≠ project family (scope boundBody) := by
  intro same
  have readout := congrArg (fun value => probed value ()) same
  change (coalgebra probe (scope capturedBody) ()).map (project family) =
    (coalgebra probe (scope boundBody) ()).map (project family) at readout
  rw [probe_scope, probe_scope] at readout
  change some (project family (scope capturedBody)) = none at readout
  cases readout

def enabledInput : Sub signature [()] [] := fun _ position => match position with
  | .zero => tick stop
  | .succ old => nomatch old

/-- Substitution need not preserve an inert variable's operational behavior.
The positive square's input-domain obligation is necessary. -/
theorem enabled_input_breaks_unqualified_substitution :
    coalgebra law (bind enabledInput (.var (.zero : Var [()] ()))) () ≠
      (coalgebra law (.var (.zero : Var [()] ())) ()).map (bind enabledInput) := by
  change some stop ≠ none
  intro same
  cases same

end Mettapedia.OSLF.Binding.BehavioralEquationDescentBindingControls
