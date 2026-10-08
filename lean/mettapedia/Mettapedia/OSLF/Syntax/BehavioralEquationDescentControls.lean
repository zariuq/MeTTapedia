import Mettapedia.OSLF.Syntax.BehavioralEquationDescent

/-!
# A genuine binder and an independently computed quotient coalgebra

The local law has an inert constructor, a prefix that emits its supplied
child, and an active scope that forwards a step below its declared binder.
Moving a prefix across that binder preserves complete successor classes.
The quotient is proper: a prefix remains distinguishable from an inert term.
An equation identifying those two has no descended coalgebra for this law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BehavioralEquationDescentControls

open FreeBindingTerms BindingEquationFamilyCongruence BehavioralEquationDescent

inductive Operator where
  | stop
  | tick
  | scope
  deriving DecidableEq

abbrev signature : Signature where
  Srt := Unit
  Op := fun _ => Operator
  arity := fun operator => match operator with
    | .stop => []
    | .tick => [([], ())]
    | .scope => [([()], ())]

abbrev stop {Γ : Ctx signature} : Term signature Γ () := .op .stop .nil

abbrev tick {Γ : Ctx signature} (child : Term signature Γ ()) : Term signature Γ () :=
  .op .tick (.cons child .nil)

abbrev scope {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) : Term signature Γ () :=
  .op .scope (.cons body .nil)

abbrev actions (_ : signature.Srt) : Type := Unit

def law : LocalLaw signature actions where
  onVariable := fun _ _ => none
  operation := fun operator arguments => match operator, arguments with
    | .stop, .nil => fun _ => none
    | .tick, .cons child .nil => fun _ => some child.1
    | .scope, .cons child .nil => fun action => (child.2 action).map scope

theorem behavior_stop {Γ : Ctx signature} : coalgebra law (stop (Γ := Γ)) = fun _ => none := by
  rw [coalgebra_operation]
  rfl

theorem behavior_tick {Γ : Ctx signature} (child : Term signature Γ ()) :
    coalgebra law (tick child) = fun _ => some child := by
  rw [coalgebra_operation]
  rfl

theorem behavior_scope {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    coalgebra law (scope body) = fun action => (coalgebra law body action).map scope := by
  rw [coalgebra_operation]
  rfl

abbrev metas : List (MetaArity signature) := [([()], ())]

def schemaBody : Term (withMetas signature metas) [()] () :=
  .op (.inr (.mk ⟨0, by decide⟩)) (.cons (.var .zero) .nil)

def scopeTick : EqAxiom signature metas where
  ctx := []
  sort := ()
  lhs := .op (.inl .scope) (.cons (.op (.inl .tick) (.cons schemaBody .nil)) .nil)
  rhs := .op (.inl .tick) (.cons (.op (.inl .scope) (.cons schemaBody .nil)) .nil)

def family (equation : EqAxiom signature metas) : Prop := equation = scopeTick

theorem scope_related {Γ : Ctx signature} {first second : Term signature (() :: Γ) ()}
    (related : Related family first second) : Related family (scope first) (scope second) :=
  Related.operation (S := signature) (family := family) Operator.scope (.cons related .nil)

theorem map_scope_respects {Γ : Ctx signature}
    {first second : Option (Term signature (() :: Γ) ())}
    (agree : first.map (project family) = second.map (project family)) :
    (first.map scope).map (project family) = (second.map scope).map (project family) := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some value => cases agree
  | some first =>
    cases second with
    | none => cases agree
    | some second =>
      apply congrArg some
      apply Quotient.sound
      exact scope_related (Quotient.exact (Option.some.inj agree))

theorem constructors : ConstructorCompatible law family
  | _, (), .stop, .nil, .nil, .nil, _ => rfl
  | _, (), .tick, .cons _first .nil, .cons _second .nil, .cons head .nil, _ =>
    congrArg some (Quotient.sound head.1)
  | _, (), .scope, .cons _first .nil, .cons _second .nil, .cons head .nil, action =>
    map_scope_respects (head.2 action)

theorem weakenSub_nil {Γ Δ : Ctx signature} (environment : Sub signature Γ Δ) :
    ContextualAssignment.weakenSub [] environment = environment := by
  funext sort position
  exact rename_id (environment sort position)

theorem equations : EquationCompatible law family := by
  intro equation admitted Θ Γ bodies ambient ordinary action
  cases admitted
  change ((coalgebra law (scope (tick _))) action).map (project family) =
    ((coalgebra law (tick (scope _))) action).map (project family)
  rw [behavior_scope, behavior_tick, behavior_tick]
  rw [weakenSub_nil, weakenSub_nil]
  rfl

def descended {Γ : Ctx signature} :
    Classes family Γ () → Unit → Option (Classes family Γ ()) :=
  quotientCoalgebra law constructors equations

/-- The equation changes the raw constructor tree and retains its actual
bound argument. Its two operational successors are equal even before quotient. -/
theorem binder_prefix_behavior {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    coalgebra law (scope (tick body)) () = some (scope body) ∧
      coalgebra law (tick (scope body)) () = some (scope body) := by
  simp only [behavior_scope, behavior_tick, Option.map_some]
  exact ⟨trivial, trivial⟩

def suppliedBody {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    ContextualAssignment signature metas Γ :=
  Fin.cases (motive := fun position =>
    Term signature ((metas.get position).1 ++ Γ) (metas.get position).2)
    body (fun position => Fin.elim0 position)

/-- Supplying the complete contextual metavariable body instantiates exactly
the authored equation, rather than a new hand-built relation. -/
theorem binder_prefix_related {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    Related family (scope (tick body)) (tick (scope body)) := by
  refine ⟨[scopeTick], ?_, ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · let emptyEnvironment : Sub signature [] Γ := fun _ position => nomatch position
    have instanceProof := EqClosure.ax (E := [scopeTick]) ⟨0, by decide⟩
      (Θ := Γ) (Γ := Γ) (suppliedBody body)
      (fun _ position => .var position) emptyEnvironment
    change EqClosure [scopeTick]
      (ContextualAssignment.instantiate
        (suppliedBody body)
        (fun _ position => .var position) emptyEnvironment scopeTick.lhs)
      (ContextualAssignment.instantiate
        (suppliedBody body)
        (fun _ position => .var position) emptyEnvironment scopeTick.rhs) at instanceProof
    let freshEnvironment : Sub signature [()] (() :: Γ) := fun _ position => match position with
      | .zero => .var .zero
      | .succ old => nomatch old
    have identity : ContextualAssignment.joinSub freshEnvironment
        (ContextualAssignment.weakenSub [()]
          (fun (sort : signature.Srt) (position : Var Γ sort) => .var position)) =
        (fun (sort : signature.Srt) (position : Var (() :: Γ) sort) => .var position) := by
      funext sort position
      cases position <;> rfl
    simp only [scopeTick, schemaBody, ContextualAssignment.instantiate,
      ContextualAssignment.instantiateArgs, ContextualAssignment.apply, suppliedBody] at instanceProof
    rw [weakenSub_nil, weakenSub_nil] at instanceProof
    change EqClosure [scopeTick]
      (scope (tick (bind (ContextualAssignment.joinSub freshEnvironment
        (ContextualAssignment.weakenSub [()]
          (fun (sort : signature.Srt) (position : Var Γ sort) => .var position))) body)))
      (tick (scope (bind (ContextualAssignment.joinSub freshEnvironment
        (ContextualAssignment.weakenSub [()]
          (fun (sort : signature.Srt) (position : Var Γ sort) => .var position))) body))) at instanceProof
    rw [identity] at instanceProof
    have identityBody :
        bind (fun (sort : signature.Srt) (position : Var (() :: Γ) sort) => .var position) body = body :=
      bind_id body
    rw [identityBody] at instanceProof
    exact instanceProof


theorem quotient_binder_prefix {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    project family (scope (tick body)) = project family (tick (scope body)) :=
  Quotient.sound (binder_prefix_related body)

/-- Both presentations use the actual descended optional-successor coalgebra. -/
theorem descended_binder_prefix {Γ : Ctx signature} (body : Term signature (() :: Γ) ()) :
    descended (project family (scope (tick body))) () = some (project family (scope body)) ∧
      descended (project family (tick (scope body))) () = some (project family (scope body)) := by
  change ((coalgebra law (scope (tick body))) ()).map (project family) = _ ∧
    ((coalgebra law (tick (scope body))) ()).map (project family) = _
  rw [(binder_prefix_behavior body).1, (binder_prefix_behavior body).2]
  exact ⟨rfl, rfl⟩

/-- Open and bound positions remain distinct in the supplied positive witness. -/
def capturedBody : Term signature [(), ()] () := .var (.succ .zero)

def boundBody : Term signature [(), ()] () := .var .zero

theorem raw_bound_positions_distinct : capturedBody ≠ boundBody := by
  intro same
  cases same

theorem actual_captured_binder_readout :
    descended (project family (scope (tick capturedBody))) () =
      some (project family (scope capturedBody)) :=
  (descended_binder_prefix capturedBody).1

/-- The positive quotient retains enabledness. It does not identify every
constructor merely because some equation family has been supplied. -/
theorem proper_quotient {Γ : Ctx signature} :
    project family (stop (Γ := Γ)) ≠ project family (tick stop) := by
  intro same
  have behavior := congrArg (fun value => descended value ()) same
  change (coalgebra law (stop (Γ := Γ)) ()).map (project family) =
    (coalgebra law (tick (stop (Γ := Γ))) ()).map (project family) at behavior
  rw [behavior_stop, behavior_tick] at behavior
  cases behavior

def badEquation : EqAxiom signature ([] : List (MetaArity signature)) where
  ctx := []
  sort := ()
  lhs := .op (.inl .stop) .nil
  rhs := .op (.inl .tick) (.cons (.op (.inl .stop) .nil) .nil)

def badFamily (equation : EqAxiom signature ([] : List (MetaArity signature))) : Prop :=
  equation = badEquation

theorem bad_quotient_equal :
    project badFamily (stop (Γ := [])) = project badFamily (tick stop) := by
  apply Quotient.sound
  refine ⟨[badEquation], ?_, ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · exact EqClosure.ax (E := [badEquation]) ⟨0, by decide⟩ (Θ := [])
      (fun position => nomatch position) (fun _ position => nomatch position)
      (fun _ position => nomatch position)

/-- A genuine equation quotient need not admit the independently formed
behavior. No candidate optional-successor map can have the required raw square. -/
theorem no_bad_behavioral_descent :
    ¬ ∃ candidate : Classes badFamily [] () → Unit → Option (Classes badFamily [] ()),
      ∀ term action, candidate (project badFamily term) action =
        (coalgebra law term action).map (project badFamily) := by
  rintro ⟨candidate, square⟩
  have same := congrArg (fun value => candidate value ()) bad_quotient_equal
  rw [square, square, behavior_stop, behavior_tick] at same
  cases same

end Mettapedia.OSLF.Binding.BehavioralEquationDescentControls
