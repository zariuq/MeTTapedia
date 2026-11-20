import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStage

/-!
# Protected micro-executions and logical executions are in bijection

Completed ready-to-ready paths retain all logical labels and all path witnesses.
The phase controller cannot admit a public action between a protocol's two
primitive firings. The bijection is over the stated plan family; a language's
allocator and match-identity choices remain explicit parameters of that family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStage

open Interface (Frames)

universe uO uT uH uOcc uS uF uPlan uL
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Interface.Step X O State Firing}
  {Plan : State → Type uPlan} {Label : Type uL} (C : Configuration P Plan Label)

def Collapsed (source : Phase Plan) (word : List Label) (target : State) : Type (max uS uF uPlan uL) :=
  match source with
  | .ready state => MacroTrace C state word target
  | .pending plan =>
      {rest : (tail : List Label) × MacroTrace C (C.realize plan).finishState tail target //
        word = C.protocolLabel plan :: rest.1}

noncomputable def enterMacro {source : State} (plan : Plan source) {word : List Label} {target : State}
    (rest : Collapsed C (.pending plan) word target) : MacroTrace C source word target :=
  rest.property.symm ▸ MacroTrace.cons (.protocol plan) rest.val.2

noncomputable def rebuild : {source : Phase Plan} → {word : List Label} → {target : State} →
    Collapsed C source word target → MicroTrace C source word (.ready target)
  | .ready _, _, _, rest => expand C rest
  | .pending plan, _, _, rest =>
      rest.property.symm ▸ MicroTrace.cons (.finish plan) (expand C rest.val.2)

noncomputable def collapseAny : {source last : Phase Plan} → {word : List Label} →
    MicroTrace C source word last → (target : State) → last = .ready target → Collapsed C source word target
  | _, _, _, .nil _, _, same => by cases same; exact .nil _
  | _, _, _, .cons (.external firing admitted permitted) later, target, same =>
      MacroTrace.cons (.external firing admitted permitted) (collapseAny later target same)
  | _, _, _, .cons (.enter plan) later, target, same => enterMacro C plan (collapseAny later target same)
  | _, _, _, .cons (.finish plan) later, target, same => ⟨⟨_, collapseAny later target same⟩, rfl⟩

noncomputable def collapse {source : Phase Plan} {word : List Label} {target : State}
    (path : MicroTrace C source word (.ready target)) : Collapsed C source word target :=
  collapseAny C path target rfl

theorem expand_enterMacro {source : State} (plan : Plan source) {word : List Label} {target : State}
    (rest : Collapsed C (.pending plan) word target) :
    expand C (enterMacro C plan rest) = MicroTrace.cons (.enter plan) (rebuild C rest) := by
  rcases rest with ⟨⟨tail, path⟩, same⟩
  cases same
  rfl

theorem rebuild_collapseAny : ∀ {source last : Phase Plan} {word : List Label}
    (path : MicroTrace C source word last) (target : State) (same : last = .ready target),
    rebuild C (collapseAny C path target same) = same ▸ path := by
  intro source last word path
  induction path with
  | nil source =>
    intro target same
    cases same
    rfl
  | cons move later ih =>
    intro target same
    cases move with
    | external firing admitted permitted =>
      cases same
      exact congrArg (MicroTrace.cons (.external firing admitted permitted)) (ih target rfl)
    | enter plan =>
      cases same
      change expand C (enterMacro C plan (collapseAny C later target rfl)) = _
      rw [expand_enterMacro]
      exact congrArg (MicroTrace.cons (.enter plan)) (ih target rfl)
    | finish plan =>
      cases same
      exact congrArg (MicroTrace.cons (.finish plan)) (ih target rfl)

theorem rebuild_collapse {source : Phase Plan} {word : List Label} {target : State}
    (path : MicroTrace C source word (.ready target)) : rebuild C (collapse C path) = path :=
  rebuild_collapseAny C path target rfl

theorem collapse_expand : ∀ {source target : State} {word : List Label}
    (path : MacroTrace C source word target), collapse C (expand C path) = path
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons (.external firing admitted permitted) later =>
      congrArg (MacroTrace.cons (.external firing admitted permitted)) (collapse_expand later)
  | _, _, _, .cons (.protocol plan) later =>
      congrArg (MacroTrace.cons (.protocol plan)) (collapse_expand later)

noncomputable def readyTraceEquiv (source target : State) (word : List Label) :
    MacroTrace C source word target ≃ MicroTrace C (.ready source) word (.ready target) where
  toFun := expand C
  invFun := collapse C
  left_inv := collapse_expand C
  right_inv := rebuild_collapse C

#print axioms expand_enterMacro
#print axioms rebuild_collapse
#print axioms collapse_expand
#print axioms readyTraceEquiv

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStage
