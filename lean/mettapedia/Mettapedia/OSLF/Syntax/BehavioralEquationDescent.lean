import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel

/-!
# Descent of an independently formed binding behavior through equations

A local constructor law computes optional successors from complete child
states and child behaviors. Its operational extension is a fold on the
existing intrinsically scoped free terms. Two local checks suffice for descent:
constructor clauses preserve related states and quotient successor readouts,
and each authored equation instance has matching successor readouts.

Congruence induction earns the global compatibility condition. The result is
an actual optional-successor coalgebra on the existing equation quotient,
with a unique projection square. No equation-saturated step relation is used.
This binder-indexed local-law interface does not claim that every such law is
a higher-order GSOS law or that every authored presentation is admissible.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BehavioralEquationDescent

open FreeBindingTerms BindingEquationFamilyCongruence

universe u

variable {S : Signature} (Actions : S.Srt → Type u)

abbrev Behavior (Γ : Ctx S) (sort : S.Srt) :=
  Actions sort → Option (Term S Γ sort)

abbrev Result (Γ : Ctx S) (sort : S.Srt) :=
  Term S Γ sort × Behavior Actions Γ sort

/-- Independently supplied variable and constructor clauses, before choosing
any equations or quotient. Every child retains its own binder context. -/
structure LocalLaw (S : Signature) (Actions : S.Srt → Type u) where
  onVariable : {Γ : Ctx S} → {sort : S.Srt} → Var Γ sort → Behavior Actions Γ sort
  operation : {Γ : Ctx S} → {sort : S.Srt} → (operator : S.Op sort) →
    FamilyArgs S (Result Actions) (S.arity operator) Γ → Behavior Actions Γ sort

variable {Actions} (law : LocalLaw S Actions)

/-- The actual fold algebra retains each term and calculates its behavior. -/
def algebra : FreeBindingTerms.Algebra.{u} S where
  Carrier := Result Actions
  injectVar := fun position => (.var position, law.onVariable position)
  operation := fun operator arguments =>
    (.op operator ((terms.familyToSyntax S) (FamilyArgs.map Prod.fst arguments)),
      law.operation operator arguments)

def evaluate {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) : Result Actions Γ sort :=
  FreeBindingTerms.fold (algebra law) term

def evaluateArgs {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args S arity Γ) : FamilyArgs S (Result Actions) arity Γ :=
  FreeBindingTerms.foldArgs (algebra law) arguments

mutual

theorem evaluate_source : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
    (evaluate law term).1 = term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments =>
    congrArg (Term.op operator) (evaluateArgs_source arguments)

theorem evaluateArgs_source :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (arguments : Args S arity Γ),
      (terms.familyToSyntax S) (FamilyArgs.map Prod.fst (evaluateArgs law arguments)) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
    congrArg₂ Args.cons (evaluate_source head) (evaluateArgs_source tail)

end

def coalgebra {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) : Behavior Actions Γ sort :=
  (evaluate law term).2

theorem evaluate_pair {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    evaluate law term = (term, coalgebra law term) :=
  Prod.ext (evaluate_source law term) rfl

theorem evaluateArgs_pair :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S} (arguments : Args S arity Γ),
      evaluateArgs law arguments =
        FamilyArgs.map (fun term => (term, coalgebra law term)) (syntaxToFamily arguments)
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
    congrArg₂ FamilyArgs.cons (evaluate_pair law head) (evaluateArgs_pair tail)

theorem coalgebra_variable {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) :
    coalgebra law (.var position) = law.onVariable position := rfl

theorem coalgebra_operation {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : Args S (S.arity operator) Γ) :
    coalgebra law (.op operator arguments) =
      law.operation operator
        (FamilyArgs.map (fun term => (term, coalgebra law term)) (syntaxToFamily arguments)) := by
  change law.operation operator (evaluateArgs law arguments) = _
  rw [evaluateArgs_pair]

variable {M : List (MetaArity S)} (family : EqAxiom S M → Prop)

abbrev Classes (Γ : Ctx S) (sort : S.Srt) :=
  BindingEquationFamilyModel.Carrier family Γ sort

abbrev project {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) : Classes family Γ sort :=
  BindingEquationFamilyModel.project family term

/-- State agreement and complete optional-successor agreement are separate
requirements; enabledness and the actual successor class are retained. -/
def PairRelated {Γ : Ctx S} {sort : S.Srt}
    (first second : Result Actions Γ sort) : Prop :=
  Related family first.1 second.1 ∧
    ∀ action, (first.2 action).map (project family) =
      (second.2 action).map (project family)

inductive PairArgsRelated (family : EqAxiom S M → Prop) : {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S (Result Actions) arity Γ → FamilyArgs S (Result Actions) arity Γ → Prop where
  | nil {Γ : Ctx S} : PairArgsRelated family (FamilyArgs.nil (Γ := Γ)) .nil
  | cons {binders : Ctx S} {sort : S.Srt} {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {first second : Result Actions (binders ++ Γ) sort}
      {tail tail' : FamilyArgs S (Result Actions) arity Γ} :
      PairRelated family first second → PairArgsRelated family tail tail' →
        PairArgsRelated family (.cons first tail) (.cons second tail')

/-- Each constructor clause is checked on arbitrary complete child inputs,
at the exact contexts opened by its signature. This is a local clause check. -/
def ConstructorCompatible : Prop :=
  ∀ {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    {first second : FamilyArgs S (Result Actions) (S.arity operator) Γ},
    PairArgsRelated family first second → ∀ action,
      (law.operation operator first action).map (project family) =
        (law.operation operator second action).map (project family)

/-- Only the declared equation schemas are checked, instantiated with arbitrary
captured bodies and independent ordinary and ambient substitutions. -/
def EquationCompatible : Prop :=
  ∀ equation, family equation → ∀ {Θ Γ : Ctx S}
    (bodies : ContextualAssignment S M Θ)
    (ambient : Sub S Θ Γ) (ordinary : Sub S equation.ctx Γ) (action : Actions equation.sort),
    (coalgebra law (ContextualAssignment.instantiate bodies ambient ordinary equation.lhs) action).map
        (project family) =
      (coalgebra law (ContextualAssignment.instantiate bodies ambient ordinary equation.rhs) action).map
        (project family)

variable {family}

mutual

/-- Congruence induction earns behavior agreement beneath every binder. -/
theorem eqClosure_behavior (constructors : ConstructorCompatible law family)
    (equations : EquationCompatible law family) {fragment : List (EqAxiom S M)} (support : Supported family fragment) :
    ∀ {Γ : Ctx S} {sort : S.Srt} {first second : Term S Γ sort},
      EqClosure fragment first second → ∀ action,
        (coalgebra law first action).map (project family) =
          (coalgebra law second action).map (project family)
  | _, _, _, _, .ax position bodies ambient ordinary =>
    equations (fragment.get position) (support _ (List.get_mem fragment position))
      bodies ambient ordinary
  | _, _, _, _, .refl _ => fun _ => rfl
  | _, _, _, _, .symm proof => fun action =>
    (eqClosure_behavior constructors equations support proof action).symm
  | _, _, _, _, .trans first second => fun action =>
    (eqClosure_behavior constructors equations support first action).trans (eqClosure_behavior constructors equations support second action)
  | _, _, _, _, .cong operator arguments => by
    rw [coalgebra_operation, coalgebra_operation]
    exact constructors operator (eqArgs_results constructors equations support arguments)

theorem eqArgs_results (constructors : ConstructorCompatible law family)
    (equations : EquationCompatible law family) {fragment : List (EqAxiom S M)} (support : Supported family fragment) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {first second : Args S arity Γ}, EqArgs fragment first second →
      PairArgsRelated family
        (FamilyArgs.map (fun term => (term, coalgebra law term)) (syntaxToFamily first))
        (FamilyArgs.map (fun term => (term, coalgebra law term)) (syntaxToFamily second))
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail =>
    .cons ⟨⟨fragment, support, head⟩, eqClosure_behavior constructors equations support head⟩
      (eqArgs_results constructors equations support tail)

end

variable (constructors : ConstructorCompatible law family) (equations : EquationCompatible law family)

include constructors equations

theorem related_behavior {Γ : Ctx S} {sort : S.Srt} {first second : Term S Γ sort}
    (related : Related family first second) (action : Actions sort) :
    (coalgebra law first action).map (project family) =
      (coalgebra law second action).map (project family) := by
  obtain ⟨fragment, support, proof⟩ := related
  exact eqClosure_behavior law constructors equations support proof action

omit constructors equations in
/-- The lifted relation compares actual optional successors, retaining both
enabledness and a generated equation derivation between the supplied targets. -/
inductive SuccessorsRelated {Γ : Ctx S} {sort : S.Srt} :
    Option (Term S Γ sort) → Option (Term S Γ sort) → Prop where
  | none : SuccessorsRelated none none
  | some {first second : Term S Γ sort} : Related family first second →
    SuccessorsRelated (some first) (some second)

omit constructors equations in
theorem successorsRelated_of_projection {Γ : Ctx S} {sort : S.Srt}
    {first second : Option (Term S Γ sort)}
    (same : first.map (project family) = second.map (project family)) :
    SuccessorsRelated (family := family) first second := by
  cases first with
  | none =>
    cases second with
    | none => exact .none
    | some target => cases same
  | some first =>
    cases second with
    | none => cases same
    | some second => exact .some (Quotient.exact (Option.some.inj same))

/-- The actual generated equation congruence is a strong bisimulation for
the admitted optional-successor observation. No maximal-bisimilarity
congruence or additional name/payload observation is inferred. -/
theorem equations_strong_bisimulation {Γ : Ctx S} {sort : S.Srt}
    {first second : Term S Γ sort} (related : Related family first second) (action : Actions sort) :
    SuccessorsRelated (family := family) (coalgebra law first action) (coalgebra law second action) :=
  successorsRelated_of_projection (related_behavior law constructors equations related action)

/-- The independently formed raw coalgebra descends to optional successor
classes. The well-definedness proof is the earned congruence induction. -/
def quotientCoalgebra {Γ : Ctx S} {sort : S.Srt} :
    Classes family Γ sort → Actions sort → Option (Classes family Γ sort) :=
  Quotient.lift (fun term action => (coalgebra law term action).map (project family))
    (fun _ _ related => funext (related_behavior law constructors equations related))

theorem quotientCoalgebra_project {Γ : Ctx S} {sort : S.Srt}
    (term : Term S Γ sort) (action : Actions sort) :
    quotientCoalgebra law constructors equations (project family term) action =
      (coalgebra law term action).map (project family) := rfl

/-- Projection determines the complete descended coalgebra uniquely. -/
theorem quotientCoalgebra_unique {Γ : Ctx S} {sort : S.Srt}
    (candidate : Classes family Γ sort → Actions sort → Option (Classes family Γ sort))
    (onRaw : ∀ term action, candidate (project family term) action =
      (coalgebra law term action).map (project family)) :
    candidate = quotientCoalgebra law constructors equations := by
  funext value action
  induction value using Quotient.inductionOn with
  | _ term => exact onRaw term action

omit constructors equations in
/-- An independently specified candidate family must commute with raw
projection on every context, sort, action and complete successor. -/
def HasDescendedCoalgebra : Prop :=
  ∃ candidate : {Γ : Ctx S} → {sort : S.Srt} →
      Classes family Γ sort → Actions sort → Option (Classes family Γ sort),
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) (action : Actions sort),
      candidate (project family term) action =
        (coalgebra law term action).map (project family)

omit constructors equations in
/-- A projection square forces the local equation-instance check. Thus a
genuine equation quotient alone cannot license behavioral descent. -/
theorem equations_of_descent (descends : HasDescendedCoalgebra law (family := family)) :
    EquationCompatible law family := by
  obtain ⟨candidate, square⟩ := descends
  intro equation admitted Θ Γ bodies ambient ordinary action
  have same :
      project family (ContextualAssignment.instantiate bodies ambient ordinary equation.lhs) =
        project family (ContextualAssignment.instantiate bodies ambient ordinary equation.rhs) := by
    apply Quotient.sound
    refine ⟨[equation], ?_, ?_⟩
    · intro selected member
      obtain rfl := List.mem_singleton.mp member
      exact admitted
    · exact EqClosure.ax (E := [equation]) ⟨0, by simp⟩ bodies ambient ordinary
  have readout := congrArg (fun value => candidate value action) same
  rw [square, square] at readout
  exact readout

omit equations in
/-- With local constructor admissibility checked, local authored equations
characterize existence of the full descended optional-successor coalgebra. -/
theorem descent_iff_equations :
    HasDescendedCoalgebra law (family := family) ↔ EquationCompatible law family := by
  constructor
  · exact equations_of_descent law
  · intro compatible
    exact ⟨fun {Γ sort} => quotientCoalgebra law constructors compatible,
      fun term action => quotientCoalgebra_project law constructors compatible term action⟩

end Mettapedia.OSLF.Binding.BehavioralEquationDescent
