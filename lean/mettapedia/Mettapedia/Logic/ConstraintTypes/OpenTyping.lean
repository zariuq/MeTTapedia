import Mettapedia.Logic.ConstraintTypes.DeclarationTyping
import Mettapedia.Logic.ConstraintTypes.ResidualConstraints

/-!
# Open parametric membership from the declaration judgment

Known constructor nodes compile immediately. Unknown value leaves retain
membership requests, and nominal facts retain whole-pattern requests. All
alternatives share the queried type parameters; each constructor or fact gets
fresh private parameters. Correctness is for the same declaration judgment as
the closed checker, without enumerating its possible type instances.

A request carries a lookup context, not an interpretation of predicates. The
model is supplied when the residual is interpreted. The substitution law below
has one fixed declaration interpretation; it does not commute arbitrary edits.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.OpenTyping

open SymbolicTypes ResidualConstraints ConstructorTyping

variable {V U P Q C S Context : Type} {typeArity : C → Nat} {valueArity : S → Nat}

inductive Request (Context V U Q C S : Type) (typeArity : C → Nat) (valueArity : S → Nat) where
  | member (context : Context) (name : V)
  | pattern (pattern : OpenTree U S valueArity) (value : OpenTree V S valueArity)
  | index (pattern : OpenTree U S valueArity) (name : U)
      (present : name ∈ (ValuePatterns.patternCode pattern).variables)
      (readType : Tree S valueArity → Option (Closed Q C typeArity))
      (value : OpenTree V S valueArity)

def model (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (values : V → Tree S valueArity) : Request Context V U Q C S typeArity valueArity → Closed Q C typeArity → Prop
  | .member context name, type => DeclarationTyping.HasType declarations context (values name) type
  | .pattern pattern value, _ => ∃ matched, pattern.evaluate matched = value.evaluate values
  | .index pattern name _ readType value, type =>
      ∃ matched, pattern.evaluate matched = value.evaluate values ∧ readType (matched name) = some type


/-- Execute a ready request using the supplied declaration interpretation.
Unready requests remain data in ResidualConstraints; this function does not
choose a completion for an unbound program variable. -/
def checkRequest [DecidableEq U] [DecidableEq P] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (values : V → Tree S valueArity) : Request Context V U Q C S typeArity valueArity → Closed Q C typeArity → Bool
  | .member context name, type => DeclarationTyping.check declarations context (values name) type
  | .pattern pattern value, _ => ValuePatterns.matchValue pattern (value.evaluate values)
  | .index pattern name _ readType value, type => ValuePatterns.checkRead pattern name readType (value.evaluate values) type

theorem checkRequest_correct [DecidableEq U] [DecidableEq P] [DecidableEq Q] [DecidableEq C] [DecidableEq S]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (values : V → Tree S valueArity) (request : Request Context V U Q C S typeArity valueArity)
    (type : Closed Q C typeArity) :
    checkRequest declarations values request type = true ↔ model declarations values request type := by
  cases request with
  | member context name => exact DeclarationTyping.check_iff _ _ _ _
  | pattern pattern value => exact ValuePatterns.matchValue_iff _ _
  | index pattern name present readType value => exact ValuePatterns.checkRead_iff _ _ present _ _ _

def factRequests {X : Type}
    (fact : DeclarationTyping.Fact U P Q C S typeArity valueArity)
    (value : OpenTree V S valueArity) (target : Expr X Q C typeArity) :
    Requests (X ⊕ P) Q C (Request Context V U Q C S typeArity valueArity) typeArity :=
  (.pattern fact.pattern value, target.rename Sum.inl) ::
    fact.bindings.map fun binding =>
      (.index fact.pattern binding.name binding.present fact.readType value, .parameter (.inr binding.parameter))

theorem factRequests_correct {X : Type}
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (fact : DeclarationTyping.Fact U P Q C S typeArity valueArity)
    (term : OpenTree V S valueArity) (target : Expr X Q C typeArity)
    (outer : X → Closed Q C typeArity) (parameters : P → Closed Q C typeArity)
    (values : V → Tree S valueArity) :
    Holds (model declarations values) (Sum.elim outer parameters) (factRequests fact term target) ↔
      ∃ matched, fact.pattern.evaluate matched = term.evaluate values ∧
        ValuePatterns.BindingsHold fact.readType matched parameters fact.bindings := by
  constructor
  · intro all
    obtain ⟨matched, equal⟩ := all _ List.mem_cons_self
    refine ⟨matched, equal, ?_⟩
    intro binding present
    have read := all _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨binding, present, rfl⟩))
    obtain ⟨other, sameValue, decoded⟩ := read
    have same := ValuePatterns.matched_variable_determined fact.pattern matched other
      (equal.trans sameValue.symm) binding.name binding.present
    simpa only [TypeExpr.substitute, Sum.elim_inr, same] using decoded
  · rintro ⟨matched, equal, bound⟩ request present
    rcases List.mem_cons.1 present with rfl | present
    · exact ⟨matched, equal⟩
    · obtain ⟨binding, bindingPresent, rfl⟩ := List.mem_map.1 present
      exact ⟨matched, equal, bound binding bindingPresent⟩

def compile [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    {X : Type} (context : Context) : OpenTree V S valueArity → Expr X Q C typeArity →
      List (Problem X Q C (Request Context V U Q C S typeArity valueArity) typeArity)
  | .var name, target => [atom (.member context name) target]
  | .node symbol children, target =>
      (declarations.constructors context symbol).flatMap (fun rule =>
        (combinations ((List.finRange (valueArity symbol)).map fun i =>
          match rule.field i with
          | none => [pure ScopedConstraints.truth]
          | some fieldType => compile declarations (X := X ⊕ P) (declarations.childContext context symbol i)
              (children i) (fieldType.rename Sum.inr))).map fun body =>
          bind (conjunction
            (pure (ScopedConstraints.equation (target.rename Sum.inl) (rule.result.rename Sum.inr))) body)) ++
      (declarations.facts context).map fun fact =>
        ResidualConstraints.bind (conjunction
          (pure (ScopedConstraints.equation (target.rename Sum.inl) (fact.type.rename Sum.inr)))
          (requestsOnly (factRequests (Context := Context) fact (.node symbol children) target)))

/-- The open compiler retains exactly the ground completions admitted by the
independent declaration judgment. It does not claim that an undecided request
is already satisfied. -/
theorem compile_correct [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (term : OpenTree V S valueArity) {X : Type} (context : Context)
    (target : Expr X Q C typeArity) (outer : X → Closed Q C typeArity)
    (values : V → Tree S valueArity) :
    alternativesModel (compile declarations context term target) (model declarations values) outer ↔
      DeclarationTyping.HasType declarations context (term.evaluate values) (target.substitute outer) := by
  induction term generalizing X context with
  | var name =>
      simp only [compile, alternativesModel, List.mem_singleton, exists_eq_left, models_atom, model,
        OpenTree.evaluate]
  | node symbol children ih =>
      constructor
      · rintro ⟨problem, present, solved⟩
        rcases List.mem_append.1 present with constructorMember | factMember
        · obtain ⟨rule, rulePresent, mapped⟩ := List.mem_flatMap.1 constructorMember
          obtain ⟨body, bodyMember, equal⟩ := List.mem_map.1 mapped
          subst problem
          obtain ⟨parameters, joint⟩ := (models_bind _ _ _).1 solved
          obtain ⟨root, fields⟩ := (models_conjunction _ _ _ _).1 joint
          have resultType : target.substitute outer = rule.result.substitute parameters := by
            simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
              (ScopedConstraints.satisfies_equation _ _ _).1 ((models_pure _ _ _).1 root)
          have allFields := (models_combinations _ _ _).1 ⟨body, bodyMember, fields⟩
          rw [resultType]
          refine DeclarationTyping.HasType.constructor rule rulePresent parameters ?_
          intro i fieldType required
          have child := allFields _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
          simp only [required] at child
          have typed := (ih i (declarations.childContext context symbol i)
            (fieldType.rename Sum.inr) (Sum.elim outer parameters)).1 child
          simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inr] using typed
        · obtain ⟨fact, factPresent, equal⟩ := List.mem_map.1 factMember
          subst problem
          obtain ⟨parameters, joint⟩ := (models_bind _ _ _).1 solved
          obtain ⟨root, pending⟩ := (models_conjunction _ _ _ _).1 joint
          have resultType : target.substitute outer = fact.type.substitute parameters := by
            simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
              (ScopedConstraints.satisfies_equation _ _ _).1 ((models_pure _ _ _).1 root)
          obtain ⟨matched, equal, bound⟩ := (factRequests_correct declarations fact (.node symbol children)
            target outer parameters values).1 ((models_requestsOnly _ _ _).1 pending)
          rw [resultType]
          exact .nominal fact factPresent matched equal parameters bound
      · intro typed
        rcases (DeclarationTyping.hasType_node_iff _ _ _ _ _).1 typed with constructorCase | nominalCase
        · obtain ⟨rule, rulePresent, parameters, resultType, fields⟩ := constructorCase
          have chosen : alternativesModel
              (combinations ((List.finRange (valueArity symbol)).map fun i =>
                match rule.field i with
                | none => [pure ScopedConstraints.truth]
                | some fieldType => compile declarations (X := X ⊕ P)
                    (declarations.childContext context symbol i) (children i) (fieldType.rename Sum.inr)))
              (model declarations values) (Sum.elim outer parameters) := by
            apply (models_combinations _ _ _).2
            intro choice present
            obtain ⟨i, _, rfl⟩ := List.mem_map.1 present
            cases required : rule.field i with
            | none => exact ⟨_, List.mem_cons_self, (models_pure _ _ _).2 (ScopedConstraints.satisfies_truth _)⟩
            | some fieldType =>
                apply (ih i (declarations.childContext context symbol i)
                  (fieldType.rename Sum.inr) (Sum.elim outer parameters)).2
                simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inr] using fields i fieldType required
          obtain ⟨body, bodyPresent, solved⟩ := chosen
          refine ⟨_, List.mem_append_left _ (List.mem_flatMap.2 ⟨rule, rulePresent,
            List.mem_map.2 ⟨body, bodyPresent, rfl⟩⟩), ?_⟩
          apply (models_bind _ _ _).2
          refine ⟨parameters, (models_conjunction _ _ _ _).2 ⟨?_, solved⟩⟩
          apply (models_pure _ _ _).2
          apply (ScopedConstraints.satisfies_equation _ _ _).2
          simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
            resultType
        · obtain ⟨fact, factPresent, matched, equal, parameters, bound, resultType⟩ := nominalCase
          refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨fact, factPresent, rfl⟩), ?_⟩
          apply (models_bind _ _ _).2
          refine ⟨parameters, (models_conjunction _ _ _ _).2 ⟨?_, ?_⟩⟩
          · apply (models_pure _ _ _).2
            apply (ScopedConstraints.satisfies_equation _ _ _).2
            simpa only [TypeExpr.substitute_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
              resultType
          · apply (models_requestsOnly _ _ _).2
            exact (factRequests_correct declarations fact (.node symbol children)
              target outer parameters values).2 ⟨matched, equal, bound⟩

theorem binding_preserves_denotation [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    {W X : Type} (substitution : V → OpenTree W S valueArity) (values : W → Tree S valueArity)
    (term : OpenTree V S valueArity) (context : Context) (target : Expr X Q C typeArity)
    (outer : X → Closed Q C typeArity) :
    alternativesModel (compile declarations context (term.substitute substitution) target)
        (model declarations values) outer ↔
      alternativesModel (compile declarations context term target)
        (model declarations (fun x => (substitution x).evaluate values)) outer := by
  rw [compile_correct, compile_correct, OpenTree.evaluate_substitute]



/-- Waking a membership request on a newly exposed constructor uses the same
compiler as initial checking. Nominal pattern requests substitute their values
without changing their type equation. -/
def transferRequest [DecidableEq P] {W X : Type}
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (substitution : V → OpenTree W S valueArity) (request : Request Context V U Q C S typeArity valueArity)
    (type : Expr X Q C typeArity) : List (Problem X Q C (Request Context W U Q C S typeArity valueArity) typeArity) :=
  match request with
  | .member context name => compile declarations context (substitution name) type
  | .pattern pattern value => [atom (.pattern pattern (value.substitute substitution)) type]
  | .index pattern name present readType value =>
      [atom (.index pattern name present readType (value.substitute substitution)) type]

theorem transferRequest_correct [DecidableEq P] {W X : Type}
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (substitution : V → OpenTree W S valueArity) (values : W → Tree S valueArity)
    (request : Request Context V U Q C S typeArity valueArity) (type : Expr X Q C typeArity)
    (outer : X → Closed Q C typeArity) :
    alternativesModel (transferRequest declarations substitution request type) (model declarations values) outer ↔
      model declarations (fun x => (substitution x).evaluate values) request (type.substitute outer) := by
  cases request with
  | member context name => exact compile_correct _ _ _ _ _ _
  | pattern pattern value =>
      simp only [transferRequest, alternativesModel, List.mem_singleton, exists_eq_left, models_atom, model,
        OpenTree.evaluate_substitute]
  | index pattern name present readType value =>
      simp only [transferRequest, alternativesModel, List.mem_singleton, exists_eq_left, models_atom, model,
        OpenTree.evaluate_substitute]

def transferRequests [DecidableEq P] {W X : Type}
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (substitution : V → OpenTree W S valueArity)
    (requests : Requests X Q C (Request Context V U Q C S typeArity valueArity) typeArity) :
    List (Problem X Q C (Request Context W U Q C S typeArity valueArity) typeArity) :=
  combinations (requests.map fun request => transferRequest declarations substitution request.1 request.2)

theorem transferRequests_correct [DecidableEq P] {W X : Type}
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (substitution : V → OpenTree W S valueArity) (values : W → Tree S valueArity)
    (requests : Requests X Q C (Request Context V U Q C S typeArity valueArity) typeArity)
    (outer : X → Closed Q C typeArity) :
    alternativesModel (transferRequests declarations substitution requests) (model declarations values) outer ↔
      Holds (model declarations (fun x => (substitution x).evaluate values)) outer requests := by
  rw [transferRequests, models_combinations]
  constructor
  · intro all request present
    exact (transferRequest_correct _ _ _ _ _ _).1 (all _ (List.mem_map.2 ⟨request, present, rfl⟩))
  · intro all choice member
    obtain ⟨request, present, equal⟩ := List.mem_map.1 member
    subst choice
    exact (transferRequest_correct _ _ _ _ _ _).2 (all request present)

/-- Proper membership positions of one normalized signature. Modes are selected
before this stage, rather than being guessed as type-variable instances. -/
structure Query (V P Q C S Context : Type) (typeArity : C → Nat) (valueArity : S → Nat) where
  context : Context
  value : OpenTree V S valueArity
  type : Expr P Q C typeArity

def compileJoint [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (queries : List (Query V P Q C S Context typeArity valueArity)) :
    List (Problem P Q C (Request Context V U Q C S typeArity valueArity) typeArity) :=
  combinations (queries.map fun query => compile declarations query.context query.value query.type)

theorem compileJoint_correct [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (queries : List (Query V P Q C S Context typeArity valueArity))
    (parameters : P → Closed Q C typeArity) (values : V → Tree S valueArity) :
    alternativesModel (compileJoint declarations queries) (model declarations values) parameters ↔
      ∀ query ∈ queries, DeclarationTyping.HasType declarations query.context
        (query.value.evaluate values) (query.type.substitute parameters) := by
  rw [compileJoint, models_combinations]
  constructor
  · intro all query present
    exact (compile_correct _ _ _ _ _ _).1 (all _ (List.mem_map.2 ⟨query, present, rfl⟩))
  · intro all choice member
    obtain ⟨query, present, equal⟩ := List.mem_map.1 member
    subst choice
    exact (compile_correct _ _ _ _ _ _).2 (all query present)

def compileOverloads [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (schemes : List (List (Query V P Q C S Context typeArity valueArity))) :
    List (Problem Empty Q C (Request Context V U Q C S typeArity valueArity) typeArity) :=
  schemes.flatMap fun queries => (compileJoint declarations queries).map close

/-- One existential witness is shared by every position in one alternative.
Alternatives stay a disjunction; neither declarations nor witnesses generate
additional answers or commit before pending value checks are known. -/
theorem compileOverloads_correct [DecidableEq P]
    (declarations : DeclarationTyping.Declarations Context U P Q C S typeArity valueArity)
    (schemes : List (List (Query V P Q C S Context typeArity valueArity)))
    (values : V → Tree S valueArity) :
    alternativesModel (compileOverloads declarations schemes) (model declarations values) Empty.elim ↔
      ∃ queries ∈ schemes, ∃ parameters : P → Closed Q C typeArity,
        ∀ query ∈ queries, DeclarationTyping.HasType declarations query.context
          (query.value.evaluate values) (query.type.substitute parameters) := by
  constructor
  · rintro ⟨problem, present, solved⟩
    obtain ⟨queries, declared, mapped⟩ := List.mem_flatMap.1 present
    obtain ⟨joint, jointPresent, equal⟩ := List.mem_map.1 mapped
    subst problem
    obtain ⟨parameters, jointModel⟩ := (models_close _ _).1 solved
    exact ⟨queries, declared, parameters, (compileJoint_correct _ _ _ _).1 ⟨joint, jointPresent, jointModel⟩⟩
  · rintro ⟨queries, declared, parameters, all⟩
    obtain ⟨joint, jointPresent, solved⟩ := (compileJoint_correct _ _ _ _).2 all
    refine ⟨_, List.mem_flatMap.2 ⟨queries, declared, List.mem_map.2 ⟨joint, jointPresent, rfl⟩⟩, ?_⟩
    exact (models_close _ _).2 ⟨parameters, solved⟩

end Mettapedia.Logic.ConstraintTypes.OpenTyping
