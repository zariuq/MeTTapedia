import Mettapedia.OSLF.MeTTaIL.CanonicalRenaming
import Mettapedia.GSLT.LanguageDef.BindingSignatureWire
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.GSLT.LanguageDef.NamedFreeContext
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaTyping
import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.OSLF.MeTTaIL.BindingAgreement
import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.Syntax.VariableArgumentRecognition
import Mettapedia.OSLF.Syntax.BoundPrefixProjection
import Mettapedia.GSLT.LanguageDef.TypedPartialSpineRecovery
import Mettapedia.OSLF.Syntax.ScopedMatching
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.Syntax.ContextualRootEvents
import Mettapedia.OSLF.Syntax.ScopedBindingEquationEvents
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Dependency contexts in declaration-derived binding syntax

This module reads constructor scopes from `BindingSyntax.signatureOf` and
metavariable dependencies from the original rule's `RuleBindingSpec`.
The target is the existing intrinsically sorted `Term`/`Args` family.
Simultaneous substitution is compared with the existing raw context action,
including its lifts beneath constructor binders.

This is a term and occurrence elaboration boundary. It does not erase rule
premises or assert a conditional operational-presentation equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef}

/-- The raw assignment agrees with every typed variable image. Positions
outside the source context are deliberately unconstrained. -/
def ReadsSub {bound target : List TypeExpr}
    (sigma : Sub (signatureOf language) bound target)
    (assignment : Assignment) : Prop :=
  ∀ sort (position : Var bound sort),
    assignment (variableIndex position) = erase (sigma sort position)

theorem readsSub_lift {bound target : List TypeExpr}
    (sigma : Sub (signatureOf language) bound target)
    (assignment : Assignment) (reads : ReadsSub sigma assignment) :
    ∀ binders, ReadsSub (liftSub sigma binders) (lift binders.length assignment)
  | [] => by simpa only [List.length_nil, lift_zero, liftSub] using reads
  | binder :: binders => by
      intro sort position
      cases position with
      | zero =>
          change lift (binder :: binders).length assignment 0 = Pattern.bvar 0
          simp [lift]
      | succ old =>
          have inner := readsSub_lift sigma assignment reads binders sort old
          rw [show (binder :: binders).length = binders.length + 1 by rfl,
            ← lift_lift 1 binders.length assignment]
          change Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 1
              (lift binders.length assignment (variableIndex old)) =
            erase (weaken (liftSub sigma binders sort old))
          rw [inner, erase_weaken]

theorem parameterScope_substitute
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType)
    (assignment : Assignment) (body : Pattern) :
    substitute assignment (scope.wrap body) =
      scope.wrap (substitute (lift binders.length assignment) body) := by
  cases scope <;> simp [ParameterScope.wrap, substitute, lift_zero]

mutual
/-- Declaration-derived erasure commutes with the actual simultaneous
context substitution, including every declared binder prefix. -/
theorem erase_bind {bound target : List TypeExpr}
    (sigma : Sub (signatureOf language) bound target)
    (assignment : Assignment) (reads : ReadsSub sigma assignment) :
    ∀ {sort : TypeExpr} (term : Term (signatureOf language) bound sort),
      erase (bind sigma term) = substitute assignment (erase term)
  | _, .var position => (reads _ position).symm
  | _, .op (.constructor rule _ _ scopes) arguments => by
      change Pattern.apply rule.label
        (eraseConstructorArguments scopes (bindArgs sigma arguments)) = _
      rw [eraseConstructorArguments_bind sigma assignment reads scopes arguments]
      rfl
  | _, .op (.collectionConstructor _ _ _ kind _ _ _) arguments => by
      change Pattern.collection kind (eraseArguments (bindArgs sigma arguments)) none = _
      rw [eraseArguments_bind sigma assignment reads arguments
        (by intro slot member; exact congrArg Prod.fst (List.eq_of_mem_replicate member))]
      rfl
  | _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.lambda none (erase (bind (liftSub sigma [_]) body)) = _
          rw [erase_bind (liftSub sigma [_]) (lift 1 assignment)
            (readsSub_lift sigma assignment reads [_]) body]
          rfl
  | _, .op (.multiLambda _ _ count) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.multiLambda count [] (erase (bind (liftSub sigma _) body)) = _
          rw [erase_bind (liftSub sigma _) (lift count assignment)
            (by simpa using readsSub_lift sigma assignment reads (List.replicate count _)) body]
          rfl
  | _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          change Pattern.subst (erase (bind (liftSub sigma [_]) body))
            (erase (bind sigma replacement)) = _
          rw [erase_bind (liftSub sigma [_]) (lift 1 assignment)
              (readsSub_lift sigma assignment reads [_]) body,
            erase_bind sigma assignment reads replacement]
          rfl
  | _, .op (.collection kind _ _) arguments => by
      change Pattern.collection kind (eraseArguments (bindArgs sigma arguments)) none = _
      rw [eraseArguments_bind sigma assignment reads arguments
        (by intro slot member; exact congrArg Prod.fst (List.eq_of_mem_replicate member))]
      rfl
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

/-- Nonbinding argument rows preserve their order under the same action. -/
theorem eraseArguments_bind {bound target : List TypeExpr}
    (sigma : Sub (signatureOf language) bound target)
    (assignment : Assignment) (reads : ReadsSub sigma assignment) :
    ∀ {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf language) arity bound),
      (∀ slot ∈ arity, slot.1 = []) →
      eraseArguments (bindArgs sigma arguments) =
        substituteList assignment (eraseArguments arguments)
  | _, .nil, _ => rfl
  | (binders, _) :: _, .cons head tail, nonbinding => by
      have empty : binders = [] := nonbinding _ List.mem_cons_self
      have liftedReads : ReadsSub (liftSub sigma binders) assignment := by
        subst binders
        exact reads
      change erase (bind (liftSub sigma binders) head) ::
        eraseArguments (bindArgs sigma tail) = _
      rw [erase_bind (liftSub sigma binders) assignment liftedReads head,
        eraseArguments_bind sigma assignment reads tail
          (fun slot member => nonbinding slot (List.mem_cons_of_mem _ member))]
      rfl
termination_by _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

/-- Constructor argument readback retains each representation wrapper while
lifting the substitution by that argument's declared dependency prefix. -/
theorem eraseConstructorArguments_bind {bound target : List TypeExpr}
    (sigma : Sub (signatureOf language) bound target)
    (assignment : Assignment) (reads : ReadsSub sigma assignment) :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      eraseConstructorArguments scopes (bindArgs sigma arguments) =
        substituteList assignment (eraseConstructorArguments scopes arguments)
  | _, _, .nil, .nil => rfl
  | _, _, .cons (binders := binders) scope scopes, .cons head tail => by
      change scope.wrap (erase (bind (liftSub sigma binders) head)) ::
        eraseConstructorArguments scopes (bindArgs sigma tail) = _
      rw [erase_bind (liftSub sigma binders) (lift binders.length assignment)
          (readsSub_lift sigma assignment reads binders) head,
        eraseConstructorArguments_bind sigma assignment reads scopes tail]
      rw [← parameterScope_substitute]
      rfl
termination_by _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

/-- Metavariable arities are computed in the original type-context order.
The checked compiler below rejects missing or duplicate dependency rows. -/
def metaArities (rule : RewriteRule) (spec : RuleBindingSpec) :
    List (MetaArity (signatureOf language)) :=
  rule.typeContext.map fun entry =>
    ((dependencies? spec entry.1).getD [], entry.2)

/-- Structural source admission precedes adjoining the computed arities to
the existing constructor signature. Premises remain on the original rule. -/
def compileMetaArities? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) : Option (List (MetaArity (signatureOf language))) :=
  if decide (rule.bindings = some spec) && admittedFor rule spec &&
      dependencySortsDeclared language spec then
    some (metaArities rule spec) else none

theorem compileMetaArities?_admitted {rule : RewriteRule} {spec : RuleBindingSpec}
    {arities : List (MetaArity (signatureOf language))}
    (compiled : compileMetaArities? language rule spec = some arities) :
    rule.bindings = some spec ∧ admittedFor rule spec = true ∧
      dependencySortsDeclared language spec = true ∧
      arities = metaArities rule spec := by
  unfold compileMetaArities? at compiled
  split at compiled
  · rename_i admitted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact ⟨admitted.1.1, admitted.1.2, admitted.2,
      (Option.some.inj compiled).symm⟩
  · contradiction

@[simp] theorem metaArities_length (rule : RewriteRule) (spec : RuleBindingSpec) :
    (metaArities (language := language) rule spec).length = rule.typeContext.length := by
  simp [metaArities]

/-- One actual declaration position, with its computed dependency prefix. -/
def metaIndex (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin rule.typeContext.length) :
    Fin (metaArities (language := language) rule spec).length :=
  ⟨index.val, by simpa only [metaArities_length] using index.isLt⟩

theorem metaArities_get (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin rule.typeContext.length) :
    (metaArities (language := language) rule spec).get (metaIndex rule spec index) =
      ((dependencies? spec (rule.typeContext.get index).1).getD [],
        (rule.typeContext.get index).2) := by
  simp [metaArities, metaIndex, List.get_eq_getElem]

private theorem filter_name_unique (rows : List (String × List TypeExpr))
    (unique : (rows.map Prod.fst).Nodup) (name : String) (sorts : List TypeExpr)
    (member : (name, sorts) ∈ rows) :
    rows.filter (fun row => row.1 == name) = [(name, sorts)] := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with equal | later
      · subst head
        have absent : tail.filter (fun row => row.1 == name) = [] := by
          rw [List.filter_eq_nil_iff]
          intro row inTail matching
          apply unique.1
          exact List.mem_map.mpr ⟨row, inTail, by simpa only [beq_iff_eq] using matching⟩
        simp [absent]
      · have unequal : head.1 ≠ name := by
          intro equal
          apply unique.1
          rw [equal]
          exact List.mem_map.mpr ⟨(name, sorts), later, rfl⟩
        simpa [unequal] using ih unique.2 later

/-- Every source result declaration has one genuine dependency row after
admission. Thus the arity computation's total fallback is unreachable. -/
theorem admitted_dependencies {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true) :
    ∀ entry ∈ rule.typeContext, ∃ sorts, dependencies? spec entry.1 = some sorts := by
  simp only [admittedFor, Bool.and_eq_true, decide_eq_true_eq] at admitted
  have unique : (spec.dependencies.map Prod.fst).Nodup := admitted.1.1.1.1.2
  intro entry member
  have covered := List.all_eq_true.mp admitted.1.2 entry member
  obtain ⟨row, inRows, matching⟩ := List.any_eq_true.mp covered
  have named : row.1 = entry.1 := by simpa only [beq_iff_eq] using matching
  refine ⟨row.2, ?_⟩
  have rowMember : (entry.1, row.2) ∈ spec.dependencies := by
    simpa only [← named, Prod.mk.eta] using inRows
  simp only [dependencies?, filter_name_unique spec.dependencies unique entry.1 row.2 rowMember]

theorem admitted_metaArities_get {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true) (index : Fin rule.typeContext.length) :
    ∃ sorts, dependencies? spec (rule.typeContext.get index).1 = some sorts ∧
      (metaArities (language := language) rule spec).get (metaIndex rule spec index) =
        (sorts, (rule.typeContext.get index).2) := by
  obtain ⟨sorts, declared⟩ := admitted_dependencies admitted _ (List.get_mem _ _)
  exact ⟨sorts, declared, by rw [metaArities_get, declared]; rfl⟩

/-- The dependencies supplied to an occurrence are ordinary typed terms,
not an untyped list accepted merely because its length matching. -/
abbrev DependencyArguments (dependencies bound : List TypeExpr) :=
  Args (signatureOf language) (dependencies.map fun sort => ([], sort)) bound

@[simp] theorem eraseDependencyArguments_length :
    ∀ {dependencies bound : List TypeExpr}
      (arguments : DependencyArguments (language := language) dependencies bound),
      (eraseArguments arguments).length = dependencies.length
  | [], _, .nil => rfl
  | _ :: dependencies, _, .cons _ tail => by
      simpa only [eraseArguments, List.length_cons] using
        congrArg Nat.succ (eraseDependencyArguments_length tail)

/-- Each dependency receives exactly the source-declared sort at the same
position; repetition or permutation is not silently normalized. -/
theorem dependency_arguments_typed {dependencies bound : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies bound) :
    List.Forall₂ (HasType language FreeTypeContext.empty bound)
      (eraseArguments arguments) dependencies := by
  induction dependencies with
  | nil => cases arguments; exact .nil
  | cons sort dependencies ih =>
      cases arguments with
      | cons head tail => exact .cons (erase_typed head) (ih tail)

theorem variableIndex_lt : ∀ {bound : List TypeExpr} {sort : TypeExpr}
    (position : Var bound sort), variableIndex position < bound.length
  | _ :: _, _, .zero => by simp [variableIndex]
  | _ :: _, _, .succ position => by
      simpa only [variableIndex, List.length_cons, Nat.add_lt_add_iff_right] using
        variableIndex_lt position

theorem variableIndex_weakenVar {bound : List TypeExpr} {sort : TypeExpr}
    (position : Var bound sort) : ∀ binders,
    variableIndex (weakenVar (S := signatureOf language) binders position) =
      binders.length + variableIndex position
  | [] => by simp [weakenVar]
  | _ :: binders => by
      simp only [weakenVar, variableIndex, variableIndex_weakenVar position binders,
        List.length_cons]
      omega

private theorem occurrenceAssignment_succ (dependencies depth index : Nat)
    (head : Pattern) (tail : List Pattern) :
    occurrenceAssignment (dependencies + 1) depth (head :: tail) (index + 1) =
      occurrenceAssignment dependencies depth tail index := by
  by_cases before : index < dependencies
  · have before' : index + 1 < dependencies + 1 := by omega
    simp [occurrenceAssignment, before, before']
  · have before' : ¬ index + 1 < dependencies + 1 := by omega
    simp [occurrenceAssignment, before, before']

/-- The intrinsic occurrence supplies declared dependencies first and
retains the ambient suffix below exactly the occurrence's local binders. -/
def occurrenceSubstitution {dependencies locals ambient : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies (locals ++ ambient)) :
    Sub (signatureOf language) (dependencies ++ ambient) (locals ++ ambient) :=
  ContextualAssignment.joinSub (argsToSub arguments)
    (fun sort (position : Var ambient sort) =>
      .var (weakenVar (S := signatureOf language) locals position))

theorem occurrenceSubstitution_reads {locals ambient : List TypeExpr} :
    ∀ {dependencies : List TypeExpr}
      (arguments : DependencyArguments (language := language) dependencies (locals ++ ambient)),
      ReadsSub (occurrenceSubstitution arguments)
        (occurrenceAssignment dependencies.length locals.length (eraseArguments arguments))
  | [], .nil => by
      intro sort position
      simp only [occurrenceSubstitution, occurrenceAssignment, ContextualAssignment.joinSub,
        List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero, erase]
      exact congrArg Pattern.bvar (variableIndex_weakenVar position locals).symm
  | _ :: _, .cons head tail => by
      intro sort position
      cases position with
      | zero =>
          simp [occurrenceSubstitution, occurrenceAssignment, variableIndex,
            eraseArguments, ContextualAssignment.joinSub, argsToSub]
      | succ position =>
          change occurrenceAssignment (_ + 1) locals.length
              (erase head :: eraseArguments tail) (variableIndex position + 1) = _
          rw [occurrenceAssignment_succ]
          exact occurrenceSubstitution_reads tail sort position

theorem dependency_arguments_scoped {dependencies bound : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies bound) :
    (eraseArguments arguments).all (fun pattern => pattern.isWellScopedAt bound.length) = true := by
  induction dependencies with
  | nil => cases arguments; rfl
  | cons sort dependencies ih =>
      cases arguments with
      | cons head tail =>
          simpa only [eraseArguments, List.all_cons, Bool.and_eq_true, List.nil_append] using
            And.intro (erase_wellScoped head) (ih tail)

/-- A typed contextual value has the exact raw dependency and ambient
indices consumed by the existing scoped rule interpreter. -/
def contextualValue {dependencies ambient : List TypeExpr} {sort : TypeExpr}
    (body : Term (signatureOf language) (dependencies ++ ambient) sort) : ContextualValue where
  dependencies := dependencies
  ambient := ambient.length
  body := erase body

/-- The existing executable occurrence action equals sorted substitution
for every typed body and typed dependency spine, including ambient-open
zero-argument metavariables. No untyped arity-only acceptance is assumed. -/
theorem instantiateValue?_typed {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (body : Term (signatureOf language) (dependencies ++ ambient) sort)
    (arguments : DependencyArguments (language := language) dependencies (locals ++ ambient)) :
    instantiateValue? (contextualValue body) ambient.length locals.length
        (eraseArguments arguments) =
      some (erase (bind (occurrenceSubstitution arguments) body)) := by
  have sourceScoped := erase_wellScoped body
  have argumentScoped := dependency_arguments_scoped arguments
  have resultScoped := erase_wellScoped (bind (occurrenceSubstitution arguments) body)
  have reads := occurrenceSubstitution_reads arguments
  have action := erase_bind (occurrenceSubstitution arguments) _ reads body
  simp only [List.length_append] at sourceScoped argumentScoped resultScoped
  unfold instantiateValue? contextualValue
  simp only [Bool.not_true, eraseDependencyArguments_length,
    sourceScoped, argumentScoped, Bool.false_eq_true, if_false]
  rw [← action]
  simp [resultScoped]

/-- Reflection recovers the exact sorted result from a successful raw
occurrence action; acceptance does not permit an additional raw result. -/
theorem instantiateValue?_typed_iff {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (body : Term (signatureOf language) (dependencies ++ ambient) sort)
    (arguments : DependencyArguments (language := language) dependencies (locals ++ ambient))
    (result : Pattern) :
    instantiateValue? (contextualValue body) ambient.length locals.length
        (eraseArguments arguments) = some result ↔
      result = erase (bind (occurrenceSubstitution arguments) body) := by
  rw [instantiateValue?_typed, Option.some.injEq]
  exact eq_comm

/-- Compute an intrinsically sorted position from an actual de Bruijn
index. A same-length context with the wrong sort does not supply a position. -/
def boundPosition? : (bound : List TypeExpr) → (index : Nat) → (sort : TypeExpr) →
    Option (Var bound sort)
  | [], _, _ => none
  | first :: rest, 0, sort =>
      if same : first = sort then
        some (Eq.mp (congrArg (Var (first :: rest)) same) Var.zero)
      else none
  | _ :: rest, index + 1, sort => (boundPosition? rest index sort).map Var.succ

theorem boundPosition?_index : ∀ (bound : List TypeExpr) (index : Nat) (sort : TypeExpr)
    {position : Var bound sort}, boundPosition? bound index sort = some position →
      variableIndex position = index
  | [], _, _, _, accepted => by simp [boundPosition?] at accepted
  | first :: rest, 0, sort, position, accepted => by
      by_cases same : first = sort
      · subst sort
        simp [boundPosition?] at accepted
        subst position
        rfl
      · simp [boundPosition?, same] at accepted
  | _ :: rest, index + 1, sort, position, accepted => by
      cases found : boundPosition? rest index sort with
      | none => simp [boundPosition?, found] at accepted
      | some earlier =>
          simp only [boundPosition?, found, Option.map_some, Option.some.injEq] at accepted
          subst position
          exact congrArg Nat.succ (boundPosition?_index rest index sort found)

/-- Every typed context position is recovered at its actual index. -/
theorem boundPosition?_complete : ∀ {bound : List TypeExpr} {sort : TypeExpr}
    (position : Var bound sort),
    boundPosition? bound (variableIndex position) sort = some position
  | _, _, .zero => by simp [boundPosition?, variableIndex]
  | _, _, .succ position => by
      simp [boundPosition?, variableIndex, boundPosition?_complete position]

/-- Elaborate the variable-spine fragment in declared dependency order.
Every supplied term is checked at its dependency sort and context position. -/
def elaborateVariableArguments? (language : LanguageDef) (bound : List TypeExpr) :
    (patterns : List Pattern) → (dependencies : List TypeExpr) →
      Option (DependencyArguments (language := language) dependencies bound)
  | [], [] => some .nil
  | .bvar index :: patterns, sort :: dependencies => do
      let position ← boundPosition? bound index sort
      let rest ← elaborateVariableArguments? (language := language) bound patterns dependencies
      pure (.cons (.var position) rest)
  | _, _ => none

/-- Successful elaboration reflects the complete, ordered raw spine. -/
theorem elaborateVariableArguments?_readback (bound : List TypeExpr) :
    ∀ (patterns : List Pattern) (dependencies : List TypeExpr)
      {arguments : DependencyArguments (language := language) dependencies bound},
      elaborateVariableArguments? (language := language) bound patterns dependencies = some arguments →
        eraseArguments arguments = patterns := by
  intro patterns
  induction patterns with
  | nil =>
      intro dependencies arguments accepted
      cases dependencies with
      | nil =>
          simp only [elaborateVariableArguments?, Option.some.injEq] at accepted
          subst arguments
          rfl
      | cons sort rest => simp [elaborateVariableArguments?] at accepted
  | cons pattern patterns ih =>
      intro dependencies arguments accepted
      cases dependencies with
      | nil => simp [elaborateVariableArguments?] at accepted
      | cons sort dependencies =>
          cases pattern <;> try (simp only [elaborateVariableArguments?] at accepted; contradiction)
          rename_i index
          cases head : boundPosition? bound index sort with
          | none => simp [elaborateVariableArguments?, head] at accepted
          | some position =>
              cases tail : elaborateVariableArguments? (language := language) bound patterns dependencies with
              | none => simp [elaborateVariableArguments?, head, tail] at accepted
              | some rest =>
                  simp [elaborateVariableArguments?, head, tail] at accepted
                  subst arguments
                  simp only [eraseArguments, erase, boundPosition?_index bound index sort head,
                    ih dependencies tail]

/-- Intrinsic evidence delimiting exactly the codec's variable-spine
fragment. The term and argument carriers remain the existing ones. -/
inductive VariableArguments : {dependencies bound : List TypeExpr} →
    DependencyArguments (language := language) dependencies bound → Prop where
  | nil {bound : List TypeExpr} : VariableArguments (dependencies := [])
      (Args.nil (S := signatureOf language) (Γ := bound))
  | cons {dependencies bound : List TypeExpr} {sort : TypeExpr}
      (position : Var bound sort)
      {tail : DependencyArguments (language := language) dependencies bound} :
      VariableArguments tail → VariableArguments (dependencies := sort :: dependencies) (.cons (.var position) tail)

theorem elaborateVariableArguments?_complete {dependencies bound : List TypeExpr}
    {arguments : DependencyArguments (language := language) dependencies bound}
    (supported : VariableArguments arguments) :
    elaborateVariableArguments? (language := language) bound (eraseArguments arguments) dependencies = some arguments := by
  induction supported with
  | nil => rfl
  | cons position supported ih =>
      simp [eraseArguments, erase, elaborateVariableArguments?,
        boundPosition?_complete position, ih]

theorem elaborateVariableArguments?_supported (bound : List TypeExpr) :
    ∀ (patterns : List Pattern) (dependencies : List TypeExpr)
      {arguments : DependencyArguments (language := language) dependencies bound},
      elaborateVariableArguments? (language := language) bound patterns dependencies = some arguments →
        VariableArguments arguments := by
  intro patterns
  induction patterns with
  | nil =>
      intro dependencies arguments accepted
      cases dependencies with
      | nil =>
          simp only [elaborateVariableArguments?, Option.some.injEq] at accepted
          subst arguments
          exact .nil
      | cons sort rest => simp [elaborateVariableArguments?] at accepted
  | cons pattern patterns ih =>
      intro dependencies arguments accepted
      cases dependencies with
      | nil => simp [elaborateVariableArguments?] at accepted
      | cons sort dependencies =>
          cases pattern <;> try (simp only [elaborateVariableArguments?] at accepted; contradiction)
          rename_i index
          cases head : boundPosition? bound index sort with
          | none => simp [elaborateVariableArguments?, head] at accepted
          | some position =>
              cases tail : elaborateVariableArguments? (language := language) bound patterns dependencies with
              | none => simp [elaborateVariableArguments?, head, tail] at accepted
              | some rest =>
                  simp [elaborateVariableArguments?, head, tail] at accepted
                  subst arguments
                  exact .cons position (ih dependencies tail)

/-- The codec admits exactly variable-only typed spines with this exact
readback. This is a two-sided fragment theorem, not a new typing judgment. -/
theorem elaborateVariableArguments?_iff (bound : List TypeExpr)
    (patterns : List Pattern) (dependencies : List TypeExpr)
    (arguments : DependencyArguments (language := language) dependencies bound) :
    elaborateVariableArguments? (language := language) bound patterns dependencies = some arguments ↔
      VariableArguments arguments ∧ eraseArguments arguments = patterns := by
  constructor
  · intro accepted
    exact ⟨elaborateVariableArguments?_supported bound patterns dependencies accepted,
      elaborateVariableArguments?_readback bound patterns dependencies accepted⟩
  · rintro ⟨supported, rfl⟩
    exact elaborateVariableArguments?_complete supported

/-- A compiled occurrence retains its actual source declaration position,
requested result sort, exact dependency context, and original site/path. -/
structure CompiledOccurrence (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) where
  index : Fin rule.typeContext.length
  named : (rule.typeContext.get index).1 = name
  sorted : (rule.typeContext.get index).2 = sort
  declared : dependencies? spec name =
    some ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1
  arguments : DependencyArguments (language := language)
    ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1 bound
  source : arguments? rule spec name site path = some (eraseArguments arguments)

namespace CompiledOccurrence

variable {rule : RewriteRule} {spec : RuleBindingSpec} {bound : List TypeExpr}
  {site : RulePatternSite} {path : List Nat} {name : String} {sort : TypeExpr}

theorem result_sort (compiled : CompiledOccurrence language rule spec bound site path name sort) :
    ((metaArities (language := language) rule spec).get
      (metaIndex rule spec compiled.index)).2 = sort := by
  rw [metaArities_get]
  exact compiled.sorted

/-- Adjoin the source-selected metavariable as the existing typed operator,
passing the elaborated dependency terms in their retained order. -/
def schemaTerm (compiled : CompiledOccurrence language rule spec bound site path name sort) :
    Term (withMetas (signatureOf language) (metaArities rule spec)) bound
      ((metaArities (language := language) rule spec).get
        (metaIndex rule spec compiled.index)).2 :=
  Term.op (Sum.inr (MetaOp.mk (metaIndex rule spec compiled.index)))
    (embedArgs compiled.arguments)

def term (compiled : CompiledOccurrence language rule spec bound site path name sort) :
    Term (withMetas (signatureOf language) (metaArities rule spec)) bound sort :=
  compiled.result_sort ▸ compiled.schemaTerm

theorem instantiate_schemaTerm {ambient : List TypeExpr}
    (compiled : CompiledOccurrence language rule spec bound site path name sort)
    (bodies : ContextualAssignment (signatureOf language) (metaArities rule spec) ambient)
    (ambientSub : Sub (signatureOf language) ambient bound) :
    ContextualAssignment.instantiate bodies ambientSub (fun _ position => .var position)
        compiled.schemaTerm =
      ContextualAssignment.apply bodies (metaIndex rule spec compiled.index)
        (argsToSub compiled.arguments) ambientSub := by
  simp only [schemaTerm, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs_embedArgs, bindArgs_id]

/-- The compiled head, its authored occurrence substitution, and the
existing raw occurrence interpreter yield precisely the same result. -/
theorem instantiate_schemaTerm_readback {locals ambient : List TypeExpr}
    (compiled : CompiledOccurrence language rule spec (locals ++ ambient) site path name sort)
    (bodies : ContextualAssignment (signatureOf language) (metaArities rule spec) ambient) :
    instantiateValue? (contextualValue (bodies (metaIndex rule spec compiled.index)))
        ambient.length locals.length (eraseArguments compiled.arguments) =
      some (erase (ContextualAssignment.instantiate bodies
        (fun _ position => .var (weakenVar (S := signatureOf language) locals position))
        (fun _ position => .var position) compiled.schemaTerm)) := by
  rw [instantiate_schemaTerm]
  exact instantiateValue?_typed _ compiled.arguments

/-- A named runtime assignment is only an external argument here. Given
the same retained typed body, the actual source traversal reflects the
compiled occurrence; no matching adequacy is inferred from name lookup. -/
theorem source_occurrence_readback {locals ambient : List TypeExpr}
    (compiled : CompiledOccurrence language rule spec (locals ++ ambient) site path name sort)
    (bodies : ContextualAssignment (signatureOf language) (metaArities rule spec) ambient)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (captured : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment name =
      some (contextualValue (bodies (metaIndex rule spec compiled.index)))) :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiateAt? rule spec
        ambient.length site path locals.length assignment (.fvar name) =
      some (erase (ContextualAssignment.instantiate bodies
        (fun _ position => .var (weakenVar (S := signatureOf language) locals position))
        (fun _ position => .var position) compiled.schemaTerm)) := by
  simp only [Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiateAt?,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiateWith?, captured,
    compiled.source]
  exact compiled.instantiate_schemaTerm_readback bodies

/-- The retained source occurrence also reflects every returned raw result,
at the same site, path, binder depth, and captured contextual value. -/
theorem source_occurrence_readback_iff {locals ambient : List TypeExpr}
    (compiled : CompiledOccurrence language rule spec (locals ++ ambient) site path name sort)
    (bodies : ContextualAssignment (signatureOf language) (metaArities rule spec) ambient)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (captured : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment name =
      some (contextualValue (bodies (metaIndex rule spec compiled.index))))
    (result : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiateAt? rule spec
        ambient.length site path locals.length assignment (.fvar name) = some result ↔
      result = erase (ContextualAssignment.instantiate bodies
        (fun _ position => .var (weakenVar (S := signatureOf language) locals position))
        (fun _ position => .var position) compiled.schemaTerm) := by
  rw [compiled.source_occurrence_readback bodies assignment captured, Option.some.injEq]
  exact eq_comm

end CompiledOccurrence

def occurrenceCandidate? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr)
    (index : Fin rule.typeContext.length) :
    Option (CompiledOccurrence language rule spec bound site path name sort) :=
  if named : (rule.typeContext.get index).1 = name then
    if sorted : (rule.typeContext.get index).2 = sort then
      if declared : dependencies? spec name =
          some ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1 then
        match source : arguments? rule spec name site path with
        | none => none
        | some patterns =>
            match elaborated : elaborateVariableArguments? (language := language) bound patterns
                ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1 with
            | none => none
            | some arguments => some ⟨index, named, sorted, declared, arguments,
                by rw [source, elaborateVariableArguments?_readback bound _ _ elaborated]⟩
      else none
    else none
  else none

/-- Search original declaration positions only after source binding
admission. The executable first fragment requires variable spines; the
typed substitution theorem above also covers general dependency terms. -/
def elaborateOccurrence? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    Option (CompiledOccurrence language rule spec bound site path name sort) :=
  if decide (rule.bindings = some spec) && admittedFor rule spec &&
      dependencySortsDeclared language spec then
    (List.finRange rule.typeContext.length).findSome?
      (occurrenceCandidate? language rule spec bound site path name sort)
  else none

theorem elaborateOccurrence?_admitted {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    {compiled : CompiledOccurrence language rule spec bound site path name sort}
    (accepted : elaborateOccurrence? language rule spec bound site path name sort = some compiled) :
    rule.bindings = some spec ∧ admittedFor rule spec = true ∧
      dependencySortsDeclared language spec = true := by
  unfold elaborateOccurrence? at accepted
  split at accepted
  · rename_i admitted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact ⟨admitted.1.1, admitted.1.2, admitted.2⟩
  · contradiction

theorem occurrenceCandidate?_supported {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr} (index : Fin rule.typeContext.length)
    {compiled : CompiledOccurrence language rule spec bound site path name sort}
    (accepted : occurrenceCandidate? language rule spec bound site path name sort index =
      some compiled) : VariableArguments compiled.arguments := by
  unfold occurrenceCandidate? at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted
  · contradiction
  · rename_i patterns source
    split at accepted
    · contradiction
    · rename_i arguments elaborated
      cases Option.some.inj accepted
      exact elaborateVariableArguments?_supported bound patterns _ elaborated

theorem occurrenceCandidate?_complete {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (compiled : CompiledOccurrence language rule spec bound site path name sort)
    (supported : VariableArguments compiled.arguments) :
    occurrenceCandidate? language rule spec bound site path name sort compiled.index =
      some compiled := by
  rcases compiled with ⟨index, named, sorted, declared, arguments, source⟩
  unfold occurrenceCandidate?
  rw [dif_pos named, dif_pos sorted, dif_pos declared]
  dsimp only
  split
  · rename_i absent
    rw [absent] at source
    contradiction
  · rename_i patterns found
    have readback : patterns = eraseArguments arguments := Option.some.inj (found.symm.trans source)
    subst patterns
    split
    · rename_i absent
      have complete := elaborateVariableArguments?_complete supported
      rw [absent] at complete
      contradiction
    · rename_i returned foundArguments
      have equal : returned = arguments :=
        Option.some.inj (foundArguments.symm.trans (elaborateVariableArguments?_complete supported))
      subst returned
      rfl

private theorem findSome?_property {α β : Type} (items : List α)
    (candidate : α → Option β) (property : β → Prop)
    (sound : ∀ item result, candidate item = some result → property result) :
    ∀ {result}, items.findSome? candidate = some result → property result := by
  induction items with
  | nil => intro result accepted; simp [List.findSome?] at accepted
  | cons item items ih =>
      intro result accepted
      cases found : candidate item with
      | none => exact ih (by simpa only [List.findSome?, found] using accepted)
      | some value =>
          have equal : value = result := by
            simpa only [List.findSome?, found, Option.some.injEq] using accepted
          subst result
          exact sound item value found

private theorem findSome?_complete {α β : Type} (items : List α)
    (candidate : α → Option β) (item : α) (member : item ∈ items)
    (result : β) (accepted : candidate item = some result) :
    (items.findSome? candidate).isSome = true := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      cases found : candidate first with
      | some value => simp [List.findSome?, found]
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · rw [found] at accepted; contradiction
          · simpa only [List.findSome?, found] using ih later

theorem elaborateOccurrence?_supported {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    {compiled : CompiledOccurrence language rule spec bound site path name sort}
    (accepted : elaborateOccurrence? language rule spec bound site path name sort = some compiled) :
    VariableArguments compiled.arguments := by
  unfold elaborateOccurrence? at accepted
  split at accepted <;> try contradiction
  exact findSome?_property _ _ (fun result => VariableArguments result.arguments)
    (fun index _ found => occurrenceCandidate?_supported index found) accepted

theorem elaborateOccurrence?_complete {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (attached : rule.bindings = some spec) (admitted : admittedFor rule spec = true)
    (sortsDeclared : dependencySortsDeclared language spec = true)
    (compiled : CompiledOccurrence language rule spec bound site path name sort)
    (supported : VariableArguments compiled.arguments) :
    (elaborateOccurrence? language rule spec bound site path name sort).isSome = true := by
  simp only [elaborateOccurrence?, attached, decide_true, admitted, sortsDeclared,
    Bool.and_self, if_true]
  exact findSome?_complete _ _ compiled.index (List.mem_finRange _) compiled
    (occurrenceCandidate?_complete compiled supported)

/-- Source admission and a sorted variable-spine elaboration characterize
success exactly. Lookup order cannot manufacture an undeclared occurrence. -/
theorem elaborateOccurrence?_isSome_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (site : RulePatternSite) (path : List Nat)
    (name : String) (sort : TypeExpr) :
    (elaborateOccurrence? language rule spec bound site path name sort).isSome = true ↔
      rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        dependencySortsDeclared language spec = true ∧
        ∃ compiled : CompiledOccurrence language rule spec bound site path name sort,
          VariableArguments compiled.arguments := by
  constructor
  · intro present
    cases accepted : elaborateOccurrence? language rule spec bound site path name sort with
    | none => simp [accepted] at present
    | some compiled =>
        obtain ⟨attached, admitted, declared⟩ := elaborateOccurrence?_admitted accepted
        exact ⟨attached, admitted, declared, compiled, elaborateOccurrence?_supported accepted⟩
  · rintro ⟨attached, admitted, declared, compiled, supported⟩
    exact elaborateOccurrence?_complete attached admitted declared compiled supported

/-- Select the rule and its metadata from their physical positions in the
canonical `LanguageDef`. The occurrence receipt retains that same rule,
including all its premises; it is not a new operational rule. -/
abbrev AuthoredOccurrence (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :=
  (spec : RuleBindingSpec) ×
    CompiledOccurrence language (language.rewrites.get ruleIndex) spec bound site path name sort

def elaborateAuthoredOccurrence? (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    Option (AuthoredOccurrence language ruleIndex bound site path name sort) :=
  match (language.rewrites.get ruleIndex).bindings with
  | none => none
  | some spec =>
      (elaborateOccurrence? language (language.rewrites.get ruleIndex) spec
        bound site path name sort).map fun compiled => ⟨spec, compiled⟩

/-- The canonical source entry point succeeds exactly for attached,
source-admitted metadata and an intrinsically sorted variable-spine head. -/
theorem elaborateAuthoredOccurrence?_isSome_iff
    (ruleIndex : Fin language.rewrites.length) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    (elaborateAuthoredOccurrence? language ruleIndex bound site path name sort).isSome = true ↔
      ∃ spec, (language.rewrites.get ruleIndex).bindings = some spec ∧
        admittedFor (language.rewrites.get ruleIndex) spec = true ∧
        dependencySortsDeclared language spec = true ∧
        ∃ compiled : CompiledOccurrence language (language.rewrites.get ruleIndex) spec
            bound site path name sort,
          VariableArguments compiled.arguments := by
  cases attached : (language.rewrites.get ruleIndex).bindings with
  | none =>
      simp only [List.get_eq_getElem] at attached
      simp [elaborateAuthoredOccurrence?, List.get_eq_getElem, attached]
  | some spec =>
      simp only [elaborateAuthoredOccurrence?, attached, Option.isSome_map]
      rw [elaborateOccurrence?_isSome_iff]
      simp only [List.get_eq_getElem] at attached
      simp [List.get_eq_getElem, attached]

namespace InputRecovery

theorem variableIndex_injPrefix {bound ambient : List TypeExpr} {sort : TypeExpr}
    (position : Var bound sort) :
    variableIndex (injPrefix (S := signatureOf language) (Γ := ambient) bound position) =
      variableIndex position := by
  induction position with
  | zero => rfl
  | succ position ih => exact congrArg Nat.succ ih

/-- Adding the caller's ambient suffix preserves every local position and
all original constructor and binder metadata in the erased term. -/
theorem erase_appendAmbient {bound ambient : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) :
    erase (rename (fun _ position =>
      injPrefix (S := signatureOf language) (Γ := ambient) bound position) term) =
      erase term := by
  rw [← bind_var_eq_rename]
  rw [erase_bind _ Pattern.bvar (by
    intro sort position
    exact congrArg Pattern.bvar (variableIndex_injPrefix position).symm)]
  exact substitute_id _

def appendAmbientArguments {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (ambient : List TypeExpr) :
    DependencyArguments (language := language) dependencies (locals ++ ambient) :=
  renameArgs (fun _ position =>
    injPrefix (S := signatureOf language) (Γ := ambient) locals position) arguments

theorem appendAmbientArguments_erases {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (ambient : List TypeExpr) :
    eraseArguments (appendAmbientArguments arguments ambient) = eraseArguments arguments := by
  unfold appendAmbientArguments
  rw [← bindArgs_var_eq_renameArgs]
  rw [eraseArguments_bind _ Pattern.bvar (by
    intro sort position
    exact congrArg Pattern.bvar (variableIndex_injPrefix position).symm)
    arguments (by
      intro slot member
      obtain ⟨sort, _, rfl⟩ := List.mem_map.mp member
      rfl)]
  have identity : substitute Pattern.bvar = (id : Pattern → Pattern) :=
    funext substitute_id
  rw [substituteList_eq_map, identity, List.map_id]

/-- The existing sorted codec supplies local indices in dependency order. -/
theorem variable_arguments_indices {dependencies locals : List TypeExpr}
    {arguments : DependencyArguments (language := language) dependencies locals}
    (supported : ScopedElaboration.VariableArguments arguments) :
    ∃ indices : List Nat,
      eraseArguments arguments = indices.map Pattern.bvar ∧
      indices.length = dependencies.length ∧
      ∀ index ∈ indices, index < locals.length := by
  induction supported with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | @cons dependencies locals sort position tail supported ih =>
      obtain ⟨indices, readback, length, bounds⟩ := ih
      refine ⟨variableIndex position :: indices, ?_, ?_, ?_⟩
      · simp only [eraseArguments, erase, List.map_cons, readback]
      · simpa only [List.length_cons] using congrArg Nat.succ length
      · intro index member
        rcases List.mem_cons.mp member with rfl | later
        · exact variableIndex_lt position
        · exact bounds index later

private theorem variableSpine_bvars (depth : Nat) (indices : List Nat)
    (bounds : ∀ index ∈ indices, index < depth) :
    variableSpine? depth (indices.map Pattern.bvar) =
      if indices.Nodup then some indices else none := by
  have mapped : (indices.map Pattern.bvar).mapM (fun argument => match argument with
      | .bvar index => if index < depth then some index else none
      | _ => none) = some indices := by
    induction indices with
    | nil => rfl
    | cons index indices ih =>
        have bound := bounds index List.mem_cons_self
        have rest := ih (fun item member => bounds item (List.mem_cons_of_mem _ member))
        simp [bound, rest]
  unfold variableSpine?
  exact congrArg (fun result : Option (List Nat) =>
    result.bind (fun found => if found.Nodup then some found else none)) mapped

/-- Source codec evidence and the actual input-spine check earn numerical
injectivity; it is not an independently supplied permutation assumption. -/
theorem variable_spine_contract {dependencies locals : List TypeExpr}
    {arguments : DependencyArguments (language := language) dependencies locals}
    (supported : ScopedElaboration.VariableArguments arguments)
    (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices) :
    eraseArguments arguments = indices.map Pattern.bvar ∧
      indices.length = dependencies.length ∧ indices.Nodup ∧
      ∀ index ∈ indices, index < locals.length := by
  obtain ⟨found, readback, length, bounds⟩ := variable_arguments_indices supported
  rw [readback, variableSpine_bvars _ _ bounds] at checked
  split at checked <;> try contradiction
  cases Option.some.inj checked
  exact ⟨readback, length, by assumption, bounds⟩

/-- The actual inverse occurrence action undoes typed contextual
instantiation, including the independent ambient segment and nested binders. -/
theorem recovered_body_of_instance {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (supported : ScopedElaboration.VariableArguments arguments) (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices)
    (body : Term (signatureOf language) (dependencies ++ ambient) sort) :
    substitute (recoveryAssignment locals.length dependencies.length ambient.length indices)
        (erase (bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body)) =
      erase body := by
  obtain ⟨readback, length, unique, bounds⟩ := variable_spine_contract supported indices checked
  rw [erase_bind _ _ (occurrenceSubstitution_reads _), appendAmbientArguments_erases,
    readback, substitute_comp]
  have composed : (fun index => substitute
      (recoveryAssignment locals.length dependencies.length ambient.length indices)
      (occurrenceAssignment dependencies.length locals.length (indices.map Pattern.bvar) index)) =
      Pattern.bvar := by
    funext index
    exact Mettapedia.OSLF.MeTTaIL.CanonicalBags.raw_recovery_occurrence_identity
      _ _ _ indices length unique bounds index
  rw [composed, substitute_id]

/-- Preservation constructs recovery success from the typed contextual
body and the source-admitted injective spine; no capture-success premise is
used to obtain this equation. -/
theorem recoverValue?_typed_instance {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (supported : ScopedElaboration.VariableArguments arguments) (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices)
    (body : Term (signatureOf language) (dependencies ++ ambient) sort) :
    recoverValue? dependencies ambient.length locals.length (eraseArguments arguments)
        (erase (bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body)) =
      some (contextualValue body) := by
  have targetScoped := erase_wellScoped
    (bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body)
  have recoveredBody := recovered_body_of_instance arguments supported indices checked body
  have forward := instantiateValue?_typed body (appendAmbientArguments arguments ambient)
  rw [appendAmbientArguments_erases] at forward
  have length := (variable_spine_contract supported indices checked).2.1
  simp only [List.length_append] at targetScoped
  unfold recoverValue?
  simp only [Option.bind_eq_bind, targetScoped, Bool.not_true, Bool.false_eq_true, if_false,
    checked, Option.bind_some, length, bne_self_eq_false]
  change (if instantiateValue? ({
        dependencies := dependencies
        ambient := ambient.length
        body := substitute (recoveryAssignment locals.length dependencies.length ambient.length indices)
          (erase (bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body)) } : ContextualValue)
      ambient.length locals.length (eraseArguments arguments) ==
        some (erase (bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body)) then
      some _ else none) = _
  rw [recoveredBody]
  change (if instantiateValue? (contextualValue body) ambient.length locals.length
      (eraseArguments arguments) == some _ then some (contextualValue body) else none) = _
  simp only [forward, beq_self_eq_true, if_true]

private theorem sameVar_indices : ∀ {bound : List TypeExpr} {left right : TypeExpr}
    (first : Var bound left) (second : Var bound right),
    sameVar (S := signatureOf language) first second = true →
      variableIndex first = variableIndex second
  | _, _, _, .zero, .zero, _ => rfl
  | _, _, _, .zero, .succ _, compared => by cases compared
  | _, _, _, .succ _, .zero, compared => by cases compared
  | _, _, _, .succ first, .succ second, compared =>
      congrArg Nat.succ (sameVar_indices first second compared)

private theorem parameterScope_outerUse
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType)
    (body : Pattern) (index : Nat)
    (used : UsesOuterBound body (binders.length + index)) :
    UsesOuterBound (scope.wrap body) index := by
  cases scope with
  | simple => simpa only [ParameterScope.wrap, List.length_nil, Nat.zero_add] using used
  | abstraction | abstractionBase =>
      exact UsesOuterBound.lambda (by simpa only [List.length_singleton, Nat.add_comm] using used)
  | multiAbstraction | multiAbstractionBase =>
      exact UsesOuterBound.multiLambda (by
        simpa only [List.length_replicate, Nat.add_comm] using used)

mutual
/-- An intrinsic variable occurrence survives the declaration-derived
erasure at its exact outer position. Constructor binder wrappers are
accounted for rather than inferred from raw list lengths. -/
theorem countVar_positive_outerUse {bound : List TypeExpr} {variableSort : TypeExpr}
    (position : Var bound variableSort) :
    ∀ {sort : TypeExpr} (term : Term (signatureOf language) bound sort),
      0 < countVar position term → UsesOuterBound (erase term) (variableIndex position)
  | _, .var target, positive => by
      simp only [countVar] at positive
      have compared : sameVar (S := signatureOf language) position target = true := by
        cases compared : sameVar (S := signatureOf language) position target <;> simp_all
      rw [sameVar_indices position target compared]
      exact UsesOuterBound.bvar _
  | _, .op (.constructor rule _ _ scopes) arguments, positive => by
      obtain ⟨argument, member, used⟩ :=
        countVarConstructorArguments_positive_outerUse position scopes arguments positive
      exact UsesOuterBound.apply member used
  | _, .op (.collectionConstructor _ _ _ _ _ _ _) arguments, positive => by
      obtain ⟨element, member, used⟩ := countVarArguments_positive_outerUse position arguments
        (by intro slot inArity; exact congrArg Prod.fst (List.eq_of_mem_replicate inArity)) positive
      exact UsesOuterBound.collection member used
  | _, .op (.lambda _ _) arguments, positive =>
      match arguments with
      | .cons body .nil => by
          have used := countVar_positive_outerUse (weakenVar (S := signatureOf language) [_] position) body
            (by simpa only [countVar, countVarArgs, Nat.add_zero] using positive)
          exact UsesOuterBound.lambda (by simpa only [weakenVar, variableIndex] using used)
  | _, .op (.multiLambda _ _ count) arguments, positive =>
      match arguments with
      | .cons body .nil => by
          have used := countVar_positive_outerUse (weakenVar (S := signatureOf language) _ position) body
            (by simpa only [countVar, countVarArgs, Nat.add_zero] using positive)
          apply UsesOuterBound.multiLambda
          rw [variableIndex_weakenVar (language := language)] at used
          simpa only [List.length_replicate, Nat.add_comm] using used
  | _, .op (.subst _ _) arguments, positive =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          have either : 0 < countVar (.succ position) body ∨
              0 < countVar position replacement := by
            simp only [countVar, countVarArgs, weakenVar, Nat.add_zero] at positive
            omega
          rcases either with inBody | inReplacement
          · exact UsesOuterBound.substBody (by
              simpa only [weakenVar, variableIndex] using
                countVar_positive_outerUse (.succ position) body inBody)
          · exact UsesOuterBound.substReplacement
              (countVar_positive_outerUse position replacement inReplacement)
  | _, .op (.collection _ _ _) arguments, positive => by
      obtain ⟨element, member, used⟩ := countVarArguments_positive_outerUse position arguments
        (by intro slot inArity; exact congrArg Prod.fst (List.eq_of_mem_replicate inArity)) positive
      exact UsesOuterBound.collection member used
termination_by _ term _ => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

theorem countVarArguments_positive_outerUse {bound : List TypeExpr} {variableSort : TypeExpr}
    (position : Var bound variableSort) :
    ∀ {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf language) arity bound),
      (∀ slot ∈ arity, slot.1 = []) → 0 < countVarArgs position arguments →
        UsesOuterBoundList (eraseArguments arguments) (variableIndex position)
  | _, .nil, _, positive => by cases positive
  | (binders, _) :: _, .cons head tail, nonbinding, positive => by
      have empty : binders = [] := nonbinding _ List.mem_cons_self
      have either : 0 < countVar (weakenVar (S := signatureOf language) binders position) head ∨
          0 < countVarArgs position tail := by
        simp only [countVarArgs] at positive
        omega
      rcases either with inHead | inTail
      · refine ⟨erase head, List.mem_cons_self, ?_⟩
        have used := countVar_positive_outerUse
          (weakenVar (S := signatureOf language) binders position) head inHead
        rw [variableIndex_weakenVar (language := language)] at used
        have zeroLength : binders.length = 0 := congrArg List.length empty
        simpa only [zeroLength, Nat.zero_add] using used
      · obtain ⟨argument, member, used⟩ := countVarArguments_positive_outerUse position tail
          (fun slot member => nonbinding slot (List.mem_cons_of_mem _ member)) inTail
        exact ⟨argument, List.mem_cons_of_mem _ member, used⟩
termination_by _ arguments _ _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

theorem countVarConstructorArguments_positive_outerUse
    {bound : List TypeExpr} {variableSort : TypeExpr}
    (position : Var bound variableSort) :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      0 < countVarArgs position arguments →
        UsesOuterBoundList (eraseConstructorArguments scopes arguments) (variableIndex position)
  | _, _, .nil, .nil, positive => by cases positive
  | _, _, .cons (binders := binders) scope scopes, .cons head tail, positive => by
      have either : 0 < countVar (weakenVar (S := signatureOf language) binders position) head ∨
          0 < countVarArgs position tail := by
        simp only [countVarArgs] at positive
        omega
      rcases either with inHead | inTail
      · refine ⟨scope.wrap (erase head), List.mem_cons_self, ?_⟩
        apply parameterScope_outerUse scope (erase head)
        have used := countVar_positive_outerUse
          (weakenVar (S := signatureOf language) binders position) head inHead
        rw [variableIndex_weakenVar (language := language)] at used
        exact used
      · obtain ⟨argument, member, used⟩ :=
          countVarConstructorArguments_positive_outerUse position scopes tail inTail
        exact ⟨argument, List.mem_cons_of_mem _ member, used⟩
termination_by _ _ _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

private theorem argumentSub_erases :
    ∀ {dependencies locals : List TypeExpr}
      (arguments : DependencyArguments (language := language) dependencies locals)
      (sort : TypeExpr) (position : Var dependencies sort),
      erase (argsToSub arguments sort position) =
        (eraseArguments arguments).getD (variableIndex position) (.bvar 0)
  | [], _, .nil, _, position => nomatch position
  | _ :: _, _, .cons _ _, _, .zero => rfl
  | _ :: _, _, .cons _ tail, _, .succ position =>
      argumentSub_erases tail _ position

private theorem variableIndex_injective {bound : List TypeExpr} {sort : TypeExpr}
    (first second : Var bound sort) (same : variableIndex first = variableIndex second) :
    first = second := by
  have found := boundPosition?_complete first
  rw [same] at found
  exact Option.some.inj (found.symm.trans (boundPosition?_complete second))

private theorem variable_arguments_renaming {dependencies locals : List TypeExpr}
    {arguments : DependencyArguments (language := language) dependencies locals}
    (supported : ScopedElaboration.VariableArguments arguments) :
    ∃ rho : Ren (signatureOf language) dependencies locals,
      ∀ sort position, argsToSub arguments sort position = .var (rho sort position) := by
  induction supported with
  | nil =>
      refine ⟨(fun _ position => nomatch position), ?_⟩
      intro sort position
      exact nomatch position
  | cons head supported ih =>
      obtain ⟨tail, realized⟩ := ih
      refine ⟨prependRen head tail, ?_⟩
      intro sort position
      cases position with
      | zero => rfl
      | succ position => exact realized sort position

theorem variable_argument_renaming_index {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (rho : Ren (signatureOf language) dependencies locals)
    (realized : ∀ sort position, argsToSub arguments sort position = .var (rho sort position))
    (indices : List Nat) (readback : eraseArguments arguments = indices.map Pattern.bvar)
    (length : indices.length = dependencies.length)
    (sort : TypeExpr) (position : Var dependencies sort) :
    variableIndex (rho sort position) = indices[variableIndex position]'(by
      rw [length]; exact variableIndex_lt position) := by
  have bounded : variableIndex position < indices.length := by
    rw [length]
    exact variableIndex_lt position
  have erased := congrArg erase (realized sort position)
  rw [argumentSub_erases, readback, List.getD_map, List.getD_eq_getElem _ _ bounded] at erased
  exact (Pattern.bvar.inj erased).symm

/-- The existing variable recognizer succeeds because the actual raw
spine check has already earned injective, sorted local positions. -/
theorem recognize_checked_arguments {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (supported : ScopedElaboration.VariableArguments arguments) (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices) :
    ∃ selected : Mettapedia.OSLF.Binding.VariableArguments arguments,
      recognizeVariableArguments arguments = some selected := by
  obtain ⟨readback, length, unique, _⟩ := variable_spine_contract supported indices checked
  obtain ⟨rho, realized⟩ := variable_arguments_renaming supported
  apply recognizeVariableArguments_complete arguments rho realized
  intro sort first second same
  have firstImage := variable_argument_renaming_index arguments rho realized indices readback length sort first
  have secondImage := variable_argument_renaming_index arguments rho realized indices readback length sort second
  have indexEq : variableIndex first = variableIndex second := by
    apply unique.getElem_inj_iff.mp
    exact firstImage.symm.trans ((congrArg variableIndex same).trans secondImage)
  exact variableIndex_injective first second indexEq

/-- Extend the source-selected local renaming with the caller's ambient
identity. The two segments retain their independent lengths and sorts. -/
def appendAmbientRen {dependencies locals : List TypeExpr}
    (rho : Ren (signatureOf language) dependencies locals) (ambient : List TypeExpr) :
    Ren (signatureOf language) (dependencies ++ ambient) (locals ++ ambient) :=
  fun sort position => match splitVar (S := signatureOf language) (Γ := ambient) dependencies position with
    | .inl localPosition => injPrefix (S := signatureOf language) (Γ := ambient) locals
        (rho sort localPosition)
    | .inr ambientPosition => weakenVar (S := signatureOf language) locals ambientPosition

/-- Reuse the existing partial inverse on locals and preserve ambient
variables. It recognizes exactly the extended renaming's image. -/
def appendAmbientInverse {dependencies locals : List TypeExpr}
    {rho : Ren (signatureOf language) dependencies locals} (inverse : Strengthener rho)
    (ambient : List TypeExpr) : Strengthener (appendAmbientRen rho ambient) where
  un := fun sort position => match splitVar (S := signatureOf language) (Γ := ambient) locals position with
    | .inl localPosition => (inverse.un sort localPosition).map
        (injPrefix (S := signatureOf language) (Γ := ambient) dependencies)
    | .inr ambientPosition => some (weakenVar (S := signatureOf language) dependencies ambientPosition)
  un_rho := by
    intro sort position
    have rebuilt := splitVar_recombine (S := signatureOf language) dependencies position
    cases split : splitVar (S := signatureOf language) (Γ := ambient) dependencies position with
    | inl localPosition =>
        have original : injPrefix (S := signatureOf language) (Γ := ambient) dependencies localPosition = position := by
          simpa only [split, Sum.elim_inl] using rebuilt
        rw [← original]
        simp only [appendAmbientRen, splitVar_injPrefix, inverse.un_rho, Option.map_some]
    | inr ambientPosition =>
        have original : weakenVar (S := signatureOf language) dependencies ambientPosition = position := by
          simpa only [split, Sum.elim_inr] using rebuilt
        rw [← original]
        simp only [appendAmbientRen, splitVar_weakenVar]
  rho_un := by
    intro sort position original found
    have rebuilt := splitVar_recombine (S := signatureOf language) locals position
    cases split : splitVar (S := signatureOf language) (Γ := ambient) locals position with
    | inl localPosition =>
        simp only [split, Option.map_eq_some_iff] at found
        obtain ⟨preimage, hit, rfl⟩ := found
        simp only [appendAmbientRen, splitVar_injPrefix, inverse.rho_un _ _ _ hit]
        simpa only [split, Sum.elim_inl] using rebuilt
    | inr ambientPosition =>
        simp only [split, Option.some.injEq] at found
        subst original
        simp only [appendAmbientRen, splitVar_weakenVar]
        simpa only [split, Sum.elim_inr] using rebuilt

private theorem argument_renaming_covers :
    ∀ {dependencies locals : List TypeExpr}
      (arguments : DependencyArguments (language := language) dependencies locals)
      (rho : Ren (signatureOf language) dependencies locals),
      (∀ sort position, argsToSub arguments sort position = .var (rho sort position)) →
      ∀ pattern ∈ eraseArguments arguments,
        ∃ sort, ∃ position : Var dependencies sort,
          pattern = .bvar (variableIndex (rho sort position))
  | [], _, .nil, _, _, _, member => by cases member
  | first :: _, _, .cons head tail, rho, realized, pattern, member => by
      rcases List.mem_cons.mp member with firstPattern | later
      · refine ⟨first, .zero, ?_⟩
        rw [firstPattern]
        exact congrArg erase (realized first Var.zero)
      · obtain ⟨sort, position, same⟩ := argument_renaming_covers tail
          (fun sort position => rho sort (.succ position))
          (fun sort position => realized sort (.succ position)) pattern later
        exact ⟨sort, .succ position, same⟩

private theorem inverse_miss_not_selected {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (selected : Mettapedia.OSLF.Binding.VariableArguments arguments)
    (indices : List Nat) (readback : eraseArguments arguments = indices.map Pattern.bvar)
    (sort : TypeExpr) (position : Var locals sort)
    (miss : selected.inverse.un sort position = none) :
    variableIndex position ∉ indices := by
  intro member
  have argumentMember : .bvar (variableIndex position) ∈ eraseArguments arguments := by
    rw [readback]
    exact List.mem_map.mpr ⟨variableIndex position, member, rfl⟩
  obtain ⟨sourceSort, sourcePosition, equal⟩ :=
    argument_renaming_covers arguments selected.rho selected.realizes _ argumentMember
  have sameIndex : variableIndex position = variableIndex (selected.rho sourceSort sourcePosition) :=
    Pattern.bvar.inj equal
  have sameSort : sourceSort = sort := by
    have first := variableIndex_lookup (selected.rho sourceSort sourcePosition)
    rw [← sameIndex] at first
    exact Option.some.inj (first.symm.trans (variableIndex_lookup position))
  subst sourceSort
  have samePosition : selected.rho sort sourcePosition = position :=
    variableIndex_injective _ _ sameIndex.symm
  have hit := selected.inverse.un_rho sort sourcePosition
  rw [samePosition, miss] at hit
  contradiction

private theorem joinSub_split
    {dependencies ambient target : List TypeExpr}
    (arguments : Sub (signatureOf language) dependencies target)
    (ambientSub : Sub (signatureOf language) ambient target) :
    ∀ sort (position : Var (dependencies ++ ambient) sort),
      ContextualAssignment.joinSub arguments ambientSub sort position =
        Sum.elim (arguments sort) (ambientSub sort)
          (splitVar (S := signatureOf language) (Γ := ambient) dependencies position) := by
  induction dependencies with
  | nil => intro sort position; rfl
  | cons first dependencies ih =>
      intro sort position
      cases position with
      | zero => rfl
      | succ position =>
          have smaller := ih (fun sort position => arguments sort (.succ position)) sort position
          simp only [ContextualAssignment.joinSub]
          rw [splitVar]
          cases split : splitVar (S := signatureOf language) (Γ := ambient) dependencies position <;>
            simpa only [split, Sum.elim_inl, Sum.elim_inr] using smaller

theorem occurrenceSubstitution_is_renaming {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (selected : Mettapedia.OSLF.Binding.VariableArguments arguments) (ambient : List TypeExpr) :
    occurrenceSubstitution (appendAmbientArguments arguments ambient) =
      fun sort position => .var (appendAmbientRen selected.rho ambient sort position) := by
  funext sort position
  unfold occurrenceSubstitution
  rw [joinSub_split]
  cases split : splitVar (S := signatureOf language) (Γ := ambient) dependencies position with
  | inl localPosition =>
      simp only [Sum.elim_inl, appendAmbientArguments, argsToSub_renameArgs,
        selected.realizes, rename, appendAmbientRen, split]
  | inr ambientPosition => simp only [Sum.elim_inr, appendAmbientRen, split]

/-- Reflection earns an intrinsic body preimage for an arbitrary typed
target. The executable recovery itself supplies omitted-binder support;
the existing strengthening traversal supplies the typed body. -/
theorem recoverValue?_intrinsic_preimage {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (supported : ScopedElaboration.VariableArguments arguments) (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices)
    (target : Term (signatureOf language) (locals ++ ambient) sort) (value : ContextualValue)
    (recovered : recoverValue? dependencies ambient.length locals.length
      (eraseArguments arguments) (erase target) = some value) :
    ∃ body : Term (signatureOf language) (dependencies ++ ambient) sort,
      value = contextualValue body ∧
      bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body = target := by
  obtain ⟨readback, _, _, _⟩ := variable_spine_contract supported indices checked
  obtain ⟨selected, _⟩ := recognize_checked_arguments arguments supported indices checked
  have support := RestAwareTyping.recoverValue?_uses_only_selected_locals
    dependencies locals ambient (eraseArguments arguments) indices (erase target) value checked recovered
  obtain ⟨body, strengthened⟩ := strengthenT_isSome (appendAmbientInverse selected.inverse ambient) target (by
    intro variableSort position miss
    by_contra nonzero
    have positive : 0 < countVar position target := by omega
    have used := countVar_positive_outerUse position target positive
    have rebuilt := splitVar_recombine (S := signatureOf language) locals position
    cases split : splitVar (S := signatureOf language) (Γ := ambient) locals position with
    | inl localPosition =>
        have localMiss : selected.inverse.un variableSort localPosition = none := by
          simpa only [appendAmbientInverse, split, Option.map_eq_none_iff] using miss
        have original : injPrefix (S := signatureOf language) (Γ := ambient) locals localPosition = position := by
          simpa only [split, Sum.elim_inl] using rebuilt
        rw [← original, variableIndex_injPrefix (language := language)] at used
        exact inverse_miss_not_selected arguments selected indices readback variableSort localPosition localMiss
          (support _ used (variableIndex_lt localPosition))
    | inr ambientPosition =>
        simp only [appendAmbientInverse, split, Option.some_ne_none] at miss)
  have image := rename_strengthenT (appendAmbientInverse selected.inverse ambient) target body strengthened
  have action : bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body = target := by
    rw [occurrenceSubstitution_is_renaming arguments selected, bind_var_eq_rename]
    exact image
  have preserved := recoverValue?_typed_instance arguments supported indices checked body
  rw [action] at preserved
  exact ⟨body, Option.some.inj (recovered.symm.trans preserved), action⟩

/-- The actual raw recovery succeeds exactly at intrinsic contextual-body
preimages of the independently supplied typed target. -/
theorem recoverValue?_intrinsic_iff {dependencies locals ambient : List TypeExpr}
    {sort : TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (supported : ScopedElaboration.VariableArguments arguments) (indices : List Nat)
    (checked : variableSpine? locals.length (eraseArguments arguments) = some indices)
    (target : Term (signatureOf language) (locals ++ ambient) sort) (value : ContextualValue) :
    recoverValue? dependencies ambient.length locals.length
        (eraseArguments arguments) (erase target) = some value ↔
      ∃ body : Term (signatureOf language) (dependencies ++ ambient) sort,
        value = contextualValue body ∧
        bind (occurrenceSubstitution (appendAmbientArguments arguments ambient)) body = target := by
  constructor
  · exact recoverValue?_intrinsic_preimage arguments supported indices checked target value
  · rintro ⟨body, rfl, action⟩
    have preserved := recoverValue?_typed_instance arguments supported indices checked body
    rw [action] at preserved
    exact preserved

end InputRecovery

/-- Input admission retains the existing compiled occurrence and earns
its stronger inverse-spine contract from the same source execution. The
local context has exactly the binder depth of that occurrence address. -/
structure CompiledInputOccurrence (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) where
  compiled : CompiledOccurrence language rule spec locals site path name sort
  attached : rule.bindings = some spec
  admitted : admittedFor rule spec = true
  sortsDeclared : dependencySortsDeclared language spec = true
  supported : VariableArguments compiled.arguments
  indices : List Nat
  checked : variableSpine? locals.length (eraseArguments compiled.arguments) = some indices
  depth : occurrenceDepthAtSite? rule site path = some locals.length

/-- The additional input checks run after the shared sorted occurrence
codec. They reject repeated dependency images and a caller-local context
whose length does not match the actual authored address. -/
def elaborateInputOccurrence? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    Option (CompiledInputOccurrence language rule spec locals site path name sort) :=
  match accepted : elaborateOccurrence? language rule spec locals site path name sort with
  | none => none
  | some compiled =>
      if depth : occurrenceDepthAtSite? rule site path = some locals.length then
        match checked : variableSpine? locals.length (eraseArguments compiled.arguments) with
        | none => none
        | some indices =>
            let admission := elaborateOccurrence?_admitted accepted
            some {
              compiled := compiled
              attached := admission.1
              admitted := admission.2.1
              sortsDeclared := admission.2.2
              supported := elaborateOccurrence?_supported accepted
              indices := indices
              checked := checked
              depth := depth }
      else none

/-- Computed input admission is exactly shared sorted source admission,
the actual address depth, and the original raw injective-spine check. -/
theorem elaborateInputOccurrence?_isSome_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    (locals : List TypeExpr) (site : RulePatternSite) (path : List Nat)
    (name : String) (sort : TypeExpr) :
    (elaborateInputOccurrence? language rule spec locals site path name sort).isSome = true ↔
      (elaborateOccurrence? language rule spec locals site path name sort).isSome = true ∧
        occurrenceDepthAtSite? rule site path = some locals.length ∧
        ∃ arguments indices, arguments? rule spec name site path = some arguments ∧
          variableSpine? locals.length arguments = some indices := by
  unfold elaborateInputOccurrence?
  split
  · rename_i absent
    simp [absent]
  · rename_i compiled accepted
    split
    · rename_i depth
      split
      · rename_i checked
        simp [accepted, depth, compiled.source, checked]
      · rename_i indices checked
        simp [accepted, depth, compiled.source, checked]
    · rename_i wrongDepth
      simp [accepted, wrongDepth]

/-- A source-facing admission contract exposes the actual metadata,
typed dependency context and checked inverse image together. -/
theorem elaborateInputOccurrence?_source_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    (locals : List TypeExpr) (site : RulePatternSite) (path : List Nat)
    (name : String) (sort : TypeExpr) :
    (elaborateInputOccurrence? language rule spec locals site path name sort).isSome = true ↔
      rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        dependencySortsDeclared language spec = true ∧
        occurrenceDepthAtSite? rule site path = some locals.length ∧
        ∃ compiled : CompiledOccurrence language rule spec locals site path name sort,
          VariableArguments compiled.arguments ∧
          ∃ indices, variableSpine? locals.length (eraseArguments compiled.arguments) = some indices := by
  rw [elaborateInputOccurrence?_isSome_iff, elaborateOccurrence?_isSome_iff]
  constructor
  · rintro ⟨⟨attached, admitted, declared, compiled, supported⟩, depth,
      arguments, indices, source, checked⟩
    have sameArguments : arguments = eraseArguments compiled.arguments :=
      Option.some.inj (source.symm.trans compiled.source)
    subst arguments
    exact ⟨attached, admitted, declared, depth, compiled, supported, indices, checked⟩
  · rintro ⟨attached, admitted, declared, depth, compiled, supported, indices, checked⟩
    exact ⟨⟨attached, admitted, declared, compiled, supported⟩, depth,
      eraseArguments compiled.arguments, indices, compiled.source, checked⟩

/-- Select the input occurrence from the physical canonical rule position,
without replacing the rule or its premises with a new operational row. -/
abbrev AuthoredInputOccurrence (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :=
  (spec : RuleBindingSpec) ×
    CompiledInputOccurrence language (language.rewrites.get ruleIndex) spec locals site path name sort

def elaborateAuthoredInputOccurrence? (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    Option (AuthoredInputOccurrence language ruleIndex locals site path name sort) :=
  match (language.rewrites.get ruleIndex).bindings with
  | none => none
  | some spec =>
      (elaborateInputOccurrence? language (language.rewrites.get ruleIndex) spec
        locals site path name sort).map fun input => ⟨spec, input⟩

/-- The physical source entry point has the same two-sided admission
contract. No attached declaration or rule address is supplied separately. -/
theorem elaborateAuthoredInputOccurrence?_isSome_iff
    (ruleIndex : Fin language.rewrites.length) (locals : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    (elaborateAuthoredInputOccurrence? language ruleIndex locals site path name sort).isSome = true ↔
      ∃ spec, (language.rewrites.get ruleIndex).bindings = some spec ∧
        admittedFor (language.rewrites.get ruleIndex) spec = true ∧
        dependencySortsDeclared language spec = true ∧
        occurrenceDepthAtSite? (language.rewrites.get ruleIndex) site path = some locals.length ∧
        ∃ compiled : CompiledOccurrence language (language.rewrites.get ruleIndex) spec
            locals site path name sort,
          VariableArguments compiled.arguments ∧
          ∃ indices, variableSpine? locals.length (eraseArguments compiled.arguments) = some indices := by
  cases attached : (language.rewrites.get ruleIndex).bindings with
  | none =>
      simp only [List.get_eq_getElem] at attached
      simp [elaborateAuthoredInputOccurrence?, List.get_eq_getElem, attached]
  | some spec =>
      simp only [elaborateAuthoredInputOccurrence?, attached, Option.isSome_map]
      rw [elaborateInputOccurrence?_source_iff]
      simp only [List.get_eq_getElem] at attached
      simp [List.get_eq_getElem, attached]

namespace CompiledInputOccurrence

open InputRecovery
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

variable {rule : RewriteRule} {spec : RuleBindingSpec} {locals : List TypeExpr}
  {site : RulePatternSite} {path : List Nat} {name : String} {sort : TypeExpr}

abbrev dependencies (input : CompiledInputOccurrence language rule spec locals site path name sort) :=
  ((metaArities (language := language) rule spec).get
    (metaIndex rule spec input.compiled.index)).1

/-- The recognizer's typed inverse is earned from the actual source checks;
neither injectivity nor a permutation is an additional caller assumption. -/
theorem recognizes_arguments
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    ∃ selected : Mettapedia.OSLF.Binding.VariableArguments input.compiled.arguments,
      recognizeVariableArguments input.compiled.arguments = some selected :=
  recognize_checked_arguments input.compiled.arguments input.supported input.indices input.checked

theorem recover_typed_instance {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort) :
    recoverValue? input.dependencies ambient.length locals.length
        (eraseArguments input.compiled.arguments)
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) =
      some (contextualValue body) :=
  recoverValue?_typed_instance input.compiled.arguments input.supported input.indices input.checked body

/-- Recovery at this source-admitted input succeeds exactly when the typed
target has a typed contextual-body preimage under its actual substitution. -/
theorem recover_intrinsic_iff {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (target : Term (signatureOf language) (locals ++ ambient) sort) (value : ContextualValue) :
    recoverValue? input.dependencies ambient.length locals.length
        (eraseArguments input.compiled.arguments) (erase target) = some value ↔
      ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        value = contextualValue body ∧
        bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target :=
  recoverValue?_intrinsic_iff input.compiled.arguments input.supported input.indices input.checked target value

/-- The actual source capture reads the same dependency declaration and
the same occurrence spine. It then performs the existing assignment update. -/
theorem capture_typed_instance {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort) :
    capture? rule spec ambient.length locals.length site path initial name
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) =
      assign initial name (contextualValue body) := by
  simp only [capture?, input.compiled.declared, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  rw [input.recover_typed_instance body]
  rfl

/-- Reflection includes the real repeated-assignment test. Successful raw
capture supplies a typed body preimage and exactly the original update;
an existing incompatible assignment is not silently overwritten. -/
theorem capture_intrinsic_iff {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (target : Term (signatureOf language) (locals ++ ambient) sort) :
    capture? rule spec ambient.length locals.length site path initial name (erase target) = some final ↔
      ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target ∧
        assign initial name (contextualValue body) = some final := by
  simp only [capture?, input.compiled.declared, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  constructor
  · intro accepted
    obtain ⟨value, recovered, assigned⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨body, sameValue, action⟩ := (input.recover_intrinsic_iff target value).mp recovered
    exact ⟨body, action, by simpa only [sameValue] using assigned⟩
  · rintro ⟨body, action, assigned⟩
    refine Option.bind_eq_some_iff.mpr ⟨contextualValue body, ?_, assigned⟩
    exact (input.recover_intrinsic_iff target (contextualValue body)).mpr ⟨body, rfl, action⟩

/-- The matcher at the selected metavariable leaf is the actual capture
operation, including its refusal and multiplicity conventions. -/
theorem match_leaf_typed_instance {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort) :
    matchAtWith literalBodyComparison rule spec ambient.length site path locals.length initial
        (.fvar name) (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) =
      (assign initial name (contextualValue body)).toList := by
  simp only [matchAtWith, captureWith?_literal, input.capture_typed_instance initial body]

/-- Refusal is also reflected: every possible intrinsic preimage either
fails to instantiate to this target or fails the actual assignment test. -/
theorem capture_none_iff {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (target : Term (signatureOf language) (locals ++ ambient) sort) :
    capture? rule spec ambient.length locals.length site path initial name (erase target) = none ↔
      ∀ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target →
        assign initial name (contextualValue body) = none := by
  constructor
  · intro refused body action
    cases assigned : assign initial name (contextualValue body) with
    | none => rfl
    | some final =>
        have accepted := (input.capture_intrinsic_iff initial final target).mpr ⟨body, action, assigned⟩
        rw [refused] at accepted
        contradiction
  · intro allRefused
    cases captured : capture? rule spec ambient.length locals.length site path initial name (erase target) with
    | none => rfl
    | some final =>
        obtain ⟨body, action, assigned⟩ := (input.capture_intrinsic_iff initial final target).mp captured
        rw [allRefused body action] at assigned
        contradiction

theorem capture_fresh {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort)
    (fresh : lookup initial name = none) :
    capture? rule spec ambient.length locals.length site path initial name
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) =
      some ((name, contextualValue body) :: initial) := by
  rw [input.capture_typed_instance initial body]
  simp only [assign, fresh]

/-- Repeated occurrences compare the exact recovered contextual value and
keep the first assignment. Equality of targets at different local spines
is not substituted for equality of their bodies. -/
theorem capture_repeated_iff {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort)
    (prior : ContextualValue) (present : lookup initial name = some prior) :
    capture? rule spec ambient.length locals.length site path initial name
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) = some initial ↔
      prior = contextualValue body := by
  rw [input.capture_typed_instance initial body]
  simp only [assign, present]
  by_cases same : prior = contextualValue body <;> simp [same]

theorem capture_repeated_refused {ambient : List TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort)
    (prior : ContextualValue) (present : lookup initial name = some prior)
    (different : prior ≠ contextualValue body) :
    capture? rule spec ambient.length locals.length site path initial name
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body)) = none := by
  rw [input.capture_typed_instance initial body]
  simp [assign, present, different]

theorem dependencies_eq {otherLocals : List TypeExpr} {otherSite : RulePatternSite}
    {otherPath : List Nat}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (other : CompiledInputOccurrence language rule spec otherLocals otherSite otherPath name sort) :
    input.dependencies = other.dependencies :=
  Option.some.inj (input.compiled.declared.symm.trans other.compiled.declared)

private theorem contextualValue_cast_dependencies {dependencies otherDependencies ambient : List TypeExpr}
    {result : TypeExpr} (same : dependencies = otherDependencies)
    (body : Term (signatureOf language) (dependencies ++ ambient) result) :
    contextualValue (cast (congrArg
        (fun context => Term (signatureOf language) (context ++ ambient) result) same) body) =
      contextualValue body := by
  cases same
  rfl

private theorem lookup_same_head
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (name : String) (value : ContextualValue) :
    lookup ((name, value) :: initial) name = some value := by
  simp [lookup]

/-- Two actual admitted source addresses may have different local depths
and different injective spines. Their shared dependency declaration earns
the body transport, and the second capture retains the first raw value. -/
theorem capture_repeated_different_occurrence {ambient otherLocals : List TypeExpr}
    {otherSite : RulePatternSite} {otherPath : List Nat}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (other : CompiledInputOccurrence language rule spec otherLocals otherSite otherPath name sort)
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort)
    (fresh : lookup initial name = none) :
    let otherBody := cast (congrArg
      (fun context => Term (signatureOf language) (context ++ ambient) sort)
      (input.dependencies_eq other)) body
    (capture? rule spec ambient.length locals.length site path initial name
      (erase (bind (occurrenceSubstitution
        (appendAmbientArguments input.compiled.arguments ambient)) body))).bind (fun captured =>
      capture? rule spec ambient.length otherLocals.length otherSite otherPath captured name
        (erase (bind (occurrenceSubstitution
          (appendAmbientArguments other.compiled.arguments ambient)) otherBody))) =
      some ((name, contextualValue body) :: initial) := by
  dsimp only
  rw [input.capture_fresh initial body fresh, Option.bind_some]
  rw [other.capture_typed_instance]
  rw [contextualValue_cast_dependencies (input.dependencies_eq other) body]
  simp only [assign, lookup_same_head, beq_self_eq_true, if_true]

end CompiledInputOccurrence

namespace SchemaElaboration

variable {rule : RewriteRule} {spec : RuleBindingSpec}

abbrev SchemaSignature (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) :=
  withMetas (signatureOf language) (metaArities rule spec)

/-- Recover a head's original physical declaration position. Dependency
arguments remain in the intrinsic schema and its input-occurrence receipt. -/
def metaName (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin (metaArities (language := language) rule spec).length) : String :=
  (rule.typeContext.get
    ⟨index.val, by simpa only [metaArities_length] using index.isLt⟩).1

mutual
/-- Read the original pattern representation of an intrinsic schema. The
anonymous wrappers are its exact-readback profile; authored display names
remain on the original rule and constructor declarations. -/
def readback : {bound : List TypeExpr} → {sort : TypeExpr} →
    Term (SchemaSignature language rule spec) bound sort → Pattern
  | _, _, .var position => .bvar (variableIndex position)
  | _, _, .op (.inr (.mk index)) _ => .fvar (metaName rule spec index)
  | _, _, .op (.inl operator) arguments =>
      match operator with
      | .constructor declaration _ _ scopes =>
          .apply declaration.label (readbackConstructorArguments scopes arguments)
      | .collectionConstructor _ _ _ kind _ _ _ =>
          .collection kind (readbackArguments arguments) none
      | .lambda _ _ =>
          match arguments with
          | .cons body .nil => .lambda none (readback body)
      | .multiLambda _ _ count =>
          match arguments with
          | .cons body .nil => .multiLambda count [] (readback body)
      | .subst _ _ =>
          match arguments with
          | .cons body (.cons replacement .nil) => .subst (readback body) (readback replacement)
      | .collection kind _ _ => .collection kind (readbackArguments arguments) none

def readbackArguments : {arity : List (List TypeExpr × TypeExpr)} →
    {bound : List TypeExpr} → Args (SchemaSignature language rule spec) arity bound →
    List Pattern
  | _, _, .nil => []
  | _, _, .cons head tail => readback head :: readbackArguments tail

def readbackConstructorArguments : {parameters : List TermParam} →
    {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
    ParameterScopes parameters arity →
    Args (SchemaSignature language rule spec) arity bound → List Pattern
  | _, _, _, .nil, .nil => []
  | _, _, _, .cons scope scopes, .cons head tail =>
      scope.wrap (readback head) :: readbackConstructorArguments scopes tail
end

theorem readback_cast_context {bound target : List TypeExpr} (same : bound = target)
    {sort : TypeExpr} (term : Term (SchemaSignature language rule spec) bound sort) :
    readback (castTermCtx same term) = readback term := by
  cases same
  rfl

theorem readback_cast_sort {bound : List TypeExpr} {first second : TypeExpr}
    (same : first = second) (term : Term (SchemaSignature language rule spec) bound first) :
    readback (same ▸ term) = readback term := by
  cases same
  rfl

private theorem cast_context_inverse {S : Signature} {first second : Ctx S}
    (same : first = second) {sort : S.Srt} (term : Term S first sort) :
    castTermCtx same.symm (castTermCtx same term) = term := by
  cases same
  rfl

private theorem rename_cast_sort {S : Signature} {bound target : Ctx S}
    {first second : S.Srt} (same : first = second) (rho : Ren S bound target)
    (term : Term S bound first) : rename rho (same ▸ term) = same ▸ rename rho term := by
  cases same
  rfl

private theorem matching_supported_cast_sort {locals : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (term : Term (SchemaSignature language rule spec) (locals ++ []) first)
    (supported : MatchingSupportedT (S := signatureOf language)
      (M := metaArities rule spec) (Γ := []) locals term) :
    MatchingSupportedT (S := signatureOf language) (M := metaArities rule spec)
      (Γ := []) locals (same ▸ term) := by
  cases same
  exact supported

private theorem argsToSub_embed {dependencies locals : List TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals) :
    ∀ sort position, argsToSub (embedArgs (M := metaArities rule spec) arguments) sort position =
      embed (M := metaArities rule spec) (argsToSub arguments sort position) := by
  induction dependencies with
  | nil => intro sort position; exact nomatch position
  | cons first rest ih =>
      cases arguments with
      | cons head tail =>
          intro sort position
          cases position with
          | zero => rfl
          | succ old => exact ih tail sort old

theorem CompiledInputOccurrence.recognizes_embedded_arguments
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    ∃ selected : Mettapedia.OSLF.Binding.VariableArguments
        (embedArgs (M := metaArities rule spec) input.compiled.arguments),
      recognizeVariableArguments (embedArgs input.compiled.arguments) = some selected := by
  obtain ⟨selected, _⟩ := input.recognizes_arguments
  apply recognizeVariableArguments_complete (S := SchemaSignature language rule spec)
    (embedArgs input.compiled.arguments) selected.rho
  · intro result position
    rw [argsToSub_embed, selected.realizes]
    rfl
  · exact selected.injective

/-- The existing matcher's support predicate is earned by the source codec,
including the actual bound-prefix projection and inverse-spine recognition. -/
theorem CompiledInputOccurrence.matching_supported
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    MatchingSupportedT (S := signatureOf language) (M := metaArities rule spec) (Γ := []) locals
      (rename (fun _ position => injPrefix (S := SchemaSignature language rule spec)
        (Γ := []) locals position) input.compiled.term) := by
  rw [CompiledOccurrence.term, rename_cast_sort]
  apply matching_supported_cast_sort
  change MatchingSupportedT (S := signatureOf language) (M := metaArities rule spec)
    (Γ := []) locals
    (.op (.inr (.mk (metaIndex rule spec input.compiled.index)))
      (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
        (Γ := []) locals position)
        (embedArgs input.compiled.arguments)))
  rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
  exact ⟨embedArgs input.compiled.arguments, strengthenA_renameArgs _ _,
    CompiledInputOccurrence.recognizes_embedded_arguments input⟩

theorem CompiledInputOccurrence.readback
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    readback (rename (fun _ position => injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position) input.compiled.term) = .fvar name := by
  rw [CompiledOccurrence.term, rename_cast_sort, readback_cast_sort]
  change Pattern.fvar (metaName rule spec (metaIndex rule spec input.compiled.index)) = _
  unfold metaName metaIndex
  exact congrArg Pattern.fvar input.compiled.named

/-- Source occurrence evidence keeps the original rule, site, address,
dependency metadata and the context computed along the constructor path. -/
abbrev InputEvidence (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :=
  (site : RulePatternSite) × (locals : List TypeExpr) × (path : List Nat) ×
    (name : String) × (sort : TypeExpr) ×
      CompiledInputOccurrence language rule spec locals site path name sort

/-- One successful recursive translation retains its intrinsic schema,
exact original representation and existing recursive matcher admission. -/
structure CompiledSchema (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr) (source : Pattern) (sort : TypeExpr) where
  term : Term (SchemaSignature language rule spec) (locals ++ []) sort
  source_readback : readback term = source
  matching_supported : MatchingSupportedT (S := signatureOf language)
    (M := metaArities rule spec) (Γ := []) locals term
  inputOccurrences : List (InputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

/-- Parameter unwrapping uses the existing declaration-derived scope. The
path extension records the representation binder that the scope removes. -/
structure ParameterBody (parameter : TermParam) (source : Pattern) where
  binders : List TypeExpr
  sort : TypeExpr
  scope : ParameterScope parameter binders sort
  body : Pattern
  pathSuffix : List Nat
  source_readback : scope.wrap body = source

/-- Only canonical anonymous representation wrappers are admitted here.
The declaration's binder names are preserved in `ParameterScope`. -/
def parameterBody? : (parameter : TermParam) → (source : Pattern) →
    Option (ParameterBody parameter source)
  | .simple name sort, source => some
      { binders := [], sort := sort, scope := .simple name sort,
        body := source, pathSuffix := [], source_readback := rfl }
  | .abstractionNamed binder name (.arrow domain codomain), .lambda none body => some
      { binders := [domain], sort := codomain, scope := .abstraction binder name domain codomain,
        body := body, pathSuffix := [0], source_readback := rfl }
  | .abstractionNamed binder name (.base sort), .lambda none body => some
      { binders := [.base sort], sort := .base sort, scope := .abstractionBase binder name sort,
        body := body, pathSuffix := [0], source_readback := rfl }
  | .multiAbstractionNamed binders name (.arrow (.multiBinder domain) codomain),
      .multiLambda count [] body => some
      { binders := List.replicate count domain, sort := codomain,
        scope := .multiAbstraction binders name domain codomain count,
        body := body, pathSuffix := [0], source_readback := rfl }
  | .multiAbstractionNamed binders name (.base sort), .multiLambda count [] body => some
      { binders := List.replicate count (.base sort), sort := .base sort,
        scope := .multiAbstractionBase binders name sort count,
        body := body, pathSuffix := [0], source_readback := rfl }
  | _, _ => none

/-- All physical declarations with this label are considered together.
A unique-label profile rejects ambiguity rather than choosing by order. -/
def constructorCandidates (language : LanguageDef) (label : String) :
    List (Fin language.terms.length) :=
  (List.finRange language.terms.length).filter fun index =>
    (language.terms.get index).label == label

structure SelectedConstructor (language : LanguageDef) (label : String) where
  index : Fin language.terms.length
  unique : constructorCandidates language label = [index]

def selectConstructor? (language : LanguageDef) (label : String) :
    Option (SelectedConstructor language label) :=
  match candidates : constructorCandidates language label with
  | [index] => some { index := index, unique := candidates }
  | _ => none

theorem SelectedConstructor.named {label : String}
    (selected : SelectedConstructor language label) :
    (language.terms.get selected.index).label = label := by
  have member : selected.index ∈ constructorCandidates language label := by
    rw [selected.unique]
    exact List.mem_cons_self
  exact beq_iff_eq.mp (List.mem_filter.mp member).2

theorem selectConstructor?_complete {label : String}
    (selected : SelectedConstructor language label) :
    selectConstructor? language label = some selected := by
  unfold selectConstructor?
  split
  · rename_i index candidates
    have same : index = selected.index := by
      simpa only [List.cons.injEq, and_true] using candidates.symm.trans selected.unique
    subst index
    rfl
  · rename_i notSingleton
    exact False.elim (notSingleton selected.index selected.unique)

/-- Arguments carry exactly the existing declaration's parameter arities;
their source order and binder wrappers are checked recursively. -/
structure CompiledConstructorArguments (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (parameters : List TermParam) (sources : List Pattern) where
  arity : List (List TypeExpr × TypeExpr)
  scopes : ParameterScopes parameters arity
  arguments : Args (SchemaSignature language rule spec) arity (locals ++ [])
  source_readback : readbackConstructorArguments scopes arguments = sources
  matching_supported : MatchingSupportedA (S := signatureOf language)
    (M := metaArities rule spec) (Γ := []) locals arguments
  inputOccurrences : List (InputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

abbrev CompiledConstructorArguments.nil (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr) :
    CompiledConstructorArguments language rule spec locals [] [] :=
  { arity := [], scopes := .nil, arguments := .nil, source_readback := rfl,
    matching_supported := by
      rw [MatchingSupportedA.eq_def (S := signatureOf language)
        (M := metaArities rule spec)]
      trivial
    inputOccurrences := [], constructorOccurrences := [] }

abbrev CompiledConstructorArguments.cons {locals : List TypeExpr} {parameter : TermParam}
    {parameters : List TermParam} {source : Pattern} {sources : List Pattern}
    (body : ParameterBody parameter source)
    (head : CompiledSchema language rule spec (body.binders ++ locals) body.body body.sort)
    (tail : CompiledConstructorArguments language rule spec locals parameters sources) :
    CompiledConstructorArguments language rule spec locals (parameter :: parameters) (source :: sources) :=
  {
    arity := (body.binders, body.sort) :: tail.arity
    scopes := .cons body.scope tail.scopes
    arguments := .cons
      (castTermCtx (List.append_assoc body.binders locals []) head.term) tail.arguments
    source_readback := by
      change body.scope.wrap (readback (castTermCtx _ head.term)) ::
        readbackConstructorArguments tail.scopes tail.arguments = source :: sources
      rw [readback_cast_context, head.source_readback,
        body.source_readback, tail.source_readback]
    matching_supported := by
      rw [MatchingSupportedA.eq_def (S := signatureOf language)
        (M := metaArities rule spec)]
      exact ⟨by rw [cast_context_inverse]; exact head.matching_supported,
        tail.matching_supported⟩
    inputOccurrences := head.inputOccurrences ++ tail.inputOccurrences
    constructorOccurrences := head.constructorOccurrences ++ tail.constructorOccurrences }

/-- Assemble checked parameter bodies with the original scope interpreter.
The supplied recursive call is used on smaller source bodies by the fuelled
schema codec below; this assembly does not define a second evaluator. -/
def compileConstructorArguments?
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (locals : List TypeExpr) (path : List Nat) (offset : Nat) :
    (parameters : List TermParam) → (sources : List Pattern) →
      Option (CompiledConstructorArguments language rule spec locals parameters sources)
  | [], [] => some (.nil language rule spec locals)
  | parameter :: parameters, source :: sources => do
      let body ← parameterBody? parameter source
      let head ← compile (body.binders ++ locals) (path ++ [offset] ++ body.pathSuffix)
        body.body body.sort
      let tail ← compileConstructorArguments? compile locals path (offset + 1) parameters sources
      pure (.cons body head tail)
  | _, _ => none

def CompiledSchema.ofInput {locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    CompiledSchema language rule spec locals (.fvar name) sort where
  term := rename (fun _ position => injPrefix (S := SchemaSignature language rule spec)
    (Γ := []) locals position) input.compiled.term
  source_readback := CompiledInputOccurrence.readback input
  matching_supported := CompiledInputOccurrence.matching_supported input
  inputOccurrences := [⟨site, locals, path, name, sort, input⟩]
  constructorOccurrences := []

def CompiledSchema.castSort {locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (compiled : CompiledSchema language rule spec locals source first)
    (same : first = second) : CompiledSchema language rule spec locals source second where
  term := same ▸ compiled.term
  source_readback := (readback_cast_sort same compiled.term).trans compiled.source_readback
  matching_supported := matching_supported_cast_sort same compiled.term compiled.matching_supported
  inputOccurrences := compiled.inputOccurrences
  constructorOccurrences := compiled.constructorOccurrences

private theorem singleton_supported {locals binders : List TypeExpr} {sort : TypeExpr}
    (head : Term (SchemaSignature language rule spec) ((binders ++ locals) ++ []) sort)
    (supported : MatchingSupportedT (S := signatureOf language)
      (M := metaArities rule spec) (Γ := []) (binders ++ locals) head) :
    MatchingSupportedA (S := signatureOf language) (M := metaArities rule spec)
      (Γ := []) locals
      (.cons (castTermCtx (List.append_assoc binders locals []) head) .nil) := by
  rw [MatchingSupportedA.eq_def (S := signatureOf language) (M := metaArities rule spec)]
  refine ⟨?_, ?_⟩
  · rw [cast_context_inverse]
    exact supported
  · rw [MatchingSupportedA.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    trivial

def CompiledSchema.lambda {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain) :
    CompiledSchema language rule spec locals (.lambda none source) (.arrow domain codomain) where
  term := .op (.inl (.lambda domain codomain)) (.cons body.term .nil)
  source_readback := by change Pattern.lambda none (readback body.term) = _; rw [body.source_readback]
  matching_supported := by
    rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    exact singleton_supported (binders := [domain]) body.term body.matching_supported
  inputOccurrences := body.inputOccurrences
  constructorOccurrences := body.constructorOccurrences

def CompiledSchema.multiLambda {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain) :
    CompiledSchema language rule spec locals (.multiLambda count [] source)
      (.arrow (.multiBinder domain) codomain) where
  term := .op (.inl (.multiLambda domain codomain count))
    (.cons (castTermCtx (List.append_assoc (List.replicate count domain) locals []) body.term) .nil)
  source_readback := by
    change Pattern.multiLambda count [] (readback (castTermCtx _ body.term)) = _
    rw [readback_cast_context, body.source_readback]
  matching_supported := by
    rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    exact singleton_supported body.term body.matching_supported
  inputOccurrences := body.inputOccurrences
  constructorOccurrences := body.constructorOccurrences

def CompiledSchema.constructor {locals : List TypeExpr} {label : String}
    (path : List Nat) (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index)) {sources : List Pattern}
    (arguments : CompiledConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources) :
    CompiledSchema language rule spec locals (.apply label sources)
      (.base (language.terms.get selected.index).category) where
  term := .op (.inl (.constructor (language.terms.get selected.index)
    (List.get_mem _ _) ordinary arguments.scopes)) arguments.arguments
  source_readback := by
    change Pattern.apply (language.terms.get selected.index).label
      (readbackConstructorArguments arguments.scopes arguments.arguments) = _
    rw [selected.named, arguments.source_readback]
  matching_supported := by
    rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    exact arguments.matching_supported
  inputOccurrences := arguments.inputOccurrences
  constructorOccurrences := (path, selected.index) :: arguments.constructorOccurrences

/-- Ordered element occurrences retain their number, order and independent
source addresses in the existing finite argument family. -/
structure CompiledVectorElements (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (sources : List Pattern) (elementSort : TypeExpr) where
  arguments : Args (SchemaSignature language rule spec)
    (List.replicate sources.length ([], elementSort)) (locals ++ [])
  source_readback : readbackArguments arguments = sources
  matching_supported : MatchingSupportedA (S := signatureOf language)
    (M := metaArities rule spec) (Γ := []) locals arguments
  inputOccurrences : List (InputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

abbrev CompiledVectorElements.nil (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr) (elementSort : TypeExpr) :
    CompiledVectorElements language rule spec locals [] elementSort :=
  {
    arguments := .nil
    source_readback := rfl
    matching_supported := by
      rw [MatchingSupportedA.eq_def (S := signatureOf language) (M := metaArities rule spec)]
      trivial
    inputOccurrences := []
    constructorOccurrences := [] }

abbrev CompiledVectorElements.cons {locals : List TypeExpr} {source : Pattern} {sources : List Pattern}
    {elementSort : TypeExpr} (head : CompiledSchema language rule spec locals source elementSort)
    (tail : CompiledVectorElements language rule spec locals sources elementSort) :
    CompiledVectorElements language rule spec locals (source :: sources) elementSort :=
  {
    arguments := .cons head.term tail.arguments
    source_readback := by
      change readback head.term :: readbackArguments tail.arguments = source :: sources
      rw [head.source_readback, tail.source_readback]
    matching_supported := by
      rw [MatchingSupportedA.eq_def (S := signatureOf language) (M := metaArities rule spec)]
      exact ⟨head.matching_supported, tail.matching_supported⟩
    inputOccurrences := head.inputOccurrences ++ tail.inputOccurrences
    constructorOccurrences := head.constructorOccurrences ++ tail.constructorOccurrences }

def compileVectorElements?
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (locals : List TypeExpr) (path : List Nat) (offset : Nat) (elementSort : TypeExpr) :
    (sources : List Pattern) →
      Option (CompiledVectorElements language rule spec locals sources elementSort)
  | [] => some (.nil language rule spec locals elementSort)
  | source :: sources => do
      let head ← compile locals (path ++ [offset]) source elementSort
      let tail ← compileVectorElements? compile locals path (offset + 1) elementSort sources
      pure (.cons head tail)

def CompiledSchema.vector {locals : List TypeExpr} {sources : List Pattern}
    {elementSort : TypeExpr}
    (elements : CompiledVectorElements language rule spec locals sources elementSort) :
    CompiledSchema language rule spec locals (.collection .vec sources none)
      (.collection .vec elementSort) where
  term := .op (.inl (.collection .vec elementSort sources.length)) elements.arguments
  source_readback := by
    change Pattern.collection .vec (readbackArguments elements.arguments) none = _
    rw [elements.source_readback]
  matching_supported := by
    rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    exact elements.matching_supported
  inputOccurrences := elements.inputOccurrences
  constructorOccurrences := elements.constructorOccurrences

/-- Bare vector selection reuses the existing source checker's declaration
view. Multiple physical representation authorities are refused explicitly. -/
def vectorConstructorCandidates (language : LanguageDef) (category : String) :
    List (Fin language.terms.length) :=
  (List.finRange language.terms.length).filter fun index =>
    (bareCollectionElementType? (language.terms.get index) .vec (.base category)).isSome

structure SelectedVectorConstructor (language : LanguageDef) (category : String) where
  index : Fin language.terms.length
  unique : vectorConstructorCandidates language category = [index]
  parameterName : String
  elementSort : TypeExpr
  shape : (language.terms.get index).bareParams = [.simple parameterName (.collection .vec elementSort)]
  categorized : (language.terms.get index).category = category

def selectVectorConstructor? (language : LanguageDef) (category : String) :
    Option (SelectedVectorConstructor language category) :=
  match candidates : vectorConstructorCandidates language category with
  | [index] =>
      match shape : (language.terms.get index).bareParams with
      | [.simple parameterName (.collection .vec elementSort)] =>
          if categorized : (language.terms.get index).category = category then
            some {
              index := index
              unique := candidates
              parameterName := parameterName
              elementSort := elementSort
              shape := shape
              categorized := categorized }
          else none
      | _ => none
  | _ => none

def CompiledSchema.vectorConstructor {locals : List TypeExpr} {sources : List Pattern}
    {category : String} (path : List Nat) (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort) :
    CompiledSchema language rule spec locals (.collection .vec sources none) (.base category) :=
  CompiledSchema.castSort {
    term := .op (.inl (.collectionConstructor (language.terms.get selected.index)
      (List.get_mem _ _) selected.parameterName .vec selected.elementSort selected.shape sources.length))
      elements.arguments
    source_readback := by
      change Pattern.collection .vec (readbackArguments elements.arguments) none = _
      rw [elements.source_readback]
    matching_supported := by
      rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
      exact elements.matching_supported
    inputOccurrences := elements.inputOccurrences
    constructorOccurrences := (path, selected.index) :: elements.constructorOccurrences }
    (congrArg TypeExpr.base selected.categorized)

private theorem variableIndex_injected {S : Signature} :
    ∀ {locals : Ctx S} {sort : S.Srt} (position : Var locals sort),
      variableIndex (injPrefix (S := S) (Γ := []) locals position) = variableIndex position
  | _, _, .zero => rfl
  | _, _, .succ position => congrArg Nat.succ (variableIndex_injected position)

/-- One-step assembly for the existing raw source traversal. The family fixes
which evidence each consumer retains, while recursion and physical child
addresses are supplied by the single fuelled walker. -/
structure Assembly (family : List TypeExpr → Pattern → TypeExpr → Type) where
  bound : (locals : List TypeExpr) → (index : Nat) → (sort : TypeExpr) →
    Option (family locals (.bvar index) sort)
  free : (locals : List TypeExpr) → (path : List Nat) → (name : String) → (sort : TypeExpr) →
    Option (family locals (.fvar name) sort)
  constructor :
    ((locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
      Option (family locals source sort)) →
    (locals : List TypeExpr) → (path : List Nat) → (label : String) →
    (sources : List Pattern) → (sort : TypeExpr) →
      Option (family locals (.apply label sources) sort)
  abstraction : {locals : List TypeExpr} → {source : Pattern} → {domain codomain : TypeExpr} →
    family (domain :: locals) source codomain →
      family locals (.lambda none source) (.arrow domain codomain)
  multiAbstraction : {locals : List TypeExpr} → {source : Pattern} → {domain codomain : TypeExpr} →
    (count : Nat) → family (List.replicate count domain ++ locals) source codomain →
      family locals (.multiLambda count [] source) (.arrow (.multiBinder domain) codomain)
  substitution :
    ((locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
      Option (family locals source sort)) →
    (locals : List TypeExpr) → (path : List Nat) → (body replacement : Pattern) → (sort : TypeExpr) →
      Option (family locals (.subst body replacement) sort)
  vector :
    ((locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
      Option (family locals source sort)) →
    (locals : List TypeExpr) → (path : List Nat) → (sources : List Pattern) → (sort : TypeExpr) →
      Option (family locals (.collection .vec sources none) sort)

/-- One structural source step delegates all smaller calls through the
supplied recursion, retaining the physical addresses of the original pattern. -/
def Assembly.step {family : List TypeExpr → Pattern → TypeExpr → Type}
    (assembly : Assembly family)
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) → Option (family locals source sort)) :
    (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) → Option (family locals source sort)
  | locals, _, .bvar index, sort => assembly.bound locals index sort
  | locals, path, .fvar name, sort => assembly.free locals path name sort
  | locals, path, .apply label sources, sort =>
      assembly.constructor compile locals path label sources sort
  | locals, path, .lambda none source, .arrow domain codomain => do
      let body ← compile (domain :: locals) (path ++ [0]) source codomain
      pure (assembly.abstraction body)
  | locals, path, .multiLambda count [] source, .arrow (.multiBinder domain) codomain => do
      let body ← compile (List.replicate count domain ++ locals) (path ++ [0]) source codomain
      pure (assembly.multiAbstraction count body)
  | locals, path, .subst body replacement, sort =>
      assembly.substitution compile locals path body replacement sort
  | locals, path, .collection .vec sources none, sort => assembly.vector compile locals path sources sort
  | _, _, _, _ => none

/-- Fuelled recursion is shared by the input and output assemblies. -/
def Assembly.walk {family : List TypeExpr → Pattern → TypeExpr → Type}
    (assembly : Assembly family) : Nat → (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) → Option (family locals source sort)
  | 0 => fun _ _ _ _ => none
  | fuel + 1 => assembly.step (assembly.walk fuel)

private theorem prefix_index {S : Signature} :
    ∀ {locals : Ctx S} {sort : S.Srt} (position : Var locals sort),
      variableIndex (injPrefix (S := S) (Γ := []) locals position) = variableIndex position
  | _, _, .zero => rfl
  | _, _, .succ old => congrArg Nat.succ (prefix_index old)

abbrev CompiledSchema.bound {locals : List TypeExpr} {index : Nat} {sort : TypeExpr}
    (position : Var locals sort)
    (atIndex : variableIndex position = index) :
    CompiledSchema language rule spec locals (.bvar index) sort where
  term := .var (injPrefix (S := SchemaSignature language rule spec) (Γ := []) locals position)
  source_readback := by
    change Pattern.bvar (variableIndex (injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position)) = Pattern.bvar index
    rw [prefix_index (S := SchemaSignature language rule spec) position, atIndex]
  matching_supported := by
    rw [MatchingSupportedT.eq_def (S := signatureOf language) (M := metaArities rule spec)]
    trivial
  inputOccurrences := []
  constructorOccurrences := []

/-- Input matching retains exactly its established injective-spine evidence.
The output operation does not weaken this assembly. -/
def inputAssembly (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) : Assembly (CompiledSchema language rule spec) where
  bound locals index sort :=
    match found : boundPosition? locals index sort with
    | none => none
    | some position => some (CompiledSchema.bound position (boundPosition?_index locals index sort found))
  free locals path name sort := do
    let input ← elaborateInputOccurrence? language rule spec locals site path name sort
    pure (CompiledSchema.ofInput input)
  constructor compile locals path label sources sort := do
    let selected ← selectConstructor? language label
    if same : TypeExpr.base (language.terms.get selected.index).category = sort then
      if notBare : usesBareCollection? (language.terms.get selected.index) = false then
        let arguments ← compileConstructorArguments? compile locals path 0
          (language.terms.get selected.index).params sources
        let ordinary : ¬ UsesBareCollection (language.terms.get selected.index) := by
          intro bare
          have checked := (usesBareCollection?_eq_true_iff _).mpr bare
          rw [notBare] at checked
          cases checked
        pure ((CompiledSchema.constructor path selected ordinary arguments).castSort same)
      else none
    else none
  abstraction := CompiledSchema.lambda
  multiAbstraction := CompiledSchema.multiLambda
  substitution _ _ _ _ _ _ := none
  vector compile locals path sources sort :=
    match sort with
    | .collection .vec elementSort => do
        let elements ← compileVectorElements? compile locals path 0 elementSort sources
        pure (CompiledSchema.vector elements)
    | .base category => do
        let selected ← selectVectorConstructor? language category
        let elements ← compileVectorElements? compile locals path 0 selected.elementSort sources
        pure (CompiledSchema.vectorConstructor path selected elements)
    | _ => none

/-- Input matching specializes the common source traversal. Its assembly
retains the established inverse-spine checks and occurrence receipts. -/
def compileSchemaWithFuel? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) :
    Nat → (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort) :=
  (inputAssembly language rule spec site).walk

private theorem compileSchemaWithFuel?_zero (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (locals : List TypeExpr) (path : List Nat)
    (source : Pattern) (sort : TypeExpr) :
    compileSchemaWithFuel? language rule spec site 0 locals path source sort = none := rfl

private theorem compileSchemaWithFuel?_succ (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (fuel : Nat)
    (locals : List TypeExpr) (path : List Nat) (source : Pattern) (sort : TypeExpr) :
    compileSchemaWithFuel? language rule spec site (fuel + 1) locals path source sort =
      (inputAssembly language rule spec site).step
        (compileSchemaWithFuel? language rule spec site fuel) locals path source sort := rfl

/-- An induction algebra for the one shared source traversal. Each law only
receives already established results for smaller source calls. -/
structure Assembly.Invariant {family : List TypeExpr → Pattern → TypeExpr → Type}
    (assembly : Assembly family)
    (property : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) → family locals source sort → Prop) : Prop where
  bound : ∀ locals path index sort compiled, assembly.bound locals index sort = some compiled →
    property locals path (.bvar index) sort compiled
  free : ∀ locals path name sort compiled, assembly.free locals path name sort = some compiled →
    property locals path (.fvar name) sort compiled
  constructor : ∀ compile,
    (∀ locals path source sort compiled, compile locals path source sort = some compiled →
      property locals path source sort compiled) →
    ∀ locals path label sources sort compiled,
      assembly.constructor compile locals path label sources sort = some compiled →
        property locals path (.apply label sources) sort compiled
  abstraction : ∀ locals path source domain codomain body,
    property (domain :: locals) (path ++ [0]) source codomain body →
      property locals path (.lambda none source) (.arrow domain codomain) (assembly.abstraction body)
  multiAbstraction : ∀ locals path source domain codomain count body,
    property (List.replicate count domain ++ locals) (path ++ [0]) source codomain body →
      property locals path (.multiLambda count [] source) (.arrow (.multiBinder domain) codomain)
        (assembly.multiAbstraction count body)
  substitution : ∀ compile,
    (∀ locals path source sort compiled, compile locals path source sort = some compiled →
      property locals path source sort compiled) →
    ∀ locals path body replacement sort compiled,
      assembly.substitution compile locals path body replacement sort = some compiled →
        property locals path (.subst body replacement) sort compiled
  vector : ∀ compile,
    (∀ locals path source sort compiled, compile locals path source sort = some compiled →
      property locals path source sort compiled) →
    ∀ locals path sources sort compiled,
      assembly.vector compile locals path sources sort = some compiled →
        property locals path (.collection .vec sources none) sort compiled

theorem Assembly.walk_invariant {family : List TypeExpr → Pattern → TypeExpr → Type}
    {assembly : Assembly family}
    {property : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) → family locals source sort → Prop}
    (laws : assembly.Invariant property) :
    ∀ fuel locals path source sort compiled,
      assembly.walk fuel locals path source sort = some compiled →
        property locals path source sort compiled := by
  intro fuel
  induction fuel with
  | zero => intro locals path source sort compiled found; cases found
  | succ fuel children =>
      intro locals path source sort compiled found
      cases source with
      | bvar index => exact laws.bound locals path index sort compiled found
      | fvar name => exact laws.free locals path name sort compiled found
      | apply label sources => exact laws.constructor _ children locals path label sources sort compiled found
      | lambda annotation body =>
          cases annotation with
          | some name => cases found
          | none =>
              cases sort with
              | base name => cases found
              | multiBinder domain => cases found
              | collection kind element => cases found
              | arrow domain codomain =>
                  simp only [Assembly.walk, Assembly.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
                  obtain ⟨body, bodyFound, same⟩ := found
                  cases same
                  exact laws.abstraction locals path _ domain codomain body
                    (children _ _ _ _ body bodyFound)
      | multiLambda count names body =>
          cases names with
          | cons name names => cases found
          | nil =>
              cases sort with
              | base name => cases found
              | multiBinder domain => cases found
              | collection kind element => cases found
              | arrow domain codomain =>
                  cases domain with
                  | base name => cases found
                  | arrow first last => cases found
                  | collection kind element => cases found
                  | multiBinder domain =>
                      simp only [Assembly.walk, Assembly.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
                      obtain ⟨body, bodyFound, same⟩ := found
                      cases same
                      exact laws.multiAbstraction locals path _ domain codomain count body
                        (children _ _ _ _ body bodyFound)
      | subst body replacement => exact laws.substitution _ children locals path body replacement sort compiled found
      | collection kind sources rest =>
          cases kind with
          | hashBag => cases found
          | hashSet => cases found
          | vec =>
              cases rest with
              | some name => cases found
              | none => exact laws.vector _ children locals path sources sort compiled found


/-- An observation of a successfully compiled node at its original source site. -/
abbrev InputObservation (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :=
  (locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
    CompiledSchema language rule spec locals source sort → Prop

abbrev InputCompiler (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :=
  (locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
    Option (CompiledSchema language rule spec locals source sort)

def InputCompiler.Establishes (compile : InputCompiler language rule spec)
    (observe : InputObservation language rule spec) : Prop :=
  ∀ locals path source sort compiled,
    compile locals path source sort = some compiled → observe locals path source sort compiled

/-- Local laws for the input compiler. Its declaration, sort, scope, and
representation checks are inverted once, while each observation supplies
its own law for the assembled, ordered result. -/
structure InputAssemblyInvariant (site : RulePatternSite)
    (observe : InputObservation language rule spec) : Prop where
  bound : ∀ locals path index sort (position : Var locals sort),
    (found : boundPosition? locals index sort = some position) →
      observe locals path (.bvar index) sort
        (CompiledSchema.bound position (boundPosition?_index locals index sort found))
  free : ∀ locals path name sort
    (input : CompiledInputOccurrence language rule spec locals site path name sort),
      observe locals path (.fvar name) sort (CompiledSchema.ofInput input)
  constructor : ∀ (compile : InputCompiler language rule spec), InputCompiler.Establishes compile observe →
    ∀ locals path label sources (selected : SelectedConstructor language label)
      (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
      (arguments : CompiledConstructorArguments language rule spec locals
        (language.terms.get selected.index).params sources),
      compileConstructorArguments? compile locals path 0
        (language.terms.get selected.index).params sources = some arguments →
        observe locals path (.apply label sources) (.base (language.terms.get selected.index).category)
          (CompiledSchema.constructor path selected ordinary arguments)
  abstraction : ∀ locals path source domain codomain body,
    observe (domain :: locals) (path ++ [0]) source codomain body →
      observe locals path (.lambda none source) (.arrow domain codomain) (CompiledSchema.lambda body)
  multiAbstraction : ∀ locals path source domain codomain count body,
    observe (List.replicate count domain ++ locals) (path ++ [0]) source codomain body →
      observe locals path (.multiLambda count [] source) (.arrow (.multiBinder domain) codomain)
        (CompiledSchema.multiLambda count body)
  vector : ∀ (compile : InputCompiler language rule spec), InputCompiler.Establishes compile observe →
    ∀ locals path sources elementSort (elements : CompiledVectorElements language rule spec
      locals sources elementSort),
      compileVectorElements? compile locals path 0 elementSort sources = some elements →
        observe locals path (.collection .vec sources none) (.collection .vec elementSort)
          (CompiledSchema.vector elements)
  namedVector : ∀ (compile : InputCompiler language rule spec), InputCompiler.Establishes compile observe →
    ∀ locals path sources category (selected : SelectedVectorConstructor language category)
      (elements : CompiledVectorElements language rule spec locals sources selected.elementSort),
      compileVectorElements? compile locals path 0 selected.elementSort sources = some elements →
        observe locals path (.collection .vec sources none) (.base category)
          (CompiledSchema.vectorConstructor path selected elements)

theorem InputAssemblyInvariant.toAssemblyInvariant {site : RulePatternSite}
    {observe : InputObservation language rule spec} (laws : InputAssemblyInvariant site observe) :
    (inputAssembly language rule spec site).Invariant observe where
  bound locals path index sort compiled found := by
    dsimp only [inputAssembly] at found
    split at found
    · contradiction
    · rename_i position admitted
      cases Option.some.inj found
      exact laws.bound locals path index sort position admitted
  free locals path name sort compiled found := by
    simp only [inputAssembly, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
    obtain ⟨input, _, assembled⟩ := found
    cases Option.some.inj assembled
    exact laws.free locals path name sort input
  constructor compile children locals path label sources sort compiled found := by
    simp only [inputAssembly, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
    obtain ⟨selected, _, assembled⟩ := found
    split at assembled
    · rename_i same
      subst sort
      split at assembled
      · rename_i notBare
        simp only [Option.bind_eq_some_iff] at assembled
        obtain ⟨arguments, argumentsFound, sameResult⟩ := assembled
        cases Option.some.inj sameResult
        exact laws.constructor compile children locals path label sources selected
          (by
            intro bare
            have checked := (usesBareCollection?_eq_true_iff _).mpr bare
            rw [notBare] at checked
            cases checked)
          arguments argumentsFound
      · contradiction
    · contradiction
  abstraction := laws.abstraction
  multiAbstraction := laws.multiAbstraction
  substitution _ _ _ _ _ _ _ _ found := by cases found
  vector compile children locals path sources sort compiled found := by
    cases sort with
    | arrow first last => cases found
    | multiBinder domain => cases found
    | base category =>
        simp only [inputAssembly, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
        obtain ⟨selected, _, elements, elementsFound, assembled⟩ := found
        cases Option.some.inj assembled
        exact laws.namedVector compile children locals path sources category selected elements elementsFound
    | collection kind elementSort =>
        cases kind with
        | hashBag => cases found
        | hashSet => cases found
        | vec =>
            simp only [inputAssembly, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
            obtain ⟨elements, elementsFound, assembled⟩ := found
            cases Option.some.inj assembled
            exact laws.vector compile children locals path sources elementSort elements elementsFound

theorem InputAssemblyInvariant.walk {site : RulePatternSite}
    {observe : InputObservation language rule spec} (laws : InputAssemblyInvariant site observe)
    (fuel : Nat) : InputCompiler.Establishes (compileSchemaWithFuel? language rule spec site fuel) observe :=
  Assembly.walk_invariant laws.toAssemblyInvariant fuel

/-- Successful parameter traversal forms an ordered list of exact child calls.
The step law receives the parameter decoder, original address, and smaller
result, so it can use the actual binder scope of each child. -/
theorem compileConstructorArguments?_observes (compile : InputCompiler language rule spec)
    (locals : List TypeExpr) (path : List Nat)
    (observe : (offset : Nat) → {parameters : List TermParam} → {sources : List Pattern} →
      CompiledConstructorArguments language rule spec locals parameters sources → Prop)
    (empty : ∀ offset, observe offset (.nil language rule spec locals))
    (step : ∀ {offset parameter parameters source sources}
      (body : ParameterBody parameter source)
      (head : CompiledSchema language rule spec (body.binders ++ locals) body.body body.sort)
      (tail : CompiledConstructorArguments language rule spec locals parameters sources),
      parameterBody? parameter source = some body →
      compile (body.binders ++ locals) (path ++ [offset] ++ body.pathSuffix) body.body body.sort = some head →
      observe (offset + 1) tail → observe offset (.cons body head tail)) :
    ∀ sources offset parameters (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        observe offset arguments := by
  intro sources
  induction sources with
  | nil =>
      intro offset parameters arguments found
      cases parameters with
      | nil =>
          cases Option.some.inj found
          exact empty offset
      | cons parameter parameters => cases found
  | cons source sources children =>
      intro offset parameters arguments found
      cases parameters with
      | nil => cases found
      | cons parameter parameters =>
          simp only [compileConstructorArguments?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
          obtain ⟨body, bodyFound, head, headFound, tail, tailFound, assembled⟩ := found
          cases Option.some.inj assembled
          exact step body head tail bodyFound headFound (children _ _ tail tailFound)

/-- Literal vectors retain the ordered offset of every child, including two
physically distinct occurrences of the same source term. -/
theorem compileVectorElements?_observes (compile : InputCompiler language rule spec)
    (locals : List TypeExpr) (path : List Nat) (elementSort : TypeExpr)
    (observe : (offset : Nat) → {sources : List Pattern} →
      CompiledVectorElements language rule spec locals sources elementSort → Prop)
    (empty : ∀ offset, observe offset (.nil language rule spec locals elementSort))
    (step : ∀ {offset source sources}
      (head : CompiledSchema language rule spec locals source elementSort)
      (tail : CompiledVectorElements language rule spec locals sources elementSort),
      compile locals (path ++ [offset]) source elementSort = some head →
      observe (offset + 1) tail → observe offset (.cons head tail)) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources elementSort),
      compileVectorElements? compile locals path offset elementSort sources = some elements → observe offset elements := by
  intro sources
  induction sources with
  | nil =>
      intro offset elements found
      cases Option.some.inj found
      exact empty offset
  | cons source sources children =>
      intro offset elements found
      simp only [compileVectorElements?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨head, headFound, tail, tailFound, assembled⟩ := found
      cases Option.some.inj assembled
      exact step head tail headFound (children _ tail tailFound)

/-- Success exposes exact source readback and the existing matcher profile.
Both proofs are constructed by the codec; neither is a caller premise. -/
theorem compileSchemaWithFuel?_sound {fuel : Nat} {locals : List TypeExpr}
    {site : RulePatternSite} {path : List Nat} {source : Pattern} {sort : TypeExpr}
    {compiled : CompiledSchema language rule spec locals source sort}
    (_accepted : compileSchemaWithFuel? language rule spec site fuel locals path source sort =
      some compiled) :
    readback compiled.term = source ∧
      MatchingSupportedT (S := signatureOf language) (M := metaArities rule spec)
        (Γ := []) locals compiled.term := by
  exact ⟨compiled.source_readback, compiled.matching_supported⟩

mutual
/-- A finite structural recursion budget computed from the original source.
It is independent of declarations, candidate selection and semantic success. -/
def sourceHeight : Pattern → Nat
  | .bvar _ | .fvar _ => 1
  | .apply _ arguments => sourceListHeight arguments + 1
  | .lambda _ body | .multiLambda _ _ body => sourceHeight body + 1
  | .subst body replacement => max (sourceHeight body) (sourceHeight replacement) + 1
  | .collection _ elements _ => sourceListHeight elements + 1

def sourceListHeight : List Pattern → Nat
  | [] => 0
  | head :: tail => max (sourceHeight head) (sourceListHeight tail)
end

/-- A whole side retains its physical rewrite, attached binding specification,
original premises and independently checked source typing. No premise is
removed or reinterpreted by this term-elaboration boundary. -/
structure AuthoredSchema (language : LanguageDef) (ruleIndex : Fin language.rewrites.length)
    (site : RulePatternSite) (sort : TypeExpr) where
  spec : RuleBindingSpec
  attached : (language.rewrites.get ruleIndex).bindings = some spec
  admitted : admittedFor (language.rewrites.get ruleIndex) spec = true
  sortsDeclared : dependencySortsDeclared language spec = true
  source : Pattern
  atSite : sitePattern? (language.rewrites.get ruleIndex) site = some source
  compiled : CompiledSchema language (language.rewrites.get ruleIndex) spec [] source sort
  source_typed : HasType language
    (FreeTypeContext.ofList (language.rewrites.get ruleIndex).typeContext) [] source sort

/-- The public entry starts in the actual side's empty binder context. Nested
contexts come from declaration scopes and structural binder types, while the
original source checker supplies a separate typing derivation. -/
def elaborateAuthoredSchema? (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (site : RulePatternSite) (sort : TypeExpr) :
    Option (AuthoredSchema language ruleIndex site sort) := do
  let rule := language.rewrites.get ruleIndex
  let spec ← rule.bindings
  if attached : rule.bindings = some spec then
    if admitted : admittedFor rule spec = true then
      if declared : dependencySortsDeclared language spec = true then
        match site with
        | .left | .right =>
            match atSite : sitePattern? rule site with
            | none => none
            | some source =>
                if typed : checkHasType language (FreeTypeContext.ofList rule.typeContext)
                    [] source sort = true then
                  let compiled ← compileSchemaWithFuel? language rule spec site
                    (sourceHeight source) [] [] source sort
                  pure {
                    spec := spec
                    attached := attached
                    admitted := admitted
                    sortsDeclared := declared
                    source := source
                    atSite := atSite
                    compiled := compiled
                    source_typed := checkHasType_sound typed }
                else none
        | .premise _ _ _ => none
      else none
    else none
  else none

/-- Computed whole-side admission implies typing in the original source
judgment and exact readback from the declaration-derived intrinsic schema. -/
theorem elaborateAuthoredSchema?_source {ruleIndex : Fin language.rewrites.length}
    {site : RulePatternSite} {sort : TypeExpr}
    {compiled : AuthoredSchema language ruleIndex site sort}
    (_accepted : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    sitePattern? (language.rewrites.get ruleIndex) site = some (readback compiled.compiled.term) ∧
      HasType language (FreeTypeContext.ofList (language.rewrites.get ruleIndex).typeContext)
        [] (readback compiled.compiled.term) sort := by
  rw [compiled.compiled.source_readback]
  exact ⟨compiled.atSite, compiled.source_typed⟩

def emptySubstitution (language : LanguageDef) : Sub (signatureOf language) [] [] :=
  fun _ position => nomatch position

theorem emptySubstitution_eq_identity :
    emptySubstitution language = (fun _ position => Term.var position) := by
  funext sort position
  exact nomatch position

/-- Existing typed recursive matching is exact on every computed schema.
The capture and assignment agreement remain the original `MExtends` relation;
this boundary adds no evaluator or operational rule semantics. -/
theorem CompiledSchema.matching_adequate {locals : List TypeExpr} {source : Pattern}
    {sort : TypeExpr}
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    (compiled : CompiledSchema language rule spec locals source sort)
    (initial : MAcc (signatureOf language) (metaArities rule spec) [])
    (target : Term (signatureOf language) (locals ++ []) sort)
    (bodies : (index : Fin (metaArities (language := language) rule spec).length) →
      Term (signatureOf language) ((metaArities rule spec).get index).1
        ((metaArities rule spec).get index).2)
    (realizes : MExtends (emptySubstitution language) bodies initial) :
    (∃ final, smatchAtT locals initial compiled.term target = some final ∧
      MExtends (emptySubstitution language) bodies final) ↔
      bind (liftSub (emptySubstitution language) locals)
        (instantiate bodies compiled.term) = target :=
  smatchAtT_adequate locals initial compiled.term target compiled.matching_supported
    (emptySubstitution language) bodies realizes

section OrderedSupport

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (OrderedPattern)

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem ParameterScope.ordered {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort) {body : Pattern}
    (supported : OrderedPattern body) : OrderedPattern (scope.wrap body) := by
  cases scope with
  | simple name sort => exact supported
  | abstraction binder name domain codomain => exact .lambda none body supported
  | abstractionBase binder name sort => exact .lambda none body supported
  | multiAbstraction binders name domain codomain count => exact .multiLambda count [] body supported
  | multiAbstractionBase binders name sort count => exact .multiLambda count [] body supported

private theorem constructor_children_ordered (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec)
    (compile : (locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
      Option (CompiledSchema language rule spec locals source sort))
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → OrderedPattern source)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
      ∀ source ∈ sources, OrderedPattern source := by
  intro sources
  induction sources with
  | nil => intro offset parameters arguments found source member; cases member
  | cons source sources induction =>
      intro offset parameters arguments found pattern member
      cases parameters with
      | nil => simp [compileConstructorArguments?] at found
      | cons parameter parameters =>
          cases bodyFound : parameterBody? parameter source with
          | none => simp [compileConstructorArguments?, bodyFound] at found
          | some body =>
              cases headFound : compile (body.binders ++ locals)
                  (path ++ [offset] ++ body.pathSuffix) body.body body.sort with
              | none =>
                  simp only [compileConstructorArguments?, bodyFound, headFound,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at found
              | some head =>
                  cases tailFound : compileConstructorArguments? compile locals path
                      (offset + 1) parameters sources with
                  | none =>
                      simp only [compileConstructorArguments?, bodyFound, headFound, tailFound,
                        Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at found
                  | some tail =>
                      rcases List.mem_cons.mp member with same | member
                      · subst pattern
                        rw [← body.source_readback]
                        exact ParameterScope.ordered body.scope (children _ _ _ _ head headFound)
                      · exact induction (offset + 1) parameters tail tailFound pattern member

private theorem vector_children_ordered (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec)
    (compile : (locals : List TypeExpr) → (path : List Nat) → (source : Pattern) → (sort : TypeExpr) →
      Option (CompiledSchema language rule spec locals source sort))
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → OrderedPattern source)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources sort),
      compileVectorElements? compile locals path offset sort sources = some elements →
      ∀ source ∈ sources, OrderedPattern source := by
  intro sources
  induction sources with
  | nil => intro offset elements found source member; cases member
  | cons source sources induction =>
      intro offset elements found pattern member
      cases headFound : compile locals (path ++ [offset]) source sort with
      | none =>
          simp only [compileVectorElements?, headFound, Option.bind_eq_bind,
            Option.bind_none, reduceCtorEq] at found
      | some head =>
          cases tailFound : compileVectorElements? compile locals path (offset + 1) sort sources with
          | none =>
              simp only [compileVectorElements?, headFound, tailFound, Option.bind_eq_bind,
                Option.bind_some, Option.bind_none, reduceCtorEq] at found
          | some tail =>
              rcases List.mem_cons.mp member with same | member
              · subst pattern; exact children _ _ _ _ head headFound
              · exact induction (offset + 1) tail tailFound pattern member

/-- Structural support is earned from the actual declaration-derived source
compiler. In particular its refusal of unordered collections and rests is
retained, rather than supplied as a typing assumption to the native matcher. -/
theorem compileSchemaWithFuel?_ordered (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
      OrderedPattern source := by
  refine InputAssemblyInvariant.walk (observe := fun _ _ source _ _ => OrderedPattern source) ?_ fuel
  exact {
    bound := fun _ _ index _ _ _ => .bvar index
    free := fun _ _ name _ _ => .fvar name
    constructor := fun compile children locals path label sources selected _ arguments found =>
      .apply label sources (constructor_children_ordered language rule spec compile children
        locals path sources 0 (language.terms.get selected.index).params arguments found)
    abstraction := fun _ _ source _ _ _ ordered => .lambda none source ordered
    multiAbstraction := fun _ _ source _ _ count _ ordered => .multiLambda count [] source ordered
    vector := fun compile children locals path sources elemSort elements found =>
      .vector sources none (vector_children_ordered language rule spec compile children
        locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      .vector sources none (vector_children_ordered language rule spec compile children
        locals path selected.elementSort sources 0 elements found) }

/-- Successful authored-side admission exposes the exact compilation it ran. -/
theorem elaborateAuthoredSchema?_compilation {ruleIndex : Fin language.rewrites.length}
    {site : RulePatternSite} {sort : TypeExpr} (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    compileSchemaWithFuel? language (language.rewrites.get ruleIndex) compiled.spec site
      (sourceHeight compiled.source) [] [] compiled.source sort = some compiled.compiled := by
  cases site with
  | premise index argument depth => simp [elaborateAuthoredSchema?] at found
  | left =>
      cases bindings : (language.rewrites.get ruleIndex).bindings with
      | none =>
          simp only [elaborateAuthoredSchema?, bindings, Option.bind_eq_bind,
            Option.bind_none, reduceCtorEq] at found
      | some spec =>
          simp only [elaborateAuthoredSchema?, bindings, Option.bind_eq_bind,
            Option.bind_some, Mettapedia.OSLF.MeTTaIL.RuleBinding.sitePattern?] at found
          split at found
          · split at found
            · split at found
              · split at found
                · cases actualFound : compileSchemaWithFuel? language (language.rewrites.get ruleIndex)
                      spec .left (sourceHeight (language.rewrites.get ruleIndex).left)
                      [] [] (language.rewrites.get ruleIndex).left sort with
                  | none => simp only [actualFound, Option.bind_none, reduceCtorEq] at found
                  | some actual =>
                      simp only [actualFound, Option.bind_some, pure, Option.some.injEq] at found
                      cases found
                      exact actualFound
                · simp only [reduceCtorEq] at found
              · simp only [reduceCtorEq] at found
            · simp only [reduceCtorEq] at found
          · simp only [reduceCtorEq] at found
  | right =>
      cases bindings : (language.rewrites.get ruleIndex).bindings with
      | none =>
          simp only [elaborateAuthoredSchema?, bindings, Option.bind_eq_bind,
            Option.bind_none, reduceCtorEq] at found
      | some spec =>
          simp only [elaborateAuthoredSchema?, bindings, Option.bind_eq_bind,
            Option.bind_some, Mettapedia.OSLF.MeTTaIL.RuleBinding.sitePattern?] at found
          split at found
          · split at found
            · split at found
              · split at found
                · cases actualFound : compileSchemaWithFuel? language (language.rewrites.get ruleIndex)
                      spec .right (sourceHeight (language.rewrites.get ruleIndex).right)
                      [] [] (language.rewrites.get ruleIndex).right sort with
                  | none => simp only [actualFound, Option.bind_none, reduceCtorEq] at found
                  | some actual =>
                      simp only [actualFound, Option.bind_some, pure, Option.some.injEq] at found
                      cases found
                      exact actualFound
                · simp only [reduceCtorEq] at found
              · simp only [reduceCtorEq] at found
            · simp only [reduceCtorEq] at found
          · simp only [reduceCtorEq] at found

/-- The original whole-rule admission and source checker are executed by the
existing authored-schema compiler; their successful result earns traversal
support without deleting metadata or adding a target-only typing hypothesis. -/
theorem elaborateAuthoredSchema?_ordered (language : LanguageDef)
    {ruleIndex : Fin language.rewrites.length} {site : RulePatternSite} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    OrderedPattern compiled.source := by
  exact compileSchemaWithFuel?_ordered language _ compiled.spec site _ _ _ _ _ compiled.compiled
    (elaborateAuthoredSchema?_compilation compiled found)

end OrderedSupport

end SchemaElaboration

namespace TargetReification

open SchemaElaboration
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- The partial inverse uses the existing object signature and embedding.
Its witness records the exact typed context and result sort. -/
structure ObjectProjection {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt}
    (source : Term (withMetas S M) bound sort) where
  term : Term S bound sort
  embedding : embed term = source

structure ObjectArgumentsProjection {S : Signature} {M : List (MetaArity S)}
    {arity : List (Ctx S × S.Srt)} {bound : Ctx S}
    (source : Args (withMetas S M) arity bound) where
  arguments : Args S arity bound
  embedding : embedArgs arguments = source

mutual
/-- Reject contextual metavariable operators rather than choosing arbitrary
object bodies for them. Every rigid operator retains its original authority. -/
def projectObject? {S : Signature} {M : List (MetaArity S)} :
    {bound : Ctx S} → {sort : S.Srt} →
      (source : Term (withMetas S M) bound sort) → Option (ObjectProjection source)
  | _, _, .var position => some { term := .var position, embedding := rfl }
  | _, _, .op (.inr _) _ => none
  | _, _, .op (.inl operator) arguments => do
      let projected ← projectObjectArguments? arguments
      pure {
        term := .op operator projected.arguments
        embedding := by
          change Term.op (S := withMetas S M) (.inl operator) (embedArgs projected.arguments) = _
          rw [projected.embedding] }
termination_by _ _ source => 2 * termSize source
decreasing_by
  simp only [termSize]
  omega

def projectObjectArguments? {S : Signature} {M : List (MetaArity S)} :
    {arity : List (Ctx S × S.Srt)} → {bound : Ctx S} →
      (source : Args (withMetas S M) arity bound) →
        Option (ObjectArgumentsProjection source)
  | _, _, .nil => some { arguments := .nil, embedding := rfl }
  | _, _, .cons head tail => do
      let projectedHead ← projectObject? head
      let projectedTail ← projectObjectArguments? tail
      pure {
        arguments := .cons projectedHead.term projectedTail.arguments
        embedding := by
          change Args.cons (embed projectedHead.term) (embedArgs projectedTail.arguments) = _
          rw [projectedHead.embedding, projectedTail.embedding] }
termination_by _ _ source => 2 * argsSize source + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

mutual
/-- Projection really inverts the existing embedding; it does not normalize
operator names, binder contexts or argument order. -/
theorem projectObject?_embed {S : Signature} {M : List (MetaArity S)} :
    ∀ {bound : Ctx S} {sort : S.Srt} (term : Term S bound sort),
      projectObject? (embed (M := M) term) = some { term := term, embedding := rfl }
  | _, _, .var _ => by simp only [embed, projectObject?]
  | _, _, .op operator arguments => by
      simp only [embed, projectObject?, projectObjectArguments?_embed (M := M) arguments,
        Option.bind_eq_bind, Option.bind_some, pure]
termination_by _ _ term => 2 * termSize term
decreasing_by
  simp only [termSize]
  omega

theorem projectObjectArguments?_embed {S : Signature} {M : List (MetaArity S)} :
    ∀ {arity : List (Ctx S × S.Srt)} {bound : Ctx S} (arguments : Args S arity bound),
      projectObjectArguments? (embedArgs (M := M) arguments) =
        some { arguments := arguments, embedding := rfl }
  | _, _, .nil => by simp only [embedArgs, projectObjectArguments?]
  | _, _, .cons head tail => by
      simp only [embedArgs, projectObjectArguments?, projectObject?_embed (M := M) head,
        projectObjectArguments?_embed (M := M) tail, Option.bind_eq_bind, Option.bind_some, pure]
termination_by _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

theorem projectObject?_isSome_iff {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} (source : Term (withMetas S M) bound sort) :
    (projectObject? source).isSome = true ↔
      ∃ object : Term S bound sort, embed (M := M) object = source := by
  constructor
  · intro accepted
    cases found : projectObject? source with
    | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at accepted
    | some projected => exact ⟨projected.term, projected.embedding⟩
  · rintro ⟨object, rfl⟩
    rw [projectObject?_embed]
    rfl

theorem projectObject?_none_iff {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} (source : Term (withMetas S M) bound sort) :
    projectObject? source = none ↔
      ¬ ∃ object : Term S bound sort, embed (M := M) object = source := by
  rw [← projectObject?_isSome_iff]
  cases projectObject? source <;> simp

/-- Forget only the proof fields of the checked projection. -/
def objectTerm? {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} (source : Term (withMetas S M) bound sort) :
    Option (Term S bound sort) := (projectObject? source).map (·.term)

theorem objectTerm?_embed {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} (term : Term S bound sort) :
    objectTerm? (embed (M := M) term) = some term := by
  rw [objectTerm?, projectObject?_embed]
  rfl

theorem objectProjection_injective {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} {first second : Term S bound sort}
    (same : embed (M := M) first = embed second) : first = second := by
  have decoded := congrArg (objectTerm? (S := S) (M := M)) same
  rw [objectTerm?_embed, objectTerm?_embed] at decoded
  exact Option.some.inj decoded

theorem ObjectProjection.unique {S : Signature} {M : List (MetaArity S)}
    {bound : Ctx S} {sort : S.Srt} {source : Term (withMetas S M) bound sort}
    (first second : ObjectProjection source) : first.term = second.term :=
  objectProjection_injective (first.embedding.trans second.embedding.symm)

mutual
/-- Readback of an embedded object is the existing object erasure, for all
operators. Restricting their source profile belongs to the checked codec. -/
theorem readback_embed {rule : RewriteRule} {spec : RuleBindingSpec} :
    ∀ {bound : List TypeExpr} {sort : TypeExpr}
      (term : Term (signatureOf language) bound sort),
      readback (rule := rule) (spec := spec) (embed term) = erase term
  | _, _, .var _ => rfl
  | _, _, .op (.constructor _ _ _ scopes) arguments => by
      exact congrArg (Pattern.apply _) (readbackConstructorArguments_embed scopes arguments)
  | _, _, .op (.collectionConstructor _ _ _ kind _ _ _) arguments => by
      exact congrArg (fun elements => Pattern.collection kind elements none)
        (readbackArguments_embed arguments)
  | _, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => congrArg (Pattern.lambda none) (readback_embed body)
  | _, _, .op (.multiLambda _ _ count) arguments =>
      match arguments with
      | .cons body .nil => congrArg (Pattern.multiLambda count []) (readback_embed body)
  | _, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) =>
          congrArg₂ Pattern.subst (readback_embed body) (readback_embed replacement)
  | _, _, .op (.collection kind _ _) arguments => by
      exact congrArg (fun elements => Pattern.collection kind elements none)
        (readbackArguments_embed arguments)
termination_by _ _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

theorem readbackArguments_embed {rule : RewriteRule} {spec : RuleBindingSpec} :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) arity bound),
      readbackArguments (rule := rule) (spec := spec) (embedArgs arguments) =
        eraseArguments arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ List.cons (readback_embed head) (readbackArguments_embed tail)
termination_by _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

theorem readbackConstructorArguments_embed {rule : RewriteRule} {spec : RuleBindingSpec} :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      readbackConstructorArguments (rule := rule) (spec := spec) scopes (embedArgs arguments) =
        eraseConstructorArguments scopes arguments
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons scope scopes, .cons head tail =>
      congrArg₂ List.cons (congrArg scope.wrap (readback_embed head))
        (readbackConstructorArguments_embed scopes tail)
termination_by _ _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

theorem ObjectProjection.readback {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {sort : TypeExpr}
    {source : Term (SchemaSignature language rule spec) bound sort}
    (projected : ObjectProjection source) : erase projected.term = readback source :=
  (readback_embed projected.term).symm.trans
    (congrArg (fun node : Term (SchemaSignature language rule spec) bound sort =>
      SchemaElaboration.readback node) projected.embedding)

/-- Inspect a typed object's declaration rather than rerunning its raw
reifier. A successful row names the unique physical authored authority. -/
def canonicalConstructor? (language : LanguageDef) (declaration : GrammarRule) : Bool :=
  match selectConstructor? language declaration.label with
  | none => false
  | some selected => decide (language.terms.get selected.index = declaration)

def canonicalVectorConstructor? (language : LanguageDef) (declaration : GrammarRule)
    (parameterName : String) (elementSort : TypeExpr) : Bool :=
  match selectVectorConstructor? language declaration.category with
  | none => false
  | some selected =>
      decide (language.terms.get selected.index = declaration) &&
        decide (selected.parameterName = parameterName) && decide (selected.elementSort = elementSort)

mutual
/-- An independent structural object profile on the existing term family.
The stored result sort and context are never inferred from erasure. -/
def canonicalObject? : {bound : List TypeExpr} → {sort : TypeExpr} →
    Term (signatureOf language) bound sort → Bool
  | _, _, .var _ => true
  | _, _, .op (.constructor declaration _ _ _) arguments =>
      canonicalConstructor? language declaration && canonicalObjectArguments? arguments
  | _, _, .op (.collectionConstructor declaration _ parameterName kind elementSort _ _) arguments =>
      decide (kind = .vec) &&
        canonicalVectorConstructor? language declaration parameterName elementSort &&
          canonicalObjectArguments? arguments
  | _, _, .op (.lambda _ _) arguments => canonicalObjectArguments? arguments
  | _, _, .op (.multiLambda _ _ _) arguments => canonicalObjectArguments? arguments
  | _, _, .op (.subst _ _) _ => false
  | _, _, .op (.collection kind _ _) arguments =>
      decide (kind = .vec) && canonicalObjectArguments? arguments
termination_by _ _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

def canonicalObjectArguments? : {arity : List (List TypeExpr × TypeExpr)} →
    {bound : List TypeExpr} → Args (signatureOf language) arity bound → Bool
  | _, _, .nil => true
  | _, _, .cons head tail => canonicalObject? head && canonicalObjectArguments? tail
termination_by _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

abbrev CanonicalObject {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) : Prop := canonicalObject? term = true

theorem canonicalConstructor?_iff (declaration : GrammarRule) :
    canonicalConstructor? language declaration = true ↔
      ∃ selected : SelectedConstructor language declaration.label,
        language.terms.get selected.index = declaration := by
  unfold canonicalConstructor?
  cases found : selectConstructor? language declaration.label with
  | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists]
      intro selected same
      have present := selectConstructor?_complete selected
      rw [found] at present
      cases present
  | some selected =>
      simp only [decide_eq_true_eq]
      constructor
      · intro same; exact ⟨selected, same⟩
      · rintro ⟨other, same⟩
        have present := selectConstructor?_complete other
        rw [found] at present
        cases Option.some.inj present
        exact same

mutual
/-- Renaming preserves the structural object profile. In particular actual
body recovery cannot change its constructor authority or introduce subst. -/
theorem canonicalObject?_rename {bound target : List TypeExpr}
    (rho : Ren (signatureOf language) bound target) :
    ∀ {sort : TypeExpr} (term : Term (signatureOf language) bound sort),
      canonicalObject? (rename rho term) = canonicalObject? term
  | _, .var _ => by simp only [rename, canonicalObject?]
  | _, .op operator arguments => by
      have recoded := canonicalObjectArguments?_rename rho arguments
      cases operator <;>
        simp only [rename, canonicalObject?, recoded]
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

theorem canonicalObjectArguments?_rename {bound target : List TypeExpr}
    (rho : Ren (signatureOf language) bound target) :
    ∀ {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf language) arity bound),
      canonicalObjectArguments? (renameArgs rho arguments) = canonicalObjectArguments? arguments
  | _, .nil => by simp only [renameArgs, canonicalObjectArguments?]
  | _, .cons (bs := binders) head tail => by
      simp only [renameArgs, canonicalObjectArguments?,
        canonicalObject?_rename (liftRen rho binders) head,
        canonicalObjectArguments?_rename rho tail]
termination_by _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

theorem canonicalObject?_cast_context {bound target : List TypeExpr} (same : bound = target)
    {sort : TypeExpr} (term : Term (signatureOf language) bound sort) :
    canonicalObject? (castTermCtx same term) = canonicalObject? term := by
  cases same
  rfl

theorem canonicalObject?_strengthen {bound target : List TypeExpr}
    {rho : Ren (signatureOf language) bound target} (inverse : Strengthener rho)
    {sort : TypeExpr} (term : Term (signatureOf language) target sort)
    (body : Term (signatureOf language) bound sort)
    (recovered : strengthenT inverse term = some body) :
    canonicalObject? body = canonicalObject? term :=
  (canonicalObject?_rename rho body).symm.trans
    (congrArg (fun value : Term (signatureOf language) target sort => canonicalObject? value)
      (rename_strengthenT inverse term body recovered))

private theorem parameterScope_wrap_object {parameter : TermParam}
    {binders : List TypeExpr} {sort : TypeExpr} (scope : ParameterScope parameter binders sort)
    (body : Pattern) : isObjectPattern (scope.wrap body) = isObjectPattern body := by
  cases scope <;> rfl

mutual
/-- This independent typed profile lies in the existing source checker's
object domain, without treating source-only substitution as an object form. -/
theorem CanonicalObject.erase_object :
    ∀ {bound : List TypeExpr} {sort : TypeExpr}
      (term : Term (signatureOf language) bound sort), CanonicalObject term →
        isObjectPattern (erase term) = true
  | _, _, .var _, _ => rfl
  | _, _, .op (.constructor _ _ _ scopes) arguments, admitted => by
      simp only [CanonicalObject, canonicalObject?, Bool.and_eq_true] at admitted
      exact canonicalConstructorArguments_erase_object scopes arguments admitted.2
  | _, _, .op (.collectionConstructor _ _ _ kind _ _ _) arguments, admitted => by
      simp only [CanonicalObject, canonicalObject?, Bool.and_eq_true] at admitted
      simpa only [erase, isObjectPattern, Option.isNone_none, Bool.true_and] using
        canonicalObjectArguments_erase_object arguments admitted.2
  | _, _, .op (.lambda _ _) arguments, admitted =>
      match arguments with
      | .cons body .nil => by
          have supported : CanonicalObject body := by
            simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true] using admitted
          exact CanonicalObject.erase_object body supported
  | _, _, .op (.multiLambda _ _ _) arguments, admitted =>
      match arguments with
      | .cons body .nil => by
          have supported : CanonicalObject body := by
            simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true] using admitted
          exact CanonicalObject.erase_object body supported
  | _, _, .op (.subst _ _) _, admitted => by
      simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at admitted
  | _, _, .op (.collection kind _ _) arguments, admitted => by
      simp only [CanonicalObject, canonicalObject?, Bool.and_eq_true] at admitted
      simpa only [erase, isObjectPattern, Option.isNone_none, Bool.true_and] using
        canonicalObjectArguments_erase_object arguments admitted.2
termination_by _ _ term _ => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

theorem canonicalObjectArguments_erase_object :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) arity bound),
      canonicalObjectArguments? arguments = true →
        isObjectPatternList (eraseArguments arguments) = true
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, admitted => by
      have supported : canonicalObject? head = true ∧ canonicalObjectArguments? tail = true :=
        by simpa only [canonicalObjectArguments?, Bool.and_eq_true] using admitted
      change (isObjectPattern (erase head) && isObjectPatternList (eraseArguments tail)) = true
      rw [CanonicalObject.erase_object head supported.1,
        canonicalObjectArguments_erase_object tail supported.2]
      rfl
termination_by _ _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

theorem canonicalConstructorArguments_erase_object :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      canonicalObjectArguments? arguments = true →
        isObjectPatternList (eraseConstructorArguments scopes arguments) = true
  | _, _, _, .nil, .nil, _ => rfl
  | _, _, _, .cons scope scopes, .cons head tail, admitted => by
      have supported : canonicalObject? head = true ∧ canonicalObjectArguments? tail = true :=
        by simpa only [canonicalObjectArguments?, Bool.and_eq_true] using admitted
      change (isObjectPattern (scope.wrap (erase head)) &&
        isObjectPatternList (eraseConstructorArguments scopes tail)) = true
      rw [parameterScope_wrap_object, CanonicalObject.erase_object head supported.1,
        canonicalConstructorArguments_erase_object scopes tail supported.2]
      rfl
termination_by _ _ _ _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

theorem CanonicalObject.checked {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) (admitted : CanonicalObject term) :
    checkHasType language FreeTypeContext.empty bound (erase term) sort = true :=
  checkHasType_complete_of_object (erase_typed term) (CanonicalObject.erase_object term admitted)

theorem SelectedVectorConstructor.selected {category : String}
    (selected : SelectedVectorConstructor language category) :
    selectVectorConstructor? language category = some selected := by
  unfold selectVectorConstructor?
  split
  · rename_i index candidates
    have same : index = selected.index := by
      simpa only [List.cons.injEq, and_true] using candidates.symm.trans selected.unique
    subst index
    split
    · rename_i parameterName elementSort shape
      have payload : selected.parameterName = parameterName ∧ selected.elementSort = elementSort := by
        simpa only [selected.shape, List.cons.injEq, and_true, TermParam.simple.injEq,
          TypeExpr.collection.injEq, true_and] using shape
      rcases payload with ⟨sameName, sameSort⟩
      subst parameterName
      subst elementSort
      split
      · rfl
      · rename_i uncategorized
        exact False.elim (uncategorized selected.categorized)
    · rename_i unsupported
      exact False.elim (unsupported selected.parameterName selected.elementSort selected.shape)
  · rename_i notSingleton
    exact False.elim (notSingleton selected.index selected.unique)

theorem canonicalVectorConstructor?_iff (declaration : GrammarRule)
    (parameterName : String) (elementSort : TypeExpr) :
    canonicalVectorConstructor? language declaration parameterName elementSort = true ↔
      ∃ selected : SelectedVectorConstructor language declaration.category,
        language.terms.get selected.index = declaration ∧
          selected.parameterName = parameterName ∧ selected.elementSort = elementSort := by
  unfold canonicalVectorConstructor?
  cases found : selectVectorConstructor? language declaration.category with
  | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists]
      intro selected same
      have present := SelectedVectorConstructor.selected selected
      rw [found] at present
      cases present
  | some selected =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨same, name⟩, sort⟩; exact ⟨selected, same, name, sort⟩
      · rintro ⟨other, same, name, sort⟩
        have present := SelectedVectorConstructor.selected other
        rw [found] at present
        cases Option.some.inj present
        exact ⟨⟨same, name⟩, sort⟩

theorem sourceHeight_positive (source : Pattern) : 0 < sourceHeight source := by
  cases source <;> simp only [sourceHeight] <;> omega

theorem parameterScope_wrap_height {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort) (source : Pattern) :
    sourceHeight source ≤ sourceHeight (scope.wrap source) := by
  cases scope <;> simp only [ParameterScope.wrap, sourceHeight] <;> omega

namespace ObjectRoundtrip

/-- This is coherence for the existing prefix renaming and context transport,
not a new substitution action. -/
theorem prefix_assoc {S : Signature} :
    ∀ (binders bound : Ctx S) {sort : S.Srt} (position : Var (binders ++ bound) sort),
      (List.append_assoc binders bound [] ▸
        injPrefix (S := S) (Γ := []) (binders ++ bound) position) =
          liftRen (fun _ position => injPrefix (S := S) (Γ := []) bound position)
            binders sort position
  | [], _, _, _ => rfl
  | first :: binders, bound, _, .zero => by
      change (congrArg (List.cons first) (List.append_assoc binders bound []) ▸
        (Var.zero : Var (first :: ((binders ++ bound) ++ [])) first)) = _
      exact eqRec_var_zero (S := S) (List.append_assoc binders bound []) first
  | first :: binders, bound, _, .succ position => by
      change (congrArg (List.cons first) (List.append_assoc binders bound []) ▸
        Var.succ (injPrefix (S := S) (Γ := []) (binders ++ bound) position)) =
          Var.succ (liftRen (fun _ position => injPrefix (S := S) (Γ := []) bound position)
            binders _ position)
      rw [eqRec_var_succ (S := S) (List.append_assoc binders bound []),
        prefix_assoc binders bound position]

theorem rename_cast_context {S : Signature} {bound middle target : Ctx S}
    (same : middle = target) (rho : Ren S bound middle) (actual : Ren S bound target)
    (compatible : ∀ sort position, (same ▸ rho sort position) = actual sort position)
    {sort : S.Srt} (term : Term S bound sort) :
    castTermCtx same (rename rho term) = rename actual term := by
  cases same
  have maps : rho = actual := funext fun sort => funext fun position => compatible sort position
  rw [maps]
  rfl

theorem embed_cast_context {S : Signature} {M : List (MetaArity S)}
    {bound target : Ctx S} (same : bound = target) {sort : S.Srt} (term : Term S bound sort) :
    embed (M := M) (castTermCtx same term) =
      castTermCtx (T := withMetas S M) same (embed term) := by
  cases same
  rfl

theorem embedded_prefix_scope {S : Signature} {M : List (MetaArity S)}
    (binders bound : Ctx S) {sort : S.Srt} (term : Term S (binders ++ bound) sort) :
    castTermCtx (T := withMetas S M) (List.append_assoc binders bound [])
        (embed (M := M) (rename (fun _ position =>
          injPrefix (S := S) (Γ := []) (binders ++ bound) position) term)) =
      embed (rename (liftRen (fun _ position => injPrefix (S := S) (Γ := []) bound position)
        binders) term) := by
  rw [← embed_cast_context]
  exact congrArg (embed (M := M))
    (rename_cast_context (List.append_assoc binders bound []) _ _
      (fun _ position => prefix_assoc binders bound position) term)

def parameterChildSuffix {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr} :
    ParameterScope parameter binders sort → List Nat
  | .simple _ _ => []
  | .abstraction _ _ _ _ | .abstractionBase _ _ _ => [0]
  | .multiAbstraction _ _ _ _ _ | .multiAbstractionBase _ _ _ _ => [0]

def parameterBodyOfScope {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (source : Pattern) :
    ParameterBody parameter (scope.wrap source) where
  binders := binders
  sort := sort
  scope := scope
  body := source
  pathSuffix := parameterChildSuffix scope
  source_readback := rfl

theorem parameterBody?_wrapped {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (source : Pattern) :
    parameterBody? parameter (scope.wrap source) = some (parameterBodyOfScope scope source) := by
  cases scope <;> rfl

variable {rule : RewriteRule} {spec : RuleBindingSpec}

private theorem parameterScopes_cons_transport {parameter : TermParam}
    {parameters : List TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    {first second : List (List TypeExpr × TypeExpr)} (same : first = second)
    (scope : ParameterScope parameter binders sort) (tail : ParameterScopes parameters first) :
    (congrArg (List.cons (binders, sort)) same ▸ ParameterScopes.cons scope tail) =
      ParameterScopes.cons scope (same ▸ tail) := by
  cases same
  rfl

private theorem castArgsArity_cons {S : Signature} {bound binders : Ctx S} {sort : S.Srt}
    {first second : List (Ctx S × S.Srt)} (same : first = second)
    (head : Term S (binders ++ bound) sort) (tail : Args S first bound) :
    castArgsArity (congrArg (List.cons (binders, sort)) same) (Args.cons head tail) =
      Args.cons head (castArgsArity same tail) := by
  cases same
  rfl

/-- Recursive callback adequacy is used only to assemble the actual existing
parameter codec. The decoder earns this callback by fuel induction,
including each original wrapper and child address. -/
private theorem constructorArguments_image
    (compile : (bound : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec bound source sort))
    (fuel : Nat)
    (children : ∀ (bound : List TypeExpr) (path : List Nat) {sort : TypeExpr}
      (term : Term (signatureOf language) bound sort), CanonicalObject term →
      sourceHeight (erase term) ≤ fuel →
      ∃ compiled : CompiledSchema language rule spec bound (erase term) sort,
        compile bound path (erase term) sort = some compiled ∧
          compiled.term = embed (rename (fun _ position =>
            injPrefix (S := signatureOf language) (Γ := []) bound position) term)) :
    ∀ (bound : List TypeExpr) (path : List Nat) (offset : Nat)
      {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      canonicalObjectArguments? arguments = true →
      sourceListHeight (eraseConstructorArguments scopes arguments) ≤ fuel →
      ∃ compiled : CompiledConstructorArguments language rule spec bound parameters
          (eraseConstructorArguments scopes arguments),
        compileConstructorArguments? compile bound path offset parameters
            (eraseConstructorArguments scopes arguments) = some compiled ∧
          ∃ same : compiled.arity = arity,
            (same ▸ compiled.scopes) = scopes ∧
              castArgsArity same compiled.arguments =
                embedArgs (renameArgs (fun _ position =>
                  injPrefix (S := signatureOf language) (Γ := []) bound position) arguments)
  | _, _, _, _, _, .nil, .nil, _, _ => by
      simp only [eraseConstructorArguments, compileConstructorArguments?]
      exact ⟨_, rfl, rfl, rfl, rfl⟩
  | bound, path, offset, _, _, .cons (binders := binders) (bodyType := sort) scope scopes,
      .cons head tail, admitted, height => by
      have supported : canonicalObject? head = true ∧ canonicalObjectArguments? tail = true := by
        simpa only [canonicalObjectArguments?, Bool.and_eq_true] using admitted
      have wrappedHeight := parameterScope_wrap_height scope (erase head)
      have headHeight : sourceHeight (erase head) ≤ fuel := by
        simp only [eraseConstructorArguments, sourceListHeight] at height
        omega
      have tailHeight : sourceListHeight (eraseConstructorArguments scopes tail) ≤ fuel := by
        simp only [eraseConstructorArguments, sourceListHeight] at height
        omega
      obtain ⟨compiledHead, foundHead, headImage⟩ := children (binders ++ bound)
        (path ++ [offset] ++ parameterChildSuffix scope) head supported.1 headHeight
      obtain ⟨compiledTail, foundTail, sameArity, sameScopes, sameArguments⟩ :=
        constructorArguments_image compile fuel children bound path (offset + 1)
          scopes tail supported.2 tailHeight
      change ∃ compiled : CompiledConstructorArguments language rule spec bound _
          (scope.wrap (erase head) :: eraseConstructorArguments scopes tail),
        compileConstructorArguments? compile bound path offset _
            (scope.wrap (erase head) :: eraseConstructorArguments scopes tail) = some compiled ∧
          ∃ same : compiled.arity = (binders, sort) :: _,
            (same ▸ compiled.scopes) = ParameterScopes.cons scope scopes ∧
              castArgsArity same compiled.arguments =
                embedArgs (renameArgs (fun _ position =>
                  injPrefix (S := signatureOf language) (Γ := []) bound position) (.cons head tail))
      simp only [compileConstructorArguments?, parameterBody?_wrapped,
        Option.bind_eq_bind, Option.bind_some, parameterBodyOfScope, foundHead, foundTail, pure]
      refine ⟨_, rfl, ?_⟩
      refine ⟨congrArg (List.cons (binders, sort)) sameArity, ?_, ?_⟩
      · rw [parameterScopes_cons_transport sameArity scope compiledTail.scopes]
        exact congrArg (ParameterScopes.cons scope) sameScopes
      · change castArgsArity (congrArg (List.cons (binders, sort)) sameArity)
          (Args.cons (castTermCtx (T := SchemaSignature language rule spec)
            (List.append_assoc binders bound []) compiledHead.term) compiledTail.arguments) =
          Args.cons (embed (rename (liftRen (fun _ position =>
            injPrefix (S := signatureOf language) (Γ := []) bound position) binders) head))
            (embedArgs (renameArgs (fun _ position =>
              injPrefix (S := signatureOf language) (Γ := []) bound position) tail))
        rw [castArgsArity_cons sameArity, headImage,
          embedded_prefix_scope (M := metaArities rule spec) binders bound head, sameArguments]

theorem eraseVectorArguments_length {elementSort : TypeExpr} :
    ∀ {count : Nat} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) (List.replicate count ([], elementSort)) bound),
      (eraseArguments arguments).length = count
  | 0, _, .nil => rfl
  | _ + 1, _, .cons _ tail => by
      simpa only [eraseArguments, List.length_cons] using
        congrArg Nat.succ (eraseVectorArguments_length tail)

private theorem vectorElements_image
    (compile : (bound : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec bound source sort))
    (fuel : Nat)
    (children : ∀ (bound : List TypeExpr) (path : List Nat) {sort : TypeExpr}
      (term : Term (signatureOf language) bound sort), CanonicalObject term →
      sourceHeight (erase term) ≤ fuel →
      ∃ compiled : CompiledSchema language rule spec bound (erase term) sort,
        compile bound path (erase term) sort = some compiled ∧
          compiled.term = embed (rename (fun _ position =>
            injPrefix (S := signatureOf language) (Γ := []) bound position) term))
    (elementSort : TypeExpr) :
    ∀ {count : Nat} (bound : List TypeExpr) (path : List Nat) (offset : Nat)
      (arguments : Args (signatureOf language) (List.replicate count ([], elementSort)) bound),
      canonicalObjectArguments? arguments = true →
      sourceListHeight (eraseArguments arguments) ≤ fuel →
      ∃ compiled : CompiledVectorElements language rule spec bound (eraseArguments arguments) elementSort,
        compileVectorElements? compile bound path offset elementSort
            (eraseArguments arguments) = some compiled ∧
          ∃ same : (eraseArguments arguments).length = count,
            castArgsArity (congrArg (fun length => List.replicate length ([], elementSort)) same)
                compiled.arguments =
              embedArgs (renameArgs (fun _ position =>
                injPrefix (S := signatureOf language) (Γ := []) bound position) arguments)
  | 0, _, _, _, .nil, _, _ => by
      simp only [eraseArguments, compileVectorElements?]
      exact ⟨_, rfl, rfl, rfl⟩
  | count + 1, bound, path, offset, .cons head tail, admitted, height => by
      have supported : canonicalObject? head = true ∧ canonicalObjectArguments? tail = true := by
        simpa only [canonicalObjectArguments?, Bool.and_eq_true] using admitted
      have headHeight : sourceHeight (erase head) ≤ fuel := by
        simp only [eraseArguments, sourceListHeight] at height
        omega
      have tailHeight : sourceListHeight (eraseArguments tail) ≤ fuel := by
        simp only [eraseArguments, sourceListHeight] at height
        omega
      obtain ⟨compiledHead, foundHead, headImage⟩ := children bound (path ++ [offset])
        head supported.1 headHeight
      obtain ⟨compiledTail, foundTail, sameLength, sameArguments⟩ :=
        vectorElements_image compile fuel children elementSort bound path (offset + 1)
          tail supported.2 tailHeight
      change ∃ compiled : CompiledVectorElements language rule spec bound
          (erase head :: eraseArguments tail) elementSort,
        compileVectorElements? compile bound path offset elementSort
            (erase head :: eraseArguments tail) = some compiled ∧
          ∃ same : (erase head :: eraseArguments tail).length = count + 1,
            castArgsArity (congrArg (fun length => List.replicate length ([], elementSort)) same)
                compiled.arguments =
              embedArgs (renameArgs (fun _ position =>
                injPrefix (S := signatureOf language) (Γ := []) bound position) (.cons head tail))
      simp only [compileVectorElements?, foundHead, foundTail, Option.bind_eq_bind,
        Option.bind_some, pure]
      refine ⟨_, rfl, congrArg Nat.succ sameLength, ?_⟩
      change castArgsArity (T := SchemaSignature language rule spec) (Γ := bound ++ [])
          (congrArg (List.cons ([], elementSort))
          (congrArg (fun length => List.replicate length ([], elementSort)) sameLength))
          (Args.cons (bs := []) compiledHead.term compiledTail.arguments) =
        Args.cons (bs := []) (embed (rename (fun _ position =>
          injPrefix (S := signatureOf language) (Γ := []) bound position) head))
          (embedArgs (renameArgs (fun _ position =>
            injPrefix (S := signatureOf language) (Γ := []) bound position) tail))
      rw [castArgsArity_cons (congrArg (fun length =>
        List.replicate length ([], elementSort)) sameLength), headImage, sameArguments]
      rfl

private theorem constructor_op_transport {bound : List TypeExpr}
    {declaration : GrammarRule} {first second : List (List TypeExpr × TypeExpr)}
    (same : first = second)
    (firstScope : ParameterScopes declaration.params first)
    (secondScope : ParameterScopes declaration.params second)
    (sameScopes : (same ▸ firstScope) = secondScope)
    (firstArguments : Args (SchemaSignature language rule spec) first bound)
    (secondArguments : Args (SchemaSignature language rule spec) second bound)
    (sameArguments : castArgsArity same firstArguments = secondArguments)
    (firstMember secondMember : declaration ∈ language.terms)
    (firstOrdinary secondOrdinary : ¬ UsesBareCollection declaration) :
    (show Term (SchemaSignature language rule spec) bound (.base declaration.category) from
      .op (.inl (.constructor declaration firstMember firstOrdinary firstScope)) firstArguments) =
      .op (.inl (.constructor declaration secondMember secondOrdinary secondScope)) secondArguments := by
  cases same
  cases sameScopes
  cases sameArguments
  rfl

private theorem vector_op_transport {bound : List TypeExpr} {elementSort : TypeExpr}
    {first second : Nat} (same : first = second)
    (firstArguments : Args (SchemaSignature language rule spec)
      (List.replicate first ([], elementSort)) bound)
    (secondArguments : Args (SchemaSignature language rule spec)
      (List.replicate second ([], elementSort)) bound)
    (sameArguments : castArgsArity
      (congrArg (fun count => List.replicate count ([], elementSort)) same) firstArguments =
        secondArguments) :
    (show Term (SchemaSignature language rule spec) bound (.collection .vec elementSort) from
      .op (.inl (.collection .vec elementSort first)) firstArguments) =
      .op (.inl (.collection .vec elementSort second)) secondArguments := by
  cases same
  cases sameArguments
  rfl

private theorem vector_constructor_op_transport {bound : List TypeExpr}
    {declaration : GrammarRule} {parameterName : String} {elementSort : TypeExpr}
    {first second : Nat} (same : first = second)
    (firstArguments : Args (SchemaSignature language rule spec)
      (List.replicate first ([], elementSort)) bound)
    (secondArguments : Args (SchemaSignature language rule spec)
      (List.replicate second ([], elementSort)) bound)
    (sameArguments : castArgsArity
      (congrArg (fun count => List.replicate count ([], elementSort)) same) firstArguments =
        secondArguments)
    (firstMember secondMember : declaration ∈ language.terms)
    (firstShape secondShape :
      declaration.bareParams = [.simple parameterName (.collection .vec elementSort)]) :
    (show Term (SchemaSignature language rule spec) bound (.base declaration.category) from
      .op (.inl (.collectionConstructor declaration firstMember parameterName .vec
        elementSort firstShape first)) firstArguments) =
      .op (.inl (.collectionConstructor declaration secondMember parameterName .vec
        elementSort secondShape second)) secondArguments := by
  cases same
  cases sameArguments
  rfl

private theorem canonicalConstructor_index (declaration : GrammarRule)
    (admitted : canonicalConstructor? language declaration = true) :
    ∃ index : Fin language.terms.length,
      constructorCandidates language declaration.label = [index] ∧
        language.terms.get index = declaration := by
  obtain ⟨selected, same⟩ := (canonicalConstructor?_iff declaration).mp admitted
  exact ⟨selected.index, selected.unique, same⟩

private theorem canonicalVectorConstructor_index (declaration : GrammarRule)
    (parameterName : String) (elementSort : TypeExpr)
    (admitted : canonicalVectorConstructor? language declaration parameterName elementSort = true) :
    ∃ index : Fin language.terms.length,
      vectorConstructorCandidates language declaration.category = [index] ∧
        language.terms.get index = declaration := by
  obtain ⟨selected, same, _, _⟩ :=
    (canonicalVectorConstructor?_iff declaration parameterName elementSort).mp admitted
  exact ⟨selected.index, selected.unique, same⟩

private theorem injPrefix_shared_sorts {S : Signature} {M : List (MetaArity S)} :
    ∀ (bound : Ctx S) {ambient : Ctx S} {sort : S.Srt} (position : Var bound sort),
      injPrefix (S := withMetas S M) (Γ := ambient) bound position =
        injPrefix (S := S) (Γ := ambient) bound position
  | _, _, _, .zero => rfl
  | _ :: rest, _, _, .succ position =>
      congrArg Var.succ (injPrefix_shared_sorts rest position)

/-- The actual schema codec recovers every independently canonical object at
its supplied result sort and ordered context. The induction follows the
original source height and retains every constructor's physical selection. -/
theorem compileSchemaWithFuel?_canonical (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (fuel : Nat) :
    ∀ (bound : List TypeExpr) (path : List Nat) {sort : TypeExpr}
      (term : Term (signatureOf language) bound sort), CanonicalObject term →
      sourceHeight (erase term) ≤ fuel →
      ∃ compiled : CompiledSchema language rule spec bound (erase term) sort,
        compileSchemaWithFuel? language rule spec site fuel bound path (erase term) sort =
            some compiled ∧
          compiled.term = embed (rename (fun _ position =>
            injPrefix (S := signatureOf language) (Γ := []) bound position) term) := by
  induction fuel with
  | zero =>
      intro bound path sort term _ height
      have positive := sourceHeight_positive (erase term)
      omega
  | succ fuel children =>
      intro bound path sort term admitted height
      match term with
      | .var position =>
          change ∃ compiled : CompiledSchema language rule spec bound
              (.bvar (variableIndex position)) sort,
            compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                (.bvar (variableIndex position)) sort = some compiled ∧
              compiled.term = .var (injPrefix (S := signatureOf language)
                (Γ := []) bound position)
          simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly]
          split
          · rename_i missing
            have present := boundPosition?_complete position
            rw [missing] at present
            cases present
          · rename_i actual found
            have same : actual = position :=
              Option.some.inj (found.symm.trans (boundPosition?_complete position))
            subst actual
            refine ⟨_, rfl, ?_⟩
            exact congrArg (fun value : Var (bound ++ []) sort =>
              Term.var (S := SchemaSignature language rule spec) value)
              (injPrefix_shared_sorts (M := metaArities rule spec) bound position)
      | .op operator arguments =>
          cases operator with
          | constructor declaration member ordinary scopes =>
              have supported : canonicalConstructor? language declaration = true ∧
                  canonicalObjectArguments? arguments = true := by
                simpa only [CanonicalObject, canonicalObject?, Bool.and_eq_true] using admitted
              obtain ⟨index, unique, sameDeclaration⟩ :=
                canonicalConstructor_index declaration supported.1
              subst declaration
              let selected : SelectedConstructor language (language.terms.get index).label :=
                { index := index, unique := unique }
              have notBare : usesBareCollection? (language.terms.get selected.index) = false := by
                cases checked : usesBareCollection? (language.terms.get selected.index) with
                | false => rfl
                | true =>
                    exact False.elim (ordinary ((usesBareCollection?_eq_true_iff _).mp checked))
              have argumentsHeight : sourceListHeight (eraseConstructorArguments scopes arguments) ≤ fuel := by
                simp only [erase, sourceHeight] at height
                omega
              obtain ⟨compiledArguments, foundArguments, sameArity, sameScopes, sameArguments⟩ :=
                constructorArguments_image (compileSchemaWithFuel? language rule spec site fuel)
                  fuel children bound path 0 scopes arguments supported.2 argumentsHeight
              change ∃ compiled : CompiledSchema language rule spec bound
                  (.apply (language.terms.get selected.index).label
                    (eraseConstructorArguments scopes arguments))
                  (.base (language.terms.get selected.index).category),
                compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                    (.apply (language.terms.get selected.index).label
                      (eraseConstructorArguments scopes arguments))
                    (.base (language.terms.get selected.index).category) = some compiled ∧
                  compiled.term = embed (rename (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position)
                    (.op (.constructor _ member ordinary scopes) arguments))
              simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly]
              rw [selectConstructor?_complete selected]
              simp only [notBare, dite_true, Option.bind_eq_bind, Option.bind_some]
              rw [foundArguments]
              simp only [Option.bind_some, pure]
              refine ⟨_, rfl, ?_⟩
              change (show Term (SchemaSignature language rule spec) (bound ++ [])
                  (.base (language.terms.get selected.index).category) from
                .op (.inl (.constructor _ (List.get_mem _ _) ordinary
                  (arity := compiledArguments.arity) compiledArguments.scopes))
                  compiledArguments.arguments) =
                .op (.inl (.constructor _ member ordinary scopes))
                  (embedArgs (renameArgs (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position) arguments))
              exact constructor_op_transport sameArity _ _ sameScopes _ _ sameArguments _ _ _ _
          | collectionConstructor declaration member parameterName kind elementSort shape count =>
              have supported : ((decide (kind = .vec) &&
                  canonicalVectorConstructor? language declaration parameterName elementSort) &&
                    canonicalObjectArguments? arguments) = true := by
                simpa only [CanonicalObject, canonicalObject?] using admitted
              simp only [Bool.and_eq_true, decide_eq_true_eq] at supported
              rcases supported with ⟨⟨kindEqual, selectedProfile⟩, argumentProfile⟩
              subst kind
              obtain ⟨index, unique, sameDeclaration⟩ :=
                canonicalVectorConstructor_index declaration parameterName elementSort selectedProfile
              subst declaration
              let selected : SelectedVectorConstructor language (language.terms.get index).category :=
                { index := index, unique := unique, parameterName := parameterName,
                  elementSort := elementSort, shape := shape, categorized := rfl }
              have argumentsHeight : sourceListHeight (eraseArguments arguments) ≤ fuel := by
                simp only [erase, sourceHeight] at height
                omega
              obtain ⟨elements, foundElements, sameCount, sameArguments⟩ :=
                vectorElements_image (compileSchemaWithFuel? language rule spec site fuel) fuel
                  children selected.elementSort bound path 0 arguments argumentProfile argumentsHeight
              change ∃ compiled : CompiledSchema language rule spec bound
                  (.collection .vec (eraseArguments arguments) none)
                  (.base (language.terms.get selected.index).category),
                compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                    (.collection .vec (eraseArguments arguments) none)
                    (.base (language.terms.get selected.index).category) = some compiled ∧
                  compiled.term = embed (rename (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position)
                    (.op (.collectionConstructor _ member selected.parameterName .vec
                      selected.elementSort shape count) arguments))
              simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly]
              rw [SelectedVectorConstructor.selected selected]
              simp only [foundElements, Option.bind_eq_bind, Option.bind_some, pure]
              refine ⟨_, rfl, ?_⟩
              change (show Term (SchemaSignature language rule spec) (bound ++ [])
                  (.base (language.terms.get selected.index).category) from
                .op (.inl (.collectionConstructor _ (List.get_mem _ _) selected.parameterName .vec
                  selected.elementSort selected.shape (eraseArguments arguments).length)) elements.arguments) =
                .op (.inl (.collectionConstructor _ member selected.parameterName .vec
                  selected.elementSort shape count))
                  (embedArgs (renameArgs (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position) arguments))
              exact vector_constructor_op_transport sameCount _ _ sameArguments _ _ _ _
          | lambda domain codomain =>
              match arguments with
              | .cons body .nil =>
                  have bodyProfile : CanonicalObject body := by
                    simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true]
                      using admitted
                  have bodyHeight : sourceHeight (erase body) ≤ fuel := by
                    simp only [erase, sourceHeight] at height
                    omega
                  obtain ⟨compiledBody, foundBody, bodyImage⟩ :=
                    children (domain :: bound) (path ++ [0]) body bodyProfile bodyHeight
                  change ∃ compiled : CompiledSchema language rule spec bound
                      (.lambda none (erase body)) (.arrow domain codomain),
                    compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                        (.lambda none (erase body)) (.arrow domain codomain) = some compiled ∧
                      compiled.term = embed (rename (fun _ position =>
                        injPrefix (S := signatureOf language) (Γ := []) bound position)
                        (.op (.lambda domain codomain) (.cons body .nil)))
                  simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly, foundBody, Option.bind_eq_bind, Option.bind_some, pure]
                  refine ⟨_, rfl, ?_⟩
                  change (show Term (SchemaSignature language rule spec) (bound ++ []) (.arrow domain codomain)
                      from .op (.inl (.lambda domain codomain)) (.cons compiledBody.term .nil)) =
                    .op (.inl (.lambda domain codomain))
                      (.cons (embed (rename (liftRen (fun _ position =>
                        injPrefix (S := signatureOf language) (Γ := []) bound position) [domain]) body)) .nil)
                  rw [bodyImage]
                  exact congrArg (fun child : Term (SchemaSignature language rule spec)
                      (domain :: (bound ++ [])) codomain =>
                    (show Term (SchemaSignature language rule spec) (bound ++ []) (.arrow domain codomain)
                      from .op (.inl (.lambda domain codomain))
                        (Args.cons (S := SchemaSignature language rule spec)
                          (Γ := bound ++ []) (bs := [domain]) (s := codomain) (as := []) child .nil)))
                    (embedded_prefix_scope (M := metaArities rule spec) [domain] bound body)
          | multiLambda domain codomain count =>
              match arguments with
              | .cons body .nil =>
                  have bodyProfile : CanonicalObject body := by
                    simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true]
                      using admitted
                  have bodyHeight : sourceHeight (erase body) ≤ fuel := by
                    simp only [erase, sourceHeight] at height
                    omega
                  obtain ⟨compiledBody, foundBody, bodyImage⟩ :=
                    children (List.replicate count domain ++ bound) (path ++ [0]) body bodyProfile bodyHeight
                  change ∃ compiled : CompiledSchema language rule spec bound
                      (.multiLambda count [] (erase body)) (.arrow (.multiBinder domain) codomain),
                    compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                        (.multiLambda count [] (erase body)) (.arrow (.multiBinder domain) codomain) = some compiled ∧
                      compiled.term = embed (rename (fun _ position =>
                        injPrefix (S := signatureOf language) (Γ := []) bound position)
                        (.op (.multiLambda domain codomain count) (.cons body .nil)))
                  simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly, foundBody, Option.bind_eq_bind, Option.bind_some, pure]
                  refine ⟨_, rfl, ?_⟩
                  change (show Term (SchemaSignature language rule spec) (bound ++ [])
                      (.arrow (.multiBinder domain) codomain) from
                    .op (.inl (.multiLambda domain codomain count))
                      (.cons (castTermCtx (T := SchemaSignature language rule spec)
                        (List.append_assoc (List.replicate count domain) bound []) compiledBody.term) .nil)) =
                    .op (.inl (.multiLambda domain codomain count))
                      (.cons (embed (rename (liftRen (fun _ position =>
                        injPrefix (S := signatureOf language) (Γ := []) bound position)
                          (List.replicate count domain)) body)) .nil)
                  rw [bodyImage, embedded_prefix_scope (M := metaArities rule spec)
                    (List.replicate count domain) bound body]
          | subst domain codomain =>
              simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at admitted
          | collection kind elementSort count =>
              have supported : decide (kind = .vec) = true ∧
                  canonicalObjectArguments? arguments = true := by
                simpa only [CanonicalObject, canonicalObject?, Bool.and_eq_true] using admitted
              have kindEqual : kind = .vec := of_decide_eq_true supported.1
              subst kind
              have argumentsHeight : sourceListHeight (eraseArguments arguments) ≤ fuel := by
                simp only [erase, sourceHeight] at height
                omega
              obtain ⟨elements, foundElements, sameCount, sameArguments⟩ :=
                vectorElements_image (compileSchemaWithFuel? language rule spec site fuel) fuel
                  children elementSort bound path 0 arguments supported.2 argumentsHeight
              change ∃ compiled : CompiledSchema language rule spec bound
                  (.collection .vec (eraseArguments arguments) none) (.collection .vec elementSort),
                compileSchemaWithFuel? language rule spec site (fuel + 1) bound path
                    (.collection .vec (eraseArguments arguments) none) (.collection .vec elementSort) = some compiled ∧
                  compiled.term = embed (rename (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position)
                    (.op (.collection .vec elementSort count) arguments))
              simp only [compileSchemaWithFuel?_succ, Assembly.step, inputAssembly, foundElements, Option.bind_eq_bind, Option.bind_some, pure]
              refine ⟨_, rfl, ?_⟩
              change (show Term (SchemaSignature language rule spec) (bound ++ [])
                  (.collection .vec elementSort) from
                .op (.inl (.collection .vec elementSort (eraseArguments arguments).length)) elements.arguments) =
                .op (.inl (.collection .vec elementSort count))
                  (embedArgs (renameArgs (fun _ position =>
                    injPrefix (S := signatureOf language) (Γ := []) bound position) arguments))
              exact vector_op_transport sameCount _ _ sameArguments

end ObjectRoundtrip

/-- Target admission retains the same constructor codec and an independent
object typing check in the exact caller context. No free schema name becomes
an object constant or an arbitrary metavariable assignment. -/
structure ReifiedTarget (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) where
  compiled : CompiledSchema language rule spec bound source sort
  projection : ObjectProjection compiled.term
  canonical : CanonicalObject projection.term
  checked : checkHasType language FreeTypeContext.empty bound source sort = true
  source_typed : HasType language FreeTypeContext.empty bound source sort

def ReifiedTarget.term {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (target : ReifiedTarget language rule spec bound source sort) :
    Term (signatureOf language) (bound ++ []) sort := target.projection.term

theorem ReifiedTarget.readback {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (target : ReifiedTarget language rule spec bound source sort) :
    erase target.term = source :=
  target.projection.readback.trans target.compiled.source_readback

def reifyTargetWithFuel? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (fuel : Nat) (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option (ReifiedTarget language rule spec bound source sort) := do
  if typed : checkHasType language FreeTypeContext.empty bound source sort = true then
    let compiled ← compileSchemaWithFuel? language rule spec .left fuel bound [] source sort
    let projected ← projectObject? compiled.term
    if canonical : canonicalObject? projected.term = true then
      pure {
        compiled := compiled
        projection := projected
        canonical := canonical
        checked := typed
        source_typed := checkHasType_sound typed }
    else none
  else none

/-- The public target codec reuses the original source-height budget. -/
def reifyTarget? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option (ReifiedTarget language rule spec bound source sort) :=
  reifyTargetWithFuel? language rule spec (sourceHeight source) bound source sort

/-- Admission exposes the actual checker, recursive source codec, and a
genuine object preimage under the existing embedding. -/
theorem ObjectProjection.canonical_preimage_iff {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {sort : TypeExpr}
    {source : Term (SchemaSignature language rule spec) bound sort}
    (projected : ObjectProjection source) :
    (∃ object : Term (signatureOf language) bound sort,
      CanonicalObject object ∧ embed (M := metaArities rule spec) object = source) ↔
        CanonicalObject projected.term := by
  constructor
  · rintro ⟨object, admitted, image⟩
    have same := objectProjection_injective (image.trans projected.embedding.symm)
    simpa only [same] using admitted
  · intro admitted
    exact ⟨projected.term, admitted, projected.embedding⟩

theorem reifyTargetWithFuel?_isSome_iff (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (fuel : Nat) (bound : List TypeExpr)
    (source : Pattern) (sort : TypeExpr) :
    (reifyTargetWithFuel? language rule spec fuel bound source sort).isSome = true ↔
      checkHasType language FreeTypeContext.empty bound source sort = true ∧
        ∃ compiled : CompiledSchema language rule spec bound source sort,
          compileSchemaWithFuel? language rule spec .left fuel bound [] source sort = some compiled ∧
            ∃ object : Term (signatureOf language) (bound ++ []) sort,
              CanonicalObject object ∧ embed (M := metaArities rule spec) object = compiled.term := by
  unfold reifyTargetWithFuel?
  split
  · rename_i typed
    cases found : compileSchemaWithFuel? language rule spec .left fuel bound [] source sort with
    | none => simp [typed]
    | some compiled =>
        cases projected : projectObject? compiled.term with
        | none =>
            have absent : ¬ ∃ value : Term (signatureOf language) (bound ++ []) sort,
                CanonicalObject value ∧ embed (M := metaArities rule spec) value = compiled.term := by
              rintro ⟨value, _, image⟩
              exact ((projectObject?_none_iff compiled.term).mp projected) ⟨value, image⟩
            simp [typed, projected, absent]
        | some object =>
            have preimage := ObjectProjection.canonical_preimage_iff object
            simp only [typed, projected, Option.bind_eq_bind, Option.bind_some,
              true_and, Option.some.injEq]
            have authority :
                (∃ other : CompiledSchema language rule spec bound source sort,
                  compiled = other ∧ ∃ value : Term (signatureOf language) (bound ++ []) sort,
                    CanonicalObject value ∧ embed (M := metaArities rule spec) value = other.term) ↔
                (∃ value : Term (signatureOf language) (bound ++ []) sort,
                  CanonicalObject value ∧ embed (M := metaArities rule spec) value = compiled.term) := by
              constructor
              · rintro ⟨other, same, value⟩
                cases same
                exact value
              · intro value
                exact ⟨compiled, rfl, value⟩
            rw [authority, preimage]
            by_cases canonical : CanonicalObject object.term
            · simp only [CanonicalObject] at canonical
              simp [canonical, CanonicalObject]
            · simp only [CanonicalObject] at canonical
              simp [canonical, CanonicalObject]
  · rename_i untyped
    simp [untyped]

theorem reifyTarget?_isSome_iff (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    (reifyTarget? language rule spec bound source sort).isSome = true ↔
      checkHasType language FreeTypeContext.empty bound source sort = true ∧
        ∃ compiled : CompiledSchema language rule spec bound source sort,
          compileSchemaWithFuel? language rule spec .left (sourceHeight source)
            bound [] source sort = some compiled ∧
              ∃ object : Term (signatureOf language) (bound ++ []) sort,
                CanonicalObject object ∧ embed (M := metaArities rule spec) object = compiled.term :=
  reifyTargetWithFuel?_isSome_iff language rule spec (sourceHeight source) bound source sort

/-- Read the existing opened prefix back into the original sorted context. -/
def ReifiedTarget.object {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (target : ReifiedTarget language rule spec bound source sort) :
    Term (signatureOf language) bound sort :=
  unScope (S := signatureOf language) bound target.term

theorem ReifiedTarget.object_canonical {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (target : ReifiedTarget language rule spec bound source sort) : CanonicalObject target.object := by
  change canonicalObject? (rename (fun _ position =>
    unScopeVar (S := signatureOf language) bound position) target.term) = true
  rw [canonicalObject?_rename]
  exact target.canonical

private theorem unScopeVar_index {S : Signature} :
    ∀ (bound : Ctx S) {sort : S.Srt} (position : Var (bound ++ []) sort),
      variableIndex (unScopeVar (S := S) bound position) = variableIndex position
  | [], _, position => nomatch position
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ position => congrArg Nat.succ (unScopeVar_index rest position)

theorem ReifiedTarget.object_readback {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (target : ReifiedTarget language rule spec bound source sort) : erase target.object = source := by
  change erase (rename (fun _ position =>
    unScopeVar (S := signatureOf language) bound position) target.term) = source
  rw [erase_rename_shiftBy _ 0 0
    (fun _ position => by
      simpa only [Nat.zero_le, if_true, Nat.add_zero] using
        unScopeVar_index (S := signatureOf language) bound position) target.term,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, target.readback]

/-- This projection forgets only the receipt fields of the actual checked
target codec. Its result remains an existing intrinsically typed object. -/
def reifiedObject? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option (Term (signatureOf language) bound sort) :=
  (reifyTarget? language rule spec bound source sort).map ReifiedTarget.object

/-- A successful target receipt retains the actual recursive compilation,
rather than merely a manually supplied readback witness. -/
theorem reifyTargetWithFuel?_compiled {rule : RewriteRule} {spec : RuleBindingSpec}
    {fuel : Nat} {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    {target : ReifiedTarget language rule spec bound source sort}
    (accepted : reifyTargetWithFuel? language rule spec fuel bound source sort = some target) :
    compileSchemaWithFuel? language rule spec .left fuel bound [] source sort = some target.compiled := by
  unfold reifyTargetWithFuel? at accepted
  split at accepted
  · cases found : compileSchemaWithFuel? language rule spec .left fuel bound [] source sort with
    | none => simp only [found, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at accepted
    | some compiled =>
        cases projected : projectObject? compiled.term with
        | none =>
            simp only [found, projected, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, reduceCtorEq] at accepted
        | some object =>
            simp only [found, projected, Option.bind_eq_bind, Option.bind_some] at accepted
            split at accepted
            · simp only [pure, Option.some.injEq] at accepted
              cases accepted
              rfl
            · simp only [reduceCtorEq] at accepted
  · simp only [reduceCtorEq] at accepted

theorem reifiedObject?_canonical (rule : RewriteRule) (spec : RuleBindingSpec)
    {bound : List TypeExpr} {sort : TypeExpr} (term : Term (signatureOf language) bound sort)
    (admitted : CanonicalObject term) :
    reifiedObject? language rule spec bound (erase term) sort = some term := by
  have checked := CanonicalObject.checked term admitted
  obtain ⟨compiled, found, image⟩ := ObjectRoundtrip.compileSchemaWithFuel?_canonical
    language rule spec .left (sourceHeight (erase term)) bound [] term admitted (Nat.le_refl _)
  have objectProfile : CanonicalObject (rename (fun _ position =>
      injPrefix (S := signatureOf language) (Γ := []) bound position) term) := by
    change canonicalObject? (rename _ term) = true
    rw [canonicalObject?_rename]
    exact admitted
  have accepted : (reifyTarget? language rule spec bound (erase term) sort).isSome = true :=
    (reifyTarget?_isSome_iff language rule spec bound (erase term) sort).mpr
      ⟨checked, compiled, found, _, objectProfile, image.symm⟩
  cases actual : reifyTarget? language rule spec bound (erase term) sort with
  | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at accepted
  | some target =>
      have produced := reifyTargetWithFuel?_compiled actual
      have sameCompiled : target.compiled = compiled := Option.some.inj (produced.symm.trans found)
      have sameTerm : target.term = rename (fun _ position =>
          injPrefix (S := signatureOf language) (Γ := []) bound position) term :=
        objectProjection_injective (target.projection.embedding.trans
          ((congrArg CompiledSchema.term sameCompiled).trans image))
      unfold reifiedObject?
      rw [actual, Option.map_some]
      change some (unScope (S := signatureOf language) bound target.term) = some term
      rw [sameTerm, unScope_rename_injPrefix]

theorem reifiedObject?_sound {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    {object : Term (signatureOf language) bound sort}
    (accepted : reifiedObject? language rule spec bound source sort = some object) :
    CanonicalObject object ∧ erase object = source := by
  unfold reifiedObject? at accepted
  cases found : reifyTarget? language rule spec bound source sort with
  | none => simp only [found, Option.map_none, reduceCtorEq] at accepted
  | some target =>
      simp only [found, Option.map_some, Option.some.injEq] at accepted
      cases accepted
      exact ⟨target.object_canonical, target.object_readback⟩

theorem reifiedObject?_eq_some_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr)
    (object : Term (signatureOf language) bound sort) :
    reifiedObject? language rule spec bound source sort = some object ↔
      CanonicalObject object ∧ erase object = source := by
  constructor
  · exact reifiedObject?_sound
  · rintro ⟨admitted, rfl⟩
    exact reifiedObject?_canonical rule spec object admitted

theorem reifiedObject?_typing {rule : RewriteRule} {spec : RuleBindingSpec}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    {object : Term (signatureOf language) bound sort}
    (accepted : reifiedObject? language rule spec bound source sort = some object) :
    HasType language FreeTypeContext.empty bound source sort := by
  rw [← (reifiedObject?_sound accepted).2]
  exact erase_typed object

/-- Raw equality reflects intrinsic equality on the independently admitted
profile, with both the context and result sort fixed. -/
theorem CanonicalObject.erase_injective (rule : RewriteRule) (spec : RuleBindingSpec)
    {bound : List TypeExpr} {sort : TypeExpr}
    {first second : Term (signatureOf language) bound sort}
    (firstAdmitted : CanonicalObject first) (secondAdmitted : CanonicalObject second)
    (same : erase first = erase second) : first = second := by
  have decoded := congrArg (fun source => reifiedObject? language rule spec bound source sort) same
  rw [reifiedObject?_canonical rule spec first firstAdmitted,
    reifiedObject?_canonical rule spec second secondAdmitted] at decoded
  exact Option.some.inj decoded

/-- The repeated-value equality used by the existing raw matcher reflects
typed body agreement when both contextual bodies have this earned profile.
The ordinary ambient suffix is retained rather than normalized away. -/
theorem CanonicalObject.contextualValue_eq_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    {dependencies ambient : List TypeExpr} {sort : TypeExpr}
    {first second : Term (signatureOf language) (dependencies ++ ambient) sort}
    (firstAdmitted : CanonicalObject first) (secondAdmitted : CanonicalObject second) :
    contextualValue (dependencies := dependencies) (ambient := ambient) first =
        contextualValue (dependencies := dependencies) (ambient := ambient) second ↔ first = second := by
  constructor
  · intro same
    exact CanonicalObject.erase_injective rule spec firstAdmitted secondAdmitted
      (congrArg ContextualValue.body same)
  · rintro rfl
    rfl

theorem CanonicalObject.literal_comparison_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    (name : String) {bound : List TypeExpr} {sort : TypeExpr}
    {first second : Term (signatureOf language) bound sort}
    (firstAdmitted : CanonicalObject first) (secondAdmitted : CanonicalObject second) :
    literalBodyComparison name (erase first) (erase second) = true ↔ first = second := by
  simp only [literalBodyComparison, beq_iff_eq]
  constructor
  · exact CanonicalObject.erase_injective rule spec firstAdmitted secondAdmitted
  · rintro rfl
    rfl

/-- The raw-target admission policy is exactly representability by an
independently canonical object at the caller's declared context and sort. -/
theorem reifyTarget?_canonical_iff (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    (reifyTarget? language rule spec bound source sort).isSome = true ↔
      ∃ object : Term (signatureOf language) bound sort,
        CanonicalObject object ∧ erase object = source := by
  constructor
  · intro admitted
    cases found : reifyTarget? language rule spec bound source sort with
    | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at admitted
    | some target => exact ⟨target.object, target.object_canonical, target.object_readback⟩
  · rintro ⟨object, admitted, rfl⟩
    have decoded := reifiedObject?_canonical rule spec object admitted
    unfold reifiedObject? at decoded
    cases found : reifyTarget? language rule spec bound (erase object) sort with
    | none => simp only [found, Option.map_none, reduceCtorEq] at decoded
    | some target => rfl

end TargetReification

namespace RawMatching

open SchemaElaboration
open TargetReification
open InputRecovery
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

variable {rule : RewriteRule} {spec : RuleBindingSpec}

abbrev RawAccumulator := Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment

/-- The raw capture image of an existing typed body with no ordinary
ambient suffix. Its declared dependency context is retained exactly. -/
def bodyValue {dependencies : List TypeExpr} {sort : TypeExpr}
    (body : Term (signatureOf language) dependencies sort) : ContextualValue :=
  { dependencies := dependencies, ambient := 0, body := erase body }

theorem bodyValue_eq_iff (rule : RewriteRule) (spec : RuleBindingSpec)
    {dependencies : List TypeExpr} {sort : TypeExpr}
    {first second : Term (signatureOf language) dependencies sort}
    (firstCanonical : CanonicalObject first) (secondCanonical : CanonicalObject second) :
    bodyValue first = bodyValue second ↔ first = second := by
  constructor
  · intro equal
    exact CanonicalObject.erase_injective rule spec firstCanonical secondCanonical
      (congrArg ContextualValue.body equal)
  · rintro rfl
    rfl

private theorem injPrefix_unScope_empty {S : Signature} :
    ∀ (bound : Ctx S) {sort : S.Srt} (position : Var (bound ++ []) sort),
      injPrefix (S := S) (Γ := []) bound (unScopeVar bound position) = position
  | [], _, position => nomatch position
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ position =>
      congrArg Var.succ (injPrefix_unScope_empty rest position)

private theorem rename_prefix_unScope {S : Signature} {bound : Ctx S} {sort : S.Srt}
    (target : Term S (bound ++ []) sort) :
    rename (fun _ position => injPrefix (S := S) (Γ := []) bound position)
      (unScope bound target) = target := by
  simp only [unScope, rename_comp, injPrefix_unScope_empty, rename_id]

private theorem prefix_shared {S : Signature} {M : List (MetaArity S)} :
    ∀ (bound : Ctx S) {sort : S.Srt} (position : Var bound sort),
      injPrefix (S := withMetas S M) (Γ := []) bound position =
        injPrefix (S := S) (Γ := []) bound position
  | [], _, position => nomatch position
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ position => congrArg Var.succ (prefix_shared rest position)

/-- Source admission supplies the actual recognized injective spine. The
typed matcher's checked projection and body traversal recover precisely
the preimages under the original dependency argument substitution. -/
theorem input_typed_recovery_iff
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    {result : TypeExpr}
    (target : Term (signatureOf language) (locals ++ []) result)
    (body : Term (signatureOf language) input.dependencies result) :
    recoverBoundVariableBody
        (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
          (Γ := []) locals position) (embedArgs input.compiled.arguments)) target = some body ↔
      bind (argsToSub input.compiled.arguments) body = unScope (S := signatureOf language) locals target := by
  obtain ⟨selected, _⟩ := input.recognizes_arguments
  obtain ⟨embedded, embeddedRecognized⟩ :=
    SchemaElaboration.CompiledInputOccurrence.recognizes_embedded_arguments input
  have sameRho : embedded.rho = selected.rho := by
    funext result position
    apply Term.var.inj (S := SchemaSignature language rule spec)
    exact (embedded.realizes result position).symm.trans
      ((argsToSub_embed input.compiled.arguments result position).trans
        (congrArg (embed (M := metaArities rule spec)) (selected.realizes result position)))
  simp only [recoverBoundVariableBody, strengthenA_renameArgs,
    recoverVariableArgumentBody, embeddedRecognized]
  rw [strengthenT_eq_some_iff, sameRho, selected.bind_eq_rename]

private theorem occurrence_zero_ambient
    {dependencies locals : List TypeExpr} {sort : TypeExpr}
    (arguments : DependencyArguments (language := language) dependencies locals)
    (selected : Mettapedia.OSLF.Binding.VariableArguments arguments)
    (body : Term (signatureOf language) dependencies sort) :
    bind (occurrenceSubstitution (appendAmbientArguments arguments []))
        (rename (fun _ position => injPrefix (S := signatureOf language)
          (Γ := []) dependencies position) body) =
      rename (fun _ position => injPrefix (S := signatureOf language)
        (Γ := []) locals position) (bind (argsToSub arguments) body) := by
  rw [occurrenceSubstitution_is_renaming arguments selected [], bind_var_eq_rename,
    selected.bind_eq_rename, rename_comp, rename_comp]
  congr 1
  funext result position
  simp only [appendAmbientRen, splitVar_injPrefix]

/-- Actual raw recovery and the actual typed recovery return the same body
image. Both directions include failure; no capture-success premise is used. -/
theorem input_recovery_eq
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    {result : TypeExpr}
    (target : Term (signatureOf language) (locals ++ []) result) :
    recoverValue? input.dependencies 0 locals.length (eraseArguments input.compiled.arguments)
        (erase target) =
      (recoverBoundVariableBody
        (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
          (Γ := []) locals position) (embedArgs input.compiled.arguments)) target).map bodyValue := by
  obtain ⟨selected, _⟩ := input.recognizes_arguments
  have forward : ∀ body : Term (signatureOf language) input.dependencies result,
      recoverBoundVariableBody
          (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
            (Γ := []) locals position) (embedArgs input.compiled.arguments)) target = some body →
        recoverValue? input.dependencies 0 locals.length (eraseArguments input.compiled.arguments)
          (erase target) = some (bodyValue body) := by
    intro body recovered
    have preimage := (input_typed_recovery_iff input target body).mp recovered
    let opened := rename (fun _ position => injPrefix (S := signatureOf language)
      (Γ := []) input.dependencies position) body
    have action : bind (occurrenceSubstitution
        (appendAmbientArguments input.compiled.arguments [])) opened = target := by
      rw [occurrence_zero_ambient input.compiled.arguments selected body,
        preimage, rename_prefix_unScope]
    have raw := InputRecovery.recoverValue?_typed_instance input.compiled.arguments
      input.supported input.indices input.checked (ambient := []) opened
    rw [action] at raw
    simpa only [contextualValue, bodyValue, List.length_nil, opened,
      erase_appendAmbient] using raw
  cases typed : recoverBoundVariableBody
      (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
        (Γ := []) locals position) (embedArgs input.compiled.arguments)) target with
  | some body => simpa only [Option.map_some] using forward body typed
  | none =>
      simp only [Option.map_none]
      cases raw : recoverValue? input.dependencies 0 locals.length
          (eraseArguments input.compiled.arguments) (erase target) with
      | none => rfl
      | some value =>
          obtain ⟨opened, _, action⟩ :=
            (InputRecovery.recoverValue?_intrinsic_iff input.compiled.arguments
              input.supported input.indices input.checked (ambient := []) target value).mp raw
          let body := unScope (S := signatureOf language) input.dependencies opened
          have openedImage : rename (fun _ position => injPrefix (S := signatureOf language)
              (Γ := []) input.dependencies position) body = opened := rename_prefix_unScope opened
          have image := occurrence_zero_ambient input.compiled.arguments selected body
          rw [openedImage, action] at image
          have recovered := (input_typed_recovery_iff input target body).mpr (by
            have lowered := congrArg (unScope (S := signatureOf language) locals) image.symm
            simpa only [unScope_rename_injPrefix] using lowered)
          rw [typed] at recovered
          contradiction

/-- The original recovery traversal preserves the independently checked
canonical object profile in every successful typed contextual body. -/
theorem input_recovered_canonical
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    {result : TypeExpr}
    (target : Term (signatureOf language) (locals ++ []) result)
    (targetCanonical : CanonicalObject target)
    (body : Term (signatureOf language) input.dependencies result)
    (recovered : recoverBoundVariableBody
      (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
        (Γ := []) locals position) (embedArgs input.compiled.arguments)) target = some body) :
    CanonicalObject body := by
  obtain ⟨selected, _⟩ := input.recognizes_arguments
  have image := (input_typed_recovery_iff input target body).mp recovered
  rw [selected.bind_eq_rename] at image
  unfold CanonicalObject at targetCanonical ⊢
  have canonicalImage := congrArg canonicalObject? image
  have sameProfile : canonicalObject? body = canonicalObject? target := by
    simpa only [unScope, canonicalObject?_rename] using canonicalImage
  exact sameProfile.trans targetCanonical

/-- Source admission gives distinct names at the actual type-context
positions, independently of which occurrence the matcher visits first. -/
theorem admitted_meta_names (admitted : admittedFor rule spec = true) :
    (rule.typeContext.map Prod.fst).Nodup := by
  simp only [admittedFor, Bool.and_eq_true, decide_eq_true_eq] at admitted
  exact admitted.1.1.1.1.1

theorem metaName_injective (admitted : admittedFor rule spec = true) :
    Function.Injective (metaName (language := language) rule spec) := by
  intro first second same
  apply Fin.ext
  have firstBound : first.val < (rule.typeContext.map Prod.fst).length := by
    simpa only [List.length_map, metaArities_length] using first.isLt
  have secondBound : second.val < (rule.typeContext.map Prod.fst).length := by
    simpa only [List.length_map, metaArities_length] using second.isLt
  apply ((admitted_meta_names admitted).getElem_inj_iff
    (hi := firstBound) (hj := secondBound)).mp
  simpa only [metaName, List.get_eq_getElem, List.getElem_map] using same

abbrev TypedAccumulator (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) := MAcc (signatureOf language) (metaArities rule spec) []

/-- Correspondence observes the raw first lookup at each actual declaration
position. It retains the typed sort and dependency context of every stored
canonical body; raw order, extra rows and duplicates are not quotiented. -/
structure AccCorresponds (raw : RawAccumulator)
    (typed : TypedAccumulator language rule spec) : Prop where
  lookups : ∀ index, lookup raw (metaName rule spec index) =
    (typed.metas index).map bodyValue
  canonical : ∀ index body, typed.metas index = some body → CanonicalObject body

theorem empty_corresponds : AccCorresponds (language := language) (rule := rule)
    (spec := spec) [] emptyMAcc := by
  constructor
  · intro index
    rfl
  · intro index body accepted
    contradiction

theorem lookup_cons_self (raw : RawAccumulator) (name : String) (value : ContextualValue) :
    lookup ((name, value) :: raw) name = some value := by
  simp [lookup]

theorem lookup_cons_other (raw : RawAccumulator) (name other : String) (value : ContextualValue)
    (different : name ≠ other) :
    lookup ((name, value) :: raw) other = lookup raw other := by
  simp [lookup, different]

/-- A fresh actual raw prepend and the existing typed `setMeta` update
preserve precisely the same declaration-indexed information. -/
theorem AccCorresponds.prepend_setMeta
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed) (admitted : admittedFor rule spec = true)
    (index : Fin (metaArities (language := language) rule spec).length)
    (body : Term (signatureOf language)
      ((metaArities rule spec).get index).1 ((metaArities rule spec).get index).2)
    (canonicalBody : CanonicalObject body) :
    AccCorresponds ((metaName rule spec index, bodyValue body) :: raw)
      (setMeta typed index body) := by
  constructor
  · intro queried
    by_cases same : index = queried
    · subst queried
      simp only [lookup_cons_self, setMeta, dite_true, Option.map_some]
    · have different : metaName rule spec index ≠ metaName rule spec queried := by
        intro equal
        exact same (metaName_injective admitted equal)
      simpa only [lookup_cons_other raw _ _ _ different, setMeta, dif_neg same] using
        related.lookups queried
  · intro queried captured accepted
    by_cases same : index = queried
    · subst queried
      simp only [setMeta, dite_true, Option.some.injEq] at accepted
      subst captured
      exact canonicalBody
    · simp only [setMeta, dif_neg same] at accepted
      exact related.canonical queried captured accepted

theorem AccCorresponds.assign_fresh
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed) (admitted : admittedFor rule spec = true)
    (index : Fin (metaArities (language := language) rule spec).length)
    (body : Term (signatureOf language)
      ((metaArities rule spec).get index).1 ((metaArities rule spec).get index).2)
    (canonicalBody : CanonicalObject body) (fresh : typed.metas index = none) :
    assign raw (metaName rule spec index) (bodyValue body) =
        some ((metaName rule spec index, bodyValue body) :: raw) ∧
      AccCorresponds ((metaName rule spec index, bodyValue body) :: raw)
        (setMeta typed index body) := by
  have rawFresh := related.lookups index
  rw [fresh, Option.map_none] at rawFresh
  exact ⟨by simp only [assign, rawFresh],
    related.prepend_setMeta admitted index body canonicalBody⟩

/-- Repeated source lookup keeps its original row exactly when the actual
typed accumulator comparison accepts the recovered canonical body. -/
theorem AccCorresponds.assign_repeated
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (index : Fin (metaArities (language := language) rule spec).length)
    (prior body : Term (signatureOf language)
      ((metaArities rule spec).get index).1 ((metaArities rule spec).get index).2)
    (canonicalBody : CanonicalObject body) (stored : typed.metas index = some prior) :
    assign raw (metaName rule spec index) (bodyValue body) =
      if prior = body then some raw else none := by
  have rawStored := related.lookups index
  rw [stored, Option.map_some] at rawStored
  simp only [assign, rawStored]
  have comparison := bodyValue_eq_iff rule spec (related.canonical index prior stored) canonicalBody
  simp only [beq_iff_eq, comparison]

/-- At a fixed source signature the retained raw first-lookups determine
the canonical typed accumulator. Its ordinary variable context is empty. -/
theorem AccCorresponds.unique_typed
    {raw : RawAccumulator} {first second : TypedAccumulator language rule spec}
    (firstRelated : AccCorresponds raw first) (secondRelated : AccCorresponds raw second) :
    first = second := by
  have sameVars : first.vars = second.vars := by
    funext result position
    exact nomatch position
  have sameMetas : first.metas = second.metas := by
    funext index
    have image := (firstRelated.lookups index).symm.trans (secondRelated.lookups index)
    cases firstStored : first.metas index with
    | none =>
        cases secondStored : second.metas index with
        | none => rfl
        | some body => simp only [firstStored, secondStored, Option.map_none,
            Option.map_some, reduceCtorEq] at image
    | some body =>
        cases secondStored : second.metas index with
        | none => simp only [firstStored, secondStored, Option.map_none,
            Option.map_some, reduceCtorEq] at image
        | some other =>
            simp only [firstStored, secondStored, Option.map_some, Option.some.injEq] at image
            exact congrArg some ((bodyValue_eq_iff rule spec
              (firstRelated.canonical index body firstStored)
              (secondRelated.canonical index other secondStored)).mp image)
  cases first
  cases second
  cases sameVars
  cases sameMetas
  rfl

private theorem erase_cast_sort {bound : List TypeExpr} {first second : TypeExpr}
    (same : first = second) (body : Term (signatureOf language) bound first) :
    erase (same ▸ body) = erase body := by
  cases same
  rfl

private theorem erase_cast_context {first second : List TypeExpr} {sort : TypeExpr}
    (same : first = second) (body : Term (signatureOf language) first sort) :
    erase (castTermCtx same body) = erase body := by
  cases same
  rfl

private theorem canonical_cast_sort {bound : List TypeExpr} {first second : TypeExpr}
    (same : first = second) (body : Term (signatureOf language) bound first) :
    canonicalObject? (same ▸ body) = canonicalObject? body := by
  cases same
  rfl

private theorem smatch_cast_sort
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {bound : List TypeExpr} {first second : TypeExpr} (same : first = second)
    (typed : TypedAccumulator language rule spec)
    (pattern : Term (SchemaSignature language rule spec) (bound ++ []) first)
    (target : Term (signatureOf language) (bound ++ []) second) :
    smatchAtT bound typed (same ▸ pattern) target =
      smatchAtT bound typed pattern (same.symm ▸ target) := by
  cases same
  rfl

/-- The actual source capture uses the same typed recovery result at the
metavariable's declaration-derived result sort and then calls `assign`. -/
theorem input_capture_eq
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (raw : RawAccumulator) (target : Term (signatureOf language) (locals ++ []) sort) :
    capture? rule spec 0 locals.length site path raw name (erase target) =
      (recoverBoundVariableBody
        (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
          (Γ := []) locals position) (embedArgs input.compiled.arguments))
        (input.compiled.result_sort.symm ▸ target)).bind
          (fun body => assign raw name (bodyValue body)) := by
  have recovered := input_recovery_eq input (input.compiled.result_sort.symm ▸ target)
  rw [erase_cast_sort] at recovered
  simp only [capture?, input.compiled.declared, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  rw [recovered, Option.bind_map]
  rfl

/-- The existing typed matcher reads the same source-selected head and
uses its existing `setMeta` and literal typed repeated-body comparison. -/
theorem input_smatch_eq
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (typed : TypedAccumulator language rule spec)
    (target : Term (signatureOf language) (locals ++ []) sort) :
    smatchAtT locals typed (CompiledSchema.ofInput input).term target =
      (recoverBoundVariableBody
        (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
          (Γ := []) locals position) (embedArgs input.compiled.arguments))
        (input.compiled.result_sort.symm ▸ target)).bind fun body =>
          match typed.metas (metaIndex rule spec input.compiled.index) with
          | none => some (setMeta typed (metaIndex rule spec input.compiled.index) body)
          | some prior => if prior = body then some typed else none := by
  change smatchAtT locals typed
    (rename (fun _ position => injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position) input.compiled.term) target = _
  rw [CompiledOccurrence.term, rename_cast_sort, smatch_cast_sort]
  change smatchAtT locals typed (.op (.inr (.mk (metaIndex rule spec input.compiled.index)))
    (renameArgs _ (embedArgs input.compiled.arguments))) _ = _
  rw [smatchAtT]
  cases recovered : recoverBoundVariableBody
    (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position) (embedArgs input.compiled.arguments))
    (input.compiled.result_sort.symm ▸ target) with
  | none => rfl
  | some body =>
      simp only [Option.bind_some]
      cases stored : typed.metas (metaIndex rule spec input.compiled.index) with
      | none => rfl
      | some prior =>
          by_cases same : prior = body <;> simp [same]

/-- Exact observations of the admitted ordered traversal. This relates
existing matcher outputs; it does not decide or perform a match. -/
inductive ResultsCorrespond : List RawAccumulator →
    Option (TypedAccumulator language rule spec) → Prop where
  | refused : ResultsCorrespond [] none
  | accepted {raw : RawAccumulator} {typed : TypedAccumulator language rule spec} :
      AccCorresponds raw typed → ResultsCorrespond [raw] (some typed)

theorem ResultsCorrespond.cardinality
    {rawResults : List RawAccumulator} {typedResult : Option (TypedAccumulator language rule spec)}
    (related : ResultsCorrespond rawResults typedResult) : rawResults.length ≤ 1 := by
  cases related <;> simp

theorem ResultsCorrespond.empty_iff
    {rawResults : List RawAccumulator} {typedResult : Option (TypedAccumulator language rule spec)}
    (related : ResultsCorrespond rawResults typedResult) :
    rawResults = [] ↔ typedResult = none := by
  cases related <;> simp

theorem ResultsCorrespond.raw_sound
    {rawResults : List RawAccumulator} {typedResult : Option (TypedAccumulator language rule spec)}
    (related : ResultsCorrespond rawResults typedResult) :
    ∀ raw ∈ rawResults, ∃ typed, typedResult = some typed ∧ AccCorresponds raw typed := by
  cases related with
  | refused => simp
  | @accepted raw typed agreement =>
      intro found member
      have same : found = raw := List.mem_singleton.mp member
      subst found
      exact ⟨typed, rfl, agreement⟩

theorem ResultsCorrespond.result_iff
    {rawResults : List RawAccumulator} {typedResult : Option (TypedAccumulator language rule spec)}
    (related : ResultsCorrespond rawResults typedResult)
    (final : TypedAccumulator language rule spec) :
    typedResult = some final ↔ ∃ found ∈ rawResults, AccCorresponds found final := by
  cases related with
  | refused => simp
  | @accepted raw typed agreement =>
      simp only [List.mem_singleton, exists_eq_left, Option.some.injEq]
      constructor
      · rintro rfl
        exact agreement
      · intro finalRelated
        exact agreement.unique_typed finalRelated

/-- Sequential traversal preserves exact observations using the existing
list occurrence composition and the existing optional typed composition. -/
theorem ResultsCorrespond.bind
    {rawResults : List RawAccumulator} {typedResult : Option (TypedAccumulator language rule spec)}
    (related : ResultsCorrespond rawResults typedResult)
    (rawNext : RawAccumulator → List RawAccumulator)
    (typedNext : TypedAccumulator language rule spec → Option (TypedAccumulator language rule spec))
    (next : ∀ raw typed, AccCorresponds raw typed →
      ResultsCorrespond (rawNext raw) (typedNext typed)) :
    ResultsCorrespond (rawResults.flatMap rawNext) (typedResult.bind typedNext) := by
  cases related with
  | refused => exact .refused
  | accepted agreement =>
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_some] using
        next _ _ agreement

/-- Fresh, repeated and conflicting leaf matches have exact corresponding
outputs, including refusal and the raw result's retained first row/order. -/
theorem input_match
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (targetCanonical : CanonicalObject target) :
    ResultsCorrespond
      (matchAt rule spec 0 site path locals.length raw (.fvar name) (erase target))
      (smatchAtT locals typed (CompiledSchema.ofInput input).term target) := by
  have sameName : metaName (language := language) rule spec
      (metaIndex rule spec input.compiled.index) = name := by
    unfold metaName metaIndex
    exact input.compiled.named
  have preparedCanonical : CanonicalObject (input.compiled.result_sort.symm ▸ target) := by
    unfold CanonicalObject at targetCanonical ⊢
    rw [canonical_cast_sort]
    exact targetCanonical
  rw [input_smatch_eq, matchAt_fvar, input_capture_eq]
  cases recovered : recoverBoundVariableBody
    (renameArgs (fun _ position => injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position) (embedArgs input.compiled.arguments))
    (input.compiled.result_sort.symm ▸ target) with
  | none => exact .refused
  | some body =>
      have canonicalBody := input_recovered_canonical input _ preparedCanonical body recovered
      simp only [Option.bind_some]
      cases stored : typed.metas (metaIndex rule spec input.compiled.index) with
      | none =>
          obtain ⟨assigned, nextRelated⟩ := related.assign_fresh input.admitted
            (metaIndex rule spec input.compiled.index) body canonicalBody stored
          rw [sameName] at assigned nextRelated
          rw [assigned]
          exact .accepted nextRelated
      | some prior =>
          have assigned := related.assign_repeated (metaIndex rule spec input.compiled.index)
            prior body canonicalBody stored
          rw [sameName] at assigned
          rw [assigned]
          by_cases same : prior = body
          · simp only [same, if_true]
            exact .accepted related
          · simp only [same, if_false]
            exact .refused

theorem input_match_iff
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (targetCanonical : CanonicalObject target)
    (final : TypedAccumulator language rule spec) :
    smatchAtT locals typed (CompiledSchema.ofInput input).term target = some final ↔
      ∃ found ∈ matchAt rule spec 0 site path locals.length raw (.fvar name) (erase target),
        AccCorresponds found final :=
  (input_match input related target targetCanonical).result_iff final

theorem raw_bound_variable_match (site : RulePatternSite) (path : List Nat)
    (depth index : Nat) (raw : RawAccumulator) (target : Pattern) :
    matchAt rule spec 0 site path depth raw (.bvar index) target =
      if target = .bvar index then [raw] else [] := by
  cases target <;> simp only [matchAt, matchAtWith, reduceCtorEq, if_false]
  rename_i actual
  simp only [beq_iff_eq, Pattern.bvar.injEq]
  by_cases same : index = actual
  · rw [if_pos same, if_pos same.symm]
  · rw [if_neg same, if_neg (fun equal => same equal.symm)]

/-- Bound-variable traversal reflects exact typed positions at the fixed
sorted context; numerical equality cannot authorize a wrong-sort body. -/
theorem bound_variable_match
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {sort : TypeExpr}
    (site : RulePatternSite) (path : List Nat)
    (position : Var locals sort)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (targetCanonical : CanonicalObject target) :
    ResultsCorrespond
      (matchAt rule spec 0 site path locals.length raw (.bvar (variableIndex position)) (erase target))
      (smatchAtT locals typed
        (.var (injPrefix (S := SchemaSignature language rule spec) (Γ := []) locals position)) target) := by
  have expectedErase : erase (Term.var (S := signatureOf language)
      (injPrefix (S := signatureOf language) (Γ := []) locals position)) =
        .bvar (variableIndex position) := by
    change Pattern.bvar (variableIndex (injPrefix (S := signatureOf language)
      (Γ := []) locals position)) = _
    rw [InputRecovery.variableIndex_injPrefix]
  have same : erase target = .bvar (variableIndex position) ↔
      target = Term.var (S := signatureOf language)
        (injPrefix (S := signatureOf language) (Γ := []) locals position) := by
    constructor
    · intro image
      exact CanonicalObject.erase_injective rule spec targetCanonical
        (by simp only [CanonicalObject, canonicalObject?])
        (image.trans expectedErase.symm)
    · intro equal
      rw [equal]
      exact expectedErase
  rw [prefix_shared (S := signatureOf language) (M := metaArities rule spec) locals position,
    raw_bound_variable_match, smatchAtT,
    splitVar_injPrefix (S := signatureOf language) (Γ := []) locals position]
  change ResultsCorrespond
    (if erase target = .bvar (variableIndex position) then [raw] else [])
    (if target = Term.var (S := signatureOf language)
      (injPrefix (S := signatureOf language) (Γ := []) locals position) then some typed else none)
  by_cases equal : target = Term.var (S := signatureOf language)
      (injPrefix (S := signatureOf language) (Γ := []) locals position)
  · rw [if_pos equal, if_pos (same.mpr equal)]
    exact .accepted related
  · rw [if_neg equal, if_neg (fun image => equal (same.mp image))]
    exact .refused

/-- A proof bundle for the actual source and typed traversals at one
compiled address. It contains no traversal implementation or decision. -/
structure SchemaMatchesAt
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop where
  observed : ∀ (raw : RawAccumulator) (typed : TypedAccumulator language rule spec),
    AccCorresponds raw typed →
    ∀ target : Term (signatureOf language) (locals ++ []) sort, CanonicalObject target →
      ResultsCorrespond (matchAt rule spec 0 site path locals.length raw source (erase target))
        (smatchAtT locals typed compiled.term target)

theorem input_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    SchemaMatchesAt (CompiledSchema.ofInput input) site path :=
  ⟨fun _ _ related target canonical => input_match input related target canonical⟩

private theorem smatch_singleton
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    (locals binders : List TypeExpr) {sort : TypeExpr}
    (typed : TypedAccumulator language rule spec)
    (pattern : Term (SchemaSignature language rule spec) (binders ++ (locals ++ [])) sort)
    (target : Term (signatureOf language) (binders ++ (locals ++ [])) sort) :
    smatchAtA locals typed (.cons pattern .nil) (.cons target .nil) =
      smatchAtT (binders ++ locals) typed
        (castTermCtx (List.append_assoc binders locals []).symm pattern)
        (castTermCtx (List.append_assoc binders locals []).symm target) := by
  rw [smatchAtA]
  cases matched : smatchAtT (binders ++ locals) typed
      (castTermCtx (List.append_assoc binders locals []).symm pattern)
      (castTermCtx (List.append_assoc binders locals []).symm target) with
  | none => rfl
  | some final => exact smatchAtA_nil locals final

/-- An anonymous representation binder uses the same computed context and
physical child address in both existing traversals. -/
theorem lambda_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {source : Pattern} {domain codomain : TypeExpr}
    {site : RulePatternSite} {path : List Nat}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain)
    (bodyMatches : SchemaMatchesAt body site (path ++ [0])) :
    SchemaMatchesAt (CompiledSchema.lambda body) site path := by
  constructor
  intro raw typed related target targetCanonical
  match target with
  | .var position =>
      simp only [CompiledSchema.lambda, erase, matchAt, matchAtWith]
      rw [smatchAtT]
      exact .refused
  | .op operator arguments =>
      cases operator with
      | lambda domain codomain =>
          match arguments with
          | .cons targetBody .nil =>
              have bodyCanonical : CanonicalObject targetBody := by
                simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true]
                  using targetCanonical
              have observed := bodyMatches.observed raw typed related targetBody bodyCanonical
              simp only [CompiledSchema.lambda, erase, matchAt, matchAtWith]
              rw [smatchAtT, dif_pos rfl]
              dsimp only
              rw [smatch_singleton]
              simpa only [matchAt, List.length_cons, castTermCtx, List.singleton_append] using observed
      | multiLambda domain codomain count =>
          match arguments with
          | .cons _ .nil =>
              simp only [CompiledSchema.lambda, erase, matchAt, matchAtWith]
              rw [smatchAtT, dif_neg (by intro same; cases same)]
              exact .refused
      | subst domain codomain =>
          simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at targetCanonical

theorem cast_sort_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {source : Pattern} {first second : TypeExpr}
    {site : RulePatternSite} {path : List Nat}
    (compiled : CompiledSchema language rule spec locals source first)
    (matched : SchemaMatchesAt compiled site path) (same : first = second) :
    SchemaMatchesAt (compiled.castSort same) site path := by
  constructor
  intro raw typed related target targetCanonical
  have preparedCanonical : CanonicalObject (same.symm ▸ target) := by
    unfold CanonicalObject at targetCanonical ⊢
    rw [canonical_cast_sort]
    exact targetCanonical
  have observed := matched.observed raw typed related (same.symm ▸ target) preparedCanonical
  simpa only [CompiledSchema.castSort, smatch_cast_sort, erase_cast_sort] using observed

/-- Multiple representation binders retain their actual count and child
address. Different counts are refused by both existing matcher functions. -/
theorem multiLambda_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {source : Pattern} {domain codomain : TypeExpr}
    {site : RulePatternSite} {path : List Nat} (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    (bodyMatches : SchemaMatchesAt body site (path ++ [0])) :
    SchemaMatchesAt (CompiledSchema.multiLambda count body) site path := by
  constructor
  intro raw typed related target targetCanonical
  match target with
  | .var position =>
      simp only [CompiledSchema.multiLambda, erase, matchAt, matchAtWith]
      rw [smatchAtT]
      exact .refused
  | .op operator arguments =>
      cases operator with
      | lambda domain codomain =>
          match arguments with
          | .cons _ .nil =>
              simp only [CompiledSchema.multiLambda, erase, matchAt, matchAtWith]
              rw [smatchAtT, dif_neg (by intro same; cases same)]
              exact .refused
      | multiLambda domain codomain actualCount =>
          match arguments with
          | .cons targetBody .nil =>
              by_cases sameCount : count = actualCount
              · subst actualCount
                have bodyCanonical : CanonicalObject targetBody := by
                  simpa only [CanonicalObject, canonicalObject?, canonicalObjectArguments?, Bool.and_true]
                    using targetCanonical
                let lowered := castTermCtx
                  (List.append_assoc (List.replicate count domain) locals []).symm targetBody
                have loweredCanonical : CanonicalObject lowered := by
                  unfold CanonicalObject at bodyCanonical ⊢
                  rw [canonicalObject?_cast_context]
                  exact bodyCanonical
                have observed := bodyMatches.observed raw typed related lowered loweredCanonical
                simp only [CompiledSchema.multiLambda, erase, matchAt, matchAtWith]
                rw [if_pos (by simp), smatchAtT, dif_pos rfl]
                dsimp only
                rw [smatch_singleton, cast_context_inverse]
                simpa only [matchAt, List.length_append, List.length_replicate,
                  Nat.add_comm locals.length count, lowered, erase_cast_context]
                  using observed
              · simp only [CompiledSchema.multiLambda, erase, matchAt, matchAtWith]
                rw [if_neg (by simpa only [beq_iff_eq] using sameCount), smatchAtT]
                rw [dif_neg (by
                  intro same
                  have equal : count = actualCount := by cases same; rfl
                  exact sameCount equal)]
                exact .refused
      | subst domain codomain =>
          simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at targetCanonical

/-- An ordered element row compares the actual physical source occurrences
with the existing typed argument traversal. -/
structure VectorMatchesAt
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {sources : List Pattern} {elementSort : TypeExpr}
    (elements : CompiledVectorElements language rule spec locals sources elementSort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop where
  observed : ∀ (raw : RawAccumulator) (typed : TypedAccumulator language rule spec),
    AccCorresponds raw typed →
    ∀ targets : Args (signatureOf language)
        (List.replicate sources.length ([], elementSort)) (locals ++ []),
      canonicalObjectArguments? targets = true →
      ResultsCorrespond
        (matchArgsAt rule spec 0 site path locals.length raw offset sources (eraseArguments targets))
        (smatchAtA locals typed elements.arguments targets)

/-- Successful element compilation earns the row observation from its
actual child calls, without changing either matching operation. -/
theorem compile_vector_elements_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → SchemaMatchesAt compiled site path)
    (locals : List TypeExpr) (path : List Nat) (elementSort : TypeExpr) :
    ∀ sources offset
      (elements : CompiledVectorElements language rule spec locals sources elementSort),
      compileVectorElements? compile locals path offset elementSort sources = some elements →
        VectorMatchesAt elements site path offset := by
  refine compileVectorElements?_observes compile locals path elementSort
    (fun offset _ compiled => VectorMatchesAt compiled site path offset) ?_ ?_
  · intro offset
    constructor
    intro raw typed related targets _
    cases targets
    simp only [eraseArguments, matchArgsAt, matchArgsAtWith]
    rw [smatchAtA]
    exact .accepted related
  · intro offset source sources head tail headFound tailObserved
    have headMatches := children locals (path ++ [offset]) source elementSort head headFound
    have tailMatches := tailObserved
    constructor
    intro raw typed related targets canonical
    cases targets with
    | cons target targetTail =>
        have supported : CanonicalObject target ∧
            canonicalObjectArguments? targetTail = true := by
          simpa only [CanonicalObject, canonicalObjectArguments?, Bool.and_eq_true] using canonical
        have observed := headMatches.observed raw typed related target supported.1
        have composed := observed.bind
          (fun next => matchArgsAt rule spec 0 site path locals.length next (offset + 1)
            sources (eraseArguments targetTail))
          (fun next => smatchAtA locals next tail.arguments targetTail)
          (fun _ _ nextRelated => tailMatches.observed _ _ nextRelated targetTail supported.2)
        simp only [eraseArguments, matchArgsAt, matchArgsAtWith]
        rw [smatchAtA]
        cases headMatched : smatchAtT locals typed head.term target with
        | none =>
            simpa only [matchAt, matchArgsAt, castTermCtx, List.nil_append,
              headMatched, Option.bind_none] using composed
        | some next =>
            simpa only [matchAt, matchArgsAt, castTermCtx, List.nil_append,
              headMatched, Option.bind_some] using composed


/-- Ordered source rows cannot succeed at a different target length,
regardless of any earlier captures in the row. -/
theorem match_args_length_refusal (site : RulePatternSite) (path : List Nat) (depth : Nat) :
    ∀ (sources targets : List Pattern) (raw : RawAccumulator) (offset : Nat),
      sources.length ≠ targets.length →
      matchArgsAt rule spec 0 site path depth raw offset sources targets = [] := by
  intro sources
  induction sources with
  | nil =>
      intro targets raw offset unequal
      cases targets with
      | nil => exact False.elim (unequal rfl)
      | cons _ _ => simp only [matchArgsAt, matchArgsAtWith]
  | cons source sources induction =>
      intro targets raw offset unequal
      cases targets with
      | nil => simp only [matchArgsAt, matchArgsAtWith]
      | cons target targets =>
          have tailUnequal : sources.length ≠ targets.length := by
            intro equal
            exact unequal (congrArg Nat.succ equal)
          rw [matchArgsAt, matchArgsAtWith]
          apply List.flatMap_eq_nil_iff.mpr
          intro next _
          exact induction targets next (offset + 1) tailUnequal

private theorem raw_vector_match (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (sources targets : List Pattern) :
    matchAt rule spec 0 site path depth raw (.collection .vec sources none)
      (.collection .vec targets none) =
        matchArgsAt rule spec 0 site path depth raw 0 sources targets := by
  rw [matchAt, matchAtWith, if_pos (by decide), if_pos (by decide)]
  rfl

/-- Direct vectors keep ordered occurrence multiplicity. A target with a
different element count is refused by the actual source and typed traversals. -/
theorem vector_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {sources : List Pattern} {elementSort : TypeExpr}
    {site : RulePatternSite} {path : List Nat}
    (elements : CompiledVectorElements language rule spec locals sources elementSort)
    (elementsMatch : VectorMatchesAt elements site path 0) :
    SchemaMatchesAt (CompiledSchema.vector elements) site path := by
  constructor
  intro raw typed related target targetCanonical
  match target with
  | .var position =>
      simp only [CompiledSchema.vector, erase, matchAt, matchAtWith]
      rw [smatchAtT]
      exact .refused
  | .op operator arguments =>
      cases operator with
      | collection kind elementSort count =>
          have argumentsCanonical : canonicalObjectArguments? arguments = true := by
            simpa only [CanonicalObject, canonicalObject?, decide_true, Bool.true_and] using targetCanonical
          by_cases sameCount : sources.length = count
          · subst count
            simp only [CompiledSchema.vector, erase]
            rw [raw_vector_match, smatchAtT, dif_pos rfl]
            dsimp only
            exact elementsMatch.observed raw typed related arguments argumentsCanonical
          · have lengthUnequal : sources.length ≠ (eraseArguments arguments).length := by
              rw [ObjectRoundtrip.eraseVectorArguments_length]
              exact sameCount
            simp only [CompiledSchema.vector, erase]
            rw [raw_vector_match, match_args_length_refusal site path locals.length
              sources (eraseArguments arguments) raw 0 lengthUnequal, smatchAtT]
            rw [dif_neg (by
              intro same
              have equal : sources.length = count := by cases same; rfl
              exact sameCount equal)]
            exact .refused
      | subst domain codomain =>
          simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at targetCanonical

/-- A successful representation-wrapper match retains the declaration's
actual binding context and body sort, including multiple-binder counts. -/
theorem parameter_scope_of_nonempty
    {parameter : TermParam} {firstBinders secondBinders : List TypeExpr}
    {firstSort secondSort : TypeExpr}
    (scope : ParameterScope parameter firstBinders firstSort)
    (targetScope : ParameterScope parameter secondBinders secondSort)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (source target : Pattern)
    (nonempty : matchAt rule spec 0 site path depth raw
      (scope.wrap source) (targetScope.wrap target) ≠ []) :
    ∃ _sameBinders : firstBinders = secondBinders,
      ∃ _sameSort : firstSort = secondSort, HEq scope targetScope := by
  cases scope with
  | simple name sort =>
      cases targetScope
      exact ⟨rfl, rfl, HEq.rfl⟩
  | abstraction binder name domain codomain =>
      cases targetScope
      exact ⟨rfl, rfl, HEq.rfl⟩
  | abstractionBase binder name sort =>
      cases targetScope
      exact ⟨rfl, rfl, HEq.rfl⟩
  | multiAbstraction binders name domain codomain count =>
      cases targetScope with
      | multiAbstraction _ _ _ _ targetCount =>
          by_cases same : count = targetCount
          · subst targetCount
            exact ⟨rfl, rfl, HEq.rfl⟩
          · simp only [ParameterScope.wrap, matchAt, matchAtWith] at nonempty
            rw [if_neg (by simpa only [beq_iff_eq] using same)] at nonempty
            exact False.elim (nonempty rfl)
  | multiAbstractionBase binders name sort count =>
      cases targetScope with
      | multiAbstractionBase _ _ _ targetCount =>
          by_cases same : count = targetCount
          · subst targetCount
            exact ⟨rfl, rfl, HEq.rfl⟩
          · simp only [ParameterScope.wrap, matchAt, matchAtWith] at nonempty
            rw [if_neg (by simpa only [beq_iff_eq] using same)] at nonempty
            exact False.elim (nonempty rfl)

/-- Ordered source success forces the complete declaration-derived scope
row to agree. This earns operator alignment from actual wrapper matches;
it does not infer typed equality from erased bodies. -/
theorem constructor_scopes_of_nonempty
    (site : RulePatternSite) (path : List Nat) (depth : Nat) :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (patterns : Args (SchemaSignature language rule spec) arity bound),
    ∀ {targetArity : List (List TypeExpr × TypeExpr)}
      (targetScopes : ParameterScopes parameters targetArity)
      (targets : Args (signatureOf language) targetArity bound)
      (raw : RawAccumulator) (offset : Nat),
      matchArgsAt rule spec 0 site path depth raw offset
          (readbackConstructorArguments scopes patterns)
          (eraseConstructorArguments targetScopes targets) ≠ [] →
        ∃ same : arity = targetArity, same ▸ scopes = targetScopes := by
  intro parameters arity bound scopes
  induction scopes with
  | nil =>
      intro patterns targetArity targetScopes targets raw offset _
      cases targetScopes
      exact ⟨rfl, rfl⟩
  | @cons parameter parameters binders sort arity scope scopes induction =>
      intro patterns targetArity targetScopes targets raw offset nonempty
      match patterns with
      | .cons pattern patterns =>
          cases targetScopes with
          | @cons _ _ targetBinders targetSort targetArity targetScope targetScopes =>
              match targets with
              | .cons target targetTail =>
                  rw [readbackConstructorArguments, eraseConstructorArguments,
                    matchArgsAt, matchArgsAtWith] at nonempty
                  change ((matchAt rule spec 0 site (path ++ [offset]) depth raw
                    (scope.wrap (readback pattern)) (targetScope.wrap (erase target))).flatMap
                    (fun next => matchArgsAt rule spec 0 site path depth next (offset + 1)
                      (readbackConstructorArguments scopes patterns)
                      (eraseConstructorArguments targetScopes targetTail))) ≠ [] at nonempty
                  have surviving : ∃ next,
                      next ∈ matchAt rule spec 0 site (path ++ [offset]) depth raw
                        (scope.wrap (readback pattern)) (targetScope.wrap (erase target)) ∧
                      matchArgsAt rule spec 0 site path depth next (offset + 1)
                        (readbackConstructorArguments scopes patterns)
                        (eraseConstructorArguments targetScopes targetTail) ≠ [] := by
                    by_contra missing
                    apply nonempty
                    apply List.flatMap_eq_nil_iff.mpr
                    intro next member
                    by_contra remains
                    exact missing ⟨next, member, remains⟩
                  rcases surviving with ⟨next, member, tailNonempty⟩
                  have headNonempty : matchAt rule spec 0 site (path ++ [offset]) depth raw
                      (scope.wrap (readback pattern)) (targetScope.wrap (erase target)) ≠ [] := by
                    intro empty
                    rw [empty] at member
                    cases member
                  obtain ⟨sameBinders, sameSort, sameScope⟩ := parameter_scope_of_nonempty
                    scope targetScope site (path ++ [offset]) depth raw
                    (readback pattern) (erase target) headNonempty
                  cases sameBinders
                  cases sameSort
                  have scopeEqual := eq_of_heq sameScope
                  subst targetScope
                  obtain ⟨sameTail, sameScopes⟩ := induction patterns targetScopes targetTail
                    next (offset + 1) tailNonempty
                  cases sameTail
                  cases sameScopes
                  exact ⟨rfl, rfl⟩


/-- A declaration wrapper contributes precisely its physical child suffix
and the length of its existing intrinsic binding context. -/
theorem parameter_scope_match {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (source target : Pattern) :
    matchAt rule spec 0 site path depth raw (scope.wrap source) (scope.wrap target) =
      matchAt rule spec 0 site (path ++ ObjectRoundtrip.parameterChildSuffix scope)
        (depth + binders.length) raw source target := by
  cases scope <;>
    simp only [ParameterScope.wrap, ObjectRoundtrip.parameterChildSuffix,
      List.length_nil, List.length_cons, List.length_replicate,
      List.append_nil, Nat.add_zero, matchAt, matchAtWith, beq_self_eq_true, if_true]

/-- Successful unwrapping earns the actual suffix used by the source
compiler, including its count-zero multiple-binder case. -/
theorem parameter_body_match {parameter : TermParam} {source : Pattern}
    (body : ParameterBody parameter source)
    (found : parameterBody? parameter source = some body)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (target : Pattern) :
    matchAt rule spec 0 site path depth raw source (body.scope.wrap target) =
      matchAt rule spec 0 site (path ++ body.pathSuffix)
        (depth + body.binders.length) raw body.body target := by
  rcases body with ⟨binders, sort, scope, body, suffix, readback⟩
  cases readback
  rw [ObjectRoundtrip.parameterBody?_wrapped] at found
  cases Option.some.inj found
  exact parameter_scope_match scope site path depth raw body target

/-- Constructor arguments observe their declaration's exact scope row.
Binding wrappers are retained by the raw traversal and removed only by the
existing intrinsic arity interpreter. -/
structure ConstructorMatchesAt
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {parameters : List TermParam} {sources : List Pattern}
    (arguments : CompiledConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop where
  observed : ∀ (raw : RawAccumulator) (typed : TypedAccumulator language rule spec),
    AccCorresponds raw typed →
    ∀ targets : Args (signatureOf language) arguments.arity (locals ++ []),
      canonicalObjectArguments? targets = true →
      ResultsCorrespond
        (matchArgsAt rule spec 0 site path locals.length raw offset sources
          (eraseConstructorArguments arguments.scopes targets))
        (smatchAtA locals typed arguments.arguments targets)

/-- The actual argument compiler earns ordered matching correspondence
from each successful recursive body compilation and its authored address. -/
theorem compile_constructor_arguments_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → SchemaMatchesAt compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        ConstructorMatchesAt arguments site path offset := by
  refine compileConstructorArguments?_observes compile locals path
    (fun offset _ _ compiled => ConstructorMatchesAt compiled site path offset) ?_ ?_
  · intro offset
    constructor
    intro raw typed related targets _
    dsimp only at targets
    match targets with
    | .nil =>
        simp only [eraseConstructorArguments, matchArgsAt, matchArgsAtWith]
        rw [smatchAtA]
        exact .accepted related
  · intro offset parameter parameters source sources body head tail bodyFound headFound tailObserved
    have headMatches := children (body.binders ++ locals)
      (path ++ [offset] ++ body.pathSuffix) body.body body.sort head headFound
    have tailMatches := tailObserved
    constructor
    intro raw typed related targets canonical
    dsimp only at targets
    match targets with
    | .cons target targetTail =>
        have supported : CanonicalObject target ∧
            canonicalObjectArguments? targetTail = true := by
          simpa only [CanonicalObject, canonicalObjectArguments?, Bool.and_eq_true]
            using canonical
        let lowered := castTermCtx
          (List.append_assoc body.binders locals []).symm target
        have loweredCanonical : CanonicalObject lowered := by
          unfold CanonicalObject at supported ⊢
          rw [canonicalObject?_cast_context]
          exact supported.1
        have observed := headMatches.observed raw typed related lowered loweredCanonical
        have composed := observed.bind
          (fun next => matchArgsAt rule spec 0 site path locals.length next (offset + 1)
            sources (eraseConstructorArguments tail.scopes targetTail))
          (fun next => smatchAtA locals next tail.arguments targetTail)
          (fun _ _ nextRelated => tailMatches.observed _ _ nextRelated targetTail supported.2)
        simp only [eraseConstructorArguments, matchArgsAt, matchArgsAtWith]
        rw [← matchAt, parameter_body_match body bodyFound site
          (path ++ [offset]) locals.length raw (erase target), smatchAtA,
          cast_context_inverse]
        have sameDepth : locals.length + body.binders.length =
            (body.binders ++ locals).length := by simp only [List.length_append]; omega
        rw [sameDepth]
        cases headMatched : smatchAtT (body.binders ++ locals) typed head.term lowered with
        | none =>
            simpa only [matchArgsAt, lowered, erase_cast_context, headMatched,
              Option.bind_none] using composed
        | some next =>
            simpa only [matchArgsAt, lowered, erase_cast_context, headMatched,
              Option.bind_some] using composed


/-- A canonical target constructor with the selected authored label uses
that unique physical declaration. -/
theorem selected_constructor_declaration {label : String}
    (selected : SelectedConstructor language label) (declaration : GrammarRule)
    (canonical : canonicalConstructor? language declaration = true)
    (named : declaration.label = label) :
    language.terms.get selected.index = declaration := by
  subst label
  unfold canonicalConstructor? at canonical
  rw [selectConstructor?_complete selected] at canonical
  exact of_decide_eq_true canonical

/-- Nonempty ordinary raw matching recovers the existing typed operator,
including its arity and declaration-derived scopes. Result-sort equality
is earned through that declaration rather than inferred from erasure. -/
theorem constructor_operator_of_nonempty
    {label : String} (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (scopes : ParameterScopes (language.terms.get selected.index).params arity)
    (patterns : Args (SchemaSignature language rule spec) arity bound)
    {result : TypeExpr} (operator : Operator language result)
    (targets : Args (signatureOf language) ((signatureOf language).arity operator) bound)
    (canonical : CanonicalObject (Term.op operator targets))
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (raw : RawAccumulator)
    (nonempty : matchAt rule spec 0 site path depth raw
      (.apply label (readbackConstructorArguments scopes patterns))
      (erase (Term.op operator targets)) ≠ []) :
    HEq (Operator.constructor (language.terms.get selected.index)
      (List.get_mem _ _) ordinary scopes) operator := by
  cases operator with
  | @constructor declaration member targetOrdinary targetArity targetScopes =>
      have supported : canonicalConstructor? language declaration = true ∧
          canonicalObjectArguments? targets = true := by
        simpa only [CanonicalObject, canonicalObject?, Bool.and_eq_true] using canonical
      simp only [erase, matchAt, matchAtWith] at nonempty
      by_cases sameLabel : label = declaration.label
      · rw [if_pos (by simpa only [beq_iff_eq] using sameLabel)] at nonempty
        have sameDeclaration := selected_constructor_declaration selected declaration
          supported.1 sameLabel.symm
        subst declaration
        obtain ⟨sameArity, sameScopes⟩ := constructor_scopes_of_nonempty
          site path depth scopes patterns targetScopes targets raw 0 nonempty
        cases sameArity
        cases sameScopes
        rfl
      · rw [if_neg (by simpa only [beq_iff_eq] using sameLabel)] at nonempty
        exact False.elim (nonempty rfl)
  | collectionConstructor declaration member parameterName kind elementSort shape count =>
      simp only [erase, matchAt, matchAtWith] at nonempty
      exact False.elim (nonempty rfl)
  | lambda domain codomain =>
      match targets with
      | .cons _ .nil =>
          simp only [erase, matchAt, matchAtWith] at nonempty
          exact False.elim (nonempty rfl)
  | multiLambda domain codomain count =>
      match targets with
      | .cons _ .nil =>
          simp only [erase, matchAt, matchAtWith] at nonempty
          exact False.elim (nonempty rfl)
  | subst domain codomain =>
      simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at canonical
  | collection kind elementSort count =>
      simp only [erase, matchAt, matchAtWith] at nonempty
      exact False.elim (nonempty rfl)

/-- Ordinary constructors align their physical declaration and binding
row from actual raw matching. Different wrappers cannot bypass the
existing typed operator comparison. -/
theorem constructor_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {label : String} {sources : List Pattern}
    {site : RulePatternSite} (path : List Nat)
    (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    (arguments : CompiledConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources)
    (argumentsMatch : ConstructorMatchesAt arguments site path 0) :
    SchemaMatchesAt (CompiledSchema.constructor path selected ordinary arguments) site path := by
  constructor
  intro raw typed related target targetCanonical
  match target with
  | .var position =>
      simp only [CompiledSchema.constructor, erase, matchAt, matchAtWith]
      rw [smatchAtT]
      exact .refused
  | .op operator targets =>
      by_cases same : Operator.constructor (language.terms.get selected.index)
          (List.get_mem _ _) ordinary arguments.scopes = operator
      · subst operator
        have targetsCanonical : canonicalObjectArguments? targets = true := by
          have supported : canonicalConstructor? language (language.terms.get selected.index) = true ∧
              canonicalObjectArguments? targets = true := by
            simpa only [CanonicalObject, canonicalObject?, Bool.and_eq_true] using targetCanonical
          exact supported.2
        simp only [CompiledSchema.constructor, erase]
        rw [selected.named, matchAt, matchAtWith, if_pos (by simp), smatchAtT, dif_pos rfl]
        exact argumentsMatch.observed raw typed related targets targetsCanonical
      · have refused : matchAt rule spec 0 site path locals.length raw
            (.apply label sources) (erase (Term.op operator targets)) = [] := by
          by_contra nonempty
          rw [← arguments.source_readback] at nonempty
          exact same (eq_of_heq (constructor_operator_of_nonempty selected ordinary
            arguments.scopes arguments.arguments operator targets targetCanonical
            site path locals.length raw nonempty))
        simp only [CompiledSchema.constructor]
        rw [refused, smatchAtT, dif_neg same]
        exact .refused


/-- A canonical bare vector at the declared result category retains the
selected physical declaration, parameter name and element sort. -/
theorem selected_vector_constructor_declaration {category : String}
    (selected : SelectedVectorConstructor language category) (declaration : GrammarRule)
    (parameterName : String) (elementSort : TypeExpr)
    (canonical : canonicalVectorConstructor? language declaration parameterName elementSort = true)
    (categorized : declaration.category = category) :
    language.terms.get selected.index = declaration ∧
      selected.parameterName = parameterName ∧ selected.elementSort = elementSort := by
  subst category
  obtain ⟨other, sameDeclaration, sameName, sameSort⟩ :=
    (canonicalVectorConstructor?_iff declaration parameterName elementSort).mp canonical
  have sameSelected : selected = other :=
    Option.some.inj ((SelectedVectorConstructor.selected selected).symm.trans
      (SelectedVectorConstructor.selected other))
  cases sameSelected
  exact ⟨sameDeclaration, sameName, sameSort⟩

/-- At the independently fixed result sort, actual nonempty bare-vector
matching earns the unique operator and exact element count. A direct
collection with a different result sort cannot supply that evidence. -/
theorem vector_constructor_operator_of_nonempty
    {category : String} (selected : SelectedVectorConstructor language category)
    (sources : List Pattern) {bound : List TypeExpr} {result : TypeExpr}
    (operator : Operator language result)
    (targets : Args (signatureOf language) ((signatureOf language).arity operator) bound)
    (sorted : result = .base category)
    (canonical : CanonicalObject (Term.op operator targets))
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (raw : RawAccumulator)
    (nonempty : matchAt rule spec 0 site path depth raw
      (.collection .vec sources none) (erase (Term.op operator targets)) ≠ []) :
    HEq (Operator.collectionConstructor (language.terms.get selected.index)
      (List.get_mem _ _) selected.parameterName .vec selected.elementSort
      selected.shape sources.length) operator := by
  cases operator with
  | constructor declaration member ordinary scopes =>
      simp only [erase, matchAt, matchAtWith] at nonempty
      exact False.elim (nonempty rfl)
  | collectionConstructor declaration member parameterName kind elementSort shape count =>
      have supported : ((kind = .vec) ∧
          canonicalVectorConstructor? language declaration parameterName elementSort = true) ∧
          canonicalObjectArguments? targets = true := by
        simpa only [CanonicalObject, canonicalObject?, Bool.and_eq_true, decide_eq_true_eq]
          using canonical
      rcases supported with ⟨⟨rfl, constructorCanonical⟩, _⟩
      have categorized : declaration.category = category := TypeExpr.base.inj sorted
      obtain ⟨sameDeclaration, sameName, sameSort⟩ := selected_vector_constructor_declaration
        selected declaration parameterName elementSort constructorCanonical categorized
      simp only [erase] at nonempty
      rw [raw_vector_match] at nonempty
      have sameCount : sources.length = count := by
        by_contra different
        have unequal : sources.length ≠ (eraseArguments targets).length := by
          rw [ObjectRoundtrip.eraseVectorArguments_length]
          exact different
        exact nonempty (match_args_length_refusal site path depth sources
          (eraseArguments targets) raw 0 unequal)
      subst declaration
      subst parameterName
      subst elementSort
      subst count
      rfl
  | lambda domain codomain => cases sorted
  | multiLambda domain codomain count => cases sorted
  | subst domain codomain =>
      simp only [CanonicalObject, canonicalObject?, Bool.false_eq_true] at canonical
  | collection kind elementSort count => cases sorted

/-- Bare vectors retain their declared result category, physical
constructor, element sort and ordered element multiplicity in both
existing matching traversals. -/
theorem vector_constructor_schema_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {locals : List TypeExpr} {sources : List Pattern} {category : String}
    {site : RulePatternSite} (path : List Nat)
    (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort)
    (elementsMatch : VectorMatchesAt elements site path 0) :
    SchemaMatchesAt (CompiledSchema.vectorConstructor path selected elements) site path := by
  unfold CompiledSchema.vectorConstructor
  apply cast_sort_schema_matches
  constructor
  intro raw typed related target targetCanonical
  match target with
  | .var position =>
      simp only [erase, matchAt, matchAtWith]
      rw [smatchAtT]
      exact .refused
  | .op operator targets =>
      by_cases same : Operator.collectionConstructor (language.terms.get selected.index)
          (List.get_mem _ _) selected.parameterName .vec selected.elementSort
          selected.shape sources.length = operator
      · subst operator
        have targetsCanonical : canonicalObjectArguments? targets = true := by
          have supported : canonicalVectorConstructor? language (language.terms.get selected.index)
                selected.parameterName selected.elementSort = true ∧
              canonicalObjectArguments? targets = true := by
            simpa only [CanonicalObject, canonicalObject?, decide_true, Bool.true_and, Bool.and_eq_true]
              using targetCanonical
          exact supported.2
        simp only [erase]
        rw [raw_vector_match, smatchAtT, dif_pos rfl]
        exact elementsMatch.observed raw typed related targets targetsCanonical
      · have refused : matchAt rule spec 0 site path locals.length raw
            (.collection .vec sources none) (erase (Term.op operator targets)) = [] := by
          by_contra nonempty
          exact same (eq_of_heq (vector_constructor_operator_of_nonempty selected sources
            operator targets (congrArg TypeExpr.base selected.categorized) targetCanonical
            site path locals.length raw nonempty))
        rw [refused, smatchAtT, dif_neg same]
        exact .refused


/-- Successful execution of the actual recursive schema compiler earns
raw and typed matching correspondence on independently canonical targets.
Every child, declaration, scope, source address and capture comes from
that execution; no recursive matching callback remains as a premise. -/
theorem compileSchemaWithFuel?_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
        SchemaMatchesAt compiled site path := by
  refine InputAssemblyInvariant.walk
    (observe := fun _ path _ _ compiled => SchemaMatchesAt compiled site path) ?_ fuel
  refine {
    bound := ?_
    free := fun _ _ _ _ input => input_schema_matches input
    constructor := fun compile children locals path _ sources selected ordinary arguments found =>
      constructor_schema_matches path selected ordinary arguments
        (compile_constructor_arguments_matches compile site children locals path sources 0 _ arguments found)
    abstraction := fun _ _ _ _ _ body action => lambda_schema_matches body action
    multiAbstraction := fun _ _ _ _ _ count body action => multiLambda_schema_matches count body action
    vector := fun compile children locals path sources elemSort elements found =>
      vector_schema_matches elements
        (compile_vector_elements_matches compile site children locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      vector_constructor_schema_matches path selected elements
        (compile_vector_elements_matches compile site children locals path
          selected.elementSort sources 0 elements found) }
  intro locals path index sort position admitted
  constructor
  intro raw typed related target canonical
  have observed := bound_variable_match site path position related target canonical
  rw [boundPosition?_index locals index sort admitted] at observed
  exact observed

/-- The computed source admission and independent canonical target profile
suffice for exact observations of the two original matcher executions. -/
theorem compiled_schema_match
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {fuel : Nat} {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (canonical : CanonicalObject target) :
    ResultsCorrespond (matchAt rule spec 0 site path locals.length raw source (erase target))
      (smatchAtT locals typed compiled.term target) :=
  (compileSchemaWithFuel?_matches site fuel locals path source sort compiled found).observed
    raw typed related target canonical

theorem compiled_schema_match_iff
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {fuel : Nat} {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (canonical : CanonicalObject target) (final : TypedAccumulator language rule spec) :
    smatchAtT locals typed compiled.term target = some final ↔
      ∃ result ∈ matchAt rule spec 0 site path locals.length raw source (erase target),
        AccCorresponds result final :=
  (compiled_schema_match compiled found related target canonical).result_iff final

theorem compiled_schema_refusal_iff
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {fuel : Nat} {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : Term (signatureOf language) (locals ++ []) sort)
    (canonical : CanonicalObject target) :
    matchAt rule spec 0 site path locals.length raw source (erase target) = [] ↔
      smatchAtT locals typed compiled.term target = none :=
  (compiled_schema_match compiled found related target canonical).empty_iff

/-- A target decoded by the existing source-facing codec earns its own
canonicality and exact raw image; callers supply no extra target predicate. -/
theorem compiled_schema_reified_match
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {fuel : Nat} {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {source rawTarget : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (related : AccCorresponds raw typed)
    (target : ReifiedTarget language rule spec locals rawTarget sort) :
    ResultsCorrespond (matchAt rule spec 0 site path locals.length raw source rawTarget)
      (smatchAtT locals typed compiled.term target.term) := by
  have observed := compiled_schema_match compiled found related target.term target.canonical
  rwa [target.readback] at observed

/-- Computed whole-side admission earns whole matching correspondence by
extracting its actual compiler execution. Original typing and premises
remain in the unchanged authored receipt. -/
theorem elaborateAuthoredSchema?_matches
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {ruleIndex : Fin language.rewrites.length} {site : RulePatternSite} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    SchemaMatchesAt compiled.compiled site [] := by
  exact compileSchemaWithFuel?_matches site _ _ _ _ _ compiled.compiled
    (elaborateAuthoredSchema?_compilation compiled found)

/-- Whole authored LHS matching starts with the original empty raw and
typed accumulators and retains every accepted canonical raw capture. -/
theorem authored_left_match
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {rawTarget : Pattern}
    (compiled : AuthoredSchema language ruleIndex .left sort)
    (found : elaborateAuthoredSchema? language ruleIndex .left sort = some compiled)
    (target : ReifiedTarget language (language.rewrites.get ruleIndex) compiled.spec [] rawTarget sort) :
    ResultsCorrespond (matchRuleAt (language.rewrites.get ruleIndex) compiled.spec 0 rawTarget)
      (smatchT emptyMAcc compiled.compiled.term target.term) := by
  have observed := (elaborateAuthoredSchema?_matches compiled found).observed
    [] emptyMAcc empty_corresponds target.term target.canonical
  have atSite := compiled.atSite
  simp only [sitePattern?, Option.some.injEq] at atSite
  simpa only [← atSite, target.readback, matchAt, matchRuleAt, matchRuleWithAt,
    smatchT, List.length_nil] using observed

end RawMatching

namespace RawInstantiation

open SchemaElaboration TargetReification RawMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

variable {rule : RewriteRule} {spec : RuleBindingSpec}

abbrev Bodies (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :=
  (index : Fin (metaArities (language := language) rule spec).length) →
    Term (signatureOf language) ((metaArities rule spec).get index).1
      ((metaArities rule spec).get index).2

def inputName : InputEvidence language rule spec → String
  | ⟨_, _, _, name, _, _⟩ => name

def inputIndex : InputEvidence language rule spec →
    Fin (metaArities (language := language) rule spec).length
  | ⟨_, _, _, _, _, input⟩ => metaIndex rule spec input.compiled.index

/-- Only the actual occurrence receipts of this compiled side are read.
Unused declarations require neither a capture nor a synthesized body. -/
def CapturesInputs (inputs : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : Bodies language rule spec) : Prop :=
  ∀ input ∈ inputs, lookup raw (inputName input) = some (bodyValue (bodies (inputIndex input)))

theorem capturesInputs_append (first second : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : Bodies language rule spec) :
    CapturesInputs (first ++ second) raw bodies ↔
      CapturesInputs first raw bodies ∧ CapturesInputs second raw bodies := by
  constructor
  · intro captured
    exact ⟨fun input member => captured input (List.mem_append_left _ member),
      fun input member => captured input (List.mem_append_right _ member)⟩
  · rintro ⟨firstCaptured, secondCaptured⟩ input member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact firstCaptured input firstMember
    · exact secondCaptured input secondMember

private theorem occurrence_closed_reads {locals : List TypeExpr} :
    ∀ {dependencies : List TypeExpr}
      (arguments : DependencyArguments (language := language) dependencies locals),
      ReadsSub (argsToSub arguments)
        (occurrenceAssignment dependencies.length locals.length (eraseArguments arguments))
  | [], .nil => by intro sort position; exact nomatch position
  | _ :: _, .cons head tail => by
      intro sort position
      cases position with
      | zero => simp [occurrenceAssignment, variableIndex, eraseArguments, argsToSub]
      | succ old =>
          rw [show variableIndex (Var.succ old) = variableIndex old + 1 by rfl]
          rw [show (_ :: _).length = _ + 1 by rfl, eraseArguments,
            occurrenceAssignment_succ]
          exact occurrence_closed_reads tail sort old

/-- Existing occurrence instantiation at ambient zero is the existing
typed body substitution; no second substitution traversal is used. -/
theorem instantiateValue?_bodyValue {dependencies locals : List TypeExpr} {sort : TypeExpr}
    (body : Term (signatureOf language) dependencies sort)
    (arguments : DependencyArguments (language := language) dependencies locals) :
    instantiateValue? (bodyValue body) 0 locals.length (eraseArguments arguments) =
      some (erase (bind (argsToSub arguments) body)) := by
  have sourceScoped := erase_wellScoped body
  have argumentScoped := dependency_arguments_scoped arguments
  have resultScoped := erase_wellScoped (bind (argsToSub arguments) body)
  have action := erase_bind (argsToSub arguments) _ (occurrence_closed_reads arguments) body
  unfold instantiateValue? bodyValue
  simp only [Nat.add_zero, Bool.not_true,
    eraseDependencyArguments_length, sourceScoped, argumentScoped]
  rw [← action]
  simp [resultScoped]

private theorem erase_instantiate_cast_sort {locals : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (bodies : Bodies language rule spec)
    (term : Term (SchemaSignature language rule spec) locals first) :
    erase (instantiate bodies (same ▸ term)) = erase (instantiate bodies term) := by
  cases same
  rfl

private theorem erase_empty_prefix {locals : List TypeExpr} {sort : TypeExpr}
    (body : Term (signatureOf language) locals sort) :
    erase (rename (fun _ position => injPrefix (S := SchemaSignature language rule spec)
      (Γ := []) locals position) body) = erase body := by
  rw [erase_rename_shiftBy _ 0 0 (by
    intro result position
    simpa only [Nat.zero_le, if_true, Nat.add_zero] using
      variableIndex_injected (S := SchemaSignature language rule spec) position)]
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

theorem input_instantiates {locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (raw : RawAccumulator) (bodies : Bodies language rule spec)
    (captured : lookup raw name = some (bodyValue (bodies (metaIndex rule spec input.compiled.index)))) :
    instantiateAt? rule spec 0 site path locals.length raw (.fvar name) =
      some (erase (instantiate bodies (CompiledSchema.ofInput input).term)) := by
  simp only [instantiateAt?, instantiateWith?, captured, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  rw [instantiateValue?_bodyValue]
  simp only [CompiledSchema.ofInput, instantiate_rename, erase_empty_prefix,
    CompiledOccurrence.term, erase_instantiate_cast_sort, CompiledOccurrence.schemaTerm,
    instantiate, instantiateArgs_embedArgs]

/-- The statement observes the original instantiator and typed signature
morphism, with coverage restricted to the compiled occurrence inventory. -/
def InstantiatesAt {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop :=
  ∀ raw bodies, CapturesInputs compiled.inputOccurrences raw bodies →
    instantiateAt? rule spec 0 site path locals.length raw source =
      some (erase (instantiate bodies compiled.term))

private theorem option_return_map {A B : Type} (value : Option A) (function : A → B) :
    value.bind (fun result => some (function result)) = value.map function := by
  cases value <;> rfl

theorem parameter_scope_instantiates {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (body : Pattern) :
    instantiateAt? rule spec 0 site path depth raw (scope.wrap body) =
      (instantiateAt? rule spec 0 site (path ++ ObjectRoundtrip.parameterChildSuffix scope)
        (depth + binders.length) raw body).map scope.wrap := by
  cases scope <;>
    simp only [ParameterScope.wrap, ObjectRoundtrip.parameterChildSuffix,
      instantiateAt?, instantiateWith?, List.length_nil, List.length_cons,
      List.length_replicate, List.append_nil, Nat.add_zero, Nat.zero_add,
      Option.bind_eq_bind]
  · cases instantiateWith? Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar
      rule spec 0 site path depth raw body <;> rfl
  all_goals exact option_return_map _ _

theorem parameter_body_instantiates {parameter : TermParam} {source : Pattern}
    (body : ParameterBody parameter source)
    (found : parameterBody? parameter source = some body)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (raw : RawAccumulator) :
    instantiateAt? rule spec 0 site path depth raw source =
      (instantiateAt? rule spec 0 site (path ++ body.pathSuffix)
        (depth + body.binders.length) raw body.body).map body.scope.wrap := by
  rcases body with ⟨binders, sort, scope, body, suffix, readback⟩
  cases readback
  rw [ObjectRoundtrip.parameterBody?_wrapped] at found
  cases Option.some.inj found
  exact parameter_scope_instantiates scope site path depth raw body

private theorem erase_instantiate_cast_context {locals target : List TypeExpr}
    (same : locals = target) {sort : TypeExpr} (bodies : Bodies language rule spec)
    (term : Term (SchemaSignature language rule spec) locals sort) :
    erase (instantiate bodies (castTermCtx same term)) = erase (instantiate bodies term) := by
  cases same
  rfl

def ConstructorInstantiatesAt {locals : List TypeExpr} {parameters : List TermParam}
    {sources : List Pattern}
    (arguments : CompiledConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw bodies, CapturesInputs arguments.inputOccurrences raw bodies →
    instantiateArgsAt? rule spec 0 site path locals.length raw offset sources =
      some (eraseConstructorArguments arguments.scopes (instantiateArgs bodies arguments.arguments))

theorem compile_constructor_arguments_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → InstantiatesAt compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        ConstructorInstantiatesAt arguments site path offset := by
  refine compileConstructorArguments?_observes compile locals path
    (fun offset _ _ compiled => ConstructorInstantiatesAt compiled site path offset) ?_ ?_
  · intro offset raw bodies _
    simp only [instantiateArgsAt?, instantiateArgsWith?, instantiateArgs, eraseConstructorArguments]
  · intro offset parameter parameters source sources body head tail bodyFound headFound tailObserved
      raw bodies captured
    change CapturesInputs (head.inputOccurrences ++ tail.inputOccurrences) raw bodies at captured
    obtain ⟨headCaptured, tailCaptured⟩ := (capturesInputs_append _ _ raw bodies).mp captured
    have headAction := children _ _ _ _ head headFound raw bodies headCaptured
    have wrapped := parameter_body_instantiates (rule := rule) (spec := spec) body bodyFound site
      (path ++ [offset]) locals.length raw
    rw [show locals.length + body.binders.length = (body.binders ++ locals).length by
      simp [List.length_append, Nat.add_comm], headAction] at wrapped
    simp only [Option.map_some] at wrapped
    rw [instantiateArgsAt?, instantiateArgsWith?]
    change (instantiateAt? rule spec 0 site (path ++ [offset]) locals.length raw source).bind
        (fun first => (instantiateArgsAt? rule spec 0 site path locals.length raw
          (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
    rw [wrapped, tailObserved raw bodies tailCaptured]
    simp only [Option.bind_some, instantiateArgs, eraseConstructorArguments,
      erase_instantiate_cast_context]


def VectorInstantiatesAt {locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw bodies, CapturesInputs elements.inputOccurrences raw bodies →
    instantiateArgsAt? rule spec 0 site path locals.length raw offset sources =
      some (eraseArguments (instantiateArgs bodies elements.arguments))

theorem compile_vector_elements_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → InstantiatesAt compiled site path)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources sort),
      compileVectorElements? compile locals path offset sort sources = some elements →
        VectorInstantiatesAt elements site path offset := by
  refine compileVectorElements?_observes compile locals path sort
    (fun offset _ compiled => VectorInstantiatesAt compiled site path offset) ?_ ?_
  · intro offset raw bodies _
    simp only [instantiateArgsAt?, instantiateArgsWith?, instantiateArgs, eraseArguments]
  · intro offset source sources head tail headFound tailObserved raw bodies captured
    change CapturesInputs (head.inputOccurrences ++ tail.inputOccurrences) raw bodies at captured
    obtain ⟨headCaptured, tailCaptured⟩ := (capturesInputs_append _ _ raw bodies).mp captured
    rw [instantiateArgsAt?, instantiateArgsWith?]
    change (instantiateAt? rule spec 0 site (path ++ [offset]) locals.length raw source).bind
        (fun first => (instantiateArgsAt? rule spec 0 site path locals.length raw
          (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
    rw [children _ _ _ _ head headFound raw bodies headCaptured,
      tailObserved raw bodies tailCaptured]
    rfl


theorem input_schema_instantiates {locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    InstantiatesAt (CompiledSchema.ofInput input) site path := by
  intro raw bodies captured
  exact input_instantiates input raw bodies (captured _ (List.mem_cons_self))

theorem cast_sort_instantiates {locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (compiled : CompiledSchema language rule spec locals source first)
    (same : first = second) {site : RulePatternSite} {path : List Nat}
    (action : InstantiatesAt compiled site path) :
    InstantiatesAt (compiled.castSort same) site path := by
  intro raw bodies captured
  simpa only [CompiledSchema.castSort, erase_instantiate_cast_sort] using action raw bodies captured

theorem lambda_schema_instantiates {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain)
    (action : InstantiatesAt body site (path ++ [0])) :
    InstantiatesAt (CompiledSchema.lambda body) site path := by
  intro raw bodies captured
  have bodyAction := action raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec 0 site (path ++ [0]) (locals.length + 1) raw source).bind
    (fun result => some (Pattern.lambda none result)) = _
  rw [show locals.length + 1 = (domain :: locals).length by simp, bodyAction]
  simp only [Option.bind_some, CompiledSchema.lambda, instantiate, instantiateArgs, erase]

theorem multiLambda_schema_instantiates {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    (action : InstantiatesAt body site (path ++ [0])) :
    InstantiatesAt (CompiledSchema.multiLambda count body) site path := by
  intro raw bodies captured
  have bodyAction := action raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec 0 site (path ++ [0]) (locals.length + count) raw source).bind
    (fun result => some (Pattern.multiLambda count [] result)) = _
  rw [show locals.length + count = (List.replicate count domain ++ locals).length by
    simp [List.length_append, Nat.add_comm], bodyAction]
  simp only [Option.bind_some, CompiledSchema.multiLambda, instantiate, instantiateArgs,
    erase, erase_instantiate_cast_context]

theorem constructor_schema_instantiates {locals : List TypeExpr} {label : String}
    {sources : List Pattern} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    (arguments : CompiledConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources)
    (action : ConstructorInstantiatesAt arguments site path 0) :
    InstantiatesAt (CompiledSchema.constructor path selected ordinary arguments) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec 0 site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.apply label results)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, CompiledSchema.constructor, instantiate, erase, selected.named]

theorem vector_schema_instantiates {locals : List TypeExpr} {sources : List Pattern}
    {sort : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (action : VectorInstantiatesAt elements site path 0) :
    InstantiatesAt (CompiledSchema.vector elements) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec 0 site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.collection .vec results none)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, CompiledSchema.vector, instantiate, erase]

theorem vector_constructor_schema_instantiates {locals : List TypeExpr} {sources : List Pattern}
    {category : String} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort)
    (action : VectorInstantiatesAt elements site path 0) :
    InstantiatesAt (CompiledSchema.vectorConstructor path selected elements) site path := by
  unfold CompiledSchema.vectorConstructor
  apply cast_sort_instantiates
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec 0 site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.collection .vec results none)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, instantiate, erase]

/-- Actual recursive source compilation earns RHS instantiation preservation
with only the bodies read by its occurrence receipts required to be captured. -/
theorem compileSchemaWithFuel?_instantiates
    (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
        InstantiatesAt compiled site path := by
  refine InputAssemblyInvariant.walk
    (observe := fun _ path _ _ compiled => InstantiatesAt compiled site path) ?_ fuel
  refine {
    bound := ?_
    free := fun _ _ _ _ input => input_schema_instantiates input
    constructor := fun compile children locals path _ sources selected ordinary arguments found =>
      constructor_schema_instantiates path selected ordinary arguments
        (compile_constructor_arguments_instantiates compile site children locals path sources 0 _ arguments found)
    abstraction := fun _ _ _ _ _ body action => lambda_schema_instantiates body action
    multiAbstraction := fun _ _ _ _ _ count body action => multiLambda_schema_instantiates count body action
    vector := fun compile children locals path sources elemSort elements found =>
      vector_schema_instantiates elements
        (compile_vector_elements_instantiates compile site children locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      vector_constructor_schema_instantiates path selected elements
        (compile_vector_elements_instantiates compile site children locals path
          selected.elementSort sources 0 elements found) }
  intro locals path index sort position admitted raw bodies _
  simp only [instantiateAt?, instantiateWith?, instantiate, erase,
    variableIndex_injected (S := SchemaSignature language rule spec),
    boundPosition?_index locals index sort admitted]

/-- Computed occurrence-local readiness: every RHS input name is produced
by the authored LHS. Unused declarations do not enter this source check. -/
def rightInputsProducedOnLeft? {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort) : Bool :=
  compiled.inputOccurrences.all fun input => rule.left.freeFvarNames.contains (inputName input)

theorem rightInputsProducedOnLeft?_names {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort) :
    rightInputsProducedOnLeft? compiled = (compiled.inputOccurrences.map inputName).all
      (fun name => rule.left.freeFvarNames.contains name) := by
  simp only [rightInputsProducedOnLeft?, List.all_map]
  rfl

private theorem rightInputsProducedOnLeft?_transport {other : RuleBindingSpec}
    (same : spec = other) {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort) :
    rightInputsProducedOnLeft? (same ▸ compiled) = rightInputsProducedOnLeft? compiled := by
  cases same
  rfl

private theorem input_occurrences_length_transport {other : RuleBindingSpec}
    (same : spec = other) {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort) :
    (same ▸ compiled).inputOccurrences.length = compiled.inputOccurrences.length := by
  cases same
  rfl

theorem rightInputsProducedOnLeft?_iff {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort) :
    rightInputsProducedOnLeft? compiled = true ↔
      ∀ input ∈ compiled.inputOccurrences, inputName input ∈ rule.left.freeFvarNames := by
  simp only [rightInputsProducedOnLeft?, List.all_eq_true, List.contains_iff_mem]

theorem input_named_index (input : InputEvidence language rule spec) :
    metaName rule spec (inputIndex input) = inputName input := by
  rcases input with ⟨site, locals, path, name, sort, input⟩
  exact input.compiled.named

/-- Actual LHS matching supplies the check's captures. Declaration-indexed
correspondence and an existing body assignment recover their exact bodies. -/
theorem matched_captures_right_inputs {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (coverage : rightInputsProducedOnLeft? compiled = true)
    {target : Pattern} {raw : RawAccumulator} {typed : TypedAccumulator language rule spec}
    (matched : raw ∈ matchRuleAt rule spec 0 target)
    (related : AccCorresponds raw typed) (bodies : Bodies language rule spec)
    (realizes : MExtends (emptySubstitution language) bodies typed) :
    CapturesInputs compiled.inputOccurrences raw bodies := by
  have captured := Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain.matched_captures
    (Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.matchRuleAt_iff.mp matched)
  intro input member
  have named := input_named_index input
  obtain ⟨value, found⟩ := captured (inputName input)
    ((rightInputsProducedOnLeft?_iff compiled).mp coverage input member)
  have correspondence := related.lookups (inputIndex input)
  rw [named] at correspondence
  cases stored : typed.metas (inputIndex input) with
  | none =>
      rw [stored, Option.map_none, found] at correspondence
      cases correspondence
  | some body =>
      rw [stored, Option.map_some] at correspondence
      rw [realizes.2 _ _ stored]
      exact correspondence

/-- Whole authored-side instantiation observes the actual source compiler,
the original occurrence instantiator, and the existing typed morphism. -/
theorem elaborateAuthoredSchema?_instantiates
    {ruleIndex : Fin language.rewrites.length} {site : RulePatternSite} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    InstantiatesAt compiled.compiled site [] := by
  exact compileSchemaWithFuel?_instantiates site _ _ _ _ _ compiled.compiled
    (elaborateAuthoredSchema?_compilation compiled found)

theorem authored_right_instantiates {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex .right sort)
    (found : elaborateAuthoredSchema? language ruleIndex .right sort = some compiled)
    (raw : RawAccumulator)
    (bodies : Bodies language (language.rewrites.get ruleIndex) compiled.spec)
    (captured : CapturesInputs compiled.compiled.inputOccurrences raw bodies) :
    reduct? (language.rewrites.get ruleIndex) compiled.spec 0 raw =
      some (erase (instantiate bodies compiled.compiled.term)) := by
  have action := elaborateAuthoredSchema?_instantiates compiled found raw bodies captured
  have source : compiled.source = (language.rewrites.get ruleIndex).right := by
    exact (Option.some.inj compiled.atSite).symm
  simpa only [reduct?, List.length_nil, source] using action


mutual
/-- A successful original instantiation reads every authored free-name
occurrence. This is a refusal law, independent of typed-body availability. -/
theorem instantiateWith?_requires_captures
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (source result : Pattern)
    (found : instantiateWith? operation rule spec ambient site path depth raw source = some result) :
    Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain.Captures raw source.freeFvarNames := by
  cases source with
  | fvar name =>
      cases stored : lookup raw name with
      | none => simp only [instantiateWith?, stored, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at found
      | some value =>
          intro queried member
          simp only [Pattern.freeFvarNames, List.mem_singleton] at member
          subst queried
          exact ⟨value, stored⟩
  | bvar index =>
      intro name member
      simp only [Pattern.freeFvarNames, List.not_mem_nil] at member
  | apply label sources =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨results, argumentsFound, _⟩ := found
      simpa only [Pattern.freeFvarNames] using instantiateArgsWith?_requires_captures operation rule spec ambient site path depth raw 0
        sources results argumentsFound
  | lambda display body =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨bodyResult, bodyFound, _⟩ := found
      simpa only [Pattern.freeFvarNames] using instantiateWith?_requires_captures operation rule spec ambient site (path ++ [0])
        (depth + 1) raw body bodyResult bodyFound
  | multiLambda count display body =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨bodyResult, bodyFound, _⟩ := found
      simpa only [Pattern.freeFvarNames] using instantiateWith?_requires_captures operation rule spec ambient site (path ++ [0])
        (depth + count) raw body bodyResult bodyFound
  | subst body replacement =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨bodyResult, bodyFound, replacementResult, replacementFound, _⟩ := found
      have bodyCaptured := instantiateWith?_requires_captures operation rule spec ambient site (path ++ [0])
        (depth + 1) raw body bodyResult bodyFound
      have replacementCaptured := instantiateWith?_requires_captures operation rule spec ambient site (path ++ [1])
        depth raw replacement replacementResult replacementFound
      intro name member
      simp only [Pattern.freeFvarNames] at member
      rcases List.mem_append.mp member with member | member
      · exact bodyCaptured name member
      · exact replacementCaptured name member
  | collection kind sources rest =>
      simp only [instantiateWith?, Option.bind_eq_bind] at found
      cases argumentsFound : instantiateArgsWith? operation rule spec ambient site path depth raw 0 sources with
      | none => simp only [argumentsFound, Option.bind_none, reduceCtorEq] at found
      | some results =>
          have captured := instantiateArgsWith?_requires_captures operation rule spec ambient site path depth raw
            0 sources results argumentsFound
          cases rest with
          | none =>
              simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using captured
          | some name =>
              simp only [argumentsFound, Option.bind_some] at found
              cases stored : lookup raw name with
              | none => simp only [stored, Option.bind_none, reduceCtorEq] at found
              | some value =>
                  intro queried member
                  simp only [Pattern.freeFvarNames, Option.toList_some, List.mem_append, List.mem_singleton] at member
                  rcases member with ordinary | rfl
                  · exact captured queried ordinary
                  · exact ⟨value, stored⟩
termination_by sizeOf source

theorem instantiateArgsWith?_requires_captures
    (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (offset : Nat) (sources results : List Pattern)
    (found : instantiateArgsWith? operation rule spec ambient site path depth raw offset sources = some results) :
    Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain.Captures raw
      (sources.flatMap Pattern.freeFvarNames) := by
  cases sources with
  | nil => intro name member; simp only [List.flatMap_nil, List.not_mem_nil] at member
  | cons source sources =>
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨head, headFound, tail, tailFound, _⟩ := found
      have headCaptured := instantiateWith?_requires_captures operation rule spec ambient site
        (path ++ [offset]) depth raw source head headFound
      have tailCaptured := instantiateArgsWith?_requires_captures operation rule spec ambient site path depth raw
        (offset + 1) sources tail tailFound
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      exact member.elim (headCaptured name) (tailCaptured name)
termination_by sizeOf sources
end

/-- Missing a real source occurrence refuses the original instantiator;
a total typed body assignment cannot supply an absent runtime capture. -/
theorem instantiateAt?_missing_capture (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (source : Pattern) (name : String)
    (member : name ∈ source.freeFvarNames) (missing : lookup raw name = none) :
    instantiateAt? rule spec ambient site path depth raw source = none := by
  cases found : instantiateAt? rule spec ambient site path depth raw source with
  | none => rfl
  | some result =>
      obtain ⟨value, stored⟩ := instantiateWith?_requires_captures
        Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar rule spec ambient site path depth raw
        source result found name member
      rw [missing] at stored
      cases stored

theorem reduct?_missing_capture (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (raw : RawAccumulator) (name : String)
    (member : name ∈ rule.right.freeFvarNames) (missing : lookup raw name = none) :
    reduct? rule spec ambient raw = none :=
  instantiateAt?_missing_capture rule spec ambient .right [] 0 raw rule.right name member missing


theorem authored_specs_equal {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort) : left.spec = right.spec :=
  Option.some.inj (left.attached.symm.trans right.attached)

/-- Attachment at the same physical rule position aligns the two existing
schema signatures; no rule-name lookup chooses a different occurrence. -/
def alignedRightSchema {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort) :
    CompiledSchema language (language.rewrites.get ruleIndex) left.spec [] right.source sort :=
  (authored_specs_equal left right).symm ▸ right.compiled

private theorem instantiatesAt_transport_spec {other : RuleBindingSpec}
    (same : spec = other) {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    {site : RulePatternSite} {path : List Nat} (action : InstantiatesAt compiled site path) :
    InstantiatesAt (same ▸ compiled) site path := by
  cases same
  exact action

theorem alignedRightSchema_instantiates {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (found : elaborateAuthoredSchema? language ruleIndex .right sort = some right) :
    InstantiatesAt (alignedRightSchema left right) .right [] :=
  instantiatesAt_transport_spec (authored_specs_equal left right).symm right.compiled
    (elaborateAuthoredSchema?_instantiates right found)

/-- The existing positioned-schema kernel of the two authored sides.
Its chosen redex is the root. Authored premises remain on the side receipts;
this term kernel does not discharge those premises. -/
def authoredRootSchema {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort) :
    PositionedRewrite (SchemaSignature language (language.rewrites.get ruleIndex) left.spec) where
  ctx := []
  sort := sort
  lhs := left.compiled.term
  rhs := (alignedRightSchema left right).term
  position := {
    carrier := sort
    ctxt := .var .zero
    redex := left.compiled.term
    plugs := rfl
    linear := rfl }

private theorem root_instance_close_empty {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : RuleInstance (metaArities (language := language)
      (language.rewrites.get ruleIndex) left.spec) (authoredRootSchema left right)) :
    invocation.close = emptySubstitution language := by
  funext result position
  exact nomatch position

/-- A successful actual canonical match and source coverage give the exact
original reduct of a genuine rule invocation and its existing root-step witness.
The invocation is supplied: unused declared sorts are never populated artificially. -/
theorem authored_rule_instance_step
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {rawTarget : Pattern}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (coverage : rightInputsProducedOnLeft? (alignedRightSchema left right) = true)
    (target : ReifiedTarget language (language.rewrites.get ruleIndex) left.spec [] rawTarget sort)
    {raw : RawAccumulator}
    (matched : raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec 0 rawTarget)
    (typed : TypedAccumulator language (language.rewrites.get ruleIndex) left.spec)
    (related : AccCorresponds raw typed)
    (invocation : RuleInstance (metaArities (language := language)
      (language.rewrites.get ruleIndex) left.spec) (authoredRootSchema left right))
    (realizes : MExtends (emptySubstitution language) invocation.body typed) :
    reduct? (language.rewrites.get ruleIndex) left.spec 0 raw =
        some (erase (bind invocation.close (instantiate invocation.body (authoredRootSchema left right).rhs))) ∧
      RootStep (authoredRootSchema left right) target.term
        (bind invocation.close (instantiate invocation.body (authoredRootSchema left right).rhs)) := by
  dsimp only [authoredRootSchema] at invocation ⊢
  have typedMatched := ((authored_left_match left leftFound target).result_iff typed).mpr
    ⟨raw, matched, related⟩
  have captures := matched_captures_right_inputs (alignedRightSchema left right) coverage
    matched related invocation.body realizes
  have action := alignedRightSchema_instantiates left right rightFound raw invocation.body captures
  have source : right.source = (language.rewrites.get ruleIndex).right :=
    (Option.some.inj right.atSite).symm
  have close := root_instance_close_empty left right invocation
  have rhsClosed : bind invocation.close (instantiate invocation.body (alignedRightSchema left right).term) =
      instantiate invocation.body (alignedRightSchema left right).term := by
    change bind (Γ := []) invocation.close (instantiate invocation.body
      (alignedRightSchema left right).term) = _
    rw [close, emptySubstitution_eq_identity]
    exact bind_id _
  have lhs := smatchT_sound emptyMAcc typed left.compiled.term target.term typedMatched
    invocation.close invocation.body (by rw [close]; exact realizes)
  refine ⟨?_, ⟨invocation, lhs, rfl⟩⟩
  rw [rhsClosed]
  simpa only [reduct?, source, List.length_nil] using action

/-- The actual match-and-reduct execution agrees in both directions with
one genuine invocation of the existing positioned-schema kernel. The source
coverage check concerns used RHS occurrences, rather than all declarations. -/
theorem authored_rule_instance_adequate
    [∀ result, DecidableEq ((signatureOf language).Op result)]
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {rawTarget : Pattern}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (coverage : rightInputsProducedOnLeft? (alignedRightSchema left right) = true)
    (target : ReifiedTarget language (language.rewrites.get ruleIndex) left.spec [] rawTarget sort)
    (invocation : RuleInstance (metaArities (language := language)
      (language.rewrites.get ruleIndex) left.spec) (authoredRootSchema left right)) :
    (∃ raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec 0 rawTarget,
      ∃ typed : TypedAccumulator language (language.rewrites.get ruleIndex) left.spec,
        AccCorresponds raw typed ∧ MExtends (emptySubstitution language) invocation.body typed ∧
          reduct? (language.rewrites.get ruleIndex) left.spec 0 raw =
            some (erase (bind invocation.close (instantiate invocation.body (authoredRootSchema left right).rhs)))) ↔
      bind invocation.close (instantiate invocation.body (authoredRootSchema left right).lhs) = target.term := by
  dsimp only [authoredRootSchema] at invocation ⊢
  have close := root_instance_close_empty left right invocation
  constructor
  · rintro ⟨raw, matched, typed, related, realizes, _⟩
    have typedMatched := ((authored_left_match left leftFound target).result_iff typed).mpr
      ⟨raw, matched, related⟩
    exact smatchT_sound emptyMAcc typed left.compiled.term target.term typedMatched
      invocation.close invocation.body (by rw [close]; exact realizes)
  · intro equality
    have equality' : bind (liftSub (emptySubstitution language) [])
        (instantiate invocation.body left.compiled.term) = target.term := by
      simpa only [close, liftSub] using equality
    obtain ⟨typed, typedMatched, realizes⟩ :=
      (left.compiled.matching_adequate emptyMAcc target.term invocation.body
        (MExtends.empty (emptySubstitution language) invocation.body)).mpr equality'
    obtain ⟨raw, matched, related⟩ :=
      ((authored_left_match left leftFound target).result_iff typed).mp typedMatched
    have reduct := (authored_rule_instance_step left leftFound right rightFound coverage target
      matched typed related invocation realizes).1
    exact ⟨raw, matched, typed, related, realizes, reduct⟩

end RawInstantiation

namespace AmbientCorrespondence

open SchemaElaboration TargetReification InputRecovery RawMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

variable {rule : RewriteRule} {spec : RuleBindingSpec}

/-- The actual admitted variable spine transports the ambient suffix
without changing the canonical constructor and binder representation. -/
theorem input_action_canonical_iff
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort) :
    CanonicalObject (bind (occurrenceSubstitution
      (appendAmbientArguments input.compiled.arguments ambient)) body) ↔ CanonicalObject body := by
  obtain ⟨selected, _⟩ := input.recognizes_arguments
  rw [occurrenceSubstitution_is_renaming input.compiled.arguments selected,
    bind_var_eq_rename]
  simp only [CanonicalObject, canonicalObject?_rename]

/-- Original contextual-value execution, followed by the existing checked
reifier in the independently fixed destination context, returns the typed action. -/
theorem input_instantiation_reifies
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (body : Term (signatureOf language) (input.dependencies ++ ambient) sort)
    (canonical : CanonicalObject body) :
    (instantiateValue? (contextualValue body) ambient.length locals.length
      (eraseArguments input.compiled.arguments)).bind
        (fun result => reifiedObject? language rule spec (locals ++ ambient) result sort) =
      some (bind (occurrenceSubstitution
        (appendAmbientArguments input.compiled.arguments ambient)) body) := by
  have action := instantiateValue?_typed body
    (appendAmbientArguments input.compiled.arguments ambient)
  rw [appendAmbientArguments_erases] at action
  rw [action, Option.bind_some]
  exact reifiedObject?_canonical rule spec _
    ((input_action_canonical_iff input body).mpr canonical)

/-- Successful original recovery from an independently canonical open
target earns canonicality and computed reification of the captured body. -/
theorem input_recovery_reifies
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (target : Term (signatureOf language) (locals ++ ambient) sort)
    (canonical : CanonicalObject target) (value : ContextualValue)
    (found : recoverValue? input.dependencies ambient.length locals.length
      (eraseArguments input.compiled.arguments) (erase target) = some value) :
    ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
      value = contextualValue body ∧ CanonicalObject body ∧
      reifiedObject? language rule spec (input.dependencies ++ ambient) value.body sort = some body ∧
      bind (occurrenceSubstitution
        (appendAmbientArguments input.compiled.arguments ambient)) body = target := by
  obtain ⟨body, captured, action⟩ := (input.recover_intrinsic_iff target value).mp found
  have bodyCanonical : CanonicalObject body :=
    (input_action_canonical_iff input body).mp (action.symm ▸ canonical)
  refine ⟨body, captured, bodyCanonical, ?_, action⟩
  rw [captured]
  exact reifiedObject?_canonical rule spec body bodyCanonical

/-- Ambient-open recovery is exact at canonical contextual preimages; the
body and its destination are checked at separately fixed sorted contexts. -/
theorem input_recovery_canonical_iff
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (target : Term (signatureOf language) (locals ++ ambient) sort)
    (canonical : CanonicalObject target) (value : ContextualValue) :
    recoverValue? input.dependencies ambient.length locals.length
        (eraseArguments input.compiled.arguments) (erase target) = some value ↔
      ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        value = contextualValue body ∧ CanonicalObject body ∧
        reifiedObject? language rule spec (input.dependencies ++ ambient) value.body sort = some body ∧
        bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target := by
  constructor
  · exact input_recovery_reifies input target canonical value
  · rintro ⟨body, captured, _, _, action⟩
    exact (input.recover_intrinsic_iff target value).mpr ⟨body, captured, action⟩

/-- Refusal means that no canonical intrinsic body can account for the
target through this source occurrence's actual dependency substitution. -/
theorem input_recovery_refusal_iff
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (target : Term (signatureOf language) (locals ++ ambient) sort)
    (canonical : CanonicalObject target) :
    recoverValue? input.dependencies ambient.length locals.length
        (eraseArguments input.compiled.arguments) (erase target) = none ↔
      ¬ ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        CanonicalObject body ∧ bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target := by
  constructor
  · intro refused ⟨body, _, action⟩
    have found := input.recover_typed_instance body
    rw [action, refused] at found
    cases found
  · intro absent
    cases found : recoverValue? input.dependencies ambient.length locals.length
        (eraseArguments input.compiled.arguments) (erase target) with
    | none => rfl
    | some value =>
        obtain ⟨body, _, bodyCanonical, _, action⟩ :=
          input_recovery_reifies input target canonical value found
        exact False.elim (absent ⟨body, bodyCanonical, action⟩)

/-- Canonical capture reflection includes the original assignment update,
so repeated captures still require agreement at the fixed ambient context. -/
theorem input_capture_canonical_iff
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial final : RawAccumulator)
    (target : Term (signatureOf language) (locals ++ ambient) sort)
    (canonical : CanonicalObject target) :
    capture? rule spec ambient.length locals.length site path initial name
        (erase target) = some final ↔
      ∃ body : Term (signatureOf language) (input.dependencies ++ ambient) sort,
        CanonicalObject body ∧ bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target ∧
        assign initial name (contextualValue body) = some final := by
  rw [input.capture_intrinsic_iff initial final target]
  constructor
  · rintro ⟨body, action, assigned⟩
    exact ⟨body, (input_action_canonical_iff input body).mp (action.symm ▸ canonical),
      action, assigned⟩
  · rintro ⟨body, _, action, assigned⟩
    exact ⟨body, action, assigned⟩

end AmbientCorrespondence

namespace AmbientCorrespondence

open SchemaElaboration TargetReification RawMatching InputRecovery
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

variable {rule : RewriteRule} {spec : RuleBindingSpec}

abbrev AmbientBodies (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : List TypeExpr) :=
  ContextualAssignment (signatureOf language) (metaArities rule spec) ambient

def emptyAmbientSub (ambient : List TypeExpr) : Sub (signatureOf language) [] ambient :=
  fun _ position => nomatch position

abbrev scopedInstantiation {ambient locals : List TypeExpr} {sort : TypeExpr}
    (bodies : AmbientBodies language rule spec ambient)
    (term : Term (SchemaSignature language rule spec) (locals ++ []) sort) :=
  ContextualAssignment.instantiate bodies
    (ContextualAssignment.weakenSub (S := signatureOf language) locals
      (fun _ (position : Var ambient _) => Term.var position))
    (liftSub (emptyAmbientSub ambient) locals) term

abbrev scopedArguments {ambient locals : List TypeExpr}
    {arity : List (List TypeExpr × TypeExpr)}
    (bodies : AmbientBodies language rule spec ambient)
    (arguments : Args (SchemaSignature language rule spec) arity (locals ++ [])) :=
  ContextualAssignment.instantiateArgs bodies
    (ContextualAssignment.weakenSub (S := signatureOf language) locals
      (fun _ (position : Var ambient _) => Term.var position))
    (liftSub (emptyAmbientSub ambient) locals) arguments

private theorem erase_scoped_cast_append {ambient binders locals : List TypeExpr}
    {sort : TypeExpr} (bodies : AmbientBodies language rule spec ambient)
    (term : Term (SchemaSignature language rule spec) ((binders ++ locals) ++ []) sort) :
    erase (ContextualAssignment.instantiate bodies
      (ContextualAssignment.weakenSub binders
        (ContextualAssignment.weakenSub (S := signatureOf language) locals
          (fun _ (position : Var ambient _) => Term.var position)))
      (liftSub (liftSub (emptyAmbientSub ambient) locals) binders)
      (castTermCtx (T := SchemaSignature language rule spec)
        (List.append_assoc binders locals []) term)) =
    erase (scopedInstantiation bodies term) := by
  have action := ContextualAssignment.instantiate_append bodies
    (fun _ (position : Var ambient _) => Term.var position) (emptyAmbientSub ambient) binders locals
    (castTermCtx (T := SchemaSignature language rule spec) (List.append_assoc binders locals []) term)
  simp only [cast_context_inverse] at action
  simpa only [erase_cast_context] using (congrArg (fun result => erase result) action).symm

private theorem erase_contextual_cast_sort {ambient source target : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (bodies : AmbientBodies language rule spec ambient)
    (ambientSub : Sub (signatureOf language) ambient target)
    (valuation : Sub (signatureOf language) source target)
    (term : Term (SchemaSignature language rule spec) source first) :
    erase (ContextualAssignment.instantiate bodies ambientSub valuation (same ▸ term)) =
      erase (ContextualAssignment.instantiate bodies ambientSub valuation term) := by
  cases same
  rfl

def ContextualCapturesInputs {ambient : List TypeExpr}
    (inputs : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) : Prop :=
  ∀ input ∈ inputs, lookup raw (RawInstantiation.inputName input) =
    some (contextualValue (bodies (RawInstantiation.inputIndex input)))

theorem contextualCapturesInputs_append {ambient : List TypeExpr}
    (first second : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    ContextualCapturesInputs (first ++ second) raw bodies ↔
      ContextualCapturesInputs first raw bodies ∧ ContextualCapturesInputs second raw bodies := by
  constructor
  · intro captured
    exact ⟨fun input member => captured input (List.mem_append_left _ member),
      fun input member => captured input (List.mem_append_right _ member)⟩
  · rintro ⟨firstCaptured, secondCaptured⟩ input member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact firstCaptured input firstMember
    · exact secondCaptured input secondMember

private theorem schema_prefix_valuation {ambient locals : List TypeExpr} {sort : TypeExpr}
    (position : Var locals sort) :
    liftSub (emptyAmbientSub (language := language) ambient) locals sort
      (injPrefix (S := SchemaSignature language rule spec) (Γ := []) locals position) =
      Term.var (injPrefix (S := signatureOf language) (Γ := ambient) locals position) := by
  have shared : injPrefix (S := SchemaSignature language rule spec) (Γ := []) locals position =
      injPrefix (S := signatureOf language) (Γ := []) locals position :=
    ObjectRoundtrip.injPrefix_shared_sorts (S := signatureOf language)
      (M := metaArities rule spec) locals position
  rw [shared]
  exact liftSub_injPrefix (emptyAmbientSub ambient) locals position

theorem input_instantiates {ambient locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (raw : RawAccumulator) (bodies : AmbientBodies language rule spec ambient)
    (captured : lookup raw name =
      some (contextualValue (bodies (metaIndex rule spec input.compiled.index)))) :
    instantiateAt? rule spec ambient.length site path locals.length raw (.fvar name) =
      some (erase (scopedInstantiation bodies (CompiledSchema.ofInput input).term)) := by
  simp only [instantiateAt?, instantiateWith?, captured, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  have action := instantiateValue?_typed (bodies (metaIndex rule spec input.compiled.index))
    (appendAmbientArguments input.compiled.arguments ambient)
  rw [appendAmbientArguments_erases] at action
  rw [action]
  congr 1
  simp only [scopedInstantiation, CompiledSchema.ofInput, ContextualAssignment.instantiate_rename,
    CompiledOccurrence.term, erase_contextual_cast_sort, CompiledOccurrence.schemaTerm,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs_embedArgs]
  have valuation :
      (fun result position => liftSub (emptyAmbientSub (language := language) ambient) locals result
        (injPrefix (S := SchemaSignature language rule spec) (Γ := []) locals position)) =
      (fun result (position : Var locals result) => Term.var
        (injPrefix (S := signatureOf language) (Γ := ambient) locals position)) := by
    funext result position
    exact schema_prefix_valuation position
  rw [valuation, bindArgs_var_eq_renameArgs]
  rfl


variable {ambient : List TypeExpr}

/-- The statement observes the original instantiator and typed signature
morphism, with coverage restricted to the compiled occurrence inventory. -/
def InstantiatesAt {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    ContextualCapturesInputs compiled.inputOccurrences raw bodies →
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (erase (scopedInstantiation bodies compiled.term))

private theorem option_return_map {A B : Type} (value : Option A) (function : A → B) :
    value.bind (fun result => some (function result)) = value.map function := by
  cases value <;> rfl

theorem parameter_scope_instantiates {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (raw : RawAccumulator) (body : Pattern) :
    instantiateAt? rule spec ambient.length site path depth raw (scope.wrap body) =
      (instantiateAt? rule spec ambient.length site (path ++ ObjectRoundtrip.parameterChildSuffix scope)
        (depth + binders.length) raw body).map scope.wrap := by
  cases scope <;>
    simp only [ParameterScope.wrap, ObjectRoundtrip.parameterChildSuffix,
      instantiateAt?, instantiateWith?, List.length_nil, List.length_cons,
      List.length_replicate, List.append_nil, Nat.add_zero, Nat.zero_add,
      Option.bind_eq_bind]
  · cases instantiateWith? Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar
      rule spec ambient.length site path depth raw body <;> rfl
  all_goals exact option_return_map _ _

theorem parameter_body_instantiates {parameter : TermParam} {source : Pattern}
    (body : ParameterBody parameter source)
    (found : parameterBody? parameter source = some body)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (raw : RawAccumulator) :
    instantiateAt? rule spec ambient.length site path depth raw source =
      (instantiateAt? rule spec ambient.length site (path ++ body.pathSuffix)
        (depth + body.binders.length) raw body.body).map body.scope.wrap := by
  rcases body with ⟨binders, sort, scope, body, suffix, readback⟩
  cases readback
  rw [ObjectRoundtrip.parameterBody?_wrapped] at found
  cases Option.some.inj found
  exact parameter_scope_instantiates scope site path depth raw body

def ConstructorInstantiatesAt {locals : List TypeExpr} {parameters : List TermParam}
    {sources : List Pattern}
    (arguments : CompiledConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    ContextualCapturesInputs arguments.inputOccurrences raw bodies →
    instantiateArgsAt? rule spec ambient.length site path locals.length raw offset sources =
      some (eraseConstructorArguments arguments.scopes (scopedArguments bodies arguments.arguments))

theorem compile_constructor_arguments_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → InstantiatesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        ConstructorInstantiatesAt (ambient := ambient) arguments site path offset := by
  refine compileConstructorArguments?_observes compile locals path
    (fun offset _ _ compiled => ConstructorInstantiatesAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset raw bodies _
    simp only [instantiateArgsAt?, instantiateArgsWith?, scopedArguments, ContextualAssignment.instantiateArgs, eraseConstructorArguments]
  · intro offset parameter parameters source sources body head tail bodyFound headFound tailObserved
      raw bodies captured
    change ContextualCapturesInputs (head.inputOccurrences ++ tail.inputOccurrences) raw bodies at captured
    obtain ⟨headCaptured, tailCaptured⟩ := (contextualCapturesInputs_append _ _ raw bodies).mp captured
    have headAction := children _ _ _ _ head headFound raw bodies headCaptured
    have wrapped := parameter_body_instantiates (rule := rule) (spec := spec)
      (ambient := ambient) body bodyFound site
      (path ++ [offset]) locals.length raw
    rw [show locals.length + body.binders.length = (body.binders ++ locals).length by
      simp [List.length_append, Nat.add_comm], headAction] at wrapped
    simp only [Option.map_some] at wrapped
    rw [instantiateArgsAt?, instantiateArgsWith?]
    change (instantiateAt? rule spec ambient.length site (path ++ [offset]) locals.length raw source).bind
        (fun first => (instantiateArgsAt? rule spec ambient.length site path locals.length raw
          (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
    rw [wrapped, tailObserved raw bodies tailCaptured]
    simp only [Option.bind_some, scopedArguments, ContextualAssignment.instantiateArgs, eraseConstructorArguments,
      erase_scoped_cast_append]


def VectorInstantiatesAt {locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    ContextualCapturesInputs elements.inputOccurrences raw bodies →
    instantiateArgsAt? rule spec ambient.length site path locals.length raw offset sources =
      some (eraseArguments (scopedArguments bodies elements.arguments))

theorem compile_vector_elements_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → InstantiatesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources sort),
      compileVectorElements? compile locals path offset sort sources = some elements →
        VectorInstantiatesAt (ambient := ambient) elements site path offset := by
  refine compileVectorElements?_observes compile locals path sort
    (fun offset _ compiled => VectorInstantiatesAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset raw bodies _
    simp only [instantiateArgsAt?, instantiateArgsWith?, scopedArguments, ContextualAssignment.instantiateArgs, eraseArguments]
  · intro offset source sources head tail headFound tailObserved raw bodies captured
    change ContextualCapturesInputs (head.inputOccurrences ++ tail.inputOccurrences) raw bodies at captured
    obtain ⟨headCaptured, tailCaptured⟩ := (contextualCapturesInputs_append _ _ raw bodies).mp captured
    rw [instantiateArgsAt?, instantiateArgsWith?]
    change (instantiateAt? rule spec ambient.length site (path ++ [offset]) locals.length raw source).bind
        (fun first => (instantiateArgsAt? rule spec ambient.length site path locals.length raw
          (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
    rw [children _ _ _ _ head headFound raw bodies headCaptured,
      tailObserved raw bodies tailCaptured]
    rfl


theorem input_schema_instantiates {locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.ofInput input) site path := by
  intro raw bodies captured
  exact input_instantiates input raw bodies (captured _ (List.mem_cons_self))

theorem cast_sort_instantiates {locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (compiled : CompiledSchema language rule spec locals source first)
    (same : first = second) {site : RulePatternSite} {path : List Nat}
    (action : InstantiatesAt (ambient := ambient) compiled site path) :
    InstantiatesAt (ambient := ambient) (compiled.castSort same) site path := by
  intro raw bodies captured
  simpa only [CompiledSchema.castSort, erase_contextual_cast_sort] using action raw bodies captured

theorem lambda_schema_instantiates {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain)
    (action : InstantiatesAt (ambient := ambient) body site (path ++ [0])) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.lambda body) site path := by
  intro raw bodies captured
  have bodyAction := action raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec ambient.length site (path ++ [0]) (locals.length + 1) raw source).bind
    (fun result => some (Pattern.lambda none result)) = _
  rw [show locals.length + 1 = (domain :: locals).length by simp, bodyAction]
  simp only [Option.bind_some, CompiledSchema.lambda, scopedInstantiation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs, erase]
  exact congrArg (fun result => some (Pattern.lambda none result))
    (erase_scoped_cast_append (binders := [domain]) (locals := locals) bodies body.term).symm

theorem multiLambda_schema_instantiates {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    (action : InstantiatesAt (ambient := ambient) body site (path ++ [0])) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.multiLambda count body) site path := by
  intro raw bodies captured
  have bodyAction := action raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec ambient.length site (path ++ [0]) (locals.length + count) raw source).bind
    (fun result => some (Pattern.multiLambda count [] result)) = _
  rw [show locals.length + count = (List.replicate count domain ++ locals).length by
    simp [List.length_append, Nat.add_comm], bodyAction]
  simp only [Option.bind_some, CompiledSchema.multiLambda, scopedInstantiation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    erase, erase_scoped_cast_append]

theorem constructor_schema_instantiates {locals : List TypeExpr} {label : String}
    {sources : List Pattern} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    (arguments : CompiledConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources)
    (action : ConstructorInstantiatesAt (ambient := ambient) arguments site path 0) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.constructor path selected ordinary arguments) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.apply label results)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, CompiledSchema.constructor, scopedInstantiation, scopedArguments, ContextualAssignment.instantiate, erase, selected.named]

theorem vector_schema_instantiates {locals : List TypeExpr} {sources : List Pattern}
    {sort : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (action : VectorInstantiatesAt (ambient := ambient) elements site path 0) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.vector elements) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.collection .vec results none)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, CompiledSchema.vector, scopedInstantiation, scopedArguments, ContextualAssignment.instantiate, erase]

theorem vector_constructor_schema_instantiates {locals : List TypeExpr} {sources : List Pattern}
    {category : String} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort)
    (action : VectorInstantiatesAt (ambient := ambient) elements site path 0) :
    InstantiatesAt (ambient := ambient) (CompiledSchema.vectorConstructor path selected elements) site path := by
  unfold CompiledSchema.vectorConstructor
  apply cast_sort_instantiates
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
    (fun results => some (Pattern.collection .vec results none)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, scopedInstantiation, scopedArguments, ContextualAssignment.instantiate, erase]

/-- Actual recursive source compilation earns RHS instantiation preservation
with only the bodies read by its occurrence receipts required to be captured. -/
theorem compileSchemaWithFuel?_instantiates
    (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
        InstantiatesAt (ambient := ambient) compiled site path := by
  refine InputAssemblyInvariant.walk
    (observe := fun _ path _ _ compiled => InstantiatesAt (ambient := ambient) compiled site path) ?_ fuel
  refine {
    bound := ?_
    free := fun _ _ _ _ input => input_schema_instantiates input
    constructor := fun compile children locals path _ sources selected ordinary arguments found =>
      constructor_schema_instantiates path selected ordinary arguments
        (compile_constructor_arguments_instantiates compile site children locals path sources 0 _ arguments found)
    abstraction := fun _ _ _ _ _ body action => lambda_schema_instantiates body action
    multiAbstraction := fun _ _ _ _ _ count body action => multiLambda_schema_instantiates count body action
    vector := fun compile children locals path sources elemSort elements found =>
      vector_schema_instantiates elements
        (compile_vector_elements_instantiates compile site children locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      vector_constructor_schema_instantiates path selected elements
        (compile_vector_elements_instantiates compile site children locals path
          selected.elementSort sources 0 elements found) }
  intro locals path index sort position admitted raw bodies _
  simp only [instantiateAt?, instantiateWith?, scopedInstantiation,
    ContextualAssignment.instantiate, schema_prefix_valuation, erase]
  rw [InputRecovery.variableIndex_injPrefix position, boundPosition?_index locals index sort admitted]

open RawInstantiation

/-- Whole authored-side instantiation observes the actual source compiler,
the original occurrence instantiator, and the existing typed morphism. -/
theorem elaborateAuthoredSchema?_instantiates
    {ruleIndex : Fin language.rewrites.length} {site : RulePatternSite} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    InstantiatesAt (ambient := ambient) compiled.compiled site [] := by
  exact compileSchemaWithFuel?_instantiates site _ _ _ _ _ compiled.compiled
    (elaborateAuthoredSchema?_compilation compiled found)

theorem authored_right_instantiates {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex .right sort)
    (found : elaborateAuthoredSchema? language ruleIndex .right sort = some compiled)
    (raw : RawAccumulator)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : ContextualCapturesInputs compiled.compiled.inputOccurrences raw bodies) :
    reduct? (language.rewrites.get ruleIndex) compiled.spec ambient.length raw =
      some (erase (scopedInstantiation bodies compiled.compiled.term)) := by
  have action := elaborateAuthoredSchema?_instantiates compiled found raw bodies captured
  have source : compiled.source = (language.rewrites.get ruleIndex).right := by
    exact (Option.some.inj compiled.atSite).symm
  simpa only [reduct?, List.length_nil, source] using action

private theorem instantiatesAt_transport_spec {other : RuleBindingSpec}
    (same : spec = other) {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    {site : RulePatternSite} {path : List Nat} (action : InstantiatesAt (ambient := ambient) compiled site path) :
    InstantiatesAt (ambient := ambient) (same ▸ compiled) site path := by
  cases same
  exact action

theorem alignedRightSchema_instantiates {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (found : elaborateAuthoredSchema? language ruleIndex .right sort = some right) :
    InstantiatesAt (ambient := ambient) (alignedRightSchema left right) .right [] :=
  instantiatesAt_transport_spec (authored_specs_equal left right).symm right.compiled
    (elaborateAuthoredSchema?_instantiates right found)


/-- The original closed typed action is the empty-ambient specialization
of the same existing contextual assignment action. -/
theorem scopedInstantiation_ofClosed_empty {locals : List TypeExpr} {sort : TypeExpr}
    (bodies : RawInstantiation.Bodies language rule spec)
    (term : Term (SchemaSignature language rule spec) (locals ++ []) sort) :
    scopedInstantiation (ambient := []) (ContextualAssignment.ofClosed bodies []) term =
      instantiate bodies term := by
  have empty : emptyAmbientSub (language := language) [] =
      (fun _ position => Term.var position) := by
    funext result position
    exact nomatch position
  simp only [scopedInstantiation, ContextualAssignment.instantiate_ofClosed, empty,
    liftSub_var, bind_id]

theorem contextualValue_ofClosed_empty {dependencies : List TypeExpr} {sort : TypeExpr}
    (body : Term (signatureOf language) dependencies sort) :
    contextualValue (dependencies := dependencies) (ambient := [])
        (rename (fun _ position => injPrefix (S := signatureOf language)
          (Γ := []) dependencies position) body) = bodyValue body := by
  simp only [contextualValue, List.length_nil, InputRecovery.erase_appendAmbient, bodyValue]

theorem contextualCapturesInputs_ofClosed_empty
    (inputs : List (InputEvidence language rule spec)) (raw : RawAccumulator)
    (bodies : RawInstantiation.Bodies language rule spec) :
    ContextualCapturesInputs inputs raw (ContextualAssignment.ofClosed bodies []) ↔
      RawInstantiation.CapturesInputs inputs raw bodies := by
  simp only [ContextualCapturesInputs, RawInstantiation.CapturesInputs,
    ContextualAssignment.ofClosed, contextualValue_ofClosed_empty]

end AmbientCorrespondence
namespace AmbientCorrespondence

open SchemaElaboration TargetReification RawInstantiation
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding.ContextualRootEvents

private theorem contextual_instance_close_empty
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient) :
    invocation.close = emptyAmbientSub ambient := by
  funext result position
  exact nomatch position

theorem contextual_instance_source
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient) :
    invocation.source = scopedInstantiation (ambient := ambient) (locals := []) invocation.body left.compiled.term := by
  unfold Instance.source
  rw [contextual_instance_close_empty left right invocation]
  simp only [scopedInstantiation, liftSub]
  rfl

theorem contextual_instance_target
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient) :
    invocation.target = scopedInstantiation (ambient := ambient) (locals := []) invocation.body (alignedRightSchema left right).term := by
  unfold Instance.target
  rw [contextual_instance_close_empty left right invocation]
  simp only [scopedInstantiation, liftSub]
  rfl

/-- Both actual authored sides use the same physical rule occurrence and
the same existing contextual instance. Only captures read on those sides
are required; this term-kernel event does not discharge authored premises. -/
theorem authored_contextual_instance_execution
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    (raw : RawMatching.RawAccumulator)
    (leftCaptured : ContextualCapturesInputs left.compiled.inputOccurrences raw invocation.body)
    (rightCaptured : ContextualCapturesInputs (alignedRightSchema left right).inputOccurrences
      raw invocation.body) :
    instantiateAt? (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0
        raw (language.rewrites.get ruleIndex).left = some (erase invocation.source) ∧
      reduct? (language.rewrites.get ruleIndex) left.spec ambient.length raw =
        some (erase invocation.target) ∧
      Nonempty (Event (S := signatureOf language)
        (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
        (authoredRootSchema left right).unpositioned
        invocation.source invocation.target) := by
  have leftAction := elaborateAuthoredSchema?_instantiates (ambient := ambient)
    left leftFound raw invocation.body leftCaptured
  have rightAction := alignedRightSchema_instantiates (ambient := ambient)
    left right rightFound raw invocation.body rightCaptured
  have sourceErasure :
      erase (scopedInstantiation (ambient := ambient) (locals := []) invocation.body left.compiled.term) =
      erase invocation.source := by
    exact (congrArg (erase (language := language) (bound := ambient) (type := sort))
      (contextual_instance_source left right invocation)).symm
  have targetErasure :
      erase (scopedInstantiation (ambient := ambient) (locals := []) invocation.body
        (alignedRightSchema left right).term) = erase invocation.target := by
    exact (congrArg (erase (language := language) (bound := ambient) (type := sort))
      (contextual_instance_target left right invocation)).symm
  have leftSource : left.source = (language.rewrites.get ruleIndex).left :=
    (Option.some.inj left.atSite).symm
  have rightSource : right.source = (language.rewrites.get ruleIndex).right :=
    (Option.some.inj right.atSite).symm
  refine ⟨?_, ?_, ⟨⟨invocation, rfl, rfl⟩⟩⟩
  · simpa only [leftSource, List.length_nil] using
      leftAction.trans (congrArg some sourceErasure)
  · simpa only [reduct?, rightSource, List.length_nil] using
      rightAction.trans (congrArg some targetErasure)

/-- Empty-ambient contextual events recover the original positioned
root-step relation, preserving the two authored sides and physical index. -/
theorem authored_contextual_empty_iff_rootStep
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (right : AuthoredSchema language ruleIndex .right sort)
    (source target : Term (signatureOf language) [] sort) :
    Nonempty (Event (S := signatureOf language)
        (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
        (authoredRootSchema left right).unpositioned source target) ↔
      RootStep (authoredRootSchema left right) source target :=
  (Event.closed_iff_rootStep source target).trans
    (PositionedRewrite.rootStep_iff_unpositioned (authoredRootSchema left right)).symm

open _root_.CategoryTheory Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath

local instance {S : Signature} : Quiver (Scope S) := bindingFrameQuiver S

local instance : Quiver (Scope (signatureOf language)) := bindingFrameQuiver (signatureOf language)

/-- A permission-bearing arrow over an actual binding path exists exactly
when every selected slot on that path is permitted. Filling the path or
matching its focus cannot supply this separate permission evidence. -/
theorem permitted_context_arrow_iff {S : Signature}
    (permission : SlotPermission S) {focus outside : Scope S}
    (context : BindingContext S focus outside) :
    (∃ arrow : permittedInterface S permission focus ⟶ permittedInterface S permission outside,
      (permissionInclusion S permission).map arrow = bindingContextArrow context) ↔
    FramePermission.PermittedPath (framePermission S permission) context := by
  constructor
  · rintro ⟨arrow, retained⟩
    have witnessed : FramePermission.PermittedArrow (framePermission S permission)
        (bindingAction S) (bindingContextArrow context) := retained ▸ arrow.property
    cases witnessed with
    | context allowed => exact allowed
  · intro allowed
    exact ⟨permittedContextArrow context allowed, rfl⟩

/-- The actual side-instantiation endpoints lift through the supplied
permission-bearing binding path. The focus context can contain genuine
opened binder variables; the inherited path, slots and siblings are retained. -/
theorem authored_permitted_focus_endpoints
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    (raw : RawMatching.RawAccumulator)
    (leftCaptured : ContextualCapturesInputs left.compiled.inputOccurrences raw invocation.body)
    (rightCaptured : ContextualCapturesInputs (alignedRightSchema left right).inputOccurrences
      raw invocation.body)
    (permission : SlotPermission (signatureOf language)) {outside : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) (ambient, sort) outside)
    (allowed : FramePermission.PermittedPath (framePermission (signatureOf language) permission) context) :
    ∃ arrow : permittedInterface (signatureOf language) permission (ambient, sort) ⟶
        permittedInterface (signatureOf language) permission outside,
      (permissionInclusion (signatureOf language) permission).map arrow = bindingContextArrow context ∧
      instantiateAt? (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0
        raw (language.rewrites.get ruleIndex).left = some (erase invocation.source) ∧
      reduct? (language.rewrites.get ruleIndex) left.spec ambient.length raw =
        some (erase invocation.target) ∧
      permittedTermArrow (permission := permission) invocation.source ≫ arrow =
        permittedTermArrow (permission := permission) (fillContext context invocation.source) ∧
      permittedTermArrow (permission := permission) invocation.target ≫ arrow =
        permittedTermArrow (permission := permission) (fillContext context invocation.target) := by
  obtain ⟨leftAction, rightAction, _⟩ := authored_contextual_instance_execution
    left leftFound right rightFound invocation raw leftCaptured rightCaptured
  exact ⟨permittedContextArrow context allowed, rfl, leftAction, rightAction, rfl, rfl⟩

end AmbientCorrespondence

namespace AmbientMatching

open SchemaElaboration TargetReification InputRecovery RawMatching RawInstantiation
open AmbientCorrespondence
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

variable {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : List TypeExpr}

/-- Partial first-lookup agreement reads only the actual compiled input
inventory. Missing used captures are allowed; unused declarations are unread. -/
def ContextualAgreesInputs (inputs : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) : Prop :=
  ∀ input ∈ inputs, ∀ value, lookup raw (inputName input) = some value →
    value = contextualValue (bodies (inputIndex input))

theorem contextualAgreesInputs_append (first second : List (InputEvidence language rule spec))
    (raw : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    ContextualAgreesInputs (first ++ second) raw bodies ↔
      ContextualAgreesInputs first raw bodies ∧ ContextualAgreesInputs second raw bodies := by
  constructor
  · intro agreed
    exact ⟨fun input member => agreed input (List.mem_append_left _ member),
      fun input member => agreed input (List.mem_append_right _ member)⟩
  · rintro ⟨firstAgreed, secondAgreed⟩ input member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact firstAgreed input firstMember
    · exact secondAgreed input secondMember

theorem contextualAgreesInputs_empty (inputs : List (InputEvidence language rule spec))
    (bodies : AmbientBodies language rule spec ambient) :
    ContextualAgreesInputs inputs [] bodies := by
  intro input member value found
  cases found

theorem contextualCapturesInputs_agrees
    {inputs : List (InputEvidence language rule spec)} {raw : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient}
    (captured : ContextualCapturesInputs inputs raw bodies) :
    ContextualAgreesInputs inputs raw bodies := by
  intro input member value found
  exact Option.some.inj (found.symm.trans (captured input member))

theorem contextualAgreesInputs_of_extension
    {inputs : List (InputEvidence language rule spec)} {initial final : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient}
    (agreed : ContextualAgreesInputs inputs final bodies) (extension : Extends initial final) :
    ContextualAgreesInputs inputs initial bodies := by
  intro input member value found
  exact agreed input member value (extension _ _ found)

theorem contextualCapturesInputs_extension
    {inputs : List (InputEvidence language rule spec)} {initial final : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient}
    (captured : ContextualCapturesInputs inputs initial bodies) (extension : Extends initial final) :
    ContextualCapturesInputs inputs final bodies := by
  intro input member
  exact extension _ _ (captured input member)

theorem assign_none_iff (initial : RawAccumulator) (name : String) (value : ContextualValue) :
    assign initial name value = none ↔
      ∃ prior, lookup initial name = some prior ∧ prior ≠ value := by
  cases stored : lookup initial name with
  | none => simp only [assign, stored, reduceCtorEq, false_iff]
            rintro ⟨prior, found, _⟩
            cases found
  | some prior =>
      simp only [assign, stored, beq_iff_eq, Option.some.injEq]
      by_cases same : prior = value
      · simp [same]
      · simp [same]

theorem assign_success_iff (initial : RawAccumulator) (name : String) (value : ContextualValue) :
    (∃ final, assign initial name value = some final) ↔
      ∀ prior, lookup initial name = some prior → prior = value := by
  cases stored : lookup initial name with
  | none =>
      constructor
      · intro _ prior found
        cases found
      · intro _
        exact ⟨(name, value) :: initial, by simp only [assign, stored]⟩
  | some prior =>
      constructor
      · rintro ⟨final, assigned⟩ queried found
        have same : prior = value := by
          by_contra different
          simp only [assign, stored, beq_iff_eq, if_neg different] at assigned
          cases assigned
        exact (Option.some.inj found.symm).trans same
      · intro compatible
        have same := compatible prior rfl
        exact ⟨initial, by simp only [assign, stored, beq_iff_eq, if_pos same]⟩

/-- A correct original assignment update preserves agreement on any other
actual source input inventory, including repeated names at other spines. -/
theorem contextualAgreesInputs_assign
    {inputs : List (InputEvidence language rule spec)} {initial final : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient}
    (admitted : admittedFor rule spec = true)
    (agreed : ContextualAgreesInputs inputs initial bodies)
    (index : Fin (metaArities (language := language) rule spec).length)
    (assigned : assign initial (metaName rule spec index) (contextualValue (bodies index)) = some final) :
    ContextualAgreesInputs inputs final bodies := by
  cases stored : lookup initial (metaName rule spec index) with
  | none =>
      simp only [assign, stored, Option.some.injEq] at assigned
      subst final
      intro input member value found
      by_cases same : metaName rule spec index = inputName input
      · have sameIndex : index = inputIndex input :=
          metaName_injective admitted (same.trans (input_named_index input).symm)
        rw [← same, lookup_cons_self] at found
        exact (Option.some.inj found).symm.trans (congrArg (fun selected => contextualValue (bodies selected)) sameIndex)
      · rw [lookup_cons_other initial _ _ _ same] at found
        exact agreed input member value found
  | some prior =>
      simp only [assign, stored] at assigned
      split at assigned
      · cases Option.some.inj assigned
        exact agreed
      · cases assigned

/-- V7's actual occurrence action exposes the independently instantiated
body image used by the original recovery operation. -/
theorem input_instance_readback
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (bodies : AmbientBodies language rule spec ambient) :
    erase (scopedInstantiation bodies (CompiledSchema.ofInput input).term) =
      erase (bind (occurrenceSubstitution (appendAmbientArguments input.compiled.arguments ambient))
        (bodies (metaIndex rule spec input.compiled.index))) := by
  have compiled := AmbientCorrespondence.input_instantiates input
    [(name, contextualValue (bodies (metaIndex rule spec input.compiled.index)))] bodies
    (lookup_cons_self [] _ _)
  simp only [instantiateAt?, instantiateWith?, lookup_cons_self, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some] at compiled
  have action := instantiateValue?_typed (bodies (metaIndex rule spec input.compiled.index))
    (appendAmbientArguments input.compiled.arguments ambient)
  rw [appendAmbientArguments_erases] at action
  exact Option.some.inj (compiled.symm.trans action)

/-- The original matcher at an actual ambient instance reduces to the
original assignment test. No ambient body is restricted to a closed context. -/
theorem input_match_instance
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    matchAt rule spec ambient.length site path locals.length initial (.fvar name)
        (erase (scopedInstantiation bodies (CompiledSchema.ofInput input).term)) =
      (assign initial name (contextualValue (bodies (metaIndex rule spec input.compiled.index)))).toList := by
  rw [input_instance_readback input bodies, matchAt_fvar]
  simp only [capture?, input.compiled.declared, input.compiled.source,
    Option.bind_eq_bind, Option.bind_some]
  rw [recoverValue?_typed_instance input.compiled.arguments input.supported input.indices input.checked]
  rfl

theorem input_match_instance_refusal_iff
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    matchAt rule spec ambient.length site path locals.length initial (.fvar name)
        (erase (scopedInstantiation bodies (CompiledSchema.ofInput input).term)) = [] ↔
      ∃ prior, lookup initial name = some prior ∧
        prior ≠ contextualValue (bodies (metaIndex rule spec input.compiled.index)) := by
  rw [input_match_instance input initial bodies, Option.toList_eq_nil_iff, assign_none_iff]

theorem input_match_instance_success_iff
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    (∃ final, final ∈ matchAt rule spec ambient.length site path locals.length initial (.fvar name)
      (erase (scopedInstantiation bodies (CompiledSchema.ofInput input).term))) ↔
      ∀ prior, lookup initial name = some prior →
        prior = contextualValue (bodies (metaIndex rule spec input.compiled.index)) := by
  rw [input_match_instance input initial bodies]
  simpa only [Option.mem_toList] using assign_success_iff initial name
    (contextualValue (bodies (metaIndex rule spec input.compiled.index)))

/-- Observations of an existing match result list relative to one actual
contextual assignment. This proposition contains no matching procedure. -/
structure InstanceMatchResults (inputs : List (InputEvidence language rule spec))
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient)
    (results : List RawAccumulator) : Prop where
  captures : ∀ final ∈ results, ContextualCapturesInputs inputs final bodies
  extension : ∀ final ∈ results, Extends initial final
  preserves : ∀ final ∈ results, ∀ otherInputs,
    ContextualAgreesInputs otherInputs initial bodies → ContextualAgreesInputs otherInputs final bodies
  complete : ContextualAgreesInputs inputs initial bodies → ∃ final, final ∈ results

theorem InstanceMatchResults.compatible
    {inputs : List (InputEvidence language rule spec)} {initial : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient} {results : List RawAccumulator}
    (observed : InstanceMatchResults inputs initial bodies results) {final : RawAccumulator}
    (member : final ∈ results) : ContextualAgreesInputs inputs initial bodies :=
  contextualAgreesInputs_of_extension (contextualCapturesInputs_agrees (observed.captures final member))
    (observed.extension final member)

theorem InstanceMatchResults.refusal_iff
    {inputs : List (InputEvidence language rule spec)} {initial : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient} {results : List RawAccumulator}
    (observed : InstanceMatchResults inputs initial bodies results) :
    results = [] ↔ ¬ ContextualAgreesInputs inputs initial bodies := by
  constructor
  · intro empty agreed
    obtain ⟨final, member⟩ := observed.complete agreed
    rw [empty] at member
    cases member
  · intro conflict
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro final member
    exact conflict (observed.compatible member)

theorem InstanceMatchResults.nilInputs (initial : RawAccumulator)
    (bodies : AmbientBodies language rule spec ambient) :
    InstanceMatchResults [] initial bodies [initial] := by
  constructor
  · intro final member input within
    cases within
  · intro final member
    have same := List.mem_singleton.mp member
    subst final
    exact Extends.refl initial
  · intro final member otherInputs agreed
    have same := List.mem_singleton.mp member
    subst final
    exact agreed
  · intro agreed
    exact ⟨initial, List.mem_singleton_self initial⟩

/-- Sequential composition is the original ordered list flatMap. The
proof retains both captured prefixes and compatibility at later reads. -/
theorem InstanceMatchResults.bind
    {first second : List (InputEvidence language rule spec)} {initial : RawAccumulator}
    {bodies : AmbientBodies language rule spec ambient} {results : List RawAccumulator}
    (observed : InstanceMatchResults first initial bodies results)
    (next : RawAccumulator → List RawAccumulator)
    (continuations : ∀ middle ∈ results, InstanceMatchResults second middle bodies (next middle)) :
    InstanceMatchResults (first ++ second) initial bodies (results.flatMap next) := by
  constructor
  · intro final member
    obtain ⟨middle, firstMember, secondMember⟩ := List.mem_flatMap.mp member
    have continued := continuations middle firstMember
    exact (contextualCapturesInputs_append first second final bodies).mpr
      ⟨contextualCapturesInputs_extension (observed.captures middle firstMember)
          (continued.extension final secondMember),
        continued.captures final secondMember⟩
  · intro final member
    obtain ⟨middle, firstMember, secondMember⟩ := List.mem_flatMap.mp member
    exact (observed.extension middle firstMember).trans
      ((continuations middle firstMember).extension final secondMember)
  · intro final member otherInputs agreed
    obtain ⟨middle, firstMember, secondMember⟩ := List.mem_flatMap.mp member
    exact (continuations middle firstMember).preserves final secondMember otherInputs
      (observed.preserves middle firstMember otherInputs agreed)
  · intro agreed
    obtain ⟨firstAgreed, secondAgreed⟩ :=
      (contextualAgreesInputs_append first second initial bodies).mp agreed
    obtain ⟨middle, firstMember⟩ := observed.complete firstAgreed
    obtain ⟨final, secondMember⟩ := (continuations middle firstMember).complete
      (observed.preserves middle firstMember second secondAgreed)
    exact ⟨final, List.mem_flatMap.mpr ⟨middle, firstMember, secondMember⟩⟩

/-- The original raw match at one actual compiled instance retains exact
capture agreement and extends the initial assignment without overwrites. -/
def InstanceMatchesAt {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop :=
  ∀ initial (bodies : AmbientBodies language rule spec ambient),
    InstanceMatchResults compiled.inputOccurrences initial bodies
      (matchAt rule spec ambient.length site path locals.length initial source
        (erase (scopedInstantiation bodies compiled.term)))

theorem input_schema_instance_matches
    {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.ofInput input) site path := by
  intro initial bodies
  rw [input_match_instance input initial bodies]
  let evidence : InputEvidence language rule spec := ⟨site, locals, path, name, sort, input⟩
  constructor
  · intro final member queried within
    have assigned := Option.mem_toList.mp member
    have same : queried = evidence := List.mem_singleton.mp within
    subst queried
    exact assign_lookup assigned
  · intro final member
    exact assign_extends (Option.mem_toList.mp member)
  · intro final member otherInputs agreed
    have assigned := Option.mem_toList.mp member
    have named : metaName (language := language) rule spec
        (metaIndex rule spec input.compiled.index) = name := input_named_index evidence
    exact contextualAgreesInputs_assign input.admitted agreed (metaIndex rule spec input.compiled.index) (by
      simpa only [named] using assigned)
  · intro agreed
    have compatible : ∀ prior, lookup initial name = some prior →
        prior = contextualValue (bodies (metaIndex rule spec input.compiled.index)) :=
      agreed evidence (List.mem_singleton_self evidence)
    obtain ⟨final, assigned⟩ := (assign_success_iff initial name _).mpr compatible
    exact ⟨final, Option.mem_toList.mpr assigned⟩

theorem cast_sort_instance_matches {locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (compiled : CompiledSchema language rule spec locals source first)
    (same : first = second) {site : RulePatternSite} {path : List Nat}
    (observed : InstanceMatchesAt (ambient := ambient) compiled site path) :
    InstanceMatchesAt (ambient := ambient) (compiled.castSort same) site path := by
  cases same
  exact observed

theorem lambda_schema_instance_matches {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain)
    (observed : InstanceMatchesAt (ambient := ambient) body site (path ++ [0])) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.lambda body) site path := by
  intro initial bodies
  simp only [CompiledSchema.lambda, scopedInstantiation, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs, erase, matchAt, matchAtWith]
  rw [show erase (ContextualAssignment.instantiate bodies
      (ContextualAssignment.weakenSub [domain]
        (ContextualAssignment.weakenSub locals (fun _ (position : Var ambient _) => Term.var position)))
      (liftSub (liftSub (emptyAmbientSub ambient) locals) [domain]) body.term) =
      erase (scopedInstantiation bodies body.term) from
    erase_scoped_cast_append (binders := [domain]) (locals := locals) bodies body.term]
  change InstanceMatchResults body.inputOccurrences initial bodies
    (matchAt rule spec ambient.length site (path ++ [0]) (locals.length + 1) initial source
      (erase (scopedInstantiation bodies body.term)))
  rw [show locals.length + 1 = (domain :: locals).length by simp]
  exact observed initial bodies

theorem multiLambda_schema_instance_matches {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    (observed : InstanceMatchesAt (ambient := ambient) body site (path ++ [0])) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.multiLambda count body) site path := by
  intro initial bodies
  simp only [CompiledSchema.multiLambda, scopedInstantiation, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs, erase, erase_scoped_cast_append, matchAt, matchAtWith,
    beq_self_eq_true, if_true]
  change InstanceMatchResults body.inputOccurrences initial bodies
    (matchAt rule spec ambient.length site (path ++ [0]) (locals.length + count) initial source
      (erase (scopedInstantiation bodies body.term)))
  rw [show locals.length + count = (List.replicate count domain ++ locals).length by
    simp [List.length_append, Nat.add_comm]]
  exact observed initial bodies

theorem parameter_scope_instance_match {parameter : TermParam} {binders : List TypeExpr}
    {sort : TypeExpr} (scope : ParameterScope parameter binders sort)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : RawAccumulator) (source target : Pattern) :
    matchAt rule spec ambient.length site path depth initial (scope.wrap source) (scope.wrap target) =
      matchAt rule spec ambient.length site (path ++ ObjectRoundtrip.parameterChildSuffix scope)
        (depth + binders.length) initial source target := by
  cases scope <;>
    simp only [ParameterScope.wrap, ObjectRoundtrip.parameterChildSuffix,
      List.length_nil, List.length_cons, List.length_replicate,
      List.append_nil, Nat.add_zero, matchAt, matchAtWith, beq_self_eq_true, if_true]

theorem parameter_body_instance_match {parameter : TermParam} {source : Pattern}
    (body : ParameterBody parameter source)
    (found : parameterBody? parameter source = some body)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : RawAccumulator) (target : Pattern) :
    matchAt rule spec ambient.length site path depth initial source (body.scope.wrap target) =
      matchAt rule spec ambient.length site (path ++ body.pathSuffix)
        (depth + body.binders.length) initial body.body target := by
  rcases body with ⟨binders, sort, scope, body, suffix, readback⟩
  cases readback
  rw [ObjectRoundtrip.parameterBody?_wrapped] at found
  cases Option.some.inj found
  exact parameter_scope_instance_match scope site path depth initial body target

def ConstructorInstanceMatchesAt {locals : List TypeExpr} {parameters : List TermParam}
    {sources : List Pattern}
    (arguments : CompiledConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ initial (bodies : AmbientBodies language rule spec ambient),
    InstanceMatchResults arguments.inputOccurrences initial bodies
      (matchArgsAt rule spec ambient.length site path locals.length initial offset sources
        (eraseConstructorArguments arguments.scopes (scopedArguments bodies arguments.arguments)))

theorem compile_constructor_arguments_instance_matches
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled →
        InstanceMatchesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        ConstructorInstanceMatchesAt (ambient := ambient) arguments site path offset := by
  refine compileConstructorArguments?_observes compile locals path
    (fun offset _ _ compiled => ConstructorInstanceMatchesAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset initial bodies
    simpa only [scopedArguments, ContextualAssignment.instantiateArgs,
      eraseConstructorArguments, matchArgsAt, matchArgsAtWith] using
      InstanceMatchResults.nilInputs initial bodies
  · intro offset parameter parameters source sources body head tail bodyFound headFound tailObserved initial bodies
    have headObserved := children _ _ _ _ head headFound initial bodies
    have composed := headObserved.bind
      (fun middle => matchArgsAt rule spec ambient.length site path locals.length middle
        (offset + 1) sources
        (eraseConstructorArguments tail.scopes (scopedArguments bodies tail.arguments)))
      (fun middle _ => tailObserved middle bodies)
    simp only [scopedArguments, ContextualAssignment.instantiateArgs,
      eraseConstructorArguments, erase_scoped_cast_append, matchArgsAt, matchArgsAtWith]
    rw [← matchAt, parameter_body_instance_match body bodyFound site
      (path ++ [offset]) locals.length initial]
    rw [show locals.length + body.binders.length = (body.binders ++ locals).length by
      simp [List.length_append, Nat.add_comm]]
    simpa only [matchArgsAt] using composed


def VectorInstanceMatchesAt {locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ initial (bodies : AmbientBodies language rule spec ambient),
    InstanceMatchResults elements.inputOccurrences initial bodies
      (matchArgsAt rule spec ambient.length site path locals.length initial offset sources
        (eraseArguments (scopedArguments bodies elements.arguments)))

theorem compile_vector_elements_instance_matches
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled →
        InstanceMatchesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources sort),
      compileVectorElements? compile locals path offset sort sources = some elements →
        VectorInstanceMatchesAt (ambient := ambient) elements site path offset := by
  refine compileVectorElements?_observes compile locals path sort
    (fun offset _ compiled => VectorInstanceMatchesAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset initial bodies
    simpa only [scopedArguments, ContextualAssignment.instantiateArgs,
      eraseArguments, matchArgsAt, matchArgsAtWith] using
      InstanceMatchResults.nilInputs initial bodies
  · intro offset source sources head tail headFound tailObserved initial bodies
    have composed := (children _ _ _ _ head headFound initial bodies).bind
      (fun middle => matchArgsAt rule spec ambient.length site path locals.length middle
        (offset + 1) sources (eraseArguments (scopedArguments bodies tail.arguments)))
      (fun middle _ => tailObserved middle bodies)
    simp only [scopedArguments, ContextualAssignment.instantiateArgs,
      eraseArguments, matchArgsAt, matchArgsAtWith]
    rw [show erase (ContextualAssignment.instantiate bodies
        (ContextualAssignment.weakenSub []
          (ContextualAssignment.weakenSub locals
            (fun _ (position : Var ambient _) => Term.var position)))
        (liftSub (liftSub (emptyAmbientSub ambient) locals) []) head.term) =
        erase (scopedInstantiation bodies head.term) from
      erase_scoped_cast_append (binders := []) (locals := locals) bodies head.term]
    simpa only [matchAt, matchArgsAt] using composed


theorem constructor_schema_instance_matches {locals : List TypeExpr} {label : String}
    {sources : List Pattern} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    (arguments : CompiledConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources)
    (observed : ConstructorInstanceMatchesAt (ambient := ambient) arguments site path 0) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.constructor path selected ordinary arguments)
      site path := by
  intro initial bodies
  simp only [CompiledSchema.constructor, scopedInstantiation, ContextualAssignment.instantiate,
    erase, matchAt, matchAtWith, selected.named, beq_self_eq_true, if_true]
  exact observed initial bodies

theorem vector_schema_instance_matches {locals : List TypeExpr} {sources : List Pattern}
    {sort : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (elements : CompiledVectorElements language rule spec locals sources sort)
    (observed : VectorInstanceMatchesAt (ambient := ambient) elements site path 0) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.vector elements) site path := by
  intro initial bodies
  simp only [CompiledSchema.vector, scopedInstantiation, ContextualAssignment.instantiate,
    erase, matchAt, matchAtWith, beq_self_eq_true, Option.isNone_none, Bool.true_and, if_true]
  exact observed initial bodies

theorem vector_constructor_schema_instance_matches {locals : List TypeExpr} {sources : List Pattern}
    {category : String} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort)
    (observed : VectorInstanceMatchesAt (ambient := ambient) elements site path 0) :
    InstanceMatchesAt (ambient := ambient) (CompiledSchema.vectorConstructor path selected elements)
      site path := by
  unfold CompiledSchema.vectorConstructor
  apply cast_sort_instance_matches
  intro initial bodies
  simp only [scopedInstantiation, ContextualAssignment.instantiate, erase, matchAt, matchAtWith,
    beq_self_eq_true, Option.isNone_none, Bool.true_and, if_true]
  exact observed initial bodies

/-- Actual recursive source compilation earns matching at its contextual
instance, including exact capture, agreement preservation and conflict refusal. -/
theorem compileSchemaWithFuel?_instance_matches
    (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
        InstanceMatchesAt (ambient := ambient) compiled site path := by
  refine InputAssemblyInvariant.walk
    (observe := fun _ path _ _ compiled => InstanceMatchesAt (ambient := ambient) compiled site path) ?_ fuel
  refine {
    bound := ?_
    free := fun _ _ _ _ input => input_schema_instance_matches input
    constructor := fun compile children locals path _ sources selected ordinary arguments found =>
      constructor_schema_instance_matches path selected ordinary arguments
        (compile_constructor_arguments_instance_matches compile site children locals path sources 0 _ arguments found)
    abstraction := fun _ _ _ _ _ body action => lambda_schema_instance_matches body action
    multiAbstraction := fun _ _ _ _ _ count body action => multiLambda_schema_instance_matches count body action
    vector := fun compile children locals path sources elemSort elements found =>
      vector_schema_instance_matches elements
        (compile_vector_elements_instance_matches compile site children locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      vector_constructor_schema_instance_matches path selected elements
        (compile_vector_elements_instance_matches compile site children locals path
          selected.elementSort sources 0 elements found) }
  intro locals path index sort position admitted initial bodies
  simp only [scopedInstantiation, ContextualAssignment.instantiate,
    schema_prefix_valuation, erase, matchAt, matchAtWith]
  rw [InputRecovery.variableIndex_injPrefix position, boundPosition?_index locals index sort admitted]
  simp only [beq_self_eq_true, if_true]
  exact InstanceMatchResults.nilInputs initial bodies

/-- Reconstruction observes the existing relational match and the existing
instantiator under any later assignment that retains its first lookups. -/
def ReconstructsAt (source : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat) : Prop :=
  ∀ initial final completed target,
    Matches rule spec ambient.length site path depth initial source target final →
    Extends final completed → target.hasCanonicalBinderMetadata = true →
    instantiateAt? rule spec ambient.length site path depth completed source = some target

def ArgumentsReconstructAt (sources : List Pattern) (site : RulePatternSite)
    (path : List Nat) (depth offset : Nat) : Prop :=
  ∀ initial final completed targets,
    Arguments rule spec ambient.length site path depth initial offset sources targets final →
    Extends final completed → Pattern.hasCanonicalBinderMetadataList targets = true →
    instantiateArgsAt? rule spec ambient.length site path depth completed offset sources = some targets

theorem input_reconstructs (name : String) (site : RulePatternSite) (path : List Nat) (depth : Nat) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient) (.fvar name) site path depth := by
  intro initial final completed target matched extension _
  cases matched with
  | capture captured =>
      obtain ⟨dependencies, arguments, value, _, occurrence, _, retained, interpreted, _⟩ :=
        capture_interpretation captured
      simp only [instantiateAt?, instantiateWith?, extension _ _ retained, occurrence,
        Option.bind_eq_bind, Option.bind_some]
      exact interpreted

theorem bound_reconstructs (index : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient) (.bvar index) site path depth := by
  intro initial final completed target matched _ _
  cases matched
  simp only [instantiateAt?, instantiateWith?]

theorem arguments_nil_reconstruct (site : RulePatternSite) (path : List Nat) (depth offset : Nat) :
    ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient) [] site path depth offset := by
  intro initial final completed targets matched _ _
  cases matched
  simp only [instantiateArgsAt?, instantiateArgsWith?]

theorem arguments_cons_reconstruct {source : Pattern} {sources : List Pattern}
    {site : RulePatternSite} {path : List Nat} {depth offset : Nat}
    (first : ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      source site (path ++ [offset]) depth)
    (rest : ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient)
      sources site path depth (offset + 1)) :
    ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient)
      (source :: sources) site path depth offset := by
  intro initial final completed targets matched extension canonical
  cases matched with
  | cons head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
      have headAction := first _ _ _ _ head (tail.extends.trans extension) canonical.1
      have tailAction := rest _ _ _ _ tail extension canonical.2
      unfold instantiateAt? at headAction
      unfold instantiateArgsAt? at tailAction ⊢
      simp only [instantiateArgsWith?, headAction, tailAction, Option.bind_eq_bind, Option.bind_some]

theorem lambda_reconstructs {source : Pattern} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    (body : ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      source site (path ++ [0]) (depth + 1)) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      (.lambda none source) site path depth := by
  intro initial final completed target matched extension canonical
  cases matched with
  | binder matchedBody =>
      rename_i actualDisplay targetBody
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      have anonymous := Option.isNone_iff_eq_none.mp canonical.1
      subst actualDisplay
      have action := body _ _ _ _ matchedBody extension canonical.2
      unfold instantiateAt? at action ⊢
      simp only [instantiateWith?, action, Option.bind_eq_bind, Option.bind_some]

theorem multiLambda_reconstructs {source : Pattern} {site : RulePatternSite} {path : List Nat}
    {depth count : Nat}
    (body : ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      source site (path ++ [0]) (depth + count)) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      (.multiLambda count [] source) site path depth := by
  intro initial final completed target matched extension canonical
  cases matched with
  | binders matchedBody =>
      rename_i actualDisplays targetBody
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      have anonymous := List.isEmpty_iff.mp canonical.1
      subst actualDisplays
      have action := body _ _ _ _ matchedBody extension canonical.2
      unfold instantiateAt? at action ⊢
      simp only [instantiateWith?, action, Option.bind_eq_bind, Option.bind_some]

theorem constructor_reconstructs {label : String} {sources : List Pattern}
    {site : RulePatternSite} {path : List Nat} {depth : Nat}
    (arguments : ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient)
      sources site path depth 0) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      (.apply label sources) site path depth := by
  intro initial final completed target matched extension canonical
  cases matched with
  | constructor matchedArguments =>
      have action := arguments _ _ _ _ matchedArguments extension canonical
      unfold instantiateArgsAt? at action
      simp only [instantiateAt?, instantiateWith?, action, Option.bind_eq_bind, Option.bind_some]

theorem vector_reconstructs {sources : List Pattern} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    (arguments : ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient)
      sources site path depth 0) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      (.collection .vec sources none) site path depth := by
  intro initial final completed target matched extension canonical
  cases matched with
  | bag nonVector _ => exact False.elim (nonVector rfl)
  | vector matchedArguments =>
      have action := arguments _ _ _ _ matchedArguments extension canonical
      unfold instantiateArgsAt? at action
      simp only [instantiateAt?, instantiateWith?, action, Option.bind_eq_bind, Option.bind_some]

theorem parameter_scope_reconstructs {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (source : Pattern)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (body : ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      source site (path ++ ObjectRoundtrip.parameterChildSuffix scope) (depth + binders.length)) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      (scope.wrap source) site path depth := by
  cases scope with
  | simple =>
      simpa only [ParameterScope.wrap, ObjectRoundtrip.parameterChildSuffix,
        List.append_nil, List.length_nil, Nat.add_zero] using body
  | abstraction =>
      apply lambda_reconstructs
      simpa only [ObjectRoundtrip.parameterChildSuffix, List.length_cons, List.length_nil] using body
  | abstractionBase =>
      apply lambda_reconstructs
      simpa only [ObjectRoundtrip.parameterChildSuffix, List.length_cons, List.length_nil] using body
  | multiAbstraction =>
      apply multiLambda_reconstructs
      simpa only [ObjectRoundtrip.parameterChildSuffix, List.length_replicate] using body
  | multiAbstractionBase =>
      apply multiLambda_reconstructs
      simpa only [ObjectRoundtrip.parameterChildSuffix, List.length_replicate] using body

theorem parameter_body_reconstructs {parameter : TermParam} {source : Pattern}
    (body : ParameterBody parameter source) (found : parameterBody? parameter source = some body)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (action : ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient)
      body.body site (path ++ body.pathSuffix) (depth + body.binders.length)) :
    ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient) source site path depth := by
  rcases body with ⟨binders, sort, scope, body, suffix, readback⟩
  cases readback
  rw [ObjectRoundtrip.parameterBody?_wrapped] at found
  cases Option.some.inj found
  exact parameter_scope_reconstructs scope body site path depth action

def SchemaReconstructsAt {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (_compiled : CompiledSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop :=
  ReconstructsAt (rule := rule) (spec := spec) (ambient := ambient) source site path locals.length

def ConstructorReconstructsAt {locals : List TypeExpr} {parameters : List TermParam} {sources : List Pattern}
    (_arguments : CompiledConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient) sources site path locals.length offset

def VectorReconstructsAt {locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (_elements : CompiledVectorElements language rule spec locals sources sort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ArgumentsReconstructAt (rule := rule) (spec := spec) (ambient := ambient) sources site path locals.length offset

theorem compile_constructor_arguments_reconstruct
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → SchemaReconstructsAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : CompiledConstructorArguments language rule spec locals parameters sources),
      compileConstructorArguments? compile locals path offset parameters sources = some arguments →
        ConstructorReconstructsAt (ambient := ambient) arguments site path offset := by
  refine compileConstructorArguments?_observes compile locals path
    (fun offset _ _ compiled => ConstructorReconstructsAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset
    exact arguments_nil_reconstruct site path locals.length offset
  · intro offset parameter parameters source sources body head tail bodyFound headFound tailObserved
    apply arguments_cons_reconstruct
    · apply parameter_body_reconstructs body bodyFound site (path ++ [offset]) locals.length
      have action := children _ _ _ _ head headFound
      simpa only [SchemaReconstructsAt, List.length_append, Nat.add_comm] using action
    · exact tailObserved


theorem compile_vector_elements_reconstruct
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (CompiledSchema language rule spec locals source sort))
    (site : RulePatternSite)
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled → SchemaReconstructsAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : CompiledVectorElements language rule spec locals sources sort),
      compileVectorElements? compile locals path offset sort sources = some elements →
        VectorReconstructsAt (ambient := ambient) elements site path offset := by
  refine compileVectorElements?_observes compile locals path sort
    (fun offset _ compiled => VectorReconstructsAt (ambient := ambient) compiled site path offset) ?_ ?_
  · intro offset
    exact arguments_nil_reconstruct site path locals.length offset
  · intro offset source sources head tail headFound tailObserved
    exact arguments_cons_reconstruct (children _ _ _ _ head headFound)
      (tailObserved)


theorem cast_sort_reconstructs {locals : List TypeExpr} {source : Pattern} {first second : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source first) (same : first = second)
    {site : RulePatternSite} {path : List Nat}
    (action : SchemaReconstructsAt (ambient := ambient) compiled site path) :
    SchemaReconstructsAt (ambient := ambient) (compiled.castSort same) site path := action

theorem input_schema_reconstructs {locals : List TypeExpr} {site : RulePatternSite} {path : List Nat}
    {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.ofInput input) site path :=
  input_reconstructs name site path locals.length

theorem lambda_schema_reconstructs {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat}
    (body : CompiledSchema language rule spec (domain :: locals) source codomain)
    (action : SchemaReconstructsAt (ambient := ambient) body site (path ++ [0])) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.lambda body) site path := by
  apply lambda_reconstructs
  simpa only [SchemaReconstructsAt, List.length_cons, Nat.add_comm] using action

theorem multiLambda_schema_reconstructs {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} {site : RulePatternSite} {path : List Nat} (count : Nat)
    (body : CompiledSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    (action : SchemaReconstructsAt (ambient := ambient) body site (path ++ [0])) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.multiLambda count body) site path := by
  apply multiLambda_reconstructs
  simpa only [SchemaReconstructsAt, List.length_append, List.length_replicate, Nat.add_comm] using action

theorem constructor_schema_reconstructs {locals : List TypeExpr} {label : String} {sources : List Pattern}
    {site : RulePatternSite} (path : List Nat) (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index))
    (arguments : CompiledConstructorArguments language rule spec locals (language.terms.get selected.index).params sources)
    (action : ConstructorReconstructsAt (ambient := ambient) arguments site path 0) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.constructor path selected ordinary arguments) site path :=
  constructor_reconstructs action

theorem vector_schema_reconstructs {locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    {site : RulePatternSite} {path : List Nat} (elements : CompiledVectorElements language rule spec locals sources sort)
    (action : VectorReconstructsAt (ambient := ambient) elements site path 0) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.vector elements) site path :=
  vector_reconstructs action

theorem vector_constructor_schema_reconstructs {locals : List TypeExpr} {sources : List Pattern}
    {category : String} {site : RulePatternSite} (path : List Nat)
    (selected : SelectedVectorConstructor language category)
    (elements : CompiledVectorElements language rule spec locals sources selected.elementSort)
    (action : VectorReconstructsAt (ambient := ambient) elements site path 0) :
    SchemaReconstructsAt (ambient := ambient) (CompiledSchema.vectorConstructor path selected elements) site path :=
  vector_reconstructs action

/-- The actual compiler earns exact reconstruction from the original
ordered matcher, retaining the source addresses and anonymous wrappers. -/
theorem compileSchemaWithFuel?_reconstructs
    (site : RulePatternSite) (fuel : Nat) :
    ∀ locals path source sort (compiled : CompiledSchema language rule spec locals source sort),
      compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled →
        SchemaReconstructsAt (ambient := ambient) compiled site path := by
  refine InputAssemblyInvariant.walk
    (observe := fun _ path _ _ compiled => SchemaReconstructsAt (ambient := ambient) compiled site path) ?_ fuel
  refine {
    bound := ?_
    free := fun _ _ _ _ input => input_schema_reconstructs input
    constructor := fun compile children locals path _ sources selected ordinary arguments found =>
      constructor_schema_reconstructs path selected ordinary arguments
        (compile_constructor_arguments_reconstruct compile site children locals path sources 0 _ arguments found)
    abstraction := fun _ _ _ _ _ body action => lambda_schema_reconstructs body action
    multiAbstraction := fun _ _ _ _ _ count body action => multiLambda_schema_reconstructs count body action
    vector := fun compile children locals path sources elemSort elements found =>
      vector_schema_reconstructs elements
        (compile_vector_elements_reconstruct compile site children locals path elemSort sources 0 elements found)
    namedVector := fun compile children locals path sources _ selected elements found =>
      vector_constructor_schema_reconstructs path selected elements
        (compile_vector_elements_reconstruct compile site children locals path
          selected.elementSort sources 0 elements found) }
  intro locals path index sort position admitted
  exact bound_reconstructs index site path locals.length

theorem parameter_wrap_hasCanonicalBinderMetadata {parameter : TermParam}
    {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (body : Pattern) :
    (scope.wrap body).hasCanonicalBinderMetadata = body.hasCanonicalBinderMetadata := by
  cases scope <;> rfl

mutual
theorem erase_hasCanonicalBinderMetadata :
    ∀ {bound : List TypeExpr} {sort : TypeExpr} (term : Term (signatureOf language) bound sort),
      (erase term).hasCanonicalBinderMetadata = true
  | _, _, .var _ => rfl
  | _, _, .op (.constructor _ _ _ scopes) arguments => by
      simpa only [erase, Pattern.hasCanonicalBinderMetadata] using
        eraseConstructorArguments_hasCanonicalBinderMetadata scopes arguments
  | _, _, .op (.collectionConstructor _ _ _ _ _ _ _) arguments => by
      simpa only [erase, Pattern.hasCanonicalBinderMetadata] using
        eraseArguments_hasCanonicalBinderMetadata arguments
  | _, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          simpa only [erase, Pattern.hasCanonicalBinderMetadata, Option.isNone_none, Bool.true_and] using
            erase_hasCanonicalBinderMetadata body
  | _, _, .op (.multiLambda _ _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          simpa only [erase, Pattern.hasCanonicalBinderMetadata, List.isEmpty_nil, Bool.true_and] using
            erase_hasCanonicalBinderMetadata body
  | _, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          simp only [erase, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
          exact ⟨erase_hasCanonicalBinderMetadata body, erase_hasCanonicalBinderMetadata replacement⟩
  | _, _, .op (.collection _ _ _) arguments => by
      simpa only [erase, Pattern.hasCanonicalBinderMetadata] using
        eraseArguments_hasCanonicalBinderMetadata arguments

theorem eraseArguments_hasCanonicalBinderMetadata :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) arity bound),
      Pattern.hasCanonicalBinderMetadataList (eraseArguments arguments) = true
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [eraseArguments, Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
      exact ⟨erase_hasCanonicalBinderMetadata head, eraseArguments_hasCanonicalBinderMetadata tail⟩

theorem eraseConstructorArguments_hasCanonicalBinderMetadata :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (scopes : ParameterScopes parameters arity) (arguments : Args (signatureOf language) arity bound),
      Pattern.hasCanonicalBinderMetadataList (eraseConstructorArguments scopes arguments) = true
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons scope scopes, .cons head tail => by
      simp only [eraseConstructorArguments, Pattern.hasCanonicalBinderMetadataList,
        parameter_wrap_hasCanonicalBinderMetadata, Bool.and_eq_true]
      exact ⟨erase_hasCanonicalBinderMetadata head,
        eraseConstructorArguments_hasCanonicalBinderMetadata scopes tail⟩
end

/-- Success with the supplied contextual bodies reflects to their actual
intrinsic instance at the independently fixed result sort and ambient context. -/
theorem compileSchemaWithFuel?_match_canonical_iff
    {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr} {site : RulePatternSite}
    {path : List Nat} {fuel : Nat}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient)
    (target : Term (signatureOf language) (locals ++ ambient) sort)
    (instanceCanonical : CanonicalObject (scopedInstantiation bodies compiled.term))
    (targetCanonical : CanonicalObject target) :
    (∃ final ∈ matchAt rule spec ambient.length site path locals.length initial source (erase target),
      ContextualCapturesInputs compiled.inputOccurrences final bodies) ↔
      ContextualAgreesInputs compiled.inputOccurrences initial bodies ∧
        scopedInstantiation bodies compiled.term = target := by
  constructor
  · rintro ⟨final, matched, captured⟩
    have extension := matchAt_extends matched
    have reconstructed := compileSchemaWithFuel?_reconstructs site fuel _ _ _ _ compiled found
      initial final final (erase target) (matchAt_sound matched) (Extends.refl final)
      (erase_hasCanonicalBinderMetadata target)
    have instantiated := AmbientCorrespondence.compileSchemaWithFuel?_instantiates
      site fuel _ _ _ _ compiled found final bodies captured
    have sameImage : erase (scopedInstantiation bodies compiled.term) = erase target :=
      Option.some.inj (instantiated.symm.trans reconstructed)
    exact ⟨contextualAgreesInputs_of_extension (contextualCapturesInputs_agrees captured) extension,
      CanonicalObject.erase_injective rule spec instanceCanonical targetCanonical sameImage⟩
  · rintro ⟨agreed, same⟩
    rw [← same]
    have observed := compileSchemaWithFuel?_instance_matches site fuel _ _ _ _ compiled found initial bodies
    obtain ⟨final, member⟩ := observed.complete agreed
    exact ⟨final, member, observed.captures final member⟩

theorem compileSchemaWithFuel?_instance_refusal_iff
    {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr} {site : RulePatternSite}
    {path : List Nat} {fuel : Nat}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    (initial : RawAccumulator) (bodies : AmbientBodies language rule spec ambient) :
    matchAt rule spec ambient.length site path locals.length initial source
        (erase (scopedInstantiation bodies compiled.term)) = [] ↔
      ¬ ContextualAgreesInputs compiled.inputOccurrences initial bodies :=
  (compileSchemaWithFuel?_instance_matches site fuel _ _ _ _ compiled found initial bodies).refusal_iff

theorem compileSchemaWithFuel?_empty_match_instance
    {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr} {site : RulePatternSite}
    {path : List Nat} {fuel : Nat}
    (compiled : CompiledSchema language rule spec locals source sort)
    (found : compileSchemaWithFuel? language rule spec site fuel locals path source sort = some compiled)
    (bodies : AmbientBodies language rule spec ambient) :
    ∃ final ∈ matchAt rule spec ambient.length site path locals.length [] source
        (erase (scopedInstantiation bodies compiled.term)),
      ContextualCapturesInputs compiled.inputOccurrences final bodies := by
  have observed := compileSchemaWithFuel?_instance_matches site fuel _ _ _ _ compiled found [] bodies
  obtain ⟨final, member⟩ := observed.complete (contextualAgreesInputs_empty _ bodies)
  exact ⟨final, member, observed.captures final member⟩

/-- The attached authored compiler earns instance matching and exact
reconstruction at the original physical rule and source-side address. -/
theorem elaborateAuthoredSchema?_matching
    {ruleIndex : Fin language.rewrites.length} {site : RulePatternSite} {sort : TypeExpr}
    (compiled : AuthoredSchema language ruleIndex site sort)
    (found : elaborateAuthoredSchema? language ruleIndex site sort = some compiled) :
    InstanceMatchesAt (ambient := ambient) compiled.compiled site [] ∧
      SchemaReconstructsAt (ambient := ambient) compiled.compiled site [] := by
  have built := elaborateAuthoredSchema?_compilation compiled found
  exact ⟨compileSchemaWithFuel?_instance_matches site _ _ _ _ _ compiled.compiled built,
    compileSchemaWithFuel?_reconstructs site _ _ _ _ _ compiled.compiled built⟩

/-- Canonical reflection at the original root matching entry point uses
the attached source compiler and the supplied independently sorted ambient bodies. -/
theorem authored_left_match_canonical_iff
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (found : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) left.spec ambient)
    (target : Term (signatureOf language) ambient sort)
    (instanceCanonical : CanonicalObject (scopedInstantiation bodies left.compiled.term))
    (targetCanonical : CanonicalObject target) :
    (∃ raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase target),
      ContextualCapturesInputs left.compiled.inputOccurrences raw bodies) ↔
      scopedInstantiation bodies left.compiled.term = target := by
  have properties := elaborateAuthoredSchema?_matching (ambient := ambient) left found
  have leftSource : left.source = (language.rewrites.get ruleIndex).left := (Option.some.inj left.atSite).symm
  change (∃ raw ∈ matchAt (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0 []
      (language.rewrites.get ruleIndex).left (erase target),
    ContextualCapturesInputs left.compiled.inputOccurrences raw bodies) ↔ _
  rw [← leftSource]
  constructor
  · rintro ⟨raw, matched, captured⟩
    have reconstructed := properties.2 [] raw raw (erase target) (matchAt_sound matched)
      (Extends.refl raw) (erase_hasCanonicalBinderMetadata target)
    have instantiated := AmbientCorrespondence.elaborateAuthoredSchema?_instantiates
      (ambient := ambient) left found raw bodies captured
    exact CanonicalObject.erase_injective (language.rewrites.get ruleIndex) left.spec
      instanceCanonical targetCanonical (Option.some.inj (instantiated.symm.trans reconstructed))
  · intro same
    rw [← same]
    have observed := properties.1 [] bodies
    obtain ⟨raw, matched⟩ := observed.complete (contextualAgreesInputs_empty _ bodies)
    exact ⟨raw, matched, observed.captures raw matched⟩

/-- The original source coverage check supplies presence; actual matching
agreement supplies the body at every read RHS occurrence. -/
theorem matched_captures_right_inputs {locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : CompiledSchema language rule spec locals source sort)
    (coverage : rightInputsProducedOnLeft? compiled = true)
    {target : Pattern} {raw : RawAccumulator}
    (matched : raw ∈ matchRuleAt rule spec ambient.length target)
    (bodies : AmbientBodies language rule spec ambient)
    (agreed : ContextualAgreesInputs compiled.inputOccurrences raw bodies) :
    ContextualCapturesInputs compiled.inputOccurrences raw bodies := by
  have present := Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain.matched_captures
    (matchRuleAt_iff.mp matched)
  intro input member
  obtain ⟨value, found⟩ := present (inputName input)
    ((rightInputsProducedOnLeft?_iff compiled).mp coverage input member)
  rw [agreed input member value found] at found
  exact found

open Mettapedia.OSLF.Binding.ContextualRootEvents

/-- Every actual answer at an authored contextual instance supplies its
used LHS bodies and preserves agreement on the actual RHS inventory. -/
theorem authored_contextual_match_captures
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    {raw : RawAccumulator}
    (matched : raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length
      (erase invocation.source)) :
    ContextualCapturesInputs left.compiled.inputOccurrences raw invocation.body ∧
      ContextualAgreesInputs (alignedRightSchema left right).inputOccurrences raw invocation.body := by
  have observed := (elaborateAuthoredSchema?_matching (ambient := ambient) left leftFound).1 [] invocation.body
  have leftSource : left.source = (language.rewrites.get ruleIndex).left := (Option.some.inj left.atSite).symm
  have sourceErasure : erase (scopedInstantiation (ambient := ambient) (locals := [])
      invocation.body left.compiled.term) = erase invocation.source :=
    (congrArg (erase (language := language) (bound := ambient) (type := sort))
      (contextual_instance_source left right invocation)).symm
  have sameResults : matchAt (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0 []
      left.source (erase (scopedInstantiation invocation.body left.compiled.term)) =
      matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase invocation.source) := by
    simp only [matchRuleAt, matchRuleWithAt, matchAt, leftSource]
    exact congrArg (matchAtWith literalBodyComparison (language.rewrites.get ruleIndex) left.spec
      ambient.length .left [] 0 [] (language.rewrites.get ruleIndex).left) sourceErasure
  have rootObserved : InstanceMatchResults left.compiled.inputOccurrences [] invocation.body
      (matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase invocation.source)) := by
    rw [← sameResults]
    exact observed
  exact ⟨rootObserved.captures raw matched,
    rootObserved.preserves raw matched _ (contextualAgreesInputs_empty _ invocation.body)⟩

/-- Existing occurrence-local coverage joins every original ambient match
answer to the actual reduct and contextual event at the same physical rule. -/
theorem authored_contextual_match_execution
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (coverage : rightInputsProducedOnLeft? (alignedRightSchema left right) = true)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    {raw : RawAccumulator}
    (matched : raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length
      (erase invocation.source)) :
    instantiateAt? (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0 raw
        (language.rewrites.get ruleIndex).left = some (erase invocation.source) ∧
      reduct? (language.rewrites.get ruleIndex) left.spec ambient.length raw = some (erase invocation.target) ∧
      Nonempty (Event (S := signatureOf language)
        (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
        (authoredRootSchema left right).unpositioned invocation.source invocation.target) := by
  obtain ⟨leftCaptured, rightAgreed⟩ := authored_contextual_match_captures left leftFound right invocation matched
  have rightCaptured := matched_captures_right_inputs (alignedRightSchema left right) coverage
    matched invocation.body rightAgreed
  exact authored_contextual_instance_execution left leftFound right rightFound invocation raw
    leftCaptured rightCaptured

theorem authored_contextual_instance_has_match
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient) :
    ∃ raw, raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase invocation.source) := by
  have observed := (elaborateAuthoredSchema?_matching (ambient := ambient) left leftFound).1 [] invocation.body
  have leftSource : left.source = (language.rewrites.get ruleIndex).left := (Option.some.inj left.atSite).symm
  have sourceErasure : erase (scopedInstantiation (ambient := ambient) (locals := [])
      invocation.body left.compiled.term) = erase invocation.source :=
    (congrArg (erase (language := language) (bound := ambient) (type := sort))
      (contextual_instance_source left right invocation)).symm
  obtain ⟨raw, matched⟩ := observed.complete (contextualAgreesInputs_empty _ invocation.body)
  refine ⟨raw, ?_⟩
  simpa only [matchRuleAt, matchRuleWithAt, matchAt, leftSource, sourceErasure, List.length_nil] using matched

/-- Preservation and reflection concern one genuine existing contextual
invocation; unused declared sorts are never filled to manufacture totality. -/
theorem authored_contextual_rule_adequate
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (coverage : rightInputsProducedOnLeft? (alignedRightSchema left right) = true)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    (target : Term (signatureOf language) ambient sort)
    (instanceCanonical : CanonicalObject invocation.source)
    (targetCanonical : CanonicalObject target) :
    (∃ raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase target),
      ContextualCapturesInputs left.compiled.inputOccurrences raw invocation.body ∧
        reduct? (language.rewrites.get ruleIndex) left.spec ambient.length raw = some (erase invocation.target)) ↔
      invocation.source = target := by
  have instanceAdmitted : CanonicalObject (scopedInstantiation invocation.body left.compiled.term) := by
    rw [← contextual_instance_source left right invocation]
    exact instanceCanonical
  have reflected := authored_left_match_canonical_iff left leftFound invocation.body target instanceAdmitted targetCanonical
  constructor
  · rintro ⟨raw, matched, captured, _⟩
    exact (contextual_instance_source left right invocation).trans (reflected.mp ⟨raw, matched, captured⟩)
  · intro same
    subst target
    obtain ⟨raw, matched⟩ := authored_contextual_instance_has_match left leftFound right invocation
    exact ⟨raw, matched, (authored_contextual_match_captures left leftFound right invocation matched).1,
      (authored_contextual_match_execution left leftFound right rightFound coverage invocation matched).2.1⟩

open _root_.CategoryTheory Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath

local instance {S : Signature} : Quiver (Scope S) := bindingFrameQuiver S

local instance : Quiver (Scope (signatureOf language)) := bindingFrameQuiver (signatureOf language)

/-- Actual matching supplies the ambient side captures, while the selected
binding path still requires its independent slot-permission authority. -/
theorem authored_contextual_match_permitted_focus
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (right : AuthoredSchema language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? language ruleIndex .right sort = some right)
    (coverage : rightInputsProducedOnLeft? (alignedRightSchema left right) = true)
    (invocation : Instance (S := signatureOf language)
      (M := metaArities (language := language) (language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    {raw : RawAccumulator}
    (matched : raw ∈ matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length
      (erase invocation.source))
    (permission : SlotPermission (signatureOf language)) {outside : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) (ambient, sort) outside)
    (allowed : FramePermission.PermittedPath (framePermission (signatureOf language) permission) context) :
    ∃ arrow : permittedInterface (signatureOf language) permission (ambient, sort) ⟶
        permittedInterface (signatureOf language) permission outside,
      (permissionInclusion (signatureOf language) permission).map arrow = bindingContextArrow context ∧
      instantiateAt? (language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0
        raw (language.rewrites.get ruleIndex).left = some (erase invocation.source) ∧
      reduct? (language.rewrites.get ruleIndex) left.spec ambient.length raw = some (erase invocation.target) ∧
      permittedTermArrow (permission := permission) invocation.source ≫ arrow =
        permittedTermArrow (permission := permission) (fillContext context invocation.source) ∧
      permittedTermArrow (permission := permission) invocation.target ≫ arrow =
        permittedTermArrow (permission := permission) (fillContext context invocation.target) := by
  obtain ⟨leftCaptured, rightAgreed⟩ := authored_contextual_match_captures left leftFound right invocation matched
  have rightCaptured := matched_captures_right_inputs (alignedRightSchema left right) coverage
    matched invocation.body rightAgreed
  exact authored_permitted_focus_endpoints left leftFound right rightFound invocation raw
    leftCaptured rightCaptured permission context allowed

end AmbientMatching
namespace Controls

def t : TypeExpr := .base "T"
def u : TypeExpr := .base "U"

def exampleLanguage : LanguageDef := LanguageDef.ofCore "ScopedDependencyFragment"
  [TypeDecl.plain "T", TypeDecl.plain "U"] [] [] []

def spec : RuleBindingSpec where
  dependencies := [("P", [t, u])]
  occurrences := [
    ⟨"P", .left, [0, 0], [.bvar 1, .bvar 0]⟩,
    ⟨"P", .right, [0, 0], [.bvar 1, .bvar 0]⟩]

/-- The occurrence compiler can inspect this conditional source row,
without making its freshness premise disappear into a rule firing. -/
def rule : RewriteRule where
  name := "DependentOccurrence"
  typeContext := [("P", t)]
  premises := [.freshness ⟨"fresh", .fvar "P"⟩]
  left := .lambda none (.lambda none (.fvar "P"))
  right := .lambda none (.lambda none (.fvar "P"))
  bindings := some spec

theorem nonempty_dependencies_compile :
    compileMetaArities? exampleLanguage rule spec = some [([t, u], t)] := by decide +kernel

theorem source_premise_retained : rule.premises = [.freshness ⟨"fresh", .fvar "P"⟩] := rfl

/-- Dependency order differs from local-context order. The computed
elaborator must retain the heterogeneous permutation rather than zip sorts. -/
theorem permuted_occurrence_compiles :
    (elaborateOccurrence? exampleLanguage rule spec [u, t] .left [0, 0] "P" t).isSome = true := by
  decide +kernel

def permutedArguments : DependencyArguments (language := exampleLanguage) [t, u] [u, t, t] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def dependencyBody : Term (signatureOf exampleLanguage) ([t, u] ++ [t]) t := .var .zero
def ambientBody : Term (signatureOf exampleLanguage) ([t, u] ++ [t]) t :=
  .var (.succ (.succ .zero))

theorem declared_dependency_is_permuted :
    instantiateValue? (contextualValue dependencyBody) 1 2
      (eraseArguments permutedArguments) = some (.bvar 1) := by
  exact instantiateValue?_typed (locals := [u, t]) (ambient := [t]) dependencyBody permutedArguments

theorem ambient_suffix_is_separate :
    instantiateValue? (contextualValue ambientBody) 1 2
      (eraseArguments permutedArguments) = some (.bvar 2) := by
  exact instantiateValue?_typed (locals := [u, t]) (ambient := [t]) ambientBody permutedArguments

def boundDependencyBody : Term (signatureOf exampleLanguage) ([t, u] ++ [t]) (.arrow u t) :=
  .op (.lambda u t) (.cons (.var (.succ .zero)) .nil)

/-- An additional object binder fixes its own variable and shifts the
supplied dependency image. This is the capture-avoiding typed action. -/
theorem binder_lifts_dependency_image :
    instantiateValue? (contextualValue boundDependencyBody) 1 2
      (eraseArguments permutedArguments) = some (.lambda none (.bvar 2)) := by
  exact instantiateValue?_typed (locals := [u, t]) (ambient := [t])
    boundDependencyBody permutedArguments

theorem capture_is_a_different_result :
    instantiateValue? (contextualValue boundDependencyBody) 1 2
      (eraseArguments permutedArguments) ≠ some (.lambda none (.bvar 1)) := by
  rw [binder_lifts_dependency_image]
  decide +kernel

def emptyArguments : DependencyArguments (language := exampleLanguage) [] [u, t] := .nil
def ambientOpenBody : Term (signatureOf exampleLanguage) ([] ++ [t]) t := .var .zero

/-- Empty dependency arity permits an ambient-open value; it does not mean
that the body's ambient suffix is empty or that the body stays unshifted. -/
theorem zero_dependencies_retain_ambient :
    instantiateValue? (contextualValue ambientOpenBody) 1 1 [] = some (.bvar 1) := by
  exact instantiateValue?_typed (locals := [u]) (ambient := [t]) ambientOpenBody emptyArguments

theorem dependency_order_is_checked :
    elaborateVariableArguments? exampleLanguage [u, t] [.bvar 0, .bvar 1] [t, u] = none := by
  decide +kernel

theorem out_of_scope_dependency_is_refused :
    elaborateVariableArguments? exampleLanguage [t] [.bvar 1] [t] = none := by decide +kernel

theorem arity_mismatch_is_refused :
    elaborateVariableArguments? exampleLanguage [t] [.bvar 0] [t, t] = none := by decide +kernel

theorem nonvariable_spine_is_outside_codec :
    elaborateVariableArguments? exampleLanguage [t] [.apply "K" []] [t] = none := by decide +kernel

def repeatedArguments : DependencyArguments (language := exampleLanguage) [t, t] [t] :=
  .cons (.var .zero) (.cons (.var .zero) .nil)

/-- The output occurrence codec preserves repeated variable images. It
does not impose the input matcher's stronger invertibility condition. -/
theorem repeated_images_are_retained :
    elaborateVariableArguments? exampleLanguage [t] [.bvar 0, .bvar 0] [t, t] =
      some repeatedArguments := by
  exact elaborateVariableArguments?_complete (.cons .zero (.cons .zero .nil))

theorem repeated_images_are_not_an_invertible_match :
    variableSpine? 1 [.bvar 0, .bvar 0] = none := by decide +kernel

theorem unknown_name_is_refused :
    elaborateOccurrence? exampleLanguage rule spec [u, t] .left [0, 0] "Unknown" t = none := by
  decide +kernel

theorem wrong_result_sort_is_refused :
    elaborateOccurrence? exampleLanguage rule spec [u, t] .left [0, 0] "P" u = none := by
  decide +kernel

theorem wrong_occurrence_address_is_refused :
    elaborateOccurrence? exampleLanguage rule spec [u, t] .left [0] "P" t = none := by decide +kernel

def omittedSpines : RuleBindingSpec := { spec with occurrences := [] }
def omittedSpineRule : RewriteRule := { rule with bindings := some omittedSpines }

theorem nonempty_spine_is_not_inferred :
    elaborateOccurrence? exampleLanguage omittedSpineRule omittedSpines [u, t]
      .left [0, 0] "P" t = none := by decide +kernel

def duplicateDependencies : RuleBindingSpec := { spec with dependencies := [("P", [t, u]), ("P", [])] }
def duplicateRule : RewriteRule := { rule with bindings := some duplicateDependencies }

theorem duplicate_declarations_are_refused :
    compileMetaArities? exampleLanguage duplicateRule duplicateDependencies = none := by decide +kernel

theorem detached_binding_spec_is_refused :
    compileMetaArities? exampleLanguage rule omittedSpines = none := by decide +kernel

def authoredLanguage : LanguageDef := { exampleLanguage with rewrites := [rule] }

theorem canonical_rule_position_compiles :
    (elaborateAuthoredOccurrence? authoredLanguage ⟨0, by decide⟩ [u, t]
      .right [0, 0] "P" t).isSome = true := by decide +kernel

def absentBindingLanguage : LanguageDef :=
  { exampleLanguage with rewrites := [{ rule with bindings := none }] }

theorem absent_attached_metadata_is_refused :
    elaborateAuthoredOccurrence? absentBindingLanguage ⟨0, by decide⟩ [u, t]
      .right [0, 0] "P" t = none := by decide +kernel

namespace InputControls

open InputRecovery
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

def localArguments : DependencyArguments (language := exampleLanguage) [t, u] [u, t] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

theorem local_arguments_are_checked :
    variableSpine? 2 (eraseArguments localArguments) = some [1, 0] := by decide +kernel

theorem permuted_source_input_compiles :
    (elaborateInputOccurrence? exampleLanguage rule spec [u, t] .left [0, 0] "P" t).isSome = true := by
  decide +kernel

def permutedInput : CompiledInputOccurrence exampleLanguage rule spec [u, t] .left [0, 0] "P" t :=
  (elaborateInputOccurrence? exampleLanguage rule spec [u, t] .left [0, 0] "P" t).get
    permuted_source_input_compiles

/-- This observation is obtained through the receipt produced by the
computed source entry point, not through a supplied raw capture result. -/
theorem computed_input_captures_dependency :
    capture? rule spec 1 2 .left [0, 0] [] "P" (.bvar 1) =
      some [("P", contextualValue dependencyBody)] := by
  exact permutedInput.capture_fresh [] dependencyBody rfl

theorem computed_input_captures_ambient :
    capture? rule spec 1 2 .left [0, 0] [] "P" (.bvar 2) =
      some [("P", contextualValue ambientBody)] := by
  exact permutedInput.capture_fresh [] ambientBody rfl

theorem actual_leaf_match_retains_capture :
    matchAt rule spec 1 .left [0, 0] 2 [] (.fvar "P") (.bvar 1) =
      [[("P", contextualValue dependencyBody)]] := by
  exact permutedInput.match_leaf_typed_instance [] dependencyBody

theorem typed_bound_body_is_recovered :
    recoverValue? [t, u] 1 2 [.bvar 1, .bvar 0] (.lambda none (.bvar 2)) =
      some (contextualValue boundDependencyBody) := by
  exact recoverValue?_typed_instance localArguments (.cons (.succ .zero) (.cons .zero .nil))
    [1, 0] local_arguments_are_checked boundDependencyBody

theorem source_output_codec_allows_extra_local_context :
    (elaborateOccurrence? exampleLanguage rule spec [u, t, t] .left [0, 0] "P" t).isSome = true := by
  decide +kernel

theorem source_input_depth_mismatch_is_refused :
    elaborateInputOccurrence? exampleLanguage rule spec [u, t, t]
      .left [0, 0] "P" t = none := by decide +kernel

theorem canonical_source_input_compiles :
    (elaborateAuthoredInputOccurrence? authoredLanguage ⟨0, by decide⟩ [u, t]
      .left [0, 0] "P" t).isSome = true := by decide +kernel

theorem canonical_input_missing_metadata_is_refused :
    elaborateAuthoredInputOccurrence? absentBindingLanguage ⟨0, by decide⟩ [u, t]
      .left [0, 0] "P" t = none := by decide +kernel

def partialSpec : RuleBindingSpec where
  dependencies := [("P", [t])]
  occurrences := [⟨"P", .left, [0, 0], [.bvar 1]⟩]

def partialRule : RewriteRule := { rule with
  bindings := some partialSpec
  right := .fvar "P" }

theorem partial_spine_source_compiles :
    (elaborateInputOccurrence? exampleLanguage partialRule partialSpec [t, t]
      .left [0, 0] "P" t).isSome = true := by decide +kernel

theorem omitted_local_is_refused :
    capture? partialRule partialSpec 1 2 .left [0, 0] [] "P" (.bvar 0) = none := by
  decide +kernel

theorem omitted_local_under_binder_is_refused :
    recoverValue? [t] 1 2 [.bvar 1] (.lambda none (.bvar 1)) = none := by decide +kernel

theorem selected_local_is_recovered :
    capture? partialRule partialSpec 1 2 .left [0, 0] [] "P" (.bvar 1) =
      some [("P", ⟨[t], 1, .bvar 0⟩)] := by decide +kernel

theorem partial_spine_preserves_ambient :
    capture? partialRule partialSpec 1 2 .left [0, 0] [] "P" (.bvar 2) =
      some [("P", ⟨[t], 1, .bvar 1⟩)] := by decide +kernel

def emptyLocalArguments : DependencyArguments (language := exampleLanguage) [] [u] := .nil

theorem zero_arity_recovers_open_ambient :
    recoverValue? [] 1 1 [] (.bvar 1) = some (contextualValue ambientOpenBody) := by
  exact recoverValue?_typed_instance emptyLocalArguments .nil [] rfl ambientOpenBody

theorem zero_arity_does_not_capture_local :
    recoverValue? [] 1 1 [] (.bvar 0) = none := by decide +kernel

def duplicatedInputSpec : RuleBindingSpec where
  dependencies := [("P", [t, t])]
  occurrences := [
    ⟨"P", .left, [0], [.bvar 0, .bvar 0]⟩,
    ⟨"P", .right, [0], [.bvar 0, .bvar 0]⟩]

def duplicatedInputRule : RewriteRule := { rule with
  bindings := some duplicatedInputSpec
  left := .lambda none (.fvar "P")
  right := .lambda none (.fvar "P") }

theorem repeated_output_images_still_compile :
    (elaborateOccurrence? exampleLanguage duplicatedInputRule duplicatedInputSpec [t]
      .left [0] "P" t).isSome = true := by decide +kernel

theorem repeated_input_images_are_refused :
    elaborateInputOccurrence? exampleLanguage duplicatedInputRule duplicatedInputSpec [t]
      .left [0] "P" t = none := by decide +kernel

def differingDepthSpec : RuleBindingSpec where
  dependencies := [("P", [t, u])]
  occurrences := [
    ⟨"P", .left, [0, 0], [.bvar 1, .bvar 0]⟩,
    ⟨"P", .right, [0, 0, 0], [.bvar 2, .bvar 0]⟩]

def differingDepthRule : RewriteRule := { rule with
  bindings := some differingDepthSpec
  right := .lambda none (.lambda none (.lambda none (.fvar "P"))) }

def differingDepthLanguage : LanguageDef := { exampleLanguage with rewrites := [differingDepthRule] }

theorem differing_depths_are_admitted :
    (elaborateAuthoredInputOccurrence? differingDepthLanguage ⟨0, by decide⟩ [u, t]
      .left [0, 0] "P" t).isSome = true ∧
    (elaborateAuthoredInputOccurrence? differingDepthLanguage ⟨0, by decide⟩ [u, u, t]
      .right [0, 0, 0] "P" t).isSome = true := by decide +kernel

def firstDepthInput : CompiledInputOccurrence differingDepthLanguage differingDepthRule
    differingDepthSpec [u, t] .left [0, 0] "P" t :=
  (elaborateInputOccurrence? differingDepthLanguage differingDepthRule differingDepthSpec
    [u, t] .left [0, 0] "P" t).get (by decide +kernel)

def secondDepthInput : CompiledInputOccurrence differingDepthLanguage differingDepthRule
    differingDepthSpec [u, u, t] .right [0, 0, 0] "P" t :=
  (elaborateInputOccurrence? differingDepthLanguage differingDepthRule differingDepthSpec
    [u, u, t] .right [0, 0, 0] "P" t).get (by decide +kernel)

def sharedDepthBody : Term (signatureOf differingDepthLanguage) ([t, u] ++ [t]) t := .var .zero

/-- The two input targets are different. Their actual recovery is equal,
so the second site preserves the first capture and its list position. -/
theorem repeated_capture_across_different_depths :
    (capture? differingDepthRule differingDepthSpec 1 2 .left [0, 0] [] "P" (.bvar 1)).bind
      (fun captured => capture? differingDepthRule differingDepthSpec 1 3 .right [0, 0, 0]
        captured "P" (.bvar 2)) = some [("P", contextualValue sharedDepthBody)] := by
  exact firstDepthInput.capture_repeated_different_occurrence secondDepthInput [] sharedDepthBody rfl

theorem repeated_different_body_is_refused :
    capture? rule spec 1 2 .right [0, 0] [("P", contextualValue dependencyBody)] "P" (.bvar 2) =
      none := by decide +kernel

theorem repeated_dependency_context_difference_is_refused :
    capture? rule spec 1 2 .right [0, 0] [("P", ⟨[u, t], 1, .bvar 0⟩)] "P" (.bvar 1) =
      none := by decide +kernel

theorem repeated_ambient_difference_is_refused :
    capture? rule spec 1 2 .right [0, 0] [("P", ⟨[t, u], 0, .bvar 0⟩)] "P" (.bvar 1) =
      none := by decide +kernel

theorem repeated_capture_retains_first_lookup_and_multiplicity :
    capture? rule spec 1 2 .right [0, 0]
      [("P", contextualValue dependencyBody), ("P", contextualValue ambientBody)] "P" (.bvar 1) =
      some [("P", contextualValue dependencyBody), ("P", contextualValue ambientBody)] := by
  decide +kernel

def scopedConstructor : GrammarRule where
  label := "Box"
  category := "T"
  params := [.abstraction "body" (.arrow u t)]
  syntaxPattern := [.terminal "box", .nonTerminal "body"]

def constructorLanguage : LanguageDef := { exampleLanguage with terms := [scopedConstructor] }

def boxOperator : Operator constructorLanguage t :=
  .constructor scopedConstructor (by simp [constructorLanguage])
    (by simp [UsesBareCollection, scopedConstructor])
    (.cons (.abstraction none "body" u t) .nil)

def constructorLocalArguments : DependencyArguments (language := constructorLanguage) [t, u] [u, t] :=
  .cons (.var (.succ .zero)) (.cons (.var .zero) .nil)

def constructorBody : Term (signatureOf constructorLanguage) ([t, u] ++ [t]) t :=
  .op boxOperator (.cons (.var (.succ .zero)) .nil)

/-- This target is independently built from the authored constructor and
its binding arity; it is not defined as the substitution of a desired body. -/
def constructorTarget : Term (signatureOf constructorLanguage) ([u, t] ++ [t]) t :=
  .op boxOperator (.cons (.var (.succ (.succ .zero))) .nil)

theorem declared_constructor_body_recovers :
    recoverValue? [t, u] 1 2 [.bvar 1, .bvar 0] (erase constructorTarget) =
      some (contextualValue constructorBody) := by decide +kernel

/-- Actual recovery of the independent constructor target earns its typed
body preimage through the general reflection theorem. -/
theorem declared_constructor_recovery_has_typed_preimage :
    ∃ body : Term (signatureOf constructorLanguage) ([t, u] ++ [t]) t,
      contextualValue constructorBody = contextualValue body ∧
      bind (occurrenceSubstitution
        (appendAmbientArguments constructorLocalArguments [t])) body = constructorTarget := by
  exact (recoverValue?_intrinsic_iff constructorLocalArguments
    (.cons (.succ .zero) (.cons .zero .nil)) [1, 0] rfl
    constructorTarget (contextualValue constructorBody)).mp declared_constructor_body_recovers

theorem omitted_local_under_declared_constructor_is_refused :
    recoverValue? [t] 1 2 [.bvar 1] (.apply "Box" [.lambda none (.bvar 1)]) = none := by
  decide +kernel

end InputControls

namespace RecursiveControls

open SchemaElaboration

def boxDeclaration : GrammarRule :=
  { label := "ScopedBox", category := "T",
    params := [.abstractionNamed (some "declared-u") "body" (.arrow u t)],
    syntaxPattern := [.terminal "box", .nonTerminal "body"] }

def pairDeclaration : GrammarRule :=
  { label := "ScopedPair", category := "T",
    params := [.simple "first" t, .simple "second" t],
    syntaxPattern := [.terminal "pair", .nonTerminal "first", .nonTerminal "second"] }

def closedDeclaration : GrammarRule :=
  { label := "ScopedZero", category := "T", params := [], syntaxPattern := [.terminal "zero"] }

/-- This source is authored independently of intrinsic schema readback. -/
def recursiveSource : Pattern :=
  .apply "ScopedPair"
    [.apply "ScopedBox" [.lambda none (.fvar "P")],
     .apply "ScopedBox" [.lambda none (.fvar "P")]]

def recursiveSpec : RuleBindingSpec :=
  { dependencies := [("P", [u])],
    occurrences := [⟨"P", .left, [0, 0, 0], [.bvar 0]⟩,
      ⟨"P", .left, [1, 0, 0], [.bvar 0]⟩] }

def recursiveRule : RewriteRule :=
  { name := "constructor-binder-input", typeContext := [("P", t)],
    premises := [.freshness ⟨"unused", .apply "ScopedZero" []⟩],
    left := recursiveSource, right := .apply "ScopedZero" [], bindings := some recursiveSpec }

def recursiveLanguage : LanguageDef :=
  LanguageDef.ofCore "recursive-scoped-codec" ["T", "U"]
    [pairDeclaration, boxDeclaration, closedDeclaration] [] [recursiveRule]

def recursiveIndex : Fin recursiveLanguage.rewrites.length := ⟨0, by decide⟩

theorem independent_constructor_source_accepted :
    (elaborateAuthoredSchema? recursiveLanguage recursiveIndex .left t).isSome = true := by
  decide +kernel

def compiledLeft : AuthoredSchema recursiveLanguage recursiveIndex .left t :=
  Option.get _ independent_constructor_source_accepted

theorem independent_constructor_source_readback :
    readback compiledLeft.compiled.term = recursiveSource := by
  rw [compiledLeft.compiled.source_readback]
  have atSite := compiledLeft.atSite
  change some recursiveSource = some compiledLeft.source at atSite
  exact (Option.some.inj atSite).symm

theorem declaration_binder_name_retained :
    (recursiveLanguage.terms.get ⟨1, by decide⟩).params =
      [.abstractionNamed (some "declared-u") "body" (.arrow u t)] := rfl

theorem computed_local_contexts :
    compiledLeft.compiled.inputOccurrences.map (fun evidence => evidence.2.1) = [[u], [u]] := by
  decide +kernel

theorem actual_occurrence_paths :
    compiledLeft.compiled.inputOccurrences.map (fun evidence => evidence.2.2.1) =
      [[0, 0, 0], [1, 0, 0]] := by
  decide +kernel

theorem physical_constructor_order :
    compiledLeft.compiled.constructorOccurrences.map (fun evidence => (evidence.1, evidence.2.val)) =
      [([], 0), ([0], 1), ([1], 1)] := by
  decide +kernel

theorem original_premise_retained :
    (recursiveLanguage.rewrites.get recursiveIndex).premises = recursiveRule.premises := rfl

theorem closed_constructor_source_accepted :
    (elaborateAuthoredSchema? recursiveLanguage recursiveIndex .right t).isSome = true := by
  decide +kernel

theorem actual_source_typed :
    HasType recursiveLanguage (FreeTypeContext.ofList recursiveRule.typeContext) [] recursiveSource t := by
  rw [← independent_constructor_source_readback, compiledLeft.compiled.source_readback]
  exact compiledLeft.source_typed

theorem recursive_support_earned :
    MatchingSupportedT (S := signatureOf recursiveLanguage)
      (M := metaArities (language := recursiveLanguage) recursiveRule recursiveSpec)
      (Γ := []) [] compiledLeft.compiled.term := by
  exact compiledLeft.compiled.matching_supported

def closedOperator : Operator recursiveLanguage t :=
  .constructor closedDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, closedDeclaration]) .nil

def pairOperator : Operator recursiveLanguage t :=
  .constructor pairDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, pairDeclaration])
    (.cons (.simple "first" t) (.cons (.simple "second" t) .nil))

def boxOperator : Operator recursiveLanguage t :=
  .constructor boxDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, boxDeclaration])
    (.cons (.abstraction (some "declared-u") "body" u t) .nil)

def closedInstance {locals : List TypeExpr} : Term (signatureOf recursiveLanguage) locals t :=
  .op closedOperator .nil

def boxInstance {locals : List TypeExpr}
    (body : Term (signatureOf recursiveLanguage) (u :: locals) t) :
    Term (signatureOf recursiveLanguage) locals t :=
  .op boxOperator (.cons body .nil)

def pairInstance {locals : List TypeExpr}
    (first second : Term (signatureOf recursiveLanguage) locals t) :
    Term (signatureOf recursiveLanguage) locals t :=
  .op pairOperator (.cons first (.cons second .nil))

/-- The target is built independently from the original declaration family. -/
def independentTarget : Term (signatureOf recursiveLanguage) [] t :=
  pairInstance (boxInstance closedInstance) (boxInstance closedInstance)

def closedBodies : (index : Fin (metaArities (language := recursiveLanguage)
    recursiveRule recursiveSpec).length) →
    Term (signatureOf recursiveLanguage)
      ((metaArities (language := recursiveLanguage) recursiveRule recursiveSpec).get index).1
      ((metaArities (language := recursiveLanguage) recursiveRule recursiveSpec).get index).2 :=
  fun index => by
    refine Fin.cases ?_ (fun index => Fin.elim0 index) index
    exact closedInstance

theorem recursive_instantiation_independent_target :
    instantiate closedBodies compiledLeft.compiled.term = independentTarget := rfl

theorem recursive_actual_matching_positive
    [∀ sort, DecidableEq ((signatureOf recursiveLanguage).Op sort)] :
    ∃ final, smatchAtT (S := signatureOf recursiveLanguage)
      (M := metaArities recursiveRule recursiveSpec) [] emptyMAcc
        compiledLeft.compiled.term independentTarget = some final ∧
      MExtends (S := signatureOf recursiveLanguage) (emptySubstitution recursiveLanguage)
        closedBodies final := by
  apply (CompiledSchema.matching_adequate (language := recursiveLanguage)
    compiledLeft.compiled emptyMAcc independentTarget
    closedBodies (MExtends.empty _ _)).mpr
  rfl

def ambientBodies : ContextualAssignment (signatureOf recursiveLanguage)
    (metaArities (language := recursiveLanguage) recursiveRule recursiveSpec) [t] :=
  fun index => by
    refine Fin.cases ?_ (fun index => Fin.elim0 index) index
    exact .var (.succ .zero)

theorem recursive_open_ambient_instantiation :
    erase (ContextualAssignment.instantiate ambientBodies
      (fun _ position => .var position)
      (fun _ (position : Var ([] : List TypeExpr) _) => nomatch position)
      compiledLeft.compiled.term) =
        .apply "ScopedPair" [.apply "ScopedBox" [.lambda none (.bvar 1)],
          .apply "ScopedBox" [.lambda none (.bvar 1)]] := rfl

def leafSchema : Term (SchemaSignature recursiveLanguage recursiveRule recursiveSpec) [u] t :=
  .op (.inr (.mk ⟨0, by decide⟩)) (.cons (.var .zero) .nil)

def constructorSchema : Term (SchemaSignature recursiveLanguage recursiveRule recursiveSpec) [] t :=
  .op (.inl pairOperator)
    (.cons (.op (.inl boxOperator) (.cons leafSchema .nil))
      (.cons (.op (.inl boxOperator) (.cons leafSchema .nil)) .nil))

theorem computed_intrinsic_constructor_shape : compiledLeft.compiled.term = constructorSchema := rfl

def conflictingTarget : Term (signatureOf recursiveLanguage) [] t :=
  pairInstance (boxInstance closedInstance) (boxInstance (boxInstance closedInstance))

private theorem conflicting_bodies :
    (closedInstance : Term (signatureOf recursiveLanguage) [u] t) ≠
      boxInstance closedInstance := by
  intro same
  have source := congrArg erase same
  change Pattern.apply "ScopedZero" [] =
    Pattern.apply "ScopedBox" [.lambda none (.apply "ScopedZero" [])] at source
  exact (by decide : "ScopedZero" ≠ "ScopedBox") (Pattern.apply.inj source).1

theorem recursive_actual_repeated_conflict_refused_at_assignment
    [∀ sort, DecidableEq ((signatureOf recursiveLanguage).Op sort)] :
    ¬ ∃ final, smatchAtT (S := signatureOf recursiveLanguage)
      (M := metaArities recursiveRule recursiveSpec) [] emptyMAcc
        compiledLeft.compiled.term conflictingTarget = some final ∧
      MExtends (S := signatureOf recursiveLanguage) (emptySubstitution recursiveLanguage)
        closedBodies final := by
  intro found
  have same := (CompiledSchema.matching_adequate compiledLeft.compiled emptyMAcc conflictingTarget
    closedBodies (MExtends.empty _ _)).mp found
  have ordinary : bind (liftSub (emptySubstitution recursiveLanguage) [])
      (instantiate closedBodies compiledLeft.compiled.term) = independentTarget := rfl
  have raw := congrArg erase (ordinary.symm.trans same)
  exact (by decide +kernel : erase independentTarget ≠ erase conflictingTarget) raw

def identityInstance {locals : List TypeExpr} (sort : TypeExpr) :
    Term (signatureOf recursiveLanguage) locals (.arrow sort sort) :=
  .op (.lambda sort sort) (.cons (.var .zero) .nil)

def firstSubstitutionBody : Term (signatureOf recursiveLanguage) [u] t :=
  .op (.subst (.arrow u u) t) (.cons closedInstance (.cons (identityInstance u) .nil))

def secondSubstitutionBody : Term (signatureOf recursiveLanguage) [u] t :=
  .op (.subst (.arrow t t) t) (.cons closedInstance (.cons (identityInstance t) .nil))

def substitutionDomain : {locals : List TypeExpr} → {sort : TypeExpr} →
    Term (signatureOf recursiveLanguage) locals sort → Option TypeExpr
  | _, _, .op (.subst domain _) _ => some domain
  | _, _, _ => none

/-- Unrestricted intrinsic erasure is not an equality reflection principle.
The recursive source codec rejects these substitution forms; a later raw
matcher join must earn its target profile or use the existing raw equality. -/
theorem distinct_intrinsic_bodies_have_same_raw_image :
    erase firstSubstitutionBody = erase secondSubstitutionBody := rfl

theorem same_raw_image_does_not_imply_typed_body_agreement :
    firstSubstitutionBody ≠ secondSubstitutionBody := by
  intro same
  have domains := congrArg substitutionDomain same
  change some (TypeExpr.arrow u u) = some (TypeExpr.arrow t t) at domains
  exact (by decide +kernel : some (TypeExpr.arrow u u) ≠ some (TypeExpr.arrow t t)) domains

def multipleDeclaration : GrammarRule :=
  { label := "ScopedMany", category := "T",
    params := [.multiAbstractionNamed ["declared-first", "declared-second"] "body"
      (.arrow (.multiBinder u) u)], syntaxPattern := [.terminal "many", .nonTerminal "body"] }
def multipleSource : Pattern := .apply "ScopedMany" [.multiLambda 2 [] (.bvar 1)]
def multipleRule : RewriteRule :=
  { name := "multiple-scope-input", typeContext := [], premises := [],
    left := multipleSource, right := multipleSource, bindings := some { dependencies := [] } }
def multipleLanguage : LanguageDef :=
  LanguageDef.ofCore "multiple-scoped-codec" [TypeDecl.plain "T", TypeDecl.plain "U"]
    [multipleDeclaration] [] [multipleRule]

theorem declared_multiple_binder_source_accepted :
    (elaborateAuthoredSchema? multipleLanguage ⟨0, by decide⟩ .left t).isSome = true := by
  decide +kernel

theorem multiple_parameter_count_retained :
    (parameterBody? (multipleDeclaration.params.get ⟨0, by decide⟩)
      (.multiLambda 2 [] (.bvar 1))).map (fun body => body.binders) = some [u, u] := by
  decide +kernel

theorem multiple_declaration_names_retained :
    multipleDeclaration.params =
      [.multiAbstractionNamed ["declared-first", "declared-second"] "body"
        (.arrow (.multiBinder u) u)] := rfl

def vectorSource : Pattern :=
  .collection .vec [.apply "ScopedBox" [.lambda none (.fvar "P")],
    .apply "ScopedBox" [.lambda none (.fvar "P")]] none
def vectorRule : RewriteRule :=
  { recursiveRule with
    left := vectorSource
    right := .collection .vec [.apply "ScopedZero" []] none }
def vectorLanguage : LanguageDef := { recursiveLanguage with rewrites := [vectorRule] }

theorem ordered_vector_source_accepted :
    (elaborateAuthoredSchema? vectorLanguage ⟨0, by decide⟩ .left (.collection .vec t)).isSome = true := by
  decide +kernel

def compiledVector : AuthoredSchema vectorLanguage ⟨0, by decide⟩ .left (.collection .vec t) :=
  Option.get _ ordered_vector_source_accepted

theorem ordered_vector_source_readback : readback compiledVector.compiled.term = vectorSource := by
  rw [compiledVector.compiled.source_readback]
  have atSite := compiledVector.atSite
  change some vectorSource = some compiledVector.source at atSite
  exact (Option.some.inj atSite).symm

theorem vector_occurrence_order_and_multiplicity :
    compiledVector.compiled.inputOccurrences.map (fun evidence => evidence.2.2.1) =
      [[0, 0, 0], [1, 0, 0]] := by
  decide +kernel

theorem vector_nested_constructor_order :
    compiledVector.compiled.constructorOccurrences.map (fun evidence => (evidence.1, evidence.2.val)) =
      [([0], 1), ([1], 1)] := by
  decide +kernel

def vectorAmbientBodies : ContextualAssignment (signatureOf vectorLanguage)
    (metaArities (language := vectorLanguage) vectorRule recursiveSpec) [t] :=
  fun index => by
    refine Fin.cases ?_ (fun index => Fin.elim0 index) index
    exact .var (.succ .zero)

theorem vector_open_ambient_instantiation :
    erase (ContextualAssignment.instantiate vectorAmbientBodies
      (fun _ position => .var position)
      (fun _ (position : Var ([] : List TypeExpr) _) => nomatch position)
      compiledVector.compiled.term) =
        .collection .vec [.apply "ScopedBox" [.lambda none (.bvar 1)],
          .apply "ScopedBox" [.lambda none (.bvar 1)]] none := rfl

def bareVectorDeclaration : GrammarRule :=
  { label := "ScopedItems", category := "T", params := [.simple "items" (.collection .vec t)],
    syntaxPattern := [.nonTerminal "items"] }
def bareVectorSource : Pattern :=
  .collection .vec [.apply "ScopedZero" [], .apply "ScopedZero" []] none
def bareVectorRule : RewriteRule :=
  { name := "bare-vector-input", typeContext := [], premises := [], left := bareVectorSource,
    right := bareVectorSource, bindings := some { dependencies := [] } }
def bareVectorLanguage : LanguageDef :=
  LanguageDef.ofCore "bare-vector-scoped-codec" [TypeDecl.plain "T", TypeDecl.plain "U"]
    [bareVectorDeclaration, closedDeclaration] [] [bareVectorRule]

theorem declared_bare_vector_source_accepted :
    (elaborateAuthoredSchema? bareVectorLanguage ⟨0, by decide⟩ .left t).isSome = true := by
  decide +kernel

def compiledBareVector : AuthoredSchema bareVectorLanguage ⟨0, by decide⟩ .left t :=
  Option.get _ declared_bare_vector_source_accepted

theorem bare_vector_physical_declaration_retained :
    compiledBareVector.compiled.constructorOccurrences.map (fun evidence => (evidence.1, evidence.2.val)) =
      [([], 0), ([0], 1), ([1], 1)] := by
  decide +kernel

theorem bare_vector_original_shape_retained :
    readback compiledBareVector.compiled.term = bareVectorSource := by
  rw [compiledBareVector.compiled.source_readback]
  have atSite := compiledBareVector.atSite
  change some bareVectorSource = some compiledBareVector.source at atSite
  exact (Option.some.inj atSite).symm

def ambiguousBareVectorLanguage : LanguageDef :=
  { bareVectorLanguage with terms := [bareVectorDeclaration, closedDeclaration,
      { bareVectorDeclaration with label := "OtherScopedItems" }] }

theorem ambiguous_bare_vector_refused :
    (elaborateAuthoredSchema? ambiguousBareVectorLanguage ⟨0, by decide⟩ .left t).isSome = false := by
  decide +kernel

theorem label_form_of_bare_vector_refused :
    (compileSchemaWithFuel? bareVectorLanguage bareVectorRule { dependencies := [] } .left 4
      [] [] (.apply "ScopedItems" [bareVectorSource]) t).isSome = false := by
  decide +kernel

theorem wrong_direct_vector_element_sort_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      bareVectorSource (.collection .vec u)).isSome = false := by
  decide +kernel

theorem empty_direct_vector_accepted :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 1 [] []
      (.collection .vec [] none) (.collection .vec t)).isSome = true := by
  decide +kernel

def wrongDependencySortDeclaration : GrammarRule :=
  { boxDeclaration with params := [.abstractionNamed (some "declared-t") "body" (.arrow t t)] }
def wrongDependencySortLanguage : LanguageDef :=
  { recursiveLanguage with terms := [pairDeclaration, wrongDependencySortDeclaration, closedDeclaration] }

theorem ordinary_typing_does_not_check_dependency_image :
    checkHasType wrongDependencySortLanguage (FreeTypeContext.ofList recursiveRule.typeContext)
      [] recursiveSource t = true := by
  decide +kernel

theorem wrong_dependency_sort_refused :
    (elaborateAuthoredSchema? wrongDependencySortLanguage ⟨0, by decide⟩ .left t).isSome = false := by
  decide +kernel

theorem wrong_root_sort_refused :
    (elaborateAuthoredSchema? recursiveLanguage recursiveIndex .left u).isSome = false := by
  decide +kernel

theorem wrong_occurrence_depth_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 4
      [u, u] [0, 0, 0] (.fvar "P") t).isSome = false := by
  decide +kernel

def missingDependencySpec : RuleBindingSpec := { recursiveSpec with dependencies := [] }
def missingDependencyRule : RewriteRule :=
  { recursiveRule with bindings := some missingDependencySpec }
def missingDependencyLanguage : LanguageDef :=
  { recursiveLanguage with rewrites := [missingDependencyRule] }

theorem missing_dependency_refused :
    (elaborateAuthoredSchema? missingDependencyLanguage ⟨0, by decide⟩ .left t).isSome = false := by
  decide +kernel

def namedWrapperRule : RewriteRule :=
  { recursiveRule with
    left := .apply "ScopedPair"
      [.apply "ScopedBox" [.lambda (some "display-u") (.fvar "P")],
       .apply "ScopedBox" [.lambda none (.fvar "P")]] }
def namedWrapperLanguage : LanguageDef :=
  { recursiveLanguage with rewrites := [namedWrapperRule] }

theorem named_source_wrapper_refused :
    (elaborateAuthoredSchema? namedWrapperLanguage ⟨0, by decide⟩ .left t).isSome = false := by
  decide +kernel

def duplicateConstructorLanguage : LanguageDef :=
  { recursiveLanguage with terms :=
      [pairDeclaration, boxDeclaration, closedDeclaration, boxDeclaration] }

theorem duplicate_constructor_label_refused :
    (elaborateAuthoredSchema? duplicateConstructorLanguage ⟨0, by decide⟩ .left t).isSome = false := by
  decide +kernel

theorem missing_constructor_label_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.apply "Missing" []) t).isSome = false := by
  decide +kernel

theorem wrong_constructor_arity_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.apply "ScopedPair" [.apply "ScopedZero" []]) t).isSome = false := by
  decide +kernel

theorem wrong_constructor_body_sort_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [u] []
      (.apply "ScopedPair" [.bvar 0, .bvar 0]) t).isSome = false := by
  decide +kernel

theorem missing_parameter_wrapper_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.apply "ScopedBox" [.apply "ScopedZero" []]) t).isSome = false := by
  decide +kernel

theorem structural_lambda_accepted :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.lambda none (.bvar 0)) (.arrow u u)).isSome = true := by
  decide +kernel

theorem structural_multi_binder_accepted :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.multiLambda 2 [] (.bvar 1)) (.arrow (.multiBinder u) u)).isSome = true := by
  decide +kernel

theorem wrong_multi_binder_depth_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.multiLambda 1 [] (.bvar 1)) (.arrow (.multiBinder u) u)).isSome = false := by
  decide +kernel

theorem named_multi_wrapper_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.multiLambda 2 ["first", "second"] (.bvar 1)) (.arrow (.multiBinder u) u)).isSome = false := by
  decide +kernel

theorem explicit_substitution_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 4 [] []
      (.subst (.bvar 0) (.apply "ScopedZero" [])) t).isSome = false := by
  decide +kernel

theorem unordered_collection_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.collection .hashBag [.apply "ScopedZero" []] none) (.collection .hashBag t)).isSome = false := by
  decide +kernel

theorem collection_rest_refused :
    (compileSchemaWithFuel? recursiveLanguage recursiveRule recursiveSpec .left 3 [] []
      (.collection .vec [] (some "rest")) (.collection .vec t)).isSome = false := by
  decide +kernel

theorem premise_entry_not_admitted :
    (elaborateAuthoredSchema? recursiveLanguage recursiveIndex (.premise 0 0 0) t).isSome = false := by
  decide +kernel

end RecursiveControls

namespace TargetControls

open SchemaElaboration TargetReification RecursiveControls
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

def independentRawTarget : Pattern :=
  .apply "ScopedPair"
    [.apply "ScopedBox" [.lambda none (.apply "ScopedZero" [])],
     .apply "ScopedBox" [.lambda none (.apply "ScopedZero" [])]]

theorem constructor_target_admitted :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [] independentRawTarget t).isSome =
      true := by decide +kernel

def constructorTarget : ReifiedTarget recursiveLanguage recursiveRule recursiveSpec []
    independentRawTarget t := Option.get _ constructor_target_admitted

theorem constructor_target_exact_raw : erase constructorTarget.term = independentRawTarget :=
  constructorTarget.readback

theorem constructor_target_independent_intrinsic : constructorTarget.term = independentTarget := by
  apply TargetReification.objectProjection_injective (M := metaArities recursiveRule recursiveSpec)
  exact constructorTarget.projection.embedding.trans (by cbv)

theorem target_typing_is_original :
    HasType recursiveLanguage FreeTypeContext.empty [] independentRawTarget t :=
  constructorTarget.source_typed

theorem target_context_position_admitted :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [t, u] (.bvar 1) u).isSome = true := by
  decide +kernel

theorem target_context_sort_refused :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [t, u] (.bvar 1) t).isSome = false := by
  decide +kernel

theorem target_unknown_context_position_refused :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [t] (.bvar 1) t).isSome = false := by
  decide +kernel

theorem source_schema_name_is_not_an_object_constant :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [] (.fvar "P") t).isSome = false := by
  decide +kernel

theorem target_single_binder_admitted :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec []
      (.lambda none (.bvar 0)) (.arrow u u)).isSome = true := by decide +kernel

theorem target_multiple_binder_admitted :
    (reifyTarget? multipleLanguage multipleRule { dependencies := [] } [] multipleSource t).isSome =
      true := by decide +kernel

theorem target_ordered_vector_admitted :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec []
      (.collection .vec [independentRawTarget, .apply "ScopedZero" []] none)
      (.collection .vec t)).isSome = true := by decide +kernel

theorem target_bare_vector_admitted :
    (reifyTarget? bareVectorLanguage bareVectorRule { dependencies := [] } [] bareVectorSource t).isSome =
      true := by decide +kernel

theorem target_ambiguous_bare_vector_refused :
    (reifyTarget? ambiguousBareVectorLanguage bareVectorRule { dependencies := [] } [] bareVectorSource t).isSome =
      false := by decide +kernel

theorem target_erasure_collision_not_admitted :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [u]
      (erase firstSubstitutionBody) t).isSome = false ∧
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [u]
      (erase secondSubstitutionBody) t).isSome = false := by decide +kernel

theorem independent_constructor_profile : CanonicalObject independentTarget := by
  decide +kernel

theorem independent_constructor_roundtrip :
    reifiedObject? recursiveLanguage recursiveRule recursiveSpec [] (erase independentTarget) t =
      some independentTarget :=
  reifiedObject?_canonical recursiveRule recursiveSpec independentTarget independent_constructor_profile

theorem admitted_target_is_canonical : CanonicalObject constructorTarget.object :=
  constructorTarget.object_canonical

theorem admitted_target_exact_sorted_context :
    erase constructorTarget.object = independentRawTarget := constructorTarget.object_readback

theorem actual_target_constructor_positions :
    constructorTarget.compiled.constructorOccurrences.map (fun row => (row.1, row.2.val)) =
      [([], 0), ([0], 1), ([0, 0, 0], 2), ([1], 1), ([1, 0, 0], 2)] := by
  decide +kernel

theorem actual_object_has_no_input_capture : constructorTarget.compiled.inputOccurrences = [] := by
  decide +kernel

def independentMultipleTarget : Term (signatureOf multipleLanguage) [] t :=
  .op (.constructor multipleDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, multipleDeclaration])
    (.cons (.multiAbstraction ["declared-first", "declared-second"] "body" u u 2) .nil))
      (.cons (.var (.succ .zero)) .nil)

theorem independent_multiple_profile : CanonicalObject independentMultipleTarget := by
  decide +kernel

theorem independent_multiple_exact_source : erase independentMultipleTarget = multipleSource := rfl

theorem independent_multiple_roundtrip :
    reifiedObject? multipleLanguage multipleRule { dependencies := [] } [] multipleSource t =
      some independentMultipleTarget := by
  rw [← independent_multiple_exact_source]
  exact reifiedObject?_canonical multipleRule _ independentMultipleTarget independent_multiple_profile

def independentVectorTarget : Term (signatureOf recursiveLanguage) [] (.collection .vec t) :=
  .op (.collection .vec t 2) (.cons independentTarget (.cons closedInstance .nil))

theorem independent_vector_profile : CanonicalObject independentVectorTarget := by
  decide +kernel

theorem independent_vector_roundtrip :
    reifiedObject? recursiveLanguage recursiveRule recursiveSpec [] (erase independentVectorTarget)
        (.collection .vec t) = some independentVectorTarget :=
  reifiedObject?_canonical recursiveRule recursiveSpec independentVectorTarget independent_vector_profile

def bareClosedInstance {bound : List TypeExpr} : Term (signatureOf bareVectorLanguage) bound t :=
  .op (.constructor closedDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, closedDeclaration]) .nil) .nil

def bareVectorOperator : Operator bareVectorLanguage t :=
  .collectionConstructor bareVectorDeclaration (by decide +kernel) "items" .vec t rfl 2

def independentBareVectorTarget : Term (signatureOf bareVectorLanguage) [] t :=
  .op bareVectorOperator
    (.cons (bs := []) (Γ := []) (bareClosedInstance (bound := []))
      (.cons (bs := []) (Γ := []) (bareClosedInstance (bound := [])) .nil))

theorem independent_bare_vector_profile : CanonicalObject independentBareVectorTarget := by
  decide +kernel

theorem independent_bare_vector_exact_source : erase independentBareVectorTarget = bareVectorSource := rfl

theorem independent_bare_vector_roundtrip :
    reifiedObject? bareVectorLanguage bareVectorRule { dependencies := [] } [] bareVectorSource t =
      some independentBareVectorTarget := by
  rw [← independent_bare_vector_exact_source]
  exact reifiedObject?_canonical bareVectorRule _ independentBareVectorTarget independent_bare_vector_profile

def independentContextTarget : Term (signatureOf recursiveLanguage) [t, u] u := .var (.succ .zero)

theorem independent_context_profile : CanonicalObject independentContextTarget := by
  decide +kernel

theorem independent_context_roundtrip :
    reifiedObject? recursiveLanguage recursiveRule recursiveSpec [t, u] (.bvar 1) u =
      some independentContextTarget :=
  reifiedObject?_canonical recursiveRule recursiveSpec independentContextTarget independent_context_profile

def independentZeroCountTarget : Term (signatureOf recursiveLanguage) [] (.arrow (.multiBinder u) t) :=
  .op (.multiLambda u t 0) (.cons closedInstance .nil)

theorem zero_count_multiple_profile : CanonicalObject independentZeroCountTarget := by
  decide +kernel

theorem zero_count_multiple_roundtrip :
    reifiedObject? recursiveLanguage recursiveRule recursiveSpec [] (erase independentZeroCountTarget)
        (.arrow (.multiBinder u) t) = some independentZeroCountTarget :=
  reifiedObject?_canonical recursiveRule recursiveSpec independentZeroCountTarget zero_count_multiple_profile

theorem unordered_object_profile_refused :
    canonicalObject? (Term.op (S := signatureOf recursiveLanguage)
      (.collection .hashBag t 0) (Args.nil (Γ := []))) = false := by decide +kernel

theorem both_collision_bodies_outside_profile :
    canonicalObject? firstSubstitutionBody = false ∧
      canonicalObject? secondSubstitutionBody = false := by decide +kernel

theorem target_multiple_wrong_depth_refused :
    (reifyTarget? multipleLanguage multipleRule { dependencies := [] } []
      (.apply "ScopedMany" [.multiLambda 2 [] (.bvar 2)]) t).isSome = false := by
  decide +kernel

theorem target_missing_declaration_refused :
    (reifyTarget? recursiveLanguage recursiveRule recursiveSpec [] (.apply "Absent" []) t).isSome = false := by
  decide +kernel

theorem independent_repeat_agreement :
    literalBodyComparison "P" (erase (closedInstance : Term (signatureOf recursiveLanguage) [u] t))
      (erase (closedInstance : Term (signatureOf recursiveLanguage) [u] t)) = true := by
  decide +kernel

theorem independent_repeat_conflict :
    literalBodyComparison "P" (erase (closedInstance : Term (signatureOf recursiveLanguage) [u] t))
      (erase (boxInstance closedInstance : Term (signatureOf recursiveLanguage) [u] t)) = false := by
  decide +kernel

theorem ordinary_body_is_canonical :
    CanonicalObject (closedInstance : Term (signatureOf recursiveLanguage) [u] t) ∧
      CanonicalObject (boxInstance closedInstance : Term (signatureOf recursiveLanguage) [u] t) := by
  decide +kernel

theorem independent_repeat_comparison_reflects_typed_agreement :
    literalBodyComparison "P" (erase (closedInstance : Term (signatureOf recursiveLanguage) [u] t))
      (erase (boxInstance closedInstance : Term (signatureOf recursiveLanguage) [u] t)) = true ↔
        (closedInstance : Term (signatureOf recursiveLanguage) [u] t) = boxInstance closedInstance :=
  CanonicalObject.literal_comparison_iff recursiveRule recursiveSpec "P"
    ordinary_body_is_canonical.1 ordinary_body_is_canonical.2

end TargetControls

namespace RawMatchingControls

open SchemaElaboration TargetReification RawMatching RecursiveControls TargetControls
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- The original raw matcher retains one capture after repeated agreement. -/
theorem recursive_raw_agreement :
    matchRuleAt recursiveRule recursiveSpec 0 independentRawTarget =
      [[("P", bodyValue (closedInstance : Term (signatureOf recursiveLanguage) [u] t))]] := by
  decide +kernel

theorem recursive_raw_conflict :
    matchRuleAt recursiveRule recursiveSpec 0 (erase conflictingTarget) = [] := by
  decide +kernel

theorem conflicting_target_canonical : CanonicalObject conflictingTarget := by
  decide +kernel

theorem recursive_whole_correspondence
    [∀ sort, DecidableEq ((signatureOf recursiveLanguage).Op sort)] :
    ResultsCorrespond (matchRuleAt recursiveRule recursiveSpec 0 independentRawTarget)
      (smatchT emptyMAcc compiledLeft.compiled.term independentTarget) := by
  have actual := authored_left_match compiledLeft
    (Option.eq_some_of_isSome independent_constructor_source_accepted) constructorTarget
  change ResultsCorrespond (matchRuleAt recursiveRule recursiveSpec 0 independentRawTarget)
    (smatchT emptyMAcc compiledLeft.compiled.term constructorTarget.term) at actual
  rw [constructor_target_independent_intrinsic] at actual
  exact actual

/-- The full actual typed match records exactly the independent closed body. -/
theorem recursive_typed_agreement
    [∀ sort, DecidableEq ((signatureOf recursiveLanguage).Op sort)] :
    smatchT emptyMAcc compiledLeft.compiled.term independentTarget =
      some (setMeta emptyMAcc ⟨0, by decide⟩
        (closedInstance : Term (signatureOf recursiveLanguage) [u] t)) := by
  apply recursive_whole_correspondence.result_iff _ |>.mpr
  refine ⟨[("P", bodyValue (closedInstance : Term (signatureOf recursiveLanguage) [u] t))], ?_, ?_⟩
  · rw [recursive_raw_agreement]
    exact List.mem_cons_self
  · exact (empty_corresponds (language := recursiveLanguage) (rule := recursiveRule)
      (spec := recursiveSpec)).prepend_setMeta (by decide +kernel) ⟨0, by decide⟩
      (closedInstance : Term (signatureOf recursiveLanguage) [u] t) ordinary_body_is_canonical.1

/-- Full raw refusal reflects to the actual typed matcher, without a
caller-selected total assignment masking the incompatible second capture. -/
theorem recursive_typed_conflict
    [∀ sort, DecidableEq ((signatureOf recursiveLanguage).Op sort)] :
    smatchT emptyMAcc compiledLeft.compiled.term conflictingTarget = none := by
  have matched := (elaborateAuthoredSchema?_matches compiledLeft
    (Option.eq_some_of_isSome independent_constructor_source_accepted)).observed
      [] emptyMAcc empty_corresponds conflictingTarget conflicting_target_canonical
  apply matched.empty_iff.mp
  exact recursive_raw_conflict

def compiledMultiple : AuthoredSchema multipleLanguage ⟨0, by decide⟩ .left t :=
  Option.get _ declared_multiple_binder_source_accepted

def differentMultipleTarget : Term (signatureOf multipleLanguage) [] t :=
  .op (.constructor multipleDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, multipleDeclaration])
    (.cons (.multiAbstraction ["declared-first", "declared-second"] "body" u u 1) .nil))
      (.cons (.var .zero) .nil)

theorem different_multiple_canonical : CanonicalObject differentMultipleTarget := by
  decide +kernel

theorem multiple_raw_agreement :
    matchRuleAt multipleRule { dependencies := [] } 0 multipleSource = [[]] := by
  decide +kernel

theorem multiple_raw_count_refusal :
    matchRuleAt multipleRule { dependencies := [] } 0 (erase differentMultipleTarget) = [] := by
  decide +kernel

theorem multiple_typed_count_refusal
    [∀ sort, DecidableEq ((signatureOf multipleLanguage).Op sort)] :
    smatchT emptyMAcc compiledMultiple.compiled.term differentMultipleTarget = none := by
  have matched := (elaborateAuthoredSchema?_matches compiledMultiple
    (Option.eq_some_of_isSome declared_multiple_binder_source_accepted)).observed
      [] emptyMAcc empty_corresponds differentMultipleTarget different_multiple_canonical
  exact matched.empty_iff.mp multiple_raw_count_refusal

def differentBareVectorTarget : Term (signatureOf bareVectorLanguage) [] t :=
  .op (.collectionConstructor bareVectorDeclaration (by decide +kernel)
    "items" .vec t rfl 1) (.cons (bareClosedInstance (bound := [])) .nil)

theorem different_bare_vector_canonical : CanonicalObject differentBareVectorTarget := by
  decide +kernel

theorem bare_vector_raw_agreement :
    matchRuleAt bareVectorRule { dependencies := [] } 0 bareVectorSource = [[]] := by
  decide +kernel

theorem bare_vector_raw_count_refusal :
    matchRuleAt bareVectorRule { dependencies := [] } 0 (erase differentBareVectorTarget) = [] := by
  decide +kernel

theorem bare_vector_typed_count_refusal
    [∀ sort, DecidableEq ((signatureOf bareVectorLanguage).Op sort)] :
    smatchT emptyMAcc compiledBareVector.compiled.term differentBareVectorTarget = none := by
  have matched := (elaborateAuthoredSchema?_matches compiledBareVector
    (Option.eq_some_of_isSome declared_bare_vector_source_accepted)).observed
      [] emptyMAcc empty_corresponds differentBareVectorTarget different_bare_vector_canonical
  exact matched.empty_iff.mp bare_vector_raw_count_refusal

end RawMatchingControls

namespace RawInstantiationControls

open SchemaElaboration TargetReification RawMatching RawInstantiation RecursiveControls
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

def dependencyDeclaration : GrammarRule :=
  { label := "ScopedUse", category := "T", params := [.simple "argument" u],
    syntaxPattern := [.terminal "use"] }

def outputSource : Pattern := .apply "ScopedBox" [.lambda none (.fvar "P")]

def outputSpec : RuleBindingSpec := { recursiveSpec with
  occurrences := recursiveSpec.occurrences ++ [⟨"P", .right, [0, 0], [.bvar 0]⟩] }

def outputRule : RewriteRule := { recursiveRule with
  name := "scoped-output", premises := [], right := outputSource, bindings := some outputSpec }

/-- Both authored occurrences have the same display name. The second
physical occurrence is retained in every compiler and execution receipt. -/
def outputLanguage : LanguageDef :=
  LanguageDef.ofCore "scoped-rule-execution" ["T", "U", "V"]
    [pairDeclaration, boxDeclaration, closedDeclaration, dependencyDeclaration] [] [outputRule, outputRule]

def outputIndex : Fin outputLanguage.rewrites.length := ⟨1, by decide⟩

def sourceTarget : Pattern :=
  .apply "ScopedPair"
    [.apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 0])],
      .apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 0])]]

def sourceResult : Pattern := .apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 0])]

def sourceCapture : ContextualValue := ⟨[u], 0, .apply "ScopedUse" [.bvar 0]⟩

def dependentBody : Term (signatureOf outputLanguage) [u] t :=
  .op (.constructor dependencyDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, dependencyDeclaration, u])
    (.cons (.simple "argument" u) .nil)) (.cons (.var .zero) .nil)

def typedResult : Term (signatureOf outputLanguage) [] t :=
  .op (.constructor boxDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, boxDeclaration])
    (.cons (.abstraction (some "declared-u") "body" u t) .nil)) (.cons dependentBody .nil)

theorem actual_binder_capture :
    matchRuleAt outputRule outputSpec 0 sourceTarget = [[("P", sourceCapture)]] := by
  decide +kernel

theorem actual_binder_rhs_result :
    reduct? outputRule outputSpec 0 [("P", sourceCapture)] = some sourceResult := by
  decide +kernel

theorem second_physical_position_both_sides_admitted :
    (elaborateAuthoredSchema? outputLanguage outputIndex .left t).isSome = true ∧
      (elaborateAuthoredSchema? outputLanguage outputIndex .right t).isSome = true := by
  decide +kernel

def outputLeft : AuthoredSchema outputLanguage outputIndex .left t :=
  Option.get _ second_physical_position_both_sides_admitted.1

def outputRight : AuthoredSchema outputLanguage outputIndex .right t :=
  Option.get _ second_physical_position_both_sides_admitted.2

theorem used_rhs_capture_source_check :
    rightInputsProducedOnLeft? (alignedRightSchema outputLeft outputRight) = true ∧
      (alignedRightSchema outputLeft outputRight).inputOccurrences.length = 1 := by
  unfold alignedRightSchema
  rw [rightInputsProducedOnLeft?_transport (authored_specs_equal outputLeft outputRight).symm
    outputRight.compiled, input_occurrences_length_transport
    (authored_specs_equal outputLeft outputRight).symm outputRight.compiled]
  constructor
  · rw [rightInputsProducedOnLeft?_names]
    have names : outputRight.compiled.inputOccurrences.map inputName = ["P"] := by decide +kernel
    rw [names]
    change ["P"].all (fun name => recursiveSource.freeFvarNames.contains name) = true
    simp [recursiveSource, Pattern.freeFvarNames]
  · decide +kernel

theorem independent_target_admitted :
    (reifyTarget? outputLanguage outputRule outputSpec [] sourceTarget t).isSome = true := by
  decide +kernel

def outputTarget : ReifiedTarget outputLanguage outputRule outputSpec [] sourceTarget t :=
  Option.get _ independent_target_admitted

def outputInvocation : RuleInstance
    (metaArities (language := outputLanguage) outputRule outputSpec)
    (authoredRootSchema outputLeft outputRight) where
  body := fun index => by
    refine Fin.cases ?_ (fun old => Fin.elim0 old) index
    exact dependentBody
  close := emptySubstitution outputLanguage

/-- The whole semantic join uses computed side admission, a nonempty RHS
capture inventory, an independently authored target and an existing instance. -/
theorem actual_same_position_root_step
    [∀ sort, DecidableEq ((signatureOf outputLanguage).Op sort)] :
    ∃ raw ∈ matchRuleAt outputRule outputSpec 0 sourceTarget,
      reduct? outputRule outputSpec 0 raw = some sourceResult ∧
        RootStep (authoredRootSchema outputLeft outputRight) outputTarget.term
          (bind outputInvocation.close
            (instantiate outputInvocation.body (authoredRootSchema outputLeft outputRight).rhs)) := by
  let typed := setMeta (emptyMAcc : TypedAccumulator outputLanguage outputRule outputSpec)
    ⟨0, by decide⟩ dependentBody
  have related : AccCorresponds [("P", sourceCapture)] typed := by
    have actual := (empty_corresponds (language := outputLanguage) (rule := outputRule)
      (spec := outputSpec)).prepend_setMeta (by decide +kernel) ⟨0, by decide⟩
        dependentBody (by decide +kernel)
    change AccCorresponds [(metaName (language := outputLanguage) outputRule outputSpec
      ⟨0, by decide⟩, bodyValue dependentBody)] typed
    exact actual
  have realizes : MExtends (emptySubstitution outputLanguage) outputInvocation.body typed := by
    have action := MExtends.setMeta (MExtends.empty (emptySubstitution outputLanguage) outputInvocation.body)
      (⟨0, by decide⟩ : Fin (metaArities (language := outputLanguage) outputRule outputSpec).length)
    have body : outputInvocation.body (⟨0, by decide⟩ : Fin
        (metaArities (language := outputLanguage) outputRule outputSpec).length) = dependentBody := by
      dsimp only [outputInvocation]
      rfl
    simpa only [body] using action
  have matched : [("P", sourceCapture)] ∈ matchRuleAt outputRule outputSpec 0 sourceTarget := by
    rw [actual_binder_capture]
    exact List.mem_cons_self
  have stepped := (authored_rule_instance_step outputLeft
    (Option.eq_some_of_isSome second_physical_position_both_sides_admitted.1)
    outputRight (Option.eq_some_of_isSome second_physical_position_both_sides_admitted.2)
    used_rhs_capture_source_check.1 outputTarget matched typed related outputInvocation realizes).2
  exact ⟨[("P", sourceCapture)], matched, actual_binder_rhs_result, stepped⟩

theorem independent_typed_rhs_image : erase typedResult = sourceResult := rfl

def missingOutputSpec : RuleBindingSpec := { recursiveSpec with
  dependencies := [("P", [u]), ("Q", [])] }

def missingOutputRule : RewriteRule := { outputRule with
  typeContext := [("P", t), ("Q", t)], right := .fvar "Q", bindings := some missingOutputSpec }

def missingOutputLanguage : LanguageDef := { outputLanguage with rewrites := [missingOutputRule] }

theorem missing_rhs_capture_both_sides_still_admitted :
    (elaborateAuthoredSchema? missingOutputLanguage ⟨0, by decide⟩ .left t).isSome = true ∧
      (elaborateAuthoredSchema? missingOutputLanguage ⟨0, by decide⟩ .right t).isSome = true := by
  decide +kernel

def missingRight : AuthoredSchema missingOutputLanguage ⟨0, by decide⟩ .right t :=
  Option.get _ missing_rhs_capture_both_sides_still_admitted.2

theorem missing_rhs_name_source_check_refuses :
    rightInputsProducedOnLeft? missingRight.compiled = false := by
  rw [rightInputsProducedOnLeft?_names]
  have names : missingRight.compiled.inputOccurrences.map inputName = ["Q"] := by decide +kernel
  rw [names]
  change ["Q"].all (fun name => recursiveSource.freeFvarNames.contains name) = false
  simp [recursiveSource, Pattern.freeFvarNames]

theorem missing_rhs_match_retains_only_lhs_capture :
    matchRuleAt missingOutputRule missingOutputSpec 0 sourceTarget = [[("P", sourceCapture)]] := by
  decide +kernel

theorem missing_rhs_reduct_refused :
    reduct? missingOutputRule missingOutputSpec 0 [("P", sourceCapture)] = none := by
  exact reduct?_missing_capture missingOutputRule missingOutputSpec 0 [("P", sourceCapture)] "Q"
    (by simp [missingOutputRule, Pattern.freeFvarNames]) (by decide +kernel)

def unusedSpec : RuleBindingSpec := { outputSpec with
  dependencies := [("P", [u]), ("Unused", [])] }

def unusedRule : RewriteRule := { outputRule with
  typeContext := [("P", t), ("Unused", .base "V")], bindings := some unusedSpec }

def unusedLanguage : LanguageDef := { outputLanguage with rewrites := [unusedRule] }

theorem unused_declaration_both_sides_admitted :
    (elaborateAuthoredSchema? unusedLanguage ⟨0, by decide⟩ .left t).isSome = true ∧
      (elaborateAuthoredSchema? unusedLanguage ⟨0, by decide⟩ .right t).isSome = true := by
  decide +kernel

def unusedRight : AuthoredSchema unusedLanguage ⟨0, by decide⟩ .right t :=
  Option.get _ unused_declaration_both_sides_admitted.2

theorem unused_declaration_does_not_enter_capture_check :
    rightInputsProducedOnLeft? unusedRight.compiled = true ∧
      unusedRight.compiled.inputOccurrences.map inputName = ["P"] := by
  have names : unusedRight.compiled.inputOccurrences.map inputName = ["P"] := by decide +kernel
  refine ⟨?_, names⟩
  rw [rightInputsProducedOnLeft?_names, names]
  change ["P"].all (fun name => recursiveSource.freeFvarNames.contains name) = true
  simp [recursiveSource, Pattern.freeFvarNames]

/-- The actual execution succeeds with the unused declaration absent.
No total body assignment or witness for its result sort is supplied here. -/
theorem unused_declaration_actual_rhs_succeeds :
    matchRuleAt unusedRule unusedSpec 0 sourceTarget = [[("P", sourceCapture)]] ∧
      lookup [("P", sourceCapture)] "Unused" = none ∧
        reduct? unusedRule unusedSpec 0 [("P", sourceCapture)] = some sourceResult := by
  decide +kernel

end RawInstantiationControls

namespace AmbientControls

open SchemaElaboration TargetReification AmbientCorrespondence InputControls
open RawInstantiationControls
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

def partialInput : CompiledInputOccurrence exampleLanguage partialRule partialSpec
    [t, t] .left [0, 0] "P" t :=
  (elaborateInputOccurrence? exampleLanguage partialRule partialSpec [t, t]
    .left [0, 0] "P" t).get partial_spine_source_compiles

def partialAmbientBody : Term (signatureOf exampleLanguage) ([t] ++ [t]) t :=
  .var (.succ .zero)

def partialAmbientTarget : Term (signatureOf exampleLanguage) ([t, t] ++ [t]) t :=
  .var (.succ (.succ .zero))

def omittedLocalTarget : Term (signatureOf exampleLanguage) ([t, t] ++ [t]) t := .var .zero

theorem independently_open_target_admitted :
    (reifyTarget? exampleLanguage partialRule partialSpec [t, t, t] (.bvar 2) t).isSome = true := by
  exact (reifyTarget?_canonical_iff _ _ _ _ _ _).mpr
    ⟨partialAmbientTarget,
      by simp [CanonicalObject, canonicalObject?, partialAmbientTarget], rfl⟩

theorem actual_ambient_capture_and_body_reification :
    capture? partialRule partialSpec 1 2 .left [0, 0] [] "P" (.bvar 2) =
        some [("P", ⟨[t], 1, .bvar 1⟩)] ∧
      reifiedObject? exampleLanguage partialRule partialSpec ([t] ++ [t]) (.bvar 1) t =
        some partialAmbientBody := by
  refine ⟨partial_spine_preserves_ambient, ?_⟩
  exact reifiedObject?_canonical partialRule partialSpec partialAmbientBody
    (by simp [CanonicalObject, canonicalObject?, partialAmbientBody])

theorem actual_ambient_action_and_result_reification :
    (instantiateValue? (contextualValue (dependencies := [t]) (ambient := [t])
      partialAmbientBody) 1 2 [.bvar 1]).bind
      (fun result => reifiedObject? exampleLanguage partialRule partialSpec [t, t, t] result t) =
        some partialAmbientTarget := by
  have canonical : CanonicalObject partialAmbientBody := by
    simp [CanonicalObject, canonicalObject?, partialAmbientBody]
  exact input_instantiation_reifies (ambient := [t]) partialInput partialAmbientBody canonical

theorem omitted_local_has_no_canonical_body :
    ¬ ∃ body : Term (signatureOf exampleLanguage) ([t] ++ [t]) t,
      CanonicalObject body ∧ bind (occurrenceSubstitution
        (InputRecovery.appendAmbientArguments partialInput.compiled.arguments [t])) body = omittedLocalTarget := by
  apply (input_recovery_refusal_iff partialInput omittedLocalTarget
    (by simp [CanonicalObject, canonicalObject?, omittedLocalTarget])).mp
  decide +kernel

theorem outside_ambient_context_is_refused :
    recoverValue? [t] 1 2 [.bvar 1] (.bvar 3) = none ∧
      reifiedObject? exampleLanguage partialRule partialSpec [t, t, t] (.bvar 3) t = none := by
  decide +kernel

def openSourceTarget : Pattern :=
  .apply "ScopedPair"
    [.apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 1])],
      .apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 1])]]

def openSourceResult : Pattern :=
  .apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 1])]

def openCapture : ContextualValue := ⟨[u], 1, .apply "ScopedUse" [.bvar 1]⟩

theorem whole_actual_match_keeps_ambient_dependency :
    matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      reduct? outputRule outputSpec 1 [("P", openCapture)] = some openSourceResult := by
  decide +kernel

def boxBodyContext : OneHoleContext := .apply "ScopedBox" [] (.lambda none .hole) []

theorem nested_structural_match_does_not_supply_rewrite_authority :
    matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      ¬ RuleAuthorizesContext outputRule boxBodyContext := by
  refine ⟨whole_actual_match_keeps_ambient_dependency.1, ?_⟩
  rintro ⟨source, target, member, _, _⟩
  change Premise.congruence (.fvar source) (.fvar target) ∈ [] at member
  exact List.not_mem_nil member

open Mettapedia.OSLF.Binding.ContextualRootEvents
open RawInstantiation RecursiveControls

def openDependentBody : Term (signatureOf outputLanguage) ([u] ++ [u]) t :=
  .op (.constructor dependencyDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, dependencyDeclaration, u])
    (.cons (.simple "argument" u) .nil)) (.cons (.var (.succ .zero)) .nil)

def openBodies : AmbientBodies outputLanguage outputRule outputSpec [u] :=
  fun index => by
    refine Fin.cases ?_ (fun old => Fin.elim0 old) index
    exact openDependentBody

def openInvocation : Instance (S := signatureOf outputLanguage)
    (M := metaArities (language := outputLanguage) outputRule outputSpec)
    (authoredRootSchema outputLeft outputRight).unpositioned [u] where
  body := openBodies
  close := emptyAmbientSub [u]

theorem open_capture_body_reifies_at_its_actual_sorts :
    reifiedObject? outputLanguage outputRule outputSpec ([u] ++ [u]) openCapture.body t =
      some openDependentBody := by
  rw [show openCapture.body = erase openDependentBody by rfl]
  exact reifiedObject?_canonical outputRule outputSpec openDependentBody (by decide +kernel)

theorem wrong_ambient_size_refuses_original_value_action :
    instantiateValue? openCapture 2 1 [.bvar 0] = none := by decide +kernel

theorem same_size_wrong_ambient_sort_refuses_body_reification :
    reifiedObject? outputLanguage outputRule outputSpec ([u] ++ [t]) openCapture.body t = none := by
  decide +kernel

private theorem open_inputs_captured
    (inputs : List (InputEvidence outputLanguage outputRule outputSpec)) :
    ContextualCapturesInputs inputs [("P", openCapture)] openInvocation.body := by
  intro input _
  rw [← input_named_index input]
  have index : ∀ selected : Fin (metaArities (language := outputLanguage) outputRule outputSpec).length,
      lookup [("P", openCapture)] (metaName outputRule outputSpec selected) =
        some (contextualValue (openInvocation.body selected)) := by
    intro selected
    have unique : selected = ⟨0, by decide⟩ := Fin.eq_zero selected
    subst selected
    decide +kernel
  exact index (inputIndex input)

/-- The compiler law and existing contextual event are exercised by an
actual open assignment, selected at the second physical authored position. -/
theorem actual_open_contextual_event :
    instantiateAt? outputRule outputSpec 1 .left [] 0 [("P", openCapture)] outputRule.left =
        some (erase openInvocation.source) ∧
      reduct? outputRule outputSpec 1 [("P", openCapture)] = some (erase openInvocation.target) ∧
      Nonempty (Event (S := signatureOf outputLanguage)
        (M := metaArities (language := outputLanguage) outputRule outputSpec)
        (authoredRootSchema outputLeft outputRight).unpositioned
        openInvocation.source openInvocation.target) :=
  authored_contextual_instance_execution outputLeft
    (Option.eq_some_of_isSome second_physical_position_both_sides_admitted.1) outputRight
    (Option.eq_some_of_isSome second_physical_position_both_sides_admitted.2) openInvocation
    [("P", openCapture)] (open_inputs_captured _) (open_inputs_captured _)

theorem open_event_has_independent_endpoints :
    erase openInvocation.source = openSourceTarget ∧
      erase openInvocation.target = openSourceResult := by
  have leftResult : instantiateAt? outputRule outputSpec 1 .left [] 0
      [("P", openCapture)] outputRule.left = some openSourceTarget := by decide +kernel
  exact ⟨Option.some.inj (actual_open_contextual_event.1.symm.trans leftResult),
    Option.some.inj (actual_open_contextual_event.2.1.symm.trans
      whole_actual_match_keeps_ambient_dependency.2)⟩

open _root_.CategoryTheory Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath

local instance : Quiver (Scope (signatureOf outputLanguage)) :=
  bindingFrameQuiver (signatureOf outputLanguage)

def outerBoxOperator : (signatureOf outputLanguage).Op t :=
  .constructor boxDeclaration (by decide +kernel)
    (by simp [UsesBareCollection, boxDeclaration])
    (.cons (.abstraction (some "declared-u") "body" u t) .nil)

def openFocusFrame : BindingFrame (signatureOf outputLanguage) ([u], t) ([], t) :=
  .slot (S := signatureOf outputLanguage) [] t outerBoxOperator ⟨0, by decide⟩
    (fun other different => False.elim (different (Fin.eq_zero other)))

def openFocusContext : BindingContext (signatureOf outputLanguage) ([u], t) ([], t) :=
  .cons .nil openFocusFrame

def selectedBoxPermission : SlotPermission (signatureOf outputLanguage) :=
  fun _ _ _ position => position.val = 0

def blockedBoxPermission : SlotPermission (signatureOf outputLanguage) :=
  fun _ _ _ position => position.val = 1

theorem explicit_permission_allows_actual_open_focus :
    FramePermission.PermittedPath (framePermission (signatureOf outputLanguage) selectedBoxPermission)
        openFocusContext ∧
      erase (fillContext openFocusContext openInvocation.source) =
        .apply "ScopedBox" [.lambda none openSourceTarget] ∧
      erase (fillContext openFocusContext openInvocation.target) =
        .apply "ScopedBox" [.lambda none openSourceResult] := by
  refine ⟨.cons (.nil _) rfl, ?_, ?_⟩
  · change Pattern.apply "ScopedBox" [Pattern.lambda none (erase openInvocation.source)] = _
    rw [open_event_has_independent_endpoints.1]
  · change Pattern.apply "ScopedBox" [Pattern.lambda none (erase openInvocation.target)] = _
    rw [open_event_has_independent_endpoints.2]

theorem matching_cannot_supply_blocked_focus_permission :
    matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      ¬ ∃ arrow : permittedInterface (signatureOf outputLanguage) blockedBoxPermission ([u], t) ⟶
          permittedInterface (signatureOf outputLanguage) blockedBoxPermission ([], t),
        (permissionInclusion (signatureOf outputLanguage) blockedBoxPermission).map arrow =
          bindingContextArrow openFocusContext := by
  refine ⟨whole_actual_match_keeps_ambient_dependency.1, ?_⟩
  intro supplied
  have allowed := (permitted_context_arrow_iff blockedBoxPermission openFocusContext).mp supplied
  cases allowed with
  | cons _ last =>
      change (0 : Nat) = 1 at last
      exact Nat.zero_ne_one last

end AmbientControls

namespace AmbientMatchingControls

open SchemaElaboration TargetReification RawMatching RawInstantiation AmbientCorrespondence AmbientMatching
open RawInstantiationControls RecursiveControls AmbientControls InputControls
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding.ContextualRootEvents

private theorem left_found : elaborateAuthoredSchema? outputLanguage outputIndex .left t = some outputLeft :=
  Option.eq_some_of_isSome second_physical_position_both_sides_admitted.1

private theorem right_found : elaborateAuthoredSchema? outputLanguage outputIndex .right t = some outputRight :=
  Option.eq_some_of_isSome second_physical_position_both_sides_admitted.2

private theorem matched_open : [("P", openCapture)] ∈ matchRuleAt outputRule outputSpec 1 (erase openInvocation.source) := by
  rw [open_event_has_independent_endpoints.1, whole_actual_match_keeps_ambient_dependency.1]
  exact List.mem_cons_self

theorem actual_open_matching_earns_used_captures :
    ContextualCapturesInputs outputLeft.compiled.inputOccurrences [("P", openCapture)] openInvocation.body ∧
      ContextualAgreesInputs (alignedRightSchema outputLeft outputRight).inputOccurrences
        [("P", openCapture)] openInvocation.body :=
  authored_contextual_match_captures outputLeft left_found outputRight openInvocation matched_open

theorem actual_same_fin_open_match_executes :
    instantiateAt? outputRule outputSpec 1 .left [] 0 [("P", openCapture)] outputRule.left =
        some (erase openInvocation.source) ∧
      reduct? outputRule outputSpec 1 [("P", openCapture)] = some (erase openInvocation.target) ∧
      Nonempty (Event (S := signatureOf outputLanguage)
        (M := metaArities (language := outputLanguage) outputRule outputSpec)
        (authoredRootSchema outputLeft outputRight).unpositioned openInvocation.source openInvocation.target) :=
  authored_contextual_match_execution outputLeft left_found outputRight right_found
    used_rhs_capture_source_check.1 openInvocation matched_open

theorem independently_open_whole_target_admitted :
    (reifyTarget? outputLanguage outputRule outputSpec [u] openSourceTarget t).isSome = true := by
  decide +kernel

def independentOpenTarget : ReifiedTarget outputLanguage outputRule outputSpec [u] openSourceTarget t :=
  Option.get _ independently_open_whole_target_admitted

theorem actual_open_matching_reflects_independent_target :
    openInvocation.source = independentOpenTarget.object := by
  have reflected := authored_left_match_canonical_iff outputLeft left_found openInvocation.body
    independentOpenTarget.object (by decide +kernel) independentOpenTarget.object_canonical
  have matched : [("P", openCapture)] ∈ matchRuleAt outputRule outputSpec 1 (erase independentOpenTarget.object) := by
    rw [independentOpenTarget.object_readback, whole_actual_match_keeps_ambient_dependency.1]
    exact List.mem_cons_self
  exact (contextual_instance_source outputLeft outputRight openInvocation).trans
    (reflected.mp ⟨[("P", openCapture)], matched, actual_open_matching_earns_used_captures.1⟩)

theorem independently_local_whole_target_admitted :
    (reifyTarget? outputLanguage outputRule outputSpec [u] sourceTarget t).isSome = true := by
  decide +kernel

def independentLocalTarget : ReifiedTarget outputLanguage outputRule outputSpec [u] sourceTarget t :=
  Option.get _ independently_local_whole_target_admitted

theorem different_typed_capture_cannot_realize_open_instance :
    ¬ ∃ raw ∈ matchRuleAt outputRule outputSpec 1 (erase independentLocalTarget.object),
      ContextualCapturesInputs outputLeft.compiled.inputOccurrences raw openInvocation.body := by
  intro realized
  have reflected := authored_left_match_canonical_iff outputLeft left_found openInvocation.body
    independentLocalTarget.object (by decide +kernel) independentLocalTarget.object_canonical
  have same := (contextual_instance_source outputLeft outputRight openInvocation).trans (reflected.mp realized)
  have sameImage := congrArg (erase (language := outputLanguage) (bound := [u]) (type := t)) same
  have different : openSourceTarget ≠ sourceTarget := by decide +kernel
  exact different (open_event_has_independent_endpoints.1.symm.trans
    (sameImage.trans independentLocalTarget.object_readback))

def localCapture : ContextualValue := ⟨[u], 1, .apply "ScopedUse" [.bvar 0]⟩

theorem false_prior_ambient_metadata_refuses :
    matchAt outputRule outputSpec 1 .left [] 0
      [("P", ⟨[u], 0, openCapture.body⟩)] outputRule.left openSourceTarget = [] := by
  decide +kernel

theorem false_prior_dependency_sorts_refuse :
    matchAt outputRule outputSpec 1 .left [] 0
      [("P", ⟨[t], 1, openCapture.body⟩)] outputRule.left openSourceTarget = [] := by
  decide +kernel

theorem false_prior_typed_body_refuses :
    matchAt outputRule outputSpec 1 .left [] 0 [("P", localCapture)] outputRule.left openSourceTarget = [] := by
  decide +kernel

theorem actual_open_repeated_capture_conflict_refuses :
    matchRuleAt outputRule outputSpec 1 (.apply "ScopedPair"
      [.apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 1])],
        .apply "ScopedBox" [.lambda none (.apply "ScopedUse" [.bvar 0])]]) = [] := by
  decide +kernel

theorem local_omission_and_outside_ambient_refuse_actual_match :
    matchAt partialRule partialSpec 1 .left [0, 0] 2 [] (.fvar "P") (.bvar 0) = [] ∧
      matchAt partialRule partialSpec 1 .left [0, 0] 2 [] (.fvar "P") (.bvar 3) = [] := by
  decide +kernel

theorem missing_open_rhs_capture_refuses_with_original_source_check :
    rightInputsProducedOnLeft? missingRight.compiled = false ∧
      matchRuleAt missingOutputRule missingOutputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
        reduct? missingOutputRule missingOutputSpec 1 [("P", openCapture)] = none := by
  refine ⟨missing_rhs_name_source_check_refuses, ?_, ?_⟩
  · decide +kernel
  · exact reduct?_missing_capture missingOutputRule missingOutputSpec 1 [("P", openCapture)] "Q"
      (by simp [missingOutputRule, Pattern.freeFvarNames]) (by decide +kernel)

theorem unused_sort_has_no_required_open_capture :
    rightInputsProducedOnLeft? unusedRight.compiled = true ∧
      matchRuleAt unusedRule unusedSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
        lookup [("P", openCapture)] "Unused" = none ∧
          reduct? unusedRule unusedSpec 1 [("P", openCapture)] = some openSourceResult := by
  refine ⟨unused_declaration_does_not_enter_capture_check.1, ?_⟩
  decide +kernel

open _root_.CategoryTheory Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath

local instance : Quiver (Scope (signatureOf outputLanguage)) := bindingFrameQuiver (signatureOf outputLanguage)

theorem actual_open_matching_lifts_at_explicit_permitted_focus :
    ∃ arrow : permittedInterface (signatureOf outputLanguage) selectedBoxPermission ([u], t) ⟶
        permittedInterface (signatureOf outputLanguage) selectedBoxPermission ([], t),
      (permissionInclusion (signatureOf outputLanguage) selectedBoxPermission).map arrow =
          bindingContextArrow openFocusContext ∧
      instantiateAt? outputRule outputSpec 1 .left [] 0 [("P", openCapture)] outputRule.left =
          some (erase openInvocation.source) ∧
      reduct? outputRule outputSpec 1 [("P", openCapture)] = some (erase openInvocation.target) ∧
      permittedTermArrow (permission := selectedBoxPermission) openInvocation.source ≫ arrow =
          permittedTermArrow (permission := selectedBoxPermission) (fillContext openFocusContext openInvocation.source) ∧
      permittedTermArrow (permission := selectedBoxPermission) openInvocation.target ≫ arrow =
          permittedTermArrow (permission := selectedBoxPermission) (fillContext openFocusContext openInvocation.target) :=
  authored_contextual_match_permitted_focus outputLeft left_found outputRight right_found
    used_rhs_capture_source_check.1 openInvocation matched_open selectedBoxPermission openFocusContext
    explicit_permission_allows_actual_open_focus.1

theorem successful_open_matching_has_no_blocked_context_arrow :
    matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      ¬ ∃ arrow : permittedInterface (signatureOf outputLanguage) blockedBoxPermission ([u], t) ⟶
          permittedInterface (signatureOf outputLanguage) blockedBoxPermission ([], t),
        (permissionInclusion (signatureOf outputLanguage) blockedBoxPermission).map arrow =
          bindingContextArrow openFocusContext := matching_cannot_supply_blocked_focus_permission

end AmbientMatchingControls
end Controls

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
variable {language : LanguageDef}

namespace ScopedPermissions

open Mettapedia.OSLF.MeTTaIL

open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.CategoryTheory.GroundPath
open _root_.CategoryTheory

local instance : Quiver (Scope (signatureOf language)) := bindingFrameQuiver (signatureOf language)

/-- The representation frame belonging to the actual declared parameter. -/
def parameterContext {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) : OneHoleContext :=
  match scope with
  | .simple _ _ => .hole
  | .abstraction _ _ _ _ | .abstractionBase _ _ _ => .lambda none .hole
  | .multiAbstraction _ _ _ _ count | .multiAbstractionBase _ _ _ count =>
      .multiLambda count [] .hole

theorem parameterContext_fill {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (body : Pattern) :
    (parameterContext scope).fill body = scope.wrap body := by
  cases scope <;> rfl

/-- Select the representation frame at the physical ordered parameter index. -/
def parameterContextAt : {parameters : List TermParam} →
    {arity : List (List TypeExpr × TypeExpr)} → ParameterScopes parameters arity →
      Fin arity.length → OneHoleContext
  | _, _, .nil, position => Fin.elim0 position
  | _, _, .cons head tail, position =>
      Fin.cases (parameterContext head) (parameterContextAt tail) position

/-- Split the actual stored siblings without supplying a value for the hole. -/
def splitSiblings : {count : Nat} → (position : Fin count) →
    ((other : Fin count) → other ≠ position → Pattern) → List Pattern × List Pattern
  | 0, position => Fin.elim0 position
  | count + 1, position =>
      Fin.cases
        (fun siblings => ([], List.ofFn fun other => siblings other.succ (by simp)))
        (fun selected siblings =>
          let remaining := splitSiblings selected
            (fun other different => siblings other.succ (by simpa using different))
          (siblings 0 (Fin.succ_ne_zero selected).symm :: remaining.1, remaining.2)) position

theorem splitSiblings_before_length : ∀ {count : Nat} (position : Fin count)
    (siblings : (other : Fin count) → other ≠ position → Pattern),
    (splitSiblings position siblings).1.length = position.val
  | 0, position, _ => Fin.elim0 position
  | count + 1, position, siblings => by
      revert siblings
      refine Fin.cases ?_ (fun selected => ?_) position <;> intro siblings
      · rfl
      · simpa only [splitSiblings, Fin.cases_succ, List.length_cons, Fin.val_succ] using
          congrArg (fun length => length + 1)
            (splitSiblings_before_length selected
              (fun other different => siblings other.succ (by simpa using different)))

theorem splitSiblings_fill : ∀ {count : Nat} (position : Fin count)
    (siblings : (other : Fin count) → other ≠ position → Pattern) (supplied : Pattern),
    List.ofFn (fun other => if same : other = position then supplied else siblings other same) =
      (splitSiblings position siblings).1 ++ supplied :: (splitSiblings position siblings).2
  | 0, position, _, _ => Fin.elim0 position
  | count + 1, position, siblings, supplied => by
      revert siblings
      refine Fin.cases ?_ (fun selected => ?_) position <;> intro siblings
      · simp only [splitSiblings, Fin.cases_zero, List.ofFn_succ, dite_true, List.nil_append]
        congr 1
      · simp only [splitSiblings, Fin.cases_succ, List.ofFn_succ]
        simp only [(Fin.succ_ne_zero selected).symm, dite_false,
          List.cons_append, List.cons.injEq, true_and]
        simpa only [Fin.succ_inj] using splitSiblings_fill selected
          (fun other different => siblings other.succ (by simpa using different)) supplied

theorem eraseArguments_assemble {bound : List TypeExpr} :
    ∀ (arity : List (List TypeExpr × TypeExpr))
      (arguments : (position : Fin arity.length) →
        Term (signatureOf language) ((arity.get position).1 ++ bound) (arity.get position).2),
      eraseArguments (assembleArguments bound arity arguments) =
        List.ofFn (fun position => erase (arguments position))
  | [], _ => rfl
  | _ :: tail, arguments => by
      simp only [assembleArguments, eraseArguments, List.ofFn_succ]
      exact congrArg (List.cons (erase (arguments 0)))
        (eraseArguments_assemble tail (fun position => arguments position.succ))

theorem eraseConstructorArguments_assemble {bound : List TypeExpr} :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : (position : Fin arity.length) →
        Term (signatureOf language) ((arity.get position).1 ++ bound) (arity.get position).2),
      eraseConstructorArguments (language := language) (bound := bound) scopes
        (assembleArguments (S := signatureOf language) bound arity arguments) =
        List.ofFn (fun position => (parameterContextAt scopes position).fill (erase (arguments position)))
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, arguments => by
      simp only [assembleArguments, List.ofFn_succ,
        parameterContextAt, Fin.cases_zero, Fin.cases_succ, parameterContext_fill]
      exact congrArg (List.cons (head.wrap (erase (arguments 0))))
        (eraseConstructorArguments_assemble tail (fun position => arguments position.succ))

/-- Erase an actual intrinsic slot to the existing raw zipper, including
the representation binder compressed into a constructor argument. -/
def frameContext {source target : Scope (signatureOf language)} :
    BindingFrame (signatureOf language) source target → OneHoleContext
  | .slot bound _ operator position siblings =>
      match operator with
      | .constructor rule _ _ scopes =>
          let parts := splitSiblings position (fun other different =>
            (parameterContextAt scopes other).fill (erase (siblings other different)))
          .apply rule.label parts.1 (parameterContextAt scopes position) parts.2
      | .collectionConstructor _ _ _ kind _ _ _ | .collection kind _ _ =>
          let parts := splitSiblings position (fun other different => erase (siblings other different))
          .collection kind parts.1 .hole parts.2 none
      | .lambda _ _ => .lambda none .hole
      | .multiLambda _ _ count => .multiLambda count [] .hole
      | .subst _ _ =>
          if selected : position.val = 0 then
            .substBody .hole (erase (siblings ⟨1, by change 1 < 2; decide⟩ (by
              intro same
              have indices := congrArg Fin.val same
              simp only [selected] at indices
              contradiction)))
          else
            .substReplacement (erase (siblings ⟨0, by change 0 < 2; decide⟩ (by
              intro same
              exact selected (congrArg Fin.val same).symm))) .hole

private theorem erased_selected_family {bound : List TypeExpr}
    (arity : List (List TypeExpr × TypeExpr)) (position : Fin arity.length)
    (siblings : (other : Fin arity.length) → other ≠ position →
      Term (signatureOf language) ((arity.get other).1 ++ bound) (arity.get other).2)
    (supplied : Term (signatureOf language) ((arity.get position).1 ++ bound) (arity.get position).2)
    (wrappers : Fin arity.length → OneHoleContext) :
    List.ofFn (fun other => (wrappers other).fill
        (erase (if same : other = position then same.symm ▸ supplied else siblings other same))) =
      List.ofFn (fun other => if same : other = position then
        (wrappers position).fill (erase supplied) else
        (wrappers other).fill (erase (siblings other same))) := by
  apply congrArg List.ofFn
  funext other
  by_cases same : other = position
  · subst other
    simp only [dite_true]
  · simp only [dif_neg same]

theorem frameContext_fill {source target : Scope (signatureOf language)}
    (frame : BindingFrame (signatureOf language) source target)
    (supplied : Term (signatureOf language) source.1 source.2) :
    (frameContext frame).fill (erase supplied) = erase (frame.fill supplied) := by
  cases frame with
  | slot bound sort operator position siblings =>
      cases operator with
      | constructor rule member ordinary scopes =>
          simp only [frameContext, OneHoleContext.fill, BindingFrame.fill, erase]
          rw [eraseConstructorArguments_assemble,
            erased_selected_family _ position siblings supplied (parameterContextAt scopes),
            splitSiblings_fill]
      | collectionConstructor rule member name kind element shape count =>
          simp only [frameContext, OneHoleContext.fill, BindingFrame.fill, erase]
          rw [eraseArguments_assemble]
          have read := erased_selected_family _ position siblings supplied (fun _ => .hole)
          simp only [OneHoleContext.fill_hole] at read
          rw [read, splitSiblings_fill]
      | collection kind element count =>
          simp only [frameContext, OneHoleContext.fill, BindingFrame.fill, erase]
          rw [eraseArguments_assemble]
          have read := erased_selected_family _ position siblings supplied (fun _ => .hole)
          simp only [OneHoleContext.fill_hole] at read
          rw [read, splitSiblings_fill]
      | lambda domain codomain =>
          have selected : position = 0 := Fin.eq_zero position
          subst position
          rfl
      | multiLambda domain codomain count =>
          have selected : position = 0 := Fin.eq_zero position
          subst position
          rfl
      | subst domain codomain =>
          have choices : position = ⟨0, by change 0 < 2; decide⟩ ∨
              position = ⟨1, by change 1 < 2; decide⟩ := by
            have bound := position.isLt
            simp only [List.length_cons, List.length_nil] at bound
            have values : position.val = 0 ∨ position.val = 1 := by omega
            exact values.elim (fun same => Or.inl (Fin.ext same))
              (fun same => Or.inr (Fin.ext same))
          rcases choices with selected | selected <;> subst position
          · simp [frameContext, BindingFrame.fill, assembleArguments]
            rfl
          · simp [frameContext, BindingFrame.fill, assembleArguments]
            rfl

/-- Translate separately declared operational capabilities. Parameter
typing contributes only the representation frame, never an authorization. -/
def slotAllowed (permissions : OperationalPermissions) {sort : TypeExpr}
    (operator : (signatureOf language).Op sort)
    (position : Fin ((signatureOf language).arity operator).length) : Bool :=
  match operator with
  | .constructor rule _ _ scopes =>
      permissions.permitsArgument rule.label position.val &&
        permissions.permitsContext (parameterContextAt scopes position)
  | .collectionConstructor _ _ _ kind _ _ _ | .collection kind _ _ =>
      decide (kind ∈ permissions.collectionKinds) && permissions.enabled
  | .lambda _ _ => permissions.underLambda && permissions.enabled
  | .multiLambda _ _ _ => permissions.underMultiLambda && permissions.enabled
  | .subst _ _ => false

def slotPermission (permissions : OperationalPermissions) : SlotPermission (signatureOf language) :=
  fun _ _ operator position => slotAllowed permissions operator position = true

def frameAllowed (permissions : OperationalPermissions)
    {source target : Scope (signatureOf language)}
    (frame : BindingFrame (signatureOf language) source target) : Bool :=
  match frame with
  | .slot _ _ operator position _ => slotAllowed permissions operator position

/-- Check the actual binding path. The enabled bit is retained at the root,
since every context category must still have identity arrows. -/
def pathAllowed (permissions : OperationalPermissions) :
    {source target : Scope (signatureOf language)} → BindingContext (signatureOf language) source target → Bool
  | _, _, .nil => permissions.enabled
  | _, _, .cons previous frame => pathAllowed permissions previous && frameAllowed permissions frame

theorem pathAllowed_iff (permissions : OperationalPermissions)
    {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target) :
    pathAllowed permissions context = true ↔ permissions.enabled = true ∧
      FramePermission.PermittedPath (framePermission (signatureOf language) (slotPermission permissions)) context := by
  induction context with
  | nil =>
      simp only [pathAllowed]
      exact ⟨fun enabled => ⟨enabled, .nil _⟩, fun allowed => allowed.1⟩
  | cons previous frame inductionHypothesis =>
      cases frame with
      | slot bound sort operator position siblings =>
          simp only [pathAllowed, frameAllowed, Bool.and_eq_true, inductionHypothesis]
          constructor
          · rintro ⟨⟨enabled, earlier⟩, last⟩
            exact ⟨enabled, .cons earlier last⟩
          · rintro ⟨enabled, allowed⟩
            cases allowed with
            | cons earlier last => exact ⟨⟨enabled, earlier⟩, last⟩

theorem pathAllowed_arrow_iff (permissions : OperationalPermissions)
    {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target) :
    pathAllowed permissions context = true ↔ permissions.enabled = true ∧
      ∃ arrow : permittedInterface (signatureOf language) (slotPermission permissions) source ⟶
          permittedInterface (signatureOf language) (slotPermission permissions) target,
        (permissionInclusion (signatureOf language) (slotPermission permissions)).map arrow =
          bindingContextArrow context := by
  rw [pathAllowed_iff, AmbientCorrespondence.permitted_context_arrow_iff]

/-- Read the existing binding path as an original raw one-hole context. -/
def contextZipper : {source target : Scope (signatureOf language)} →
    BindingContext (signatureOf language) source target → OneHoleContext
  | _, _, .nil => .hole
  | _, _, .cons previous frame => (frameContext frame).comp (contextZipper previous)

theorem contextZipper_fill {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target)
    (supplied : Term (signatureOf language) source.1 source.2) :
    (contextZipper context).fill (erase supplied) = erase (fillContext context supplied) := by
  induction context with
  | nil => simp only [contextZipper, fillContext, Action.path, OneHoleContext.fill_hole]
  | cons previous frame inductionHypothesis =>
      simp only [contextZipper, fillContext, Action.path]
      rw [OneHoleContext.fill_comp, inductionHypothesis, frameContext_fill]
      rfl

theorem permitsContext_enabled (permissions : OperationalPermissions)
    (context : OneHoleContext) (allowed : permissions.permitsContext context = true) :
    permissions.enabled = true := by
  induction context with
  | hole => exact allowed
  | apply constructor before inner after inductionHypothesis =>
      simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at allowed
      exact inductionHypothesis allowed.2
  | lambda name inner inductionHypothesis =>
      simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at allowed
      exact inductionHypothesis allowed.2
  | multiLambda count names inner inductionHypothesis =>
      simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at allowed
      exact inductionHypothesis allowed.2
  | collection kind before inner after rest inductionHypothesis =>
      simp only [OperationalPermissions.permitsContext, Bool.and_eq_true] at allowed
      exact inductionHypothesis allowed.2
  | substBody inner replacement _ | substReplacement body inner _ =>
      exact Bool.noConfusion allowed

theorem permitsContext_comp (permissions : OperationalPermissions)
    (outer inner : OneHoleContext) :
    permissions.permitsContext (outer.comp inner) =
      (permissions.permitsContext outer && permissions.permitsContext inner) := by
  induction outer with
  | hole =>
      change permissions.permitsContext inner = (permissions.enabled && permissions.permitsContext inner)
      cases actual : permissions.permitsContext inner
      · simp
      · rw [permitsContext_enabled permissions inner actual]
        rfl
  | apply constructor before outer after inductionHypothesis =>
      simp only [OneHoleContext.comp, OperationalPermissions.permitsContext,
        inductionHypothesis, Bool.and_assoc]
  | lambda name outer inductionHypothesis =>
      simp only [OneHoleContext.comp, OperationalPermissions.permitsContext,
        inductionHypothesis, Bool.and_assoc]
  | multiLambda count names outer inductionHypothesis =>
      simp only [OneHoleContext.comp, OperationalPermissions.permitsContext,
        inductionHypothesis, Bool.and_assoc]
  | collection kind before outer after rest inductionHypothesis =>
      simp only [OneHoleContext.comp, OperationalPermissions.permitsContext,
        inductionHypothesis, Bool.and_assoc]
  | substBody outer replacement _ | substReplacement body outer _ => rfl

theorem frameContext_permitted (permissions : OperationalPermissions)
    {source target : Scope (signatureOf language)}
    (frame : BindingFrame (signatureOf language) source target) :
    permissions.permitsContext (frameContext frame) = frameAllowed permissions frame := by
  cases frame with
  | slot bound sort operator position siblings =>
      cases operator with
      | constructor rule member ordinary scopes =>
          simp only [frameContext, OperationalPermissions.permitsContext,
            splitSiblings_before_length, frameAllowed, slotAllowed]
      | collectionConstructor rule member name kind element shape count =>
          simp only [frameContext, OperationalPermissions.permitsContext, Option.isNone_none,
            Bool.and_true, frameAllowed, slotAllowed]
      | collection kind element count =>
          simp only [frameContext, OperationalPermissions.permitsContext, Option.isNone_none,
            Bool.and_true, frameAllowed, slotAllowed]
      | lambda domain codomain => rfl
      | multiLambda domain codomain count => rfl
      | subst domain codomain =>
          simp only [frameContext, frameAllowed, slotAllowed]
          split <;> rfl

/-- Permission translation agrees with the original operational checker
on every actual path, including constructor binders and all stored siblings. -/
theorem contextZipper_permitted (permissions : OperationalPermissions)
    {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target) :
    permissions.permitsContext (contextZipper context) = pathAllowed permissions context := by
  induction context with
  | nil => simp only [contextZipper, OperationalPermissions.permitsContext, pathAllowed]
  | cons previous frame inductionHypothesis =>
      simp only [contextZipper, pathAllowed, permitsContext_comp, inductionHypothesis,
        frameContext_permitted, Bool.and_comm]

/-- An authored contextual row is a guarded candidate at its physical
premise position. This check does not execute any premise or grant a slot. -/
def authoredFocusCandidate? (rule : RewriteRule) (premiseIndex : Nat)
    {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target) : Bool :=
  match rule.premises[premiseIndex]? with
  | some (.congruence left right) =>
      decide (source.1 = target.1) &&
        decide (rule.left = (contextZipper context).fill left ∧
          rule.right = (contextZipper context).fill right)
  | some (.scopedStep step) =>
      decide (source.1 = step.binders ++ target.1 ∧ source.2 = step.resultType) &&
        decide (rule.left = (contextZipper context).fill step.source ∧
          rule.right = (contextZipper context).fill step.target)
  | _ => false

theorem authoredFocusCandidate?_iff (rule : RewriteRule) (premiseIndex : Nat)
    {source target : Scope (signatureOf language)}
    (context : BindingContext (signatureOf language) source target) :
    authoredFocusCandidate? rule premiseIndex context = true ↔
      (∃ left right, rule.premises[premiseIndex]? = some (.congruence left right) ∧
        source.1 = target.1 ∧ rule.left = (contextZipper context).fill left ∧
        rule.right = (contextZipper context).fill right) ∨
      (∃ step, rule.premises[premiseIndex]? = some (.scopedStep step) ∧
        source.1 = step.binders ++ target.1 ∧ source.2 = step.resultType ∧
        rule.left = (contextZipper context).fill step.source ∧
        rule.right = (contextZipper context).fill step.target) := by
  cases selected : rule.premises[premiseIndex]? with
  | none => simp [authoredFocusCandidate?, selected]
  | some premise =>
      cases premise <;> simp [authoredFocusCandidate?, selected, and_assoc]

open SchemaElaboration TargetReification InputRecovery RawInstantiation AmbientCorrespondence AmbientMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding.ContextualRootEvents
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Check only the captures actually read by a compiled inventory. This
reads the existing assignment and supplied contextual bodies; it neither
matches terms nor completes unused metavariable declarations. -/
def checkContextualCapturesInputs {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : List TypeExpr} (inputs : List (InputEvidence language rule spec))
    (raw : Assignment) (bodies : AmbientBodies language rule spec ambient) : Bool :=
  inputs.all fun input => decide (lookup raw (inputName input) =
    some (contextualValue (bodies (inputIndex input))))

theorem checkContextualCapturesInputs_iff {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : List TypeExpr} (inputs : List (InputEvidence language rule spec))
    (raw : Assignment) (bodies : AmbientBodies language rule spec ambient) :
    checkContextualCapturesInputs inputs raw bodies = true ↔
      ContextualCapturesInputs inputs raw bodies := by
  simp [checkContextualCapturesInputs, ContextualCapturesInputs]

theorem checkContextualCapturesInputs_refusal_iff {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : List TypeExpr} (inputs : List (InputEvidence language rule spec))
    (raw : Assignment) (bodies : AmbientBodies language rule spec ambient) :
    checkContextualCapturesInputs inputs raw bodies = false ↔
      ¬ ContextualCapturesInputs inputs raw bodies := by
  rw [← checkContextualCapturesInputs_iff]
  exact Bool.eq_false_iff

theorem contextualCapturesInputs_premises_preserved
    {environment : GeneralPremise.Environment}
    {premiseContext : GeneralPremise.Context}
    {premises : List Premise} {initial final : Assignment}
    {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold
      environment premiseContext premises initial final history)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : List TypeExpr}
    (inputs : List (InputEvidence language rule spec))
    (bodies : AmbientBodies language rule spec ambient)
    (captured : ContextualCapturesInputs inputs initial bodies) :
    ContextualCapturesInputs inputs final bodies := by
  intro input member
  exact held.extension (inputName input) _ (captured input member)

theorem canonical_erase_open_sorted {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort) (canonical : CanonicalObject term)
    (free : FreeTypeContext) : OpenPatternWellSorted language free bound sort (erase term) := by
  have typed : HasType language free bound (erase term) sort :=
    (erase_typed term).recontextualizeFree (by
      intro name type _ impossible
      simp only [FreeTypeContext.empty, reduceCtorEq] at impossible)
  exact ⟨typed, erase_hasCanonicalBinderMetadata term, canonical.erase_object term,
    typed.isWellScopedAt⟩

/-- The actual whole compiler joins the existing guarded firing semantics.
Ordered premise execution preserves the left captures; right captures may
be produced by those premises and are checked on the completed assignment. -/
theorem authored_guarded_root_firing
    (environment : GeneralPremise.Environment)
    {ruleIndex : Fin environment.language.rewrites.length} {sort : TypeExpr}
    {ambient : List TypeExpr}
    (left : AuthoredSchema environment.language ruleIndex .left sort)
    (leftFound : elaborateAuthoredSchema? environment.language ruleIndex .left sort = some left)
    (right : AuthoredSchema environment.language ruleIndex .right sort)
    (rightFound : elaborateAuthoredSchema? environment.language ruleIndex .right sort = some right)
    (specified : GeneralPremise.specification? environment ruleIndex.val =
      some left.spec)
    (unreflected : ReflectiveSubstitution.substitutionPresentationForRule?
      environment.reflection (environment.language.rewrites.get ruleIndex) = none)
    (invocation : Instance (S := signatureOf environment.language)
      (M := metaArities (language := environment.language)
        (environment.language.rewrites.get ruleIndex) left.spec)
      (authoredRootSchema left right).unpositioned ambient)
    (sourceCanonical : CanonicalObject invocation.source)
    (targetCanonical : CanonicalObject invocation.target)
    {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (matched : captured ∈ matchRuleAt (environment.language.rewrites.get ruleIndex)
      left.spec ambient.length (erase invocation.source))
    (captureTyped : GeneralPremise.checkTypedAssignment environment
      ⟨ruleIndex.val, environment.language.rewrites.get ruleIndex, left.spec, ambient, 0, 0⟩ captured = true)
    (premises : GeneralPremise.PremisesHold environment
      ⟨ruleIndex.val, environment.language.rewrites.get ruleIndex, left.spec, ambient, 0, 0⟩
      (environment.language.rewrites.get ruleIndex).premises captured completed history)
    (rightReady : checkContextualCapturesInputs (alignedRightSchema left right).inputOccurrences
      completed invocation.body = true) :
    ∃ trace,
      GeneralPremise.RootFiring environment ambient sort
        (erase invocation.source) ruleIndex.val trace captured completed history (erase invocation.target) ∧
      instantiateAt? (environment.language.rewrites.get ruleIndex) left.spec ambient.length .left [] 0
        completed (environment.language.rewrites.get ruleIndex).left = some (erase invocation.source) ∧
      reduct? (environment.language.rewrites.get ruleIndex) left.spec ambient.length completed =
        some (erase invocation.target) ∧
      Nonempty (Event (S := signatureOf environment.language)
        (M := metaArities (language := environment.language)
          (environment.language.rewrites.get ruleIndex) left.spec)
        (authoredRootSchema left right).unpositioned invocation.source invocation.target) := by
  have leftCaptured := (authored_contextual_match_captures left leftFound right invocation matched).1
  have preserved := contextualCapturesInputs_premises_preserved premises
    left.compiled.inputOccurrences invocation.body leftCaptured
  have rightCaptured := (checkContextualCapturesInputs_iff _ _ _).mp rightReady
  obtain ⟨leftAction, rightAction, event⟩ := authored_contextual_instance_execution
    left leftFound right rightFound invocation completed preserved rightCaptured
  obtain ⟨trace, traced⟩ := Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.traced_iff_matchAt.mpr matched
  have declared : environment.language.rewrites[ruleIndex.val]? =
      some (environment.language.rewrites.get ruleIndex) := by
    simp only [List.getElem?_eq_getElem ruleIndex.isLt, List.get_eq_getElem]
  refine ⟨trace, ?_, leftAction, rightAction, event⟩
  apply GeneralPremise.RootFiring.fire declared specified left.admitted
    (canonical_erase_open_sorted _ sourceCanonical environment.free) traced
    (GeneralPremise.checkTypedAssignment_sound captureTyped) premises
    ?_ (canonical_erase_open_sorted _ targetCanonical environment.free)
  simpa only [Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution.binderOperation,
    unreflected, reductWith?_ordinary] using rightAction

open Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-- An actual generated, guarded receipt earns the translated path
permission. Canonical readbacks at independently fixed focus sorts supply
both fill endpoints; no endpoint slot-permission premise is required. -/
theorem guarded_receipt_permitted_focus
    {plan : Plan} {bound : List TypeExpr} {sort : TypeExpr} {source : Pattern}
    (receipt : Receipt) (valid : receipt.Valid plan bound sort source)
    (context : BindingContext
      (signatureOf (GeneralPlanEnvironment.environment plan).language)
      (receipt.job.site.focusBound, receipt.job.site.focusType) (bound, sort))
    (sameContext : receipt.job.site.context = contextZipper context)
    (focusSource focusTarget : Term
      (signatureOf (GeneralPlanEnvironment.environment plan).language)
      receipt.job.site.focusBound receipt.job.site.focusType)
    (sourceRead : reifiedObject?
      (GeneralPlanEnvironment.environment plan).language
      receipt.job.declaration.rule receipt.job.declaration.binding.spec receipt.job.site.focusBound
      receipt.job.site.focus receipt.job.site.focusType =
        some focusSource)
    (targetRead : reifiedObject?
      (GeneralPlanEnvironment.environment plan).language
      receipt.job.declaration.rule receipt.job.declaration.binding.spec receipt.job.site.focusBound
      receipt.localTarget receipt.job.site.focusType =
        some focusTarget) :
    pathAllowed plan.permissions.sites context = true ∧
      ∃ arrow : permittedInterface
          (signatureOf (GeneralPlanEnvironment.environment plan).language)
          (slotPermission plan.permissions.sites) (receipt.job.site.focusBound, receipt.job.site.focusType) ⟶
        permittedInterface
          (signatureOf (GeneralPlanEnvironment.environment plan).language)
          (slotPermission plan.permissions.sites) (bound, sort),
        (permissionInclusion
          (signatureOf (GeneralPlanEnvironment.environment plan).language)
          (slotPermission plan.permissions.sites)).map arrow = bindingContextArrow context ∧
        erase (fillContext context focusSource) = source ∧
        erase (fillContext context focusTarget) = receipt.target := by
  have permitted := valid.1.2.permitted
  rw [sameContext, contextZipper_permitted] at permitted
  obtain ⟨_, arrow, retained⟩ := (pathAllowed_arrow_iff plan.permissions.sites context).mp permitted
  have sourceErased := (reifiedObject?_sound sourceRead).2
  have targetErased := (reifiedObject?_sound targetRead).2
  refine ⟨permitted, arrow, retained, ?_, ?_⟩
  · rw [← contextZipper_fill, sourceErased, ← sameContext]
    exact valid.1.2.source_eq
  · rw [← contextZipper_fill, targetErased, ← sameContext]
    exact valid.2.2.2.1.symm

end ScopedPermissions

namespace Controls
namespace ScopedPermissionControls

open ScopedPermissions SchemaElaboration TargetReification RawInstantiation AmbientCorrespondence AmbientMatching
open InputControls RecursiveControls RawInstantiationControls AmbientControls
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding GeneralTypedSites GeneralExecutionAdmission GeneralRuleJobs ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Binding.ScopedEncoding
open Mettapedia.GSLT.LanguageDef.WellSorted
open _root_.CategoryTheory

local instance : Quiver (Scope (signatureOf outputLanguage)) := bindingFrameQuiver (signatureOf outputLanguage)

def boxCapabilities : OperationalPermissions where
  constructorArguments := [("ScopedBox", 0)]
  underLambda := true

def blockedBinderCapabilities : OperationalPermissions := { boxCapabilities with underLambda := false }

def blockedConstructorCapabilities : OperationalPermissions := { boxCapabilities with constructorArguments := [] }

theorem actual_open_focus_translates_both_frames :
    contextZipper openFocusContext = boxBodyContext ∧
      boxCapabilities.permitsContext boxBodyContext = true ∧
      pathAllowed boxCapabilities openFocusContext = true := by
  decide +kernel

theorem authored_capabilities_earn_actual_open_arrow :
    ∃ arrow : permittedInterface (signatureOf outputLanguage) (slotPermission boxCapabilities) ([u], t) ⟶
        permittedInterface (signatureOf outputLanguage) (slotPermission boxCapabilities) ([], t),
      (permissionInclusion (signatureOf outputLanguage) (slotPermission boxCapabilities)).map arrow =
        bindingContextArrow openFocusContext :=
  ((pathAllowed_arrow_iff boxCapabilities openFocusContext).mp
    actual_open_focus_translates_both_frames.2.2).2

theorem constructor_capability_without_binder_is_blocked :
    matchRuleAt outputRule outputSpec 1 openSourceTarget = [[("P", openCapture)]] ∧
      pathAllowed blockedBinderCapabilities openFocusContext = false ∧
      ¬ ∃ arrow : permittedInterface (signatureOf outputLanguage)
          (slotPermission blockedBinderCapabilities) ([u], t) ⟶
        permittedInterface (signatureOf outputLanguage) (slotPermission blockedBinderCapabilities) ([], t),
        (permissionInclusion (signatureOf outputLanguage) (slotPermission blockedBinderCapabilities)).map arrow =
          bindingContextArrow openFocusContext := by
  have denied : pathAllowed blockedBinderCapabilities openFocusContext = false := by decide +kernel
  refine ⟨whole_actual_match_keeps_ambient_dependency.1, denied, ?_⟩
  intro arrow
  have allowed := (pathAllowed_arrow_iff blockedBinderCapabilities openFocusContext).mpr ⟨rfl, arrow⟩
  rw [denied] at allowed
  exact Bool.noConfusion allowed

theorem binder_capability_without_constructor_is_blocked :
    pathAllowed blockedConstructorCapabilities openFocusContext = false := by decide +kernel

theorem typed_slot_without_operational_capability_is_blocked :
    pathAllowed OperationalPermissions.rootOnly openFocusContext = false := by decide +kernel

theorem stopped_execution_preserves_identity_but_refuses_root :
    pathAllowed OperationalPermissions.stopped
        (.nil : BindingContext (signatureOf outputLanguage) ([u], t) ([u], t)) = false ∧
      ∃ arrow : permittedInterface (signatureOf outputLanguage)
          (slotPermission OperationalPermissions.stopped) ([u], t) ⟶
        permittedInterface (signatureOf outputLanguage) (slotPermission OperationalPermissions.stopped) ([u], t),
        (permissionInclusion (signatureOf outputLanguage) (slotPermission OperationalPermissions.stopped)).map arrow =
          bindingContextArrow (.nil : BindingContext (signatureOf outputLanguage) ([u], t) ([u], t)) := by
  exact ⟨by decide +kernel, 𝟙 _, rfl⟩

def multipleFrame : BindingFrame (signatureOf outputLanguage) ([u, u] ++ [u], t)
    ([u], .arrow (.multiBinder u) t) :=
  .slot (S := signatureOf outputLanguage) [u] (.arrow (.multiBinder u) t)
    (.multiLambda u t 2) ⟨0, by decide⟩
    (fun other different => False.elim (different (Fin.eq_zero other)))

def multipleContext : BindingContext (signatureOf outputLanguage) ([u, u] ++ [u], t)
    ([u], .arrow (.multiBinder u) t) := .cons .nil multipleFrame

theorem dynamic_multi_binder_uses_its_own_capability :
    pathAllowed boxCapabilities multipleContext = false ∧
      pathAllowed { boxCapabilities with underMultiLambda := true } multipleContext = true ∧
      contextZipper multipleContext = .multiLambda 2 [] .hole := by decide +kernel

theorem explicit_substitution_slot_has_no_operational_permission :
    slotAllowed OperationalPermissions.all (Operator.subst (language := outputLanguage) u t)
      ⟨0, by decide⟩ = false := rfl

def openWholeSource : Pattern := .apply "ScopedBox" [.lambda none openSourceTarget]

def openWholeTarget : Pattern := .apply "ScopedBox" [.lambda none openSourceResult]

def openSite : SiteData :=
  SiteData.wrapApplication 1 "ScopedBox" [.lambda none openSourceTarget] 0
    (SiteData.wrapLambda none u (.here [u] t openSourceTarget))

theorem actual_generator_keeps_allowed_open_focus :
    openSite ∈ generate outputLanguage FreeTypeContext.empty boxCapabilities [] t openWholeSource := by
  decide +kernel

theorem actual_generator_refuses_blocked_open_focus :
    openSite ∉ generate outputLanguage FreeTypeContext.empty blockedBinderCapabilities [] t openWholeSource := by
  decide +kernel

def snapshot : Snapshot where
  language := outputLanguage
  freeTypes := []
  provider := { signatures := [], rows := [] }

def permissionData : Permissions where
  sites := boxCapabilities
  includeDerivedEquations := false

def executionPlan : Plan := compile snapshot permissionData

def authoredDeclaration : RulePlan :=
  ⟨1, outputRule, ⟨outputSpec, .authored⟩⟩

theorem actual_plan_preserves_duplicate_physical_positions :
    executionPlan.rules = [⟨0, outputRule, ⟨outputSpec, .authored⟩⟩, authoredDeclaration] ∧
      (GeneralPlanEnvironment.environment executionPlan).language = outputLanguage := by
  exact ⟨by cbv, by cbv⟩

theorem duplicate_names_keep_positions_but_refuse_complete_plan :
    executionPlan.obligations = [.invalidLanguage] ∧ executionPlan.complete = false := by
  exact ⟨by cbv, by cbv⟩

def openJob : Job := ⟨1, authoredDeclaration, openSite⟩

theorem compiled_job_is_original_licensed_open_focus :
    openJob.Valid executionPlan [] t openWholeSource := by
  constructor
  · rw [actual_plan_preserves_duplicate_physical_positions.1]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · apply (generate_spec _ _ _ _ _ _ _).mp
    rw [actual_plan_preserves_duplicate_physical_positions.2]
    change openSite ∈ generate outputLanguage FreeTypeContext.empty boxCapabilities [] t openWholeSource
    exact actual_generator_keeps_allowed_open_focus

def openReceipt (trace : List GeneralScopedMatchMachine.BagChoice) : Receipt :=
  ⟨openJob, trace, [("P", openCapture)], [("P", openCapture)], [], openSourceResult, openWholeTarget⟩

theorem original_finish_has_same_open_endpoints (trace : List GeneralScopedMatchMachine.BagChoice) :
    finish? executionPlan [] t openJob trace [("P", openCapture)] [("P", openCapture)] [] =
      some (openReceipt trace) := by
  cbv

theorem original_guarded_open_receipt_exists :
    ∃ trace, (openReceipt trace).Valid executionPlan [] t openWholeSource := by
  have matched : [("P", openCapture)] ∈ matchAt outputRule outputSpec 1 .left [] 0 []
      outputRule.left openSourceTarget := by decide +kernel
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr matched
  refine ⟨trace, finish_sound compiled_job_is_original_licensed_open_focus ?_ ?_
    (original_finish_has_same_open_endpoints trace)⟩
  · exact traced
  · exact .nil

theorem actual_compiled_guarded_receipt_earns_permission_and_both_fills :
    ∃ trace,
      (openReceipt trace).Valid executionPlan [] t openWholeSource ∧
      ∃ arrow : permittedInterface (signatureOf outputLanguage) (slotPermission boxCapabilities) ([u], t) ⟶
          permittedInterface (signatureOf outputLanguage) (slotPermission boxCapabilities) ([], t),
        (permissionInclusion (signatureOf outputLanguage) (slotPermission boxCapabilities)).map arrow =
          bindingContextArrow openFocusContext ∧
        erase (fillContext openFocusContext openInvocation.source) = openWholeSource ∧
        erase (fillContext openFocusContext openInvocation.target) = openWholeTarget := by
  obtain ⟨trace, valid⟩ := original_guarded_open_receipt_exists
  have sourceRead : reifiedObject? outputLanguage outputRule outputSpec [u] openSourceTarget t =
      some openInvocation.source := by
    rw [← open_event_has_independent_endpoints.1]
    exact reifiedObject?_canonical outputRule outputSpec _ (by decide +kernel)
  have targetRead : reifiedObject? outputLanguage outputRule outputSpec [u] openSourceResult t =
      some openInvocation.target := by
    rw [← open_event_has_independent_endpoints.2]
    exact reifiedObject?_canonical outputRule outputSpec _ (by decide +kernel)
  have focusLaw := guarded_receipt_permitted_focus (openReceipt trace) valid
  rw [actual_plan_preserves_duplicate_physical_positions.2] at focusLaw
  obtain ⟨_, arrow, retained, first, second⟩ := focusLaw
    openFocusContext (by
      change openSite.context = contextZipper openFocusContext
      decide +kernel) openInvocation.source openInvocation.target
    sourceRead targetRead
  exact ⟨trace, valid, arrow, retained, first, second⟩

def rootEnvironment : GeneralPremise.Environment where
  language := outputLanguage
  free := FreeTypeContext.empty
  provider := { signatures := [], rows := [] }
  specifications := [(0, outputSpec), (1, outputSpec)]

theorem whole_original_compiler_joins_guarded_same_fin_firing :
    ∃ trace,
      GeneralPremise.RootFiring rootEnvironment [u] t openSourceTarget 1 trace
        [("P", openCapture)] [("P", openCapture)] [] openSourceResult := by
  have leftFound := Option.eq_some_of_isSome second_physical_position_both_sides_admitted.1
  have rightFound := Option.eq_some_of_isSome second_physical_position_both_sides_admitted.2
  obtain ⟨trace, firing, _⟩ := authored_guarded_root_firing rootEnvironment outputLeft leftFound
    (captured := [("P", openCapture)]) (completed := [("P", openCapture)])
    outputRight rightFound (by decide +kernel) (by decide +kernel) openInvocation
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) .nil
    (by decide +kernel)
  refine ⟨trace, ?_⟩
  exact (congrArg₂ (fun source target => GeneralPremise.RootFiring rootEnvironment [u] t
    source 1 trace [("P", openCapture)] [("P", openCapture)] [] target)
    open_event_has_independent_endpoints.1 open_event_has_independent_endpoints.2).mp firing

def scopedContextRule : RewriteRule where
  name := "box-context"
  typeContext := [("P", t), ("Q", t)]
  premises := [.scopedStep ⟨[u], t, .fvar "P", .fvar "Q"⟩]
  left := .apply "ScopedBox" [.lambda none (.fvar "P")]
  right := .apply "ScopedBox" [.lambda none (.fvar "Q")]

theorem original_authored_scoped_row_is_only_a_candidate :
    authoredFocusCandidate? scopedContextRule 0 openFocusContext = true ∧
      scopedContextRule.premises[0]? = some (.scopedStep ⟨[u], t, .fvar "P", .fvar "Q"⟩) := by
  decide +kernel

theorem wrong_authored_binder_prefix_is_refused :
    authoredFocusCandidate?
      { scopedContextRule with premises := [.scopedStep ⟨[t], t, .fvar "P", .fvar "Q"⟩] }
      0 openFocusContext = false := by decide +kernel

theorem unscoped_congruence_cannot_supply_open_binder_context :
    authoredFocusCandidate?
      { scopedContextRule with premises := [.congruence (.fvar "P") (.fvar "Q")] }
      0 openFocusContext = false := by decide +kernel

def blockedGuardRule : RewriteRule :=
  { scopedContextRule with premises := [.relationQuery "blocked" [],
    .scopedStep ⟨[u], t, .fvar "P", .fvar "Q"⟩] }

def blockedGuardEnvironment : GeneralPremise.Environment where
  language := { outputLanguage with rewrites := [blockedGuardRule] }
  free := FreeTypeContext.empty
  provider := { signatures := [], rows := [] }
  specifications := []

theorem candidate_and_path_do_not_discharge_original_guard :
    authoredFocusCandidate? blockedGuardRule 1 openFocusContext = true ∧
      pathAllowed boxCapabilities openFocusContext = true ∧
      ∀ (initial final : Assignment) (history : List GeneralPremise.Event),
        ¬ GeneralPremise.PremisesHold blockedGuardEnvironment
          ⟨0, blockedGuardRule, { dependencies := [] }, [], 0, 0⟩
          blockedGuardRule.premises initial final history := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro initial final history held
  cases held with
  | cons head tail =>
      cases head with
      | query query =>
          cases query with
          | row declared specified typed arguments completed =>
              simp only [blockedGuardEnvironment, List.getElem?_nil, reduceCtorEq] at declared
          | dynamicRow registered _ _ _ _ _ _ _ =>
              simp only [blockedGuardEnvironment, List.not_mem_nil] at registered

def guardedScopedSpec : RuleBindingSpec where
  dependencies := [("P", [u, u]), ("Q", [u, u])]
  occurrences := [⟨"P", .left, [0, 0, 0, 0, 0], [.bvar 0, .bvar 1]⟩,
    ⟨"P", .left, [0, 0, 1, 0, 0], [.bvar 0, .bvar 1]⟩,
    ⟨"Q", .right, [0, 0, 0, 0], [.bvar 0, .bvar 1]⟩,
    ⟨"P", .premise 1 0 0, [0, 0, 0], [.bvar 0, .bvar 1]⟩,
    ⟨"P", .premise 1 0 0, [1, 0, 0], [.bvar 0, .bvar 1]⟩,
    ⟨"Q", .premise 1 0 1, [0, 0], [.bvar 0, .bvar 1]⟩]

def guardedStepSource : Pattern := outputRule.left

def guardedStepTarget : Pattern := .apply "ScopedBox" [.lambda none (.fvar "Q")]

def guardedScopedRule : RewriteRule :=
  { scopedContextRule with
    premises := [.relationQuery "allowed" [], .scopedStep ⟨[u], t, guardedStepSource, guardedStepTarget⟩]
    left := .apply "ScopedBox" [.lambda none guardedStepSource]
    right := .apply "ScopedBox" [.lambda none guardedStepTarget]
    bindings := some guardedScopedSpec }

def scopedProvider : GeneralPremise.ProviderSnapshot :=
  { signatures := [⟨"allowed", [], []⟩], rows := [⟨"allowed", []⟩] }

def guardedScopedLanguage : LanguageDef :=
  { outputLanguage with rewrites := [outputRule, guardedScopedRule] }

def guardedScopedEnvironment : GeneralPremise.Environment where
  language := guardedScopedLanguage
  free := FreeTypeContext.empty
  provider := scopedProvider
  specifications := [(0, outputSpec), (1, guardedScopedSpec)]

def guardedScopedPlan : Plan := compile ⟨guardedScopedLanguage, [], scopedProvider⟩ permissionData

theorem actual_admission_keeps_guarded_scoped_parent_and_child :
    guardedScopedPlan.rules =
      [⟨0, outputRule, ⟨outputSpec, .authored⟩⟩,
        ⟨1, guardedScopedRule, ⟨guardedScopedSpec, .authored⟩⟩] ∧
      GeneralPremise.rulePremisesAdmitted guardedScopedLanguage scopedProvider
        guardedScopedRule guardedScopedSpec = true ∧
      guardedScopedPlan.complete = true := by
  exact ⟨by cbv, by cbv, by cbv⟩

theorem actual_known_head_earns_stratification_separately_from_permission :
    GeneralPremise.checkStepStratification guardedScopedLanguage = true ∧
      GeneralPremise.potentialChild (.fvar "P") guardedScopedRule = true ∧
      GeneralPremise.potentialChild guardedStepSource guardedScopedRule = false ∧
      pathAllowed blockedBinderCapabilities openFocusContext = false := by
  decide +kernel

def admittedOpenJob : Job := ⟨0, ⟨0, outputRule, ⟨outputSpec, .authored⟩⟩, openSite⟩

def admittedOpenReceipt (trace : List GeneralScopedMatchMachine.BagChoice) : Receipt :=
  ⟨admittedOpenJob, trace, [("P", openCapture)], [("P", openCapture)], [], openSourceResult,
    openWholeTarget⟩

theorem complete_plan_has_original_licensed_open_job :
    admittedOpenJob.Valid guardedScopedPlan [] t openWholeSource := by
  constructor
  · rw [actual_admission_keeps_guarded_scoped_parent_and_child.1]
    exact List.mem_cons_self
  · apply (generate_spec _ _ _ _ _ _ _).mp
    decide +kernel

theorem complete_plan_emits_actual_guarded_open_receipt :
    guardedScopedPlan.complete = true ∧
      ∃ trace, (admittedOpenReceipt trace).Valid guardedScopedPlan [] t openWholeSource := by
  refine ⟨actual_admission_keeps_guarded_scoped_parent_and_child.2.2, ?_⟩
  have matched : [("P", openCapture)] ∈ matchAt outputRule outputSpec 1 .left [] 0 []
      outputRule.left openSourceTarget := by decide +kernel
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr matched
  refine ⟨trace, finish_sound complete_plan_has_original_licensed_open_job traced .nil ?_⟩
  cbv

def parentSourceValue : ContextualValue := ⟨[u, u], 0, openCapture.body⟩

def parentTargetValue : ContextualValue := ⟨[u, u], 0, openCapture.body⟩

def parentInitial : Assignment := [("P", parentSourceValue)]

def parentCompleted : Assignment := [("Q", parentTargetValue), ("P", parentSourceValue)]

def parentContext : GeneralPremise.Context := ⟨1, guardedScopedRule, guardedScopedSpec, [], 0, 0⟩

/-- The child fires at its original physical position in the genuine open
scope. The parent retains the provider row and both scoped matcher traces. -/
theorem original_guarded_scoped_parent_fires_with_both_origins :
    ∃ (childTrace targetTrace parentTrace : List GeneralScopedMatchMachine.BagChoice),
      GeneralPremise.RootFiring guardedScopedEnvironment [] t openWholeSource 1 parentTrace
        parentInitial parentCompleted
        [.query 0 0 0 [], .child 1 0 0 [u] openSourceTarget openSourceResult
          childTrace targetTrace [("P", openCapture)] [("P", openCapture)] []]
        openWholeTarget := by
  have childMatch : [("P", openCapture)] ∈ matchAt outputRule outputSpec 1 .left [] 0 []
      outputRule.left openSourceTarget := by decide +kernel
  obtain ⟨childTrace, childMatched⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr childMatch
  have childFiring : GeneralPremise.RootFiring guardedScopedEnvironment [u] t openSourceTarget 0
      childTrace [("P", openCapture)] [("P", openCapture)] [] openSourceResult := by
    apply GeneralPremise.RootFiring.fire (environment := guardedScopedEnvironment)
      (bound := [u]) (type := t) (source := openSourceTarget) (target := openSourceResult)
      (index := 0) (rule := outputRule) (spec := outputSpec)
      (trace := childTrace) (captured := [("P", openCapture)])
      (completed := [("P", openCapture)]) (history := [])
      rfl (by decide +kernel) (by decide +kernel)
      (checkOpenPatternWellSorted_sound (by decide +kernel)) childMatched
      (GeneralPremise.checkTypedAssignment_sound (by decide +kernel)) .nil
      (by decide +kernel) (checkOpenPatternWellSorted_sound (by decide +kernel))
  have queried : GeneralPremise.TracedQuery guardedScopedEnvironment parentContext "allowed" []
      parentInitial 0 parentInitial [] :=
    .row (row := ⟨"allowed", []⟩) (signature := ⟨"allowed", [], []⟩)
      (by decide +kernel) (by decide +kernel) ⟨rfl, .nil⟩ .nil
      (GeneralPremise.checkTypedAssignment_sound (by decide +kernel))
  have targetMatch : parentCompleted ∈ matchAt guardedScopedRule guardedScopedSpec 0
      (.premise 1 0 1) [] 1 parentInitial guardedStepTarget openSourceResult := by decide +kernel
  obtain ⟨targetTrace, targetMatched⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr targetMatch
  have stepped : GeneralPremise.PremiseHolds guardedScopedEnvironment parentContext.next
      (.scopedStep ⟨[u], t, guardedStepSource, guardedStepTarget⟩) parentInitial parentCompleted
      (.child 1 0 0 [u] openSourceTarget openSourceResult childTrace targetTrace
        [("P", openCapture)] [("P", openCapture)] []) :=
    .scopedStep (by decide +kernel) childFiring targetMatched
      (GeneralPremise.checkTypedAssignment_sound (by decide +kernel))
  have guards : GeneralPremise.PremisesHold guardedScopedEnvironment parentContext
      guardedScopedRule.premises parentInitial parentCompleted
      [.query 0 0 0 [], .child 1 0 0 [u] openSourceTarget openSourceResult childTrace targetTrace
        [("P", openCapture)] [("P", openCapture)] []] :=
    .cons (.query queried) (.cons stepped .nil)
  have parentMatch : parentInitial ∈ matchAt guardedScopedRule guardedScopedSpec 0 .left [] 0 []
      guardedScopedRule.left openWholeSource := by decide +kernel
  obtain ⟨parentTrace, parentMatched⟩ := GeneralScopedMatchMachine.traced_iff_matchAt.mpr parentMatch
  refine ⟨childTrace, targetTrace, parentTrace, ?_⟩
  apply GeneralPremise.RootFiring.fire (environment := guardedScopedEnvironment)
    (bound := []) (type := t) (source := openWholeSource) (target := openWholeTarget)
    (index := 1) (rule := guardedScopedRule) (spec := guardedScopedSpec)
    (trace := parentTrace) (captured := parentInitial) (completed := parentCompleted)
    (history := [.query 0 0 0 [], .child 1 0 0 [u] openSourceTarget openSourceResult
      childTrace targetTrace [("P", openCapture)] [("P", openCapture)] []])
    rfl (by decide +kernel) (by decide +kernel)
    (checkOpenPatternWellSorted_sound (by decide +kernel)) parentMatched
    (GeneralPremise.checkTypedAssignment_sound (by decide +kernel)) guards
    (by decide +kernel) (checkOpenPatternWellSorted_sound (by decide +kernel))

def emptyScopedProviderEnvironment : GeneralPremise.Environment :=
  { guardedScopedEnvironment with provider := { scopedProvider with rows := [] } }

/-- The same declared relation with no rows cannot discharge the earlier
guard. Neither the candidate nor the permitted structural path changes it. -/
theorem empty_declared_guard_blocks_actual_scoped_parent :
    GeneralPremise.signature? emptyScopedProviderEnvironment.provider "allowed" 0 =
        some ⟨"allowed", [], []⟩ ∧
      authoredFocusCandidate? guardedScopedRule 1 openFocusContext = true ∧
      pathAllowed boxCapabilities openFocusContext = true ∧
      ∀ (initial final : Assignment) (history : List GeneralPremise.Event),
        ¬ GeneralPremise.PremisesHold emptyScopedProviderEnvironment parentContext
          guardedScopedRule.premises initial final history := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro initial final history held
  cases held with
  | cons head tail =>
      cases head with
      | query queried =>
          cases queried with
          | row declared specified typed arguments completed =>
              simp only [emptyScopedProviderEnvironment, List.getElem?_nil, reduceCtorEq] at declared
          | dynamicRow registered _ _ _ _ _ _ _ =>
              simp only [emptyScopedProviderEnvironment, scopedProvider, List.not_mem_nil] at registered

/-- The original langGSLT contextual evaluator still refuses this nonempty
scoped row. The typed guarded semantics does not enlarge that evaluator. -/
theorem original_contextual_evaluator_refuses_nonempty_scoped_row
    (base : ContextualStep.BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (bindings : Match.Bindings) :
    ContextualStep.premiseStepUsing base guardedScopedLanguage recursiveStep bindings
      (.scopedStep ⟨[u], t, guardedStepSource, guardedStepTarget⟩) = [] := rfl

end ScopedPermissionControls
end Controls

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralPremise

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- An output occurrence retains the original declaration, location and typed
dependency values without requiring a recoverable matching spine. -/
abbrev OutputEvidence (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :=
  (site : RulePatternSite) × (locals : List TypeExpr) × (path : List Nat) ×
    (name : String) × (sort : TypeExpr) ×
      CompiledOccurrence language rule spec locals site path name sort

/-- The original output representation and its effective intrinsic template
are distinct. Explicit substitution is retained in the former and performed
by the existing capture-aware binding action in the latter. -/
structure OutputSchema (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr) (source : Pattern) (sort : TypeExpr) where
  representation : Term (SchemaSignature language rule spec) locals sort
  term : Term (SchemaSignature language rule spec) locals sort
  source_readback : readback representation = source
  occurrences : List (OutputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

def OutputSchema.bound {locals : List TypeExpr} {index : Nat} {sort : TypeExpr}
    (position : Var locals sort) (found : variableIndex position = index) :
    OutputSchema language rule spec locals (.bvar index) sort where
  representation := .var position
  term := .var position
  source_readback := congrArg Pattern.bvar found
  occurrences := []
  constructorOccurrences := []

def OutputSchema.ofOccurrence {locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (occurrence : CompiledOccurrence language rule spec locals site path name sort) :
    OutputSchema language rule spec locals (.fvar name) sort where
  representation := occurrence.term
  term := occurrence.term
  source_readback := by
    rw [CompiledOccurrence.term, readback_cast_sort]
    exact congrArg Pattern.fvar occurrence.named
  occurrences := [⟨site, locals, path, name, sort, occurrence⟩]
  constructorOccurrences := []

def OutputSchema.castSort {locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (compiled : OutputSchema language rule spec locals source first)
    (same : first = second) : OutputSchema language rule spec locals source second where
  representation := same ▸ compiled.representation
  term := same ▸ compiled.term
  source_readback := (readback_cast_sort same compiled.representation).trans compiled.source_readback
  occurrences := compiled.occurrences
  constructorOccurrences := compiled.constructorOccurrences

def OutputSchema.lambda {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr}
    (body : OutputSchema language rule spec (domain :: locals) source codomain) :
    OutputSchema language rule spec locals (.lambda none source) (.arrow domain codomain) where
  representation := .op (.inl (.lambda domain codomain)) (.cons body.representation .nil)
  term := .op (.inl (.lambda domain codomain)) (.cons body.term .nil)
  source_readback := by change Pattern.lambda none (readback body.representation) = _; rw [body.source_readback]
  occurrences := body.occurrences
  constructorOccurrences := body.constructorOccurrences

def OutputSchema.multiLambda {locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} (count : Nat)
    (body : OutputSchema language rule spec (List.replicate count domain ++ locals) source codomain) :
    OutputSchema language rule spec locals (.multiLambda count [] source)
      (.arrow (.multiBinder domain) codomain) where
  representation := .op (.inl (.multiLambda domain codomain count)) (.cons body.representation .nil)
  term := .op (.inl (.multiLambda domain codomain count)) (.cons body.term .nil)
  source_readback := by change Pattern.multiLambda count [] (readback body.representation) = _; rw [body.source_readback]
  occurrences := body.occurrences
  constructorOccurrences := body.constructorOccurrences

/-- Effective substitution uses the sole binding operation, retaining both
physical source children even when substitution duplicates or erases values. -/
def OutputSchema.subst {locals : List TypeExpr} {body replacement : Pattern}
    {domain codomain : TypeExpr}
    (compiledBody : OutputSchema language rule spec (domain :: locals) body codomain)
    (compiledReplacement : OutputSchema language rule spec locals replacement domain) :
    OutputSchema language rule spec locals (.subst body replacement) codomain where
  representation := .op (.inl (.subst domain codomain))
    (.cons compiledBody.representation (.cons compiledReplacement.representation .nil))
  term := inst compiledBody.term compiledReplacement.term
  source_readback := by
    change Pattern.subst (readback compiledBody.representation) (readback compiledReplacement.representation) = _
    rw [compiledBody.source_readback, compiledReplacement.source_readback]
  occurrences := compiledBody.occurrences ++ compiledReplacement.occurrences
  constructorOccurrences := compiledBody.constructorOccurrences ++ compiledReplacement.constructorOccurrences

structure OutputConstructorArguments (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (parameters : List TermParam) (sources : List Pattern) where
  arity : List (List TypeExpr × TypeExpr)
  scopes : ParameterScopes parameters arity
  representation : Args (SchemaSignature language rule spec) arity locals
  terms : Args (SchemaSignature language rule spec) arity locals
  source_readback : readbackConstructorArguments scopes representation = sources
  occurrences : List (OutputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

def outputConstructorArguments?
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (OutputSchema language rule spec locals source sort))
    (locals : List TypeExpr) (path : List Nat) (offset : Nat) :
    (parameters : List TermParam) → (sources : List Pattern) →
      Option (OutputConstructorArguments language rule spec locals parameters sources)
  | [], [] => some {
      arity := [], scopes := .nil, representation := .nil, terms := .nil,
      source_readback := rfl, occurrences := [], constructorOccurrences := [] }
  | parameter :: parameters, source :: sources => do
      let body ← parameterBody? parameter source
      let head ← compile (body.binders ++ locals) (path ++ [offset] ++ body.pathSuffix)
        body.body body.sort
      let tail ← outputConstructorArguments? compile locals path (offset + 1) parameters sources
      pure {
        arity := (body.binders, body.sort) :: tail.arity
        scopes := .cons body.scope tail.scopes
        representation := .cons head.representation tail.representation
        terms := .cons head.term tail.terms
        source_readback := by
          change body.scope.wrap (readback head.representation) ::
            readbackConstructorArguments tail.scopes tail.representation = source :: sources
          rw [head.source_readback, body.source_readback, tail.source_readback]
        occurrences := head.occurrences ++ tail.occurrences
        constructorOccurrences := head.constructorOccurrences ++ tail.constructorOccurrences }
  | _, _ => none

def OutputSchema.constructor {locals : List TypeExpr} {label : String}
    (path : List Nat) (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index)) {sources : List Pattern}
    (arguments : OutputConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources) :
    OutputSchema language rule spec locals (.apply label sources)
      (.base (language.terms.get selected.index).category) where
  representation := .op (.inl (.constructor (language.terms.get selected.index)
    (List.get_mem _ _) ordinary arguments.scopes)) arguments.representation
  term := .op (.inl (.constructor (language.terms.get selected.index)
    (List.get_mem _ _) ordinary arguments.scopes)) arguments.terms
  source_readback := by
    change Pattern.apply (language.terms.get selected.index).label
      (readbackConstructorArguments arguments.scopes arguments.representation) = _
    rw [selected.named, arguments.source_readback]
  occurrences := arguments.occurrences
  constructorOccurrences := (path, selected.index) :: arguments.constructorOccurrences

structure OutputVectorElements (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (locals : List TypeExpr)
    (sources : List Pattern) (elementSort : TypeExpr) where
  representation : Args (SchemaSignature language rule spec)
    (List.replicate sources.length ([], elementSort)) locals
  terms : Args (SchemaSignature language rule spec)
    (List.replicate sources.length ([], elementSort)) locals
  source_readback : readbackArguments representation = sources
  occurrences : List (OutputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

def outputVectorElements?
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (OutputSchema language rule spec locals source sort))
    (locals : List TypeExpr) (path : List Nat) (offset : Nat) (elementSort : TypeExpr) :
    (sources : List Pattern) → Option (OutputVectorElements language rule spec locals sources elementSort)
  | [] => some {
      representation := .nil, terms := .nil, source_readback := rfl,
      occurrences := [], constructorOccurrences := [] }
  | source :: sources => do
      let head ← compile locals (path ++ [offset]) source elementSort
      let tail ← outputVectorElements? compile locals path (offset + 1) elementSort sources
      pure {
        representation := .cons head.representation tail.representation
        terms := .cons head.term tail.terms
        source_readback := by
          change readback head.representation :: readbackArguments tail.representation = source :: sources
          rw [head.source_readback, tail.source_readback]
        occurrences := head.occurrences ++ tail.occurrences
        constructorOccurrences := head.constructorOccurrences ++ tail.constructorOccurrences }

def OutputSchema.vector {locals : List TypeExpr} {sources : List Pattern} {elementSort : TypeExpr}
    (elements : OutputVectorElements language rule spec locals sources elementSort) :
    OutputSchema language rule spec locals (.collection .vec sources none) (.collection .vec elementSort) where
  representation := .op (.inl (.collection .vec elementSort sources.length)) elements.representation
  term := .op (.inl (.collection .vec elementSort sources.length)) elements.terms
  source_readback := by change Pattern.collection .vec (readbackArguments elements.representation) none = _; rw [elements.source_readback]
  occurrences := elements.occurrences
  constructorOccurrences := elements.constructorOccurrences

def OutputSchema.vectorConstructor {locals : List TypeExpr} {sources : List Pattern} {category : String}
    (path : List Nat) (selected : SelectedVectorConstructor language category)
    (elements : OutputVectorElements language rule spec locals sources selected.elementSort) :
    OutputSchema language rule spec locals (.collection .vec sources none) (.base category) :=
  OutputSchema.castSort {
    representation := .op (.inl (.collectionConstructor (language.terms.get selected.index)
      (List.get_mem _ _) selected.parameterName .vec selected.elementSort selected.shape sources.length)) elements.representation
    term := .op (.inl (.collectionConstructor (language.terms.get selected.index)
      (List.get_mem _ _) selected.parameterName .vec selected.elementSort selected.shape sources.length)) elements.terms
    source_readback := by change Pattern.collection .vec (readbackArguments elements.representation) none = _; rw [elements.source_readback]
    occurrences := elements.occurrences
    constructorOccurrences := (path, selected.index) :: elements.constructorOccurrences }
    (congrArg TypeExpr.base selected.categorized)

/-- Ground object arguments use the shared output source traversal with
contextual metavariable callbacks disabled. -/
def groundOutputAssembly (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (_site : RulePatternSite) : Assembly (OutputSchema language rule spec) where
  bound locals index sort := do
    match found : boundPosition? locals index sort with
    | none => none
    | some position => some (OutputSchema.bound position (boundPosition?_index locals index sort found))
  free _ _ _ _ := none
  constructor compile locals path label sources sort := do
    let selected ← selectConstructor? language label
    if same : TypeExpr.base (language.terms.get selected.index).category = sort then
      if notBare : usesBareCollection? (language.terms.get selected.index) = false then
        let arguments ← outputConstructorArguments? compile locals path 0
          (language.terms.get selected.index).params sources
        let ordinary : ¬ UsesBareCollection (language.terms.get selected.index) := by
          intro bare
          have checked := (usesBareCollection?_eq_true_iff _).mpr bare
          rw [notBare] at checked
          cases checked
        pure ((OutputSchema.constructor path selected ordinary arguments).castSort same)
      else none
    else none
  abstraction := OutputSchema.lambda
  multiAbstraction := OutputSchema.multiLambda
  substitution compile locals path body replacement sort :=
    (SchemaTyping.declaredDomains language rule locals).findSome? fun domain => do
      let compiledBody ← compile (domain :: locals) (path ++ [0]) body sort
      let compiledReplacement ← compile locals (path ++ [1]) replacement domain
      pure (OutputSchema.subst compiledBody compiledReplacement)
  vector compile locals path sources sort :=
    match sort with
    | .collection .vec elementSort => do
        let elements ← outputVectorElements? compile locals path 0 elementSort sources
        pure (OutputSchema.vector elements)
    | .base category => do
        let selected ← selectVectorConstructor? language category
        let elements ← outputVectorElements? compile locals path 0 selected.elementSort sources
        pure (OutputSchema.vectorConstructor path selected elements)
    | _ => none

/-- Read back the retained representation, before effective output substitution. -/
def groundOutputTerm? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (locals : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option { term : Term (signatureOf language) locals sort // erase term = source } := do
  let compiled ← (groundOutputAssembly language rule spec site).walk
    (sourceHeight source) locals [] source sort
  let projected ← TargetReification.projectObject? compiled.representation
  pure ⟨projected.term, projected.readback.trans compiled.source_readback⟩

/-- Dependency arguments are the original ordered typed object terms.
Only the shared source traversal decides which raw terms are admitted. -/
def groundOutputArguments? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (locals : List TypeExpr) :
    (sources : List Pattern) → (dependencies : List TypeExpr) →
      Option { arguments : DependencyArguments (language := language) dependencies locals //
        eraseArguments arguments = sources }
  | [], [] => some ⟨.nil, rfl⟩
  | source :: sources, sort :: dependencies => do
      let head ← groundOutputTerm? language rule spec site locals source sort
      let tail ← groundOutputArguments? language rule spec site locals sources dependencies
      pure ⟨.cons head.val tail.val, by
        change erase head.val :: eraseArguments tail.val = _
        rw [head.property, tail.property]⟩
  | _, _ => none

/-- Output applications accept ground dependency terms while retaining the
actual source position, metadata row and declaration guards. -/
def outputOccurrenceCandidate? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr)
    (index : Fin rule.typeContext.length) :
    Option (CompiledOccurrence language rule spec bound site path name sort) :=
  if named : (rule.typeContext.get index).1 = name then
    if sorted : (rule.typeContext.get index).2 = sort then
      if declared : dependencies? spec name =
          some ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1 then
        match source : arguments? rule spec name site path with
        | none => none
        | some patterns =>
            match groundOutputArguments? language rule spec site bound patterns
                ((metaArities (language := language) rule spec).get (metaIndex rule spec index)).1 with
            | none => none
            | some arguments => some ⟨index, named, sorted, declared, arguments.val,
                by rw [source, arguments.property]⟩
      else none
    else none
  else none

def elaborateOutputOccurrence? (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (bound : List TypeExpr)
    (site : RulePatternSite) (path : List Nat) (name : String) (sort : TypeExpr) :
    Option (CompiledOccurrence language rule spec bound site path name sort) :=
  if decide (rule.bindings = some spec) && admittedFor rule spec &&
      dependencySortsDeclared language spec then
    (List.finRange rule.typeContext.length).findSome?
      (outputOccurrenceCandidate? language rule spec bound site path name sort)
  else none

theorem elaborateOutputOccurrence?_admitted {language : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {bound : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    {compiled : CompiledOccurrence language rule spec bound site path name sort}
    (accepted : elaborateOutputOccurrence? language rule spec bound site path name sort = some compiled) :
    rule.bindings = some spec ∧ admittedFor rule spec = true ∧
      dependencySortsDeclared language spec = true := by
  unfold elaborateOutputOccurrence? at accepted
  split at accepted
  · rename_i admitted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact ⟨admitted.1.1, admitted.1.2, admitted.2⟩
  · contradiction

/-- Ground argument parsing changes only the output metavariable callback. -/
def outputAssembly (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) : Assembly (OutputSchema language rule spec) :=
  { groundOutputAssembly language rule spec site with
    free := fun locals path name sort => do
      let occurrence ← elaborateOutputOccurrence? language rule spec locals site path name sort
      pure (OutputSchema.ofOccurrence occurrence) }


/-- A whole side is independently sorted by the established schema typing
checker. Its raw output and occurrence addresses remain exact source data. -/
structure AuthoredOutputSchema (language : LanguageDef) (ruleIndex : Fin language.rewrites.length)
    (site : RulePatternSite) (sort : TypeExpr) where
  spec : RuleBindingSpec
  attached : (language.rewrites.get ruleIndex).bindings = some spec
  admitted : admittedFor (language.rewrites.get ruleIndex) spec = true
  sortsDeclared : dependencySortsDeclared language spec = true
  source : Pattern
  atSite : sitePattern? (language.rewrites.get ruleIndex) site = some source
  locals : List TypeExpr
  atBinders : siteBinders? (language.rewrites.get ruleIndex) site = some locals
  compiled : OutputSchema language (language.rewrites.get ruleIndex) spec locals source sort
  compiled_from : (outputAssembly language (language.rewrites.get ruleIndex) spec site).walk
    (sourceHeight source) locals [] source sort = some compiled
  source_typed : HasType language
    (FreeTypeContext.ofList (language.rewrites.get ruleIndex).typeContext) locals source sort

def elaborateAuthoredOutput? (language : LanguageDef)
    (ruleIndex : Fin language.rewrites.length) (site : RulePatternSite) (sort : TypeExpr) :
    Option (AuthoredOutputSchema language ruleIndex site sort) := do
  let rule := language.rewrites.get ruleIndex
  let spec ← rule.bindings
  if attached : rule.bindings = some spec then
    if admitted : admittedFor rule spec = true then
      if declared : dependencySortsDeclared language spec = true then
        let source ← sitePattern? rule site
        if atSite : sitePattern? rule site = some source then
          let locals ← siteBinders? rule site
          if atBinders : siteBinders? rule site = some locals then
            if typed : SchemaTyping.checkSchemaType (SchemaTyping.declaredDomains language rule locals) language
              (FreeTypeContext.ofList rule.typeContext) locals source sort = true then
              match compiledFound : (outputAssembly language rule spec site).walk
                  (sourceHeight source) locals [] source sort with
              | none => none
              | some compiled => pure {
                  spec := spec, attached := attached, admitted := admitted, sortsDeclared := declared,
                  source := source, atSite := atSite, locals := locals, atBinders := atBinders, compiled := compiled, compiled_from := compiledFound,
                  source_typed := SchemaTyping.checkSchemaType_sound typed }
            else none
          else none
        else none
      else none
    else none
  else none


end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open AmbientCorrespondence InputRecovery

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

abbrev outputInstantiation {ambient locals : List TypeExpr} {sort : TypeExpr}
    (bodies : AmbientBodies language rule spec ambient)
    (term : Term (SchemaSignature language rule spec) locals sort) :=
  ContextualAssignment.instantiate bodies
    (ContextualAssignment.weakenSub (S := signatureOf language) locals
      (fun _ (position : Var ambient _) => Term.var position))
    (fun _ position => Term.var
      (injPrefix (S := signatureOf language) (Γ := ambient) locals position)) term

abbrev outputArguments {ambient locals : List TypeExpr}
    {arity : List (List TypeExpr × TypeExpr)}
    (bodies : AmbientBodies language rule spec ambient)
    (arguments : Args (SchemaSignature language rule spec) arity locals) :=
  ContextualAssignment.instantiateArgs bodies
    (ContextualAssignment.weakenSub (S := signatureOf language) locals
      (fun _ (position : Var ambient _) => Term.var position))
    (fun _ position => Term.var
      (injPrefix (S := signatureOf language) (Γ := ambient) locals position)) arguments

def outputName : OutputEvidence language rule spec → String
  | ⟨_, _, _, name, _, _⟩ => name

def outputIndex : OutputEvidence language rule spec →
    Fin (metaArities (language := language) rule spec).length
  | ⟨_, _, _, _, _, occurrence⟩ => metaIndex rule spec occurrence.index

def CapturesOutputs {ambient : List TypeExpr}
    (occurrences : List (OutputEvidence language rule spec))
    (raw : Assignment) (bodies : AmbientBodies language rule spec ambient) : Prop :=
  ∀ occurrence ∈ occurrences, lookup raw (outputName occurrence) =
    some (contextualValue (bodies (outputIndex occurrence)))

theorem capturesOutputs_append {ambient : List TypeExpr}
    (first second : List (OutputEvidence language rule spec)) (raw : Assignment)
    (bodies : AmbientBodies language rule spec ambient) :
    CapturesOutputs (first ++ second) raw bodies ↔
      CapturesOutputs first raw bodies ∧ CapturesOutputs second raw bodies := by
  constructor
  · intro captured
    exact ⟨fun occurrence member => captured occurrence (List.mem_append_left _ member),
      fun occurrence member => captured occurrence (List.mem_append_right _ member)⟩
  · rintro ⟨firstCaptured, secondCaptured⟩ occurrence member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact firstCaptured occurrence firstMember
    · exact secondCaptured occurrence secondMember

private theorem erase_output_cast_sort {ambient locals : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (bodies : AmbientBodies language rule spec ambient)
    (term : Term (SchemaSignature language rule spec) locals first) :
    erase (outputInstantiation bodies (same ▸ term)) =
      erase (outputInstantiation bodies term) := by
  cases same
  rfl

/-- Applying a sorted output occurrence needs its supplied value, not the
injectivity obligations needed to recover that value from an input. -/
theorem output_occurrence_instantiates {ambient locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (occurrence : CompiledOccurrence language rule spec locals site path name sort)
    (raw : Assignment) (bodies : AmbientBodies language rule spec ambient)
    (captured : lookup raw name =
      some (contextualValue (bodies (metaIndex rule spec occurrence.index)))) :
    instantiateAt? rule spec ambient.length site path locals.length raw (.fvar name) =
      some (erase (outputInstantiation bodies occurrence.term)) := by
  simp only [instantiateAt?, instantiateWith?, captured, occurrence.source,
    Option.bind_eq_bind, Option.bind_some]
  have action := instantiateValue?_typed (bodies (metaIndex rule spec occurrence.index))
    (appendAmbientArguments occurrence.arguments ambient)
  rw [appendAmbientArguments_erases] at action
  rw [action]
  congr 1
  simp only [outputInstantiation, CompiledOccurrence.term, erase_output_cast_sort,
    CompiledOccurrence.schemaTerm, ContextualAssignment.instantiate,
    ContextualAssignment.instantiateArgs_embedArgs, bindArgs_var_eq_renameArgs]
  rfl

private theorem cast_context_cancel {S : Signature} {first second : Ctx S}
    (same : first = second) {sort : S.Srt} (term : Term S second sort) :
    castTermCtx same (castTermCtx same.symm term) = term := by
  cases same
  rfl

private theorem prefixSub_lift {S : Signature} (locals ambient : Ctx S) :
    ∀ binders : Ctx S,
      liftSub (S := S)
        (fun result (position : Var locals result) => Term.var
          (injPrefix (S := S) (Γ := ambient) locals position)) binders =
        (fun result (position : Var (binders ++ locals) result) =>
          castTermCtx (List.append_assoc binders locals ambient)
            (Term.var (injPrefix (S := S) (Γ := ambient) (binders ++ locals) position)))
  | [] => rfl
  | binder :: binders => by
      funext result position
      cases position with
      | zero =>
          change Term.var Var.zero = castTermCtx
            (congrArg (List.cons binder) (List.append_assoc binders locals ambient)) (Term.var Var.zero)
          rw [castTermCtx_var, eqRec_var_zero (S := S) (List.append_assoc binders locals ambient) binder]
      | succ old =>
          change weaken (liftSub (S := S)
              (fun r (v : Var locals r) => Term.var (injPrefix (S := S) (Γ := ambient) locals v))
              binders result old) =
            castTermCtx (congrArg (List.cons binder) (List.append_assoc binders locals ambient))
              (weaken (Term.var (injPrefix (S := S) (Γ := ambient) (binders ++ locals) old)))
          rw [castTermCtx_weaken, congrFun (congrFun (prefixSub_lift locals ambient binders) result) old]

/-- Crossing constructor binders preserves the same output interpretation;
the only target difference is reassociation of the explicit ambient suffix. -/
theorem erase_output_under_binders {ambient locals binders : List TypeExpr} {sort : TypeExpr}
    (bodies : AmbientBodies language rule spec ambient)
    (term : Term (SchemaSignature language rule spec) (binders ++ locals) sort) :
    erase (ContextualAssignment.instantiate bodies
      (ContextualAssignment.weakenSub binders
        (ContextualAssignment.weakenSub (S := signatureOf language) locals
          (fun _ (position : Var ambient _) => Term.var position)))
      (liftSub (S := signatureOf language)
        (fun result (position : Var locals result) => Term.var
          (injPrefix (S := signatureOf language) (Γ := ambient) locals position)) binders) term) =
      erase (outputInstantiation bodies term) := by
  have action := ContextualAssignment.instantiate_context_cast
    (S := signatureOf language) (M := metaArities rule spec)
    (sourceEqual := rfl) (targetEqual := List.append_assoc binders locals ambient) bodies
    (ContextualAssignment.weakenSub (S := signatureOf language) (binders ++ locals)
      (fun _ (position : Var ambient _) => Term.var position))
    (fun result (position : Var (binders ++ locals) result) => Term.var
      (injPrefix (S := signatureOf language) (Γ := ambient) (binders ++ locals) position)) term
  have environment : (fun result (position : Var ambient result) =>
      castTermCtx (List.append_assoc binders locals ambient)
        (ContextualAssignment.weakenSub (S := signatureOf language) (binders ++ locals)
          (fun _ (old : Var ambient _) => Term.var old) result position)) =
      ContextualAssignment.weakenSub binders
        (ContextualAssignment.weakenSub (S := signatureOf language) locals
          (fun _ (old : Var ambient _) => Term.var old)) := by
    rw [ContextualAssignment.weakenSub_append (S := signatureOf language)]
    funext result position
    exact cast_context_cancel _ _
  change ContextualAssignment.instantiate bodies
      (fun result (position : Var ambient result) =>
        castTermCtx (List.append_assoc binders locals ambient)
          (ContextualAssignment.weakenSub (S := signatureOf language) (binders ++ locals)
            (fun _ (old : Var ambient _) => Term.var old) result position))
      (fun result (position : Var (binders ++ locals) result) =>
        castTermCtx (List.append_assoc binders locals ambient)
          (Term.var (injPrefix (S := signatureOf language) (Γ := ambient) (binders ++ locals) position))) term =
      castTermCtx (List.append_assoc binders locals ambient) (outputInstantiation bodies term) at action
  rw [environment, ← prefixSub_lift (S := signatureOf language) locals ambient binders] at action
  have eraseCast : ∀ {first second : List TypeExpr} (same : first = second)
      (value : Term (signatureOf language) first sort),
      erase (castTermCtx same value) = erase value := by
    intro first second same value
    cases same
    rfl
  exact (congrArg (fun value => erase value) action).trans (eraseCast _ _)

/-- Eliminating an output binder commutes with contextual metavariable
instantiation, including an arbitrary ambient suffix. -/
theorem outputInstantiation_inst {ambient locals : List TypeExpr} {domain sort : TypeExpr}
    (bodies : AmbientBodies language rule spec ambient)
    (body : Term (SchemaSignature language rule spec) (domain :: locals) sort)
    (replacement : Term (SchemaSignature language rule spec) locals domain) :
    outputInstantiation bodies (inst body replacement) =
      inst (outputInstantiation bodies body) (outputInstantiation bodies replacement) := by
  dsimp only [outputInstantiation]
  rw [ContextualAssignment.instantiate_inst]
  have environment : ContextualAssignment.weakenSub [domain]
      (ContextualAssignment.weakenSub (S := signatureOf language) locals
        (fun _ (position : Var ambient _) => Term.var position)) =
      ContextualAssignment.weakenSub (S := signatureOf language) (domain :: locals)
        (fun _ (position : Var ambient _) => Term.var position) := by
    funext result position
    rfl
  have valuation : liftSub (S := signatureOf language)
      (fun result (position : Var locals result) => Term.var
        (injPrefix (S := signatureOf language) (Γ := ambient) locals position)) [domain] =
      (fun result (position : Var (domain :: locals) result) => Term.var
        (injPrefix (S := signatureOf language) (Γ := ambient) (domain :: locals) position)) := by
    funext result position
    cases position <;> rfl
  rw [environment, valuation]

/-- The checked raw instantiator and the intrinsic effective output agree
when every retained physical occurrence has its actual supplied value. -/
def OutputInstantiatesAt {ambient locals : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (compiled : OutputSchema language rule spec locals source sort)
    (site : RulePatternSite) (path : List Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    CapturesOutputs compiled.occurrences raw bodies →
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (erase (outputInstantiation bodies compiled.term))

theorem output_substitution_instantiates {ambient locals : List TypeExpr}
    {body replacement : Pattern} {domain sort : TypeExpr}
    (compiledBody : OutputSchema language rule spec (domain :: locals) body sort)
    (compiledReplacement : OutputSchema language rule spec locals replacement domain)
    {site : RulePatternSite} {path : List Nat}
    (bodyAction : OutputInstantiatesAt (ambient := ambient) compiledBody site (path ++ [0]))
    (replacementAction : OutputInstantiatesAt (ambient := ambient) compiledReplacement site (path ++ [1])) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.subst compiledBody compiledReplacement) site path := by
  intro raw bodies captured
  obtain ⟨bodyCaptured, replacementCaptured⟩ :=
    (capturesOutputs_append _ _ raw bodies).mp captured
  have bodyRun := bodyAction raw bodies bodyCaptured
  have replacementRun := replacementAction raw bodies replacementCaptured
  simp only [List.length_cons] at bodyRun
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec ambient.length site (path ++ [0]) (locals.length + 1) raw body).bind
      (fun actualBody =>
        (instantiateAt? rule spec ambient.length site (path ++ [1]) locals.length raw replacement).bind
          (fun actualReplacement => some
            (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar actualReplacement actualBody))) = _
  rw [bodyRun, replacementRun]
  simp only [Option.bind_some, OutputSchema.subst]
  rw [outputInstantiation_inst]
  exact congrArg some (erase_bind_extend _ _).symm

theorem output_bound_instantiates {ambient locals : List TypeExpr} {index : Nat} {sort : TypeExpr}
    (position : Var locals sort) (found : variableIndex position = index)
    (site : RulePatternSite) (path : List Nat) :
    OutputInstantiatesAt (ambient := ambient) (language := language) (rule := rule) (spec := spec)
      (OutputSchema.bound position found) site path := by
  intro raw bodies _
  simp only [instantiateAt?, instantiateWith?, OutputSchema.bound, outputInstantiation,
    ContextualAssignment.instantiate, erase]
  rw [InputRecovery.variableIndex_injPrefix (language := language) (ambient := ambient) position, found]

theorem output_free_instantiates {ambient locals : List TypeExpr} {site : RulePatternSite}
    {path : List Nat} {name : String} {sort : TypeExpr}
    (occurrence : CompiledOccurrence language rule spec locals site path name sort) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.ofOccurrence occurrence) site path := by
  intro raw bodies captured
  exact output_occurrence_instantiates occurrence raw bodies
    (captured ⟨site, locals, path, name, sort, occurrence⟩ (List.mem_cons_self))

theorem output_cast_instantiates {ambient locals : List TypeExpr} {source : Pattern}
    {first second : TypeExpr} (same : first = second)
    (compiled : OutputSchema language rule spec locals source first)
    {site : RulePatternSite} {path : List Nat}
    (action : OutputInstantiatesAt (ambient := ambient) compiled site path) :
    OutputInstantiatesAt (ambient := ambient) (compiled.castSort same) site path := by
  cases same
  exact action

theorem output_lambda_instantiates {ambient locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr}
    (compiled : OutputSchema language rule spec (domain :: locals) source codomain)
    {site : RulePatternSite} {path : List Nat}
    (action : OutputInstantiatesAt (ambient := ambient) compiled site (path ++ [0])) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.lambda compiled) site path := by
  intro raw bodies captured
  have bodyRun := action raw bodies captured
  simp only [List.length_cons] at bodyRun
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec ambient.length site (path ++ [0]) (locals.length + 1) raw source).bind
    (fun result => some (Pattern.lambda none result)) = _
  rw [bodyRun]
  simp only [Option.bind_some, OutputSchema.lambda, outputInstantiation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs, erase,
    erase_output_under_binders]
  rfl

theorem output_multiLambda_instantiates {ambient locals : List TypeExpr} {source : Pattern}
    {domain codomain : TypeExpr} (count : Nat)
    (compiled : OutputSchema language rule spec (List.replicate count domain ++ locals) source codomain)
    {site : RulePatternSite} {path : List Nat}
    (action : OutputInstantiatesAt (ambient := ambient) compiled site (path ++ [0])) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.multiLambda count compiled) site path := by
  intro raw bodies captured
  have bodyRun := action raw bodies captured
  rw [show (List.replicate count domain ++ locals).length = locals.length + count by
    simp [List.length_append, Nat.add_comm]] at bodyRun
  rw [instantiateAt?, instantiateWith?]
  change (instantiateAt? rule spec ambient.length site (path ++ [0]) (locals.length + count) raw source).bind
    (fun result => some (Pattern.multiLambda count [] result)) = _
  rw [bodyRun]
  simp only [Option.bind_some, OutputSchema.multiLambda, outputInstantiation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs, erase,
    erase_output_under_binders]

def OutputConstructorInstantiatesAt {ambient locals : List TypeExpr}
    {parameters : List TermParam} {sources : List Pattern}
    (arguments : OutputConstructorArguments language rule spec locals parameters sources)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    CapturesOutputs arguments.occurrences raw bodies →
    instantiateArgsAt? rule spec ambient.length site path locals.length raw offset sources =
      some (eraseConstructorArguments arguments.scopes (outputArguments bodies arguments.terms))

theorem output_constructor_arguments_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (OutputSchema language rule spec locals source sort))
    (site : RulePatternSite) {ambient : List TypeExpr}
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled →
        OutputInstantiatesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) :
    ∀ sources offset parameters
      (arguments : OutputConstructorArguments language rule spec locals parameters sources),
      outputConstructorArguments? compile locals path offset parameters sources = some arguments →
        OutputConstructorInstantiatesAt (ambient := ambient) arguments site path offset := by
  intro sources
  induction sources with
  | nil =>
      intro offset parameters arguments found
      cases parameters with
      | nil =>
          simp only [outputConstructorArguments?, Option.some.injEq] at found
          cases found
          intro raw bodies _
          simp only [instantiateArgsAt?, instantiateArgsWith?, outputArguments,
            ContextualAssignment.instantiateArgs, eraseConstructorArguments]
      | cons parameter parameters => simp [outputConstructorArguments?] at found
  | cons source sources induction =>
      intro offset parameters arguments found
      cases parameters with
      | nil => simp [outputConstructorArguments?] at found
      | cons parameter parameters =>
          cases bodyFound : parameterBody? parameter source with
          | none => simp [outputConstructorArguments?, bodyFound] at found
          | some body =>
              cases headFound : compile (body.binders ++ locals)
                  (path ++ [offset] ++ body.pathSuffix) body.body body.sort with
              | none =>
                  simp only [outputConstructorArguments?, bodyFound, headFound,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at found
              | some head =>
                  cases tailFound : outputConstructorArguments? compile locals path
                      (offset + 1) parameters sources with
                  | none =>
                      simp only [outputConstructorArguments?, bodyFound, headFound, tailFound,
                        Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at found
                  | some tail =>
                      simp only [outputConstructorArguments?, bodyFound, headFound, tailFound,
                        Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at found
                      cases found
                      intro raw bodies captured
                      change CapturesOutputs (head.occurrences ++ tail.occurrences) raw bodies at captured
                      obtain ⟨headCaptured, tailCaptured⟩ := (capturesOutputs_append _ _ raw bodies).mp captured
                      have headAction := children _ _ _ _ head headFound raw bodies headCaptured
                      have wrapped := AmbientCorrespondence.parameter_body_instantiates
                        (rule := rule) (spec := spec) (ambient := ambient) body bodyFound site
                        (path ++ [offset]) locals.length raw
                      rw [show locals.length + body.binders.length = (body.binders ++ locals).length by
                        simp [List.length_append, Nat.add_comm], headAction] at wrapped
                      simp only [Option.map_some] at wrapped
                      rw [instantiateArgsAt?, instantiateArgsWith?]
                      change (instantiateAt? rule spec ambient.length site (path ++ [offset]) locals.length raw source).bind
                          (fun first => (instantiateArgsAt? rule spec ambient.length site path locals.length raw
                            (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
                      rw [wrapped, induction (offset + 1) parameters tail tailFound raw bodies tailCaptured]
                      simp only [Option.bind_some, outputArguments, ContextualAssignment.instantiateArgs,
                        eraseConstructorArguments, erase_output_under_binders]

theorem output_constructor_instantiates {ambient locals : List TypeExpr} {label : String}
    (path : List Nat) (selected : SelectedConstructor language label)
    (ordinary : ¬ UsesBareCollection (language.terms.get selected.index)) {sources : List Pattern}
    (arguments : OutputConstructorArguments language rule spec locals
      (language.terms.get selected.index).params sources)
    {site : RulePatternSite}
    (action : OutputConstructorInstantiatesAt (ambient := ambient) arguments site path 0) :
    OutputInstantiatesAt (ambient := ambient)
      (OutputSchema.constructor path selected ordinary arguments) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
    (fun values => some (Pattern.apply label values)) = _
  rw [action raw bodies captured]
  simp only [Option.bind_some, OutputSchema.constructor, outputInstantiation,
    ContextualAssignment.instantiate, erase, selected.named]

def OutputVectorInstantiatesAt {ambient locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (elements : OutputVectorElements language rule spec locals sources sort)
    (site : RulePatternSite) (path : List Nat) (offset : Nat) : Prop :=
  ∀ raw (bodies : AmbientBodies language rule spec ambient),
    CapturesOutputs elements.occurrences raw bodies →
    instantiateArgsAt? rule spec ambient.length site path locals.length raw offset sources =
      some (eraseArguments (outputArguments bodies elements.terms))

theorem output_vector_elements_instantiates
    (compile : (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (sort : TypeExpr) →
        Option (OutputSchema language rule spec locals source sort))
    (site : RulePatternSite) {ambient : List TypeExpr}
    (children : ∀ locals path source sort compiled,
      compile locals path source sort = some compiled →
        OutputInstantiatesAt (ambient := ambient) compiled site path)
    (locals : List TypeExpr) (path : List Nat) (sort : TypeExpr) :
    ∀ sources offset (elements : OutputVectorElements language rule spec locals sources sort),
      outputVectorElements? compile locals path offset sort sources = some elements →
        OutputVectorInstantiatesAt (ambient := ambient) elements site path offset := by
  intro sources
  induction sources with
  | nil =>
      intro offset elements found
      simp only [outputVectorElements?, Option.some.injEq] at found
      cases found
      intro raw bodies _
      simp only [instantiateArgsAt?, instantiateArgsWith?, outputArguments,
        ContextualAssignment.instantiateArgs, eraseArguments]
  | cons source sources induction =>
      intro offset elements found
      cases headFound : compile locals (path ++ [offset]) source sort with
      | none => simp [outputVectorElements?, headFound] at found
      | some head =>
          cases tailFound : outputVectorElements? compile locals path (offset + 1) sort sources with
          | none => simp [outputVectorElements?, headFound, tailFound] at found
          | some tail =>
              simp only [outputVectorElements?, headFound, tailFound, Option.bind_eq_bind,
                Option.bind_some, pure, Option.some.injEq] at found
              cases found
              intro raw bodies captured
              change CapturesOutputs (head.occurrences ++ tail.occurrences) raw bodies at captured
              obtain ⟨headCaptured, tailCaptured⟩ := (capturesOutputs_append _ _ raw bodies).mp captured
              rw [instantiateArgsAt?, instantiateArgsWith?]
              change (instantiateAt? rule spec ambient.length site (path ++ [offset]) locals.length raw source).bind
                  (fun first => (instantiateArgsAt? rule spec ambient.length site path locals.length raw
                    (offset + 1) sources).bind (fun rest => some (first :: rest))) = _
              rw [children _ _ _ _ head headFound raw bodies headCaptured,
                induction (offset + 1) tail tailFound raw bodies tailCaptured]
              rfl

theorem output_vector_instantiates {ambient locals : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (elements : OutputVectorElements language rule spec locals sources sort)
    {site : RulePatternSite} {path : List Nat}
    (action : OutputVectorInstantiatesAt (ambient := ambient) elements site path 0) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.vector elements) site path := by
  intro raw bodies captured
  rw [instantiateAt?, instantiateWith?]
  change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
    (fun values => some (Pattern.collection .vec values none)) = _
  rw [action raw bodies captured]
  rfl

theorem output_vector_constructor_instantiates {ambient locals : List TypeExpr} {sources : List Pattern}
    {category : String} (path : List Nat) (selected : SelectedVectorConstructor language category)
    (elements : OutputVectorElements language rule spec locals sources selected.elementSort)
    {site : RulePatternSite}
    (action : OutputVectorInstantiatesAt (ambient := ambient) elements site path 0) :
    OutputInstantiatesAt (ambient := ambient) (OutputSchema.vectorConstructor path selected elements) site path := by
  cases selected with
  | mk index unique parameterName elementSort shape categorized =>
      cases categorized
      intro raw bodies captured
      rw [instantiateAt?, instantiateWith?]
      change (instantiateArgsAt? rule spec ambient.length site path locals.length raw 0 sources).bind
        (fun values => some (Pattern.collection .vec values none)) = _
      rw [action raw bodies captured]
      rfl

/-- Every local output assembly law is proved against the actual scoped
instantiator. No whole-redex agreement is supplied by a caller. -/
theorem outputAssemblyInvariant (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (ambient : List TypeExpr) :
    (outputAssembly language rule spec site).Invariant
      (fun _ path _ _ compiled => OutputInstantiatesAt (ambient := ambient) compiled site path) where
  bound locals path index sort compiled found := by
    dsimp only [outputAssembly, groundOutputAssembly] at found
    split at found
    · contradiction
    · rename_i position positionFound
      cases Option.some.inj found
      exact output_bound_instantiates position (boundPosition?_index locals index sort positionFound) site path
  free locals path name sort compiled found := by
    cases occurrenceFound : elaborateOutputOccurrence? language rule spec locals site path name sort with
    | none => simp [outputAssembly, groundOutputAssembly, occurrenceFound] at found
    | some occurrence =>
        simp only [outputAssembly, groundOutputAssembly, occurrenceFound, Option.bind_eq_bind,
          Option.bind_some, pure, Option.some.injEq] at found
        cases found
        exact output_free_instantiates occurrence
  constructor compile children locals path label sources sort compiled found := by
    cases selectedFound : selectConstructor? language label with
    | none => simp [outputAssembly, groundOutputAssembly, selectedFound] at found
    | some selected =>
        by_cases same : TypeExpr.base (language.terms.get selected.index).category = sort
        · by_cases notBare : usesBareCollection? (language.terms.get selected.index) = false
          · cases argumentsFound : outputConstructorArguments? compile locals path 0
                (language.terms.get selected.index).params sources with
            | none =>
                simp only [outputAssembly, groundOutputAssembly, selectedFound, same, notBare, argumentsFound,
                  dite_true, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at found
            | some arguments =>
                simp only [outputAssembly, groundOutputAssembly, selectedFound, same, notBare, argumentsFound,
                  dite_true, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at found
                cases found
                apply output_cast_instantiates same
                apply output_constructor_instantiates
                exact output_constructor_arguments_instantiates compile site children
                  locals path sources 0 _ arguments argumentsFound
          · simp only [outputAssembly, groundOutputAssembly, selectedFound, same, notBare, dite_true,
              dite_false, Option.bind_eq_bind, Option.bind_some, reduceCtorEq] at found
        · simp only [outputAssembly, groundOutputAssembly, selectedFound, same, dite_false,
            Option.bind_eq_bind, Option.bind_some, reduceCtorEq] at found
  abstraction _ _ _ _ _ body action := output_lambda_instantiates body action
  multiAbstraction _ _ _ _ _ count body action := output_multiLambda_instantiates count body action
  substitution compile children locals path body replacement sort compiled found := by
    obtain ⟨domain, _, domainFound⟩ := List.exists_of_findSome?_eq_some found
    cases bodyFound : compile (domain :: locals) (path ++ [0]) body sort with
    | none => simp [bodyFound] at domainFound
    | some compiledBody =>
        cases replacementFound : compile locals (path ++ [1]) replacement domain with
        | none => simp [bodyFound, replacementFound] at domainFound
        | some compiledReplacement =>
            simp only [bodyFound, replacementFound, Option.bind_eq_bind,
              Option.bind_some, pure, Option.some.injEq] at domainFound
            cases domainFound
            exact output_substitution_instantiates compiledBody compiledReplacement
              (children _ _ _ _ compiledBody bodyFound)
              (children _ _ _ _ compiledReplacement replacementFound)
  vector compile children locals path sources sort compiled found := by
    cases sort with
    | arrow first last => simp [outputAssembly, groundOutputAssembly] at found
    | multiBinder domain => simp [outputAssembly, groundOutputAssembly] at found
    | base category =>
        cases selectedFound : selectVectorConstructor? language category with
        | none => simp [outputAssembly, groundOutputAssembly, selectedFound] at found
        | some selected =>
            cases elementsFound : outputVectorElements? compile locals path 0 selected.elementSort sources with
            | none => simp [outputAssembly, groundOutputAssembly, selectedFound, elementsFound] at found
            | some elements =>
                simp only [outputAssembly, groundOutputAssembly, selectedFound, elementsFound, Option.bind_eq_bind,
                  Option.bind_some, pure, Option.some.injEq] at found
                cases found
                exact output_vector_constructor_instantiates path selected elements
                  (output_vector_elements_instantiates compile site children locals path
                    selected.elementSort sources 0 elements elementsFound)
    | collection kind elementSort =>
        cases kind with
        | hashBag => simp [outputAssembly, groundOutputAssembly] at found
        | hashSet => simp [outputAssembly, groundOutputAssembly] at found
        | vec =>
            cases elementsFound : outputVectorElements? compile locals path 0 elementSort sources with
            | none => simp [outputAssembly, groundOutputAssembly, elementsFound] at found
            | some elements =>
                simp only [outputAssembly, groundOutputAssembly, elementsFound, Option.bind_eq_bind,
                  Option.bind_some, pure, Option.some.injEq] at found
                cases found
                exact output_vector_instantiates elements
                  (output_vector_elements_instantiates compile site children locals path
                    elementSort sources 0 elements elementsFound)

/-- Arbitrary accepted output templates agree with the existing executable
source instantiator, for every ambient context and captured typed value. -/
theorem outputAssembly_walk_instantiates (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (ambient : List TypeExpr)
    {fuel : Nat} {locals : List TypeExpr} {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (compiled : OutputSchema language rule spec locals source sort)
    (found : (outputAssembly language rule spec site).walk fuel locals path source sort = some compiled) :
    OutputInstantiatesAt (ambient := ambient) compiled site path :=
  Assembly.walk_invariant (outputAssemblyInvariant language rule spec site ambient)
    fuel locals path source sort compiled found

/-- A successful authored output carries the actual parser run used by the
source-to-native boundary, alongside independent source sorting. -/
theorem AuthoredOutputSchema.instantiates {ruleIndex : Fin language.rewrites.length}
    {site : RulePatternSite} {sort : TypeExpr} {ambient : List TypeExpr}
    (compiled : AuthoredOutputSchema language ruleIndex site sort)
    (raw : Assignment)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : CapturesOutputs compiled.compiled.occurrences raw bodies) :
    instantiateAt? (language.rewrites.get ruleIndex) compiled.spec ambient.length
        site [] compiled.locals.length raw compiled.source =
      some (erase (outputInstantiation bodies compiled.compiled.term)) :=
  outputAssembly_walk_instantiates language _ compiled.spec site ambient
    compiled.compiled compiled.compiled_from raw bodies captured

/-- The effective output schema is precisely the contractum produced by the
original rule engine, including explicit substitution and open ambient data. -/
theorem AuthoredOutputSchema.reduct {ruleIndex : Fin language.rewrites.length}
    {sort : TypeExpr} {ambient : List TypeExpr}
    (compiled : AuthoredOutputSchema language ruleIndex .right sort)
    (raw : Assignment)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : CapturesOutputs compiled.compiled.occurrences raw bodies) :
    reduct? (language.rewrites.get ruleIndex) compiled.spec ambient.length raw =
      some (erase (outputInstantiation bodies compiled.compiled.term)) := by
  have source : compiled.source = (language.rewrites.get ruleIndex).right :=
    (Option.some.inj compiled.atSite).symm
  have locals : compiled.locals = [] := by
    have actual := compiled.atBinders
    simp only [siteBinders?, Option.some.injEq] at actual
    exact actual.symm
  simpa only [reduct?, source, locals, List.length_nil] using compiled.instantiates raw bodies captured

/-- A scoped child premise retains either actual endpoint and its original
binder context. The source site determines the endpoint; no term is chosen. -/
theorem AuthoredOutputSchema.premise_endpoint {language : LanguageDef}
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    {index endpoint : Nat} {step : ScopedStepPremise}
    (found : (language.rewrites.get ruleIndex).premises[index]? = some (.scopedStep step))
    (valid : endpoint < 2)
    (compiled : AuthoredOutputSchema language ruleIndex (.premise index 0 endpoint) sort)
    (raw : Assignment)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : CapturesOutputs compiled.compiled.occurrences raw bodies) :
    instantiateAt? (language.rewrites.get ruleIndex) compiled.spec ambient.length
        (.premise index 0 endpoint) [] step.binders.length raw
        (if endpoint = 0 then step.source else step.target) =
      some (erase (outputInstantiation bodies compiled.compiled.term)) := by
  have locals : compiled.locals = step.binders := by
    have context := compiled.atBinders
    rw [siteBinders?_scopedStep _ index step found endpoint valid] at context
    exact (Option.some.inj context).symm
  have original : compiled.source = if endpoint = 0 then step.source else step.target := by
    have actualSite : sitePattern? (language.rewrites.get ruleIndex) (.premise index 0 endpoint) =
        some (if endpoint = 0 then step.source else step.target) := by
      have cases : endpoint = 0 ∨ endpoint = 1 := by omega
      rcases cases with rfl | rfl
      · dsimp only [sitePattern?]; rw [found]; rfl
      · dsimp only [sitePattern?]; rw [found]; rfl
    exact Option.some.inj (compiled.atSite.symm.trans actualSite)
  simpa only [locals, original] using compiled.instantiates raw bodies captured

theorem AuthoredOutputSchema.premise_source {language : LanguageDef}
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    {index : Nat} {step : ScopedStepPremise}
    (found : (language.rewrites.get ruleIndex).premises[index]? = some (.scopedStep step))
    (compiled : AuthoredOutputSchema language ruleIndex (.premise index 0 0) sort)
    (raw : Assignment)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : CapturesOutputs compiled.compiled.occurrences raw bodies) :
    instantiateAt? (language.rewrites.get ruleIndex) compiled.spec ambient.length
        (.premise index 0 0) [] step.binders.length raw step.source =
      some (erase (outputInstantiation bodies compiled.compiled.term)) := by
  simpa only [ite_true] using AuthoredOutputSchema.premise_endpoint found (by decide) compiled raw bodies captured

theorem AuthoredOutputSchema.premise_target {language : LanguageDef}
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    {index : Nat} {step : ScopedStepPremise}
    (found : (language.rewrites.get ruleIndex).premises[index]? = some (.scopedStep step))
    (compiled : AuthoredOutputSchema language ruleIndex (.premise index 0 1) sort)
    (raw : Assignment)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) compiled.spec ambient)
    (captured : CapturesOutputs compiled.compiled.occurrences raw bodies) :
    instantiateAt? (language.rewrites.get ruleIndex) compiled.spec ambient.length
        (.premise index 0 1) [] step.binders.length raw step.target =
      some (erase (outputInstantiation bodies compiled.compiled.term)) := by
  simpa only [Nat.one_ne_zero, ite_false] using
    AuthoredOutputSchema.premise_endpoint found (by decide) compiled raw bodies captured

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A source body retains its exact raw spelling. Only its declared named
free occurrences are closed into a new outer context suffix. -/
structure Parsed (language : LanguageDef) (entries : List (String × TypeExpr))
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) where
  term : Term (signatureOf language) (bound ++ NamedFreeContext.contextSorts entries) sort
  closed_readback : erase term = NamedFreeContext.closeContext bound.length entries source
  source_scope : source.isWellScopedAt bound.length = true
  names_unique : (entries.map Prod.fst).Nodup

/-- The existing output traversal also handles explicit substitution; free
names are resolved by their actual finite source declarations first. -/
def parse? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (entries : List (String × TypeExpr))
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option (Parsed language entries bound source sort) :=
  if unique : (entries.map Prod.fst).Nodup then
    if scopeProof : source.isWellScopedAt bound.length = true then do
      let compiled ← groundOutputTerm? language rule spec site
        (bound ++ NamedFreeContext.contextSorts entries)
        (NamedFreeContext.closeContext bound.length entries source) sort
      pure ⟨compiled.val, compiled.property, scopeProof, unique⟩
    else none
  else none

theorem Parsed.readback {language : LanguageDef} {entries : List (String × TypeExpr)}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (parsed : Parsed language entries bound source sort) :
    NamedFreeContext.openContext bound.length entries (erase parsed.term) = source := by
  rw [parsed.closed_readback]
  exact NamedFreeContext.openNames_closeNames bound.length (entries.map Prod.fst) source
    (by rw [← Mettapedia.OSLF.MeTTaIL.Substitution.isWellScopedAt_eq_lc_at]
        exact parsed.source_scope)

/-- Successful source decoding earns the original independent authored
sorting judgment, rather than merely the target term's intrinsic sort. -/
theorem Parsed.typed {language : LanguageDef} {entries : List (String × TypeExpr)}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (parsed : Parsed language entries bound source sort) :
    HasType language (FreeTypeContext.ofList entries) bound source sort := by
  have opened := NamedFreeContext.openContext_typed_of_nodup entries parsed.names_unique
    (erase_typed parsed.term)
  rwa [parsed.readback] at opened

/-- Decoding does not merge two raw source bodies, even when they use both
bound and named free variables beneath binders. -/
theorem Parsed.term_injective {language : LanguageDef} {entries : List (String × TypeExpr)}
    {bound : List TypeExpr} {left right : Pattern} {sort : TypeExpr}
    (first : Parsed language entries bound left sort)
    (second : Parsed language entries bound right sort) (same : first.term = second.term) :
    left = right := by
  rw [← first.readback, ← second.readback, same]

/-- The computed guards are exactly the source-name and scope requirements.
The source grammar remains the existing ground output traversal. -/
theorem parse?_isSome_iff (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite)
    (entries : List (String × TypeExpr)) (bound : List TypeExpr)
    (source : Pattern) (sort : TypeExpr) :
    (parse? language rule spec site entries bound source sort).isSome = true ↔
      (entries.map Prod.fst).Nodup ∧ source.isWellScopedAt bound.length = true ∧
      (groundOutputTerm? language rule spec site (bound ++ NamedFreeContext.contextSorts entries)
        (NamedFreeContext.closeContext bound.length entries source) sort).isSome = true := by
  unfold parse?
  split
  · rename_i unique
    split
    · rename_i scopeProof
      simp only [unique, scopeProof, true_and]
      cases result : groundOutputTerm? language rule spec site
        (bound ++ NamedFreeContext.contextSorts entries)
        (NamedFreeContext.closeContext bound.length entries source) sort <;> rfl
    · rename_i absent
      simp only [absent, Option.isSome_none, Bool.false_eq_true,
        false_and, and_false]
  · rename_i absent
    simp only [absent, Option.isSome_none, Bool.false_eq_true, false_and]

/-- Original contextual indices are checked before the body is decoded. -/
structure Captured (language : LanguageDef) (entries : List (String × TypeExpr))
    (dependencies ambient : List TypeExpr) (source : ContextualValue) (sort : TypeExpr) where
  body : Parsed language entries (dependencies ++ ambient) source.body sort
  dependencies_eq : source.dependencies = dependencies
  ambient_eq : source.ambient = ambient.length

def capture? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (entries : List (String × TypeExpr))
    (dependencies ambient : List TypeExpr) (source : ContextualValue) (sort : TypeExpr) :
    Option (Captured language entries dependencies ambient source sort) :=
  if dependenciesEq : source.dependencies = dependencies then
    if ambientEq : source.ambient = ambient.length then do
      let body ← parse? language rule spec site entries (dependencies ++ ambient) source.body sort
      pure ⟨body, dependenciesEq, ambientEq⟩
    else none
  else none

/-- Reconstruction retains the original dependency types and ambient count;
new free-name slots never silently become original contextual metadata. -/
def Captured.readValue {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort) : ContextualValue where
  dependencies := dependencies
  ambient := ambient.length
  body := NamedFreeContext.openContext (dependencies ++ ambient).length entries (erase captured.body.term)

theorem Captured.readValue_eq {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort) :
    captured.readValue = source := by
  cases source
  simp only [Captured.readValue, ContextualValue.mk.injEq]
  exact ⟨captured.dependencies_eq.symm, captured.ambient_eq.symm, captured.body.readback⟩

/-- The snapshot's executable first-name lookup is the same source context
used by the independent sorting judgment. -/
theorem snapshot_free_eq_ofList (snapshot :
    Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot) :
    snapshot.free = FreeTypeContext.ofList snapshot.freeTypes := by
  funext name
  change ((snapshot.freeTypes.find? fun entry => entry.1 == name).map Prod.snd) = _
  induction snapshot.freeTypes with
  | nil => rfl
  | cons entry rest ih =>
      by_cases same : entry.1 = name
      · simp [FreeTypeContext.ofList, same]
      · simp only [List.find?_cons, beq_eq_false_iff_ne.mpr same,
          if_false, FreeTypeContext.ofList, same, ih]

/-- The original source admission already requires distinct free names. -/
theorem snapshot_names_unique {snapshot :
    Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot}
    (admitted : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.checkFreeContext snapshot = true) :
    (snapshot.freeTypes.map Prod.fst).Nodup := by
  simp only [Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.checkFreeContext,
    Bool.and_eq_true, decide_eq_true_eq] at admitted
  exact admitted.1

theorem Parsed.typed_snapshot {snapshot :
    Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (parsed : Parsed snapshot.language snapshot.freeTypes bound source sort) :
    HasType snapshot.language snapshot.free bound source sort := by
  rw [snapshot_free_eq_ofList]
  exact parsed.typed

/-- Free-name admission comes from the same snapshot as the original rule
machine. No separate free-name inventory is installed by this decoder. -/
def parseSnapshot? (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) (site : RulePatternSite)
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) :
    Option (Parsed snapshot.language snapshot.freeTypes bound source sort) :=
  if Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.checkFreeContext snapshot then
    parse? snapshot.language rule spec site snapshot.freeTypes bound source sort
  else none

/-- A snapshot admitted by the complete original plan supplies the same
name uniqueness needed by inverse body typing. -/
theorem complete_snapshot_names_unique
    {snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot}
    {permissions : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Permissions}
    (admitted : (Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.compile
      snapshot permissions).complete = true) :
    (snapshot.freeTypes.map Prod.fst).Nodup :=
  snapshot_names_unique
    (Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.complete_snapshot_checks admitted).2.1

/-- The original finite metadata selects a stored runtime capture by its
actual declared name. The retained raw value includes its original indices. -/
structure SelectedCapture (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (entries : List (String × TypeExpr)) (ambient : List TypeExpr)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (index : Fin (metaArities (language := language) rule spec).length) where
  original : ContextualValue
  stored : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment
    (metaName rule spec index) = some original
  parsed : Captured language entries ((metaArities rule spec).get index).1 ambient
    original ((metaArities rule spec).get index).2

def selectCapture? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (entries : List (String × TypeExpr)) (ambient : List TypeExpr)
    (assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (index : Fin (metaArities (language := language) rule spec).length) :
    Option (SelectedCapture language rule spec entries ambient assignment index) :=
  match found : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment
      (metaName rule spec index) with
  | none => none
  | some original => do
      let parsed ← capture? language rule spec site entries
        ((metaArities rule spec).get index).1 ambient original
        ((metaArities rule spec).get index).2
      pure ⟨original, found, parsed⟩

/-- Checked source reconstruction reads the same original runtime value,
including for source type contexts with unused declarations. -/
theorem SelectedCapture.stored_readback {language : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec} {entries : List (String × TypeExpr)}
    {ambient : List TypeExpr}
    {assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    {index : Fin (metaArities (language := language) rule spec).length}
    (selected : SelectedCapture language rule spec entries ambient assignment index) :
    Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment
      (metaName rule spec index) = some selected.parsed.readValue := by
  rw [selected.parsed.readValue_eq]
  exact selected.stored

/-- No two differently indexed raw bodies are conflated by the finite
free-name closure representation at fixed source metadata. -/
theorem Captured.term_injective {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {left right : ContextualValue} {sort : TypeExpr}
    (first : Captured language entries dependencies ambient left sort)
    (second : Captured language entries dependencies ambient right sort)
    (same : first.body.term = second.body.term) : left = right := by
  rw [← first.readValue_eq, ← second.readValue_eq]
  simp only [Captured.readValue, same]

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

private def t : TypeExpr := .base "Term"
private def u : TypeExpr := .base "Name"
private def language : LanguageDef where
  name := "finite-named-source"
  types := [{ name := "Term" }, { name := "Name" }]
  terms := []
  equations := []
  rewrites := []
private def rule : RewriteRule where
  name := "body"
  typeContext := []
  premises := []
  left := .bvar 0
  right := .bvar 0
private def spec : RuleBindingSpec := { dependencies := [] }
private def entries : List (String × TypeExpr) := [("a", t)]
private def nested : Pattern := .lambda none (.subst (.fvar "a") (.bvar 0))
private def namedMetadata : Pattern := .lambda (some "shown") (.fvar "a")
private def capturedValue : ContextualValue where
  dependencies := [t]
  ambient := 1
  body := .subst (.fvar "a") (.bvar 0)

private def parses (context : List (String × TypeExpr)) (bound : List TypeExpr)
    (source : Pattern) (sort : TypeExpr) : Bool :=
  (parse? language rule spec .right context bound source sort).isSome

private def captured : Captured language entries [t] [u] capturedValue t :=
  (capture? language rule spec .right entries [t] [u] capturedValue t).get (by decide +kernel)

example : HasType language (FreeTypeContext.ofList entries) [t, u] capturedValue.body t :=
  captured.body.typed
example : captured.readValue = capturedValue := captured.readValue_eq

private def nestedParsed : Parsed language entries [] nested (.arrow t t) :=
  (parse? language rule spec .right entries [] nested (.arrow t t)).get (by decide +kernel)

example : HasType language (FreeTypeContext.ofList entries) [] nested (.arrow t t) :=
  nestedParsed.typed
example : NamedFreeContext.openContext 0 entries (erase nestedParsed.term) = nested :=
  nestedParsed.readback

private def checks : List (String × Bool) := [
  ("declared-free-name", parses entries [] (.fvar "a") t),
  ("full-arrow-free-type", parses [("f", .arrow t t)] [] (.fvar "f") (.arrow t t)),
  ("bound-and-named-subst", parses entries [t] (.subst (.fvar "a") (.bvar 0)) t),
  ("nested-lambda-subst-retained", parses entries [] nested (.arrow t t)),
  ("unknown-free-refuses", !(parses entries [] (.fvar "missing") t)),
  ("wrong-free-sort-refuses", !(parses [("a", u)] [] (.fvar "a") t)),
  ("out-of-scope-does-not-steal-free-slot", !(parses entries [] (.bvar 0) t)),
  ("duplicate-name-conflicting-sorts-refuses", !(parses [("a", t), ("a", u)] [] (.fvar "a") t)),
  ("duplicate-name-same-sort-refuses", !(parses [ ("a", t), ("a", t)] [] (.fvar "a") t)),
  ("unknown-bound-sort-refuses", !(parses entries [u] (.bvar 0) t)),
  ("bound-prefix-retained", parses entries [t] (.bvar 0) t),
  ("captured-metadata-exact", (capture? language rule spec .right entries [t] [u] capturedValue t).isSome),
  ("captured-dependencies-wrong-sort-refuses", (capture? language rule spec .right entries [u] [u] capturedValue t).isNone),
  ("captured-ambient-count-refuses", (capture? language rule spec .right entries [t] [] capturedValue t).isNone),
  ("raw-named-binder-spelling-retained", NamedFreeContext.openContext 0 entries
    (NamedFreeContext.closeContext 0 entries namedMetadata) == namedMetadata),
  ("parser-metadata-profile-is-explicit", !(parses entries [] namedMetadata (.arrow t t))),
  ("collection-rest-metadata-is-retained", NamedFreeContext.openContext 0 entries
    (NamedFreeContext.closeContext 0 entries (.collection .hashBag [.fvar "a"] (some "tail"))) ==
      .collection .hashBag [.fvar "a"] (some "tail")),
  ("nonvector-rest-not-claimed-by-parser", !(parses entries []
    (.collection .hashBag [.fvar "a"] (some "tail")) (.collection .hashBag t)))
]

#guard checks.all Prod.snd

def main : IO Unit := do
  for (label, okay) in checks do
    unless okay do throw <| IO.userError ("FAILED " ++ label)
  IO.println s!"{checks.length} named-source controls PASS"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies.Controls

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem position_index {S : Signature} {context : Ctx S} {sort : S.Srt}
    (position : Var context sort) : variableIndex position = (varIdx position).val := by
  induction position <;> simp_all [variableIndex, varIdx]

/-- A raw view of an actual typed substitution has scoped images at every
position it can read. No out-of-context default is admitted by this law. -/
theorem readsSub_scoped {language : LanguageDef} {source target : List TypeExpr}
    (action : Sub (signatureOf language) source target)
    (raw : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (reads : ReadsSub action raw) :
    WellScopedAssignment source.length target.length raw := by
  intro index inside
  let position : Fin source.length := ⟨index, inside⟩
  let sourceVariable := varOfIdx (S := signatureOf language) source position
  have observed := reads _ sourceVariable
  have same : variableIndex sourceVariable = index := by
    calc
      variableIndex sourceVariable = (varIdx (S := signatureOf language) sourceVariable).val :=
        position_index (S := signatureOf language) sourceVariable
      _ = index := congrArg Fin.val (varIdx_varOfIdx (S := signatureOf language) source position)
  rw [same] at observed
  rw [observed]
  exact erase_wellScoped (action _ sourceVariable)

/-- The checked body representation respects actual intrinsic simultaneous
substitution and reconstructs the original raw source action. -/
theorem Parsed.substitution_readback {language : LanguageDef}
    {entries : List (String × TypeExpr)} {source target : List TypeExpr}
    {pattern : Pattern} {sort : TypeExpr}
    (parsed : Parsed language entries source pattern sort)
    (action : Sub (signatureOf language)
      (source ++ NamedFreeContext.contextSorts entries)
      (target ++ NamedFreeContext.contextSorts entries))
    (actual original : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (reads : ReadsSub action actual)
    (images : ∀ index, index < source.length →
      NamedFreeContext.openContext target.length entries (actual index) = original index)
    (slots : ∀ position : Fin entries.length,
      actual (source.length + position.val) = .bvar (target.length + position.val)) :
    NamedFreeContext.openContext target.length entries (erase (bind action parsed.term)) =
      substitute original pattern := by
  rw [ScopedElaboration.erase_bind action actual reads, parsed.closed_readback]
  apply NamedFreeContext.closeNames_substitution_readback source.length target.length
    (entries.map Prod.fst) actual original pattern parsed.source_scope
  · simpa only [List.length_map, List.length_append, NamedFreeContext.contextSorts]
      using readsSub_scoped action actual reads
  · exact images
  · intro position
    exact slots ⟨position.val, by simpa only [List.length_map] using position.isLt⟩

/-- Restore the same finite names in an existing ordered dependency list. -/
def openedArguments (entries : List (String × TypeExpr)) (bound : List TypeExpr)
    (values : List Pattern) : List Pattern :=
  values.map (NamedFreeContext.openContext bound.length entries)

private theorem openedArguments_typed {language : LanguageDef}
    {entries : List (String × TypeExpr)} (unique : (entries.map Prod.fst).Nodup)
    {bound : List TypeExpr} {values : List Pattern} {sorts : List TypeExpr}
    (typed : List.Forall₂
      (HasType language FreeTypeContext.empty (bound ++ NamedFreeContext.contextSorts entries))
      values sorts) :
    List.Forall₂ (HasType language (FreeTypeContext.ofList entries) bound)
      (openedArguments entries bound values) sorts := by
  induction typed with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (NamedFreeContext.openContext_typed_of_nodup entries unique first) ih

private theorem typed_arguments_scoped {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {values : List Pattern} {sorts : List TypeExpr}
    (typed : List.Forall₂ (HasType language free bound) values sorts) :
    values.all (fun pattern => pattern.isWellScopedAt bound.length) = true := by
  induction typed with
  | nil => rfl
  | cons first _ ih =>
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨first.isWellScopedAt, ih⟩

/-- Source metadata keeps the original ambient count; the extra name slots
only occur in the intrinsic representation's outer ambient suffix. -/
def Captured.extendedBody {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort) :
    Term (signatureOf language) (dependencies ++ (ambient ++ NamedFreeContext.contextSorts entries)) sort :=
  castTermCtx (List.append_assoc dependencies ambient (NamedFreeContext.contextSorts entries))
    captured.body.term

/-- Invoke the same existing intrinsic occurrence action with its actual
sorted arguments and extended ambient suffix. -/
def Captured.occurrence {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient locals : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    Term (signatureOf language) (locals ++ (ambient ++ NamedFreeContext.contextSorts entries)) sort :=
  bind (occurrenceSubstitution arguments) captured.extendedBody

def Captured.occurrenceReadback {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient locals : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) : Pattern :=
  NamedFreeContext.openContext (locals ++ ambient).length entries (erase (captured.occurrence arguments))

/-- The operation result independently has the requested source sort after
exact finite free-name restoration. -/
theorem Captured.occurrence_typed {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient locals : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    HasType language (FreeTypeContext.ofList entries) (locals ++ ambient)
      (captured.occurrenceReadback arguments) sort := by
  apply NamedFreeContext.openContext_typed_of_nodup entries captured.body.names_unique
  simpa only [List.append_assoc] using erase_typed (captured.occurrence arguments)

private theorem occurrenceAssignment_open_names (dependencies ambient depth : Nat)
    (names : List String) (arguments : List Pattern) (count : arguments.length = dependencies)
    (index : Nat) (inside : index < dependencies + ambient) :
    NamedFreeContext.openNames (depth + ambient) names
        (occurrenceAssignment dependencies depth arguments index) =
      occurrenceAssignment dependencies depth
        (arguments.map (NamedFreeContext.openNames (depth + ambient) names)) index := by
  by_cases dependency : index < dependencies
  · have argumentIndex : index < arguments.length := by omega
    have present : arguments[index]? = some (arguments.get ⟨index, argumentIndex⟩) :=
      List.getElem?_eq_getElem argumentIndex
    simp only [occurrenceAssignment, if_pos dependency, List.getD_eq_getElem?_getD,
      List.getElem?_map, present, Option.getD_some, Option.map_some]
  · simp only [occurrenceAssignment, if_neg dependency]
    exact NamedFreeContext.openNames_before (depth + ambient) names _ (by omega)

/-- Every native-context occurrence, with the source dependency arguments
retained, reads back as the original raw occurrence substitution. -/
theorem Captured.occurrence_readback {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient locals : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    captured.occurrenceReadback arguments =
      substitute (occurrenceAssignment dependencies.length locals.length
        (openedArguments entries (locals ++ ambient) (eraseArguments arguments))) source.body := by
  have sourceRead : erase captured.extendedBody =
      NamedFreeContext.closeContext (dependencies ++ ambient).length entries source.body := by
    have castRead : ∀ {first second : List TypeExpr} (same : first = second)
        (term : Term (signatureOf language) first sort),
        erase (castTermCtx same term) = erase term := by
      intro first second same term
      cases same
      rfl
    exact (castRead _ captured.body.term).trans captured.body.closed_readback
  unfold Captured.occurrenceReadback Captured.occurrence
  rw [ScopedElaboration.erase_bind _ _ (occurrenceSubstitution_reads arguments), sourceRead]
  apply NamedFreeContext.closeNames_substitution_readback (dependencies ++ ambient).length
    (locals ++ ambient).length (entries.map Prod.fst) _ _ source.body captured.body.source_scope
  · simpa only [List.length_append, NamedFreeContext.contextSorts, List.length_map, Nat.add_assoc]
      using readsSub_scoped (occurrenceSubstitution arguments) _ (occurrenceSubstitution_reads arguments)
  · intro index inside
    simp only [List.length_append, openedArguments]
    change NamedFreeContext.openNames (locals.length + ambient.length) (entries.map Prod.fst)
      (occurrenceAssignment dependencies.length locals.length (eraseArguments arguments) index) =
      occurrenceAssignment dependencies.length locals.length
        ((eraseArguments arguments).map
          (NamedFreeContext.openNames (locals.length + ambient.length) (entries.map Prod.fst))) index
    exact occurrenceAssignment_open_names dependencies.length ambient.length locals.length
        (entries.map Prod.fst) (eraseArguments arguments)
        (eraseDependencyArguments_length arguments) index
        (by simpa only [List.length_append] using inside)
  · intro position
    have later : ¬ (dependencies ++ ambient).length + position.val < dependencies.length := by
      simp only [List.length_append]
      omega
    simp only [occurrenceAssignment]
    rw [if_neg later]
    simp only [List.length_append]
    congr 1
    omega

/-- The original executable interpreter accepts exactly this captured
source instance with the reconstructed argument list and computed result. -/
theorem Captured.instantiateValue?_occurrence {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient locals : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    instantiateValue? source ambient.length locals.length
      (openedArguments entries (locals ++ ambient) (eraseArguments arguments)) =
        some (captured.occurrenceReadback arguments) := by
  have argumentCount :
      (openedArguments entries (locals ++ ambient) (eraseArguments arguments)).length = dependencies.length := by
    simp only [openedArguments, List.length_map, eraseDependencyArguments_length]
  have argumentTyping := openedArguments_typed (bound := locals ++ ambient)
    captured.body.names_unique
    (by simpa only [List.append_assoc] using dependency_arguments_typed arguments)
  have argumentScope := typed_arguments_scoped argumentTyping
  have bodyScope : source.body.isWellScopedAt (dependencies.length + ambient.length) = true := by
    simpa only [List.length_append] using captured.body.source_scope
  have resultScope :
      (substitute (occurrenceAssignment dependencies.length locals.length
        (openedArguments entries (locals ++ ambient) (eraseArguments arguments))) source.body).isWellScopedAt
          (locals.length + ambient.length) = true := by
    rw [← captured.occurrence_readback arguments]
    simpa only [List.length_append] using (captured.occurrence_typed arguments).isWellScopedAt
  simp only [List.length_append] at argumentScope
  simp [instantiateValue?, captured.dependencies_eq, captured.ambient_eq, argumentCount,
    bodyScope, argumentScope, resultScope]
  exact (captured.occurrence_readback arguments).symm

/-- At the original public occurrence observation, no other result is
introduced by executing a checked captured body. -/
theorem Captured.instantiateValue?_occurrence_iff {language : LanguageDef}
    {entries : List (String × TypeExpr)} {dependencies ambient locals : List TypeExpr}
    {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort)
    (arguments : DependencyArguments (language := language) dependencies
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) (result : Pattern) :
    instantiateValue? source ambient.length locals.length
        (openedArguments entries (locals ++ ambient) (eraseArguments arguments)) = some result ↔
      captured.occurrenceReadback arguments = result := by
  rw [captured.instantiateValue?_occurrence arguments, Option.some.injEq]

/-- The actual runtime lookup at the original declaration name feeds the
original captured-value interpreter, preserving its selected source value. -/
theorem SelectedCapture.instantiateValue?_stored {language : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec} {entries : List (String × TypeExpr)}
    {ambient locals : List TypeExpr}
    {assignment : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    {index : Fin (metaArities (language := language) rule spec).length}
    (selected : SelectedCapture language rule spec entries ambient assignment index)
    (arguments : DependencyArguments (language := language)
      ((metaArities rule spec).get index).1
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    (Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup assignment (metaName rule spec index)).bind
        (fun value => instantiateValue? value ambient.length locals.length
          (openedArguments entries (locals ++ ambient) (eraseArguments arguments))) =
      some (selected.parsed.occurrenceReadback arguments) := by
  rw [selected.stored, Option.bind_some]
  exact selected.parsed.instantiateValue?_occurrence arguments

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies.OperationControls
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

private def t : TypeExpr := .base "Term"
private def language : LanguageDef where
  name := "finite-named-operation"
  types := [{ name := "Term" }]
  terms := []
  equations := []
  rewrites := []
private def rule : RewriteRule where
  name := "body-operation"
  typeContext := [("B", t), ("unused", t)]
  premises := []
  left := .fvar "B"
  right := .fvar "B"
private def spec : RuleBindingSpec where
  dependencies := [("B", [t]), ("unused", [])]
private def entries : List (String × TypeExpr) := [("a", t), ("b", t)]
private def source : ContextualValue := ⟨[t], 1, .subst (.fvar "a") (.bvar 0)⟩
private def nestedSource : ContextualValue :=
  ⟨[t], 1, .lambda none (.subst (.bvar 2) (.fvar "a"))⟩
private def ambientSource : ContextualValue := ⟨[t], 1, .bvar 1⟩
private def zeroSource : ContextualValue := ⟨[], 1, .fvar "a"⟩
private def captured : Captured language entries [t] [t] source t :=
  (capture? language rule spec .right entries [t] [t] source t).get (by decide +kernel)
private def nestedCaptured : Captured language entries [t] [t] nestedSource (.arrow t t) :=
  (capture? language rule spec .right entries [t] [t] nestedSource (.arrow t t)).get (by decide +kernel)
private def ambientCaptured : Captured language entries [t] [t] ambientSource t :=
  (capture? language rule spec .right entries [t] [t] ambientSource t).get (by decide +kernel)
private def zeroCaptured : Captured language entries [] [t] zeroSource t :=
  (capture? language rule spec .right entries [] [t] zeroSource t).get (by decide +kernel)

private def localArgument : DependencyArguments (language := language) [t]
    ([t] ++ ([t] ++ NamedFreeContext.contextSorts entries)) := .cons (.var .zero) .nil
private def namedArgument : DependencyArguments (language := language) [t]
    ([t] ++ ([t] ++ NamedFreeContext.contextSorts entries)) :=
  .cons (.var (.succ (.succ (.succ .zero)))) .nil
private def noArguments : DependencyArguments (language := language) []
    ([t] ++ ([t] ++ NamedFreeContext.contextSorts entries)) := .nil

example : instantiateValue? source 1 1 [.bvar 0] =
    some (captured.occurrenceReadback localArgument) := by
  convert captured.instantiateValue?_occurrence localArgument using 1
  decide +kernel
example : instantiateValue? source 1 1 [.fvar "b"] =
    some (captured.occurrenceReadback namedArgument) := by
  convert captured.instantiateValue?_occurrence namedArgument using 1
  decide +kernel
example : instantiateValue? nestedSource 1 1 [.fvar "b"] =
    some (nestedCaptured.occurrenceReadback namedArgument) := by
  convert nestedCaptured.instantiateValue?_occurrence namedArgument using 1
  decide +kernel
example : HasType language (FreeTypeContext.ofList entries) [t, t]
    (nestedCaptured.occurrenceReadback namedArgument) (.arrow t t) :=
  nestedCaptured.occurrence_typed namedArgument

private def raw : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment := [("B", source)]
private def first : Fin (metaArities (language := language) rule spec).length := ⟨0, by decide⟩
private def unused : Fin (metaArities (language := language) rule spec).length := ⟨1, by decide⟩
private def selected : SelectedCapture language rule spec entries [t] raw first :=
  (selectCapture? language rule spec .right entries [t] raw first).get (by decide +kernel)

example : (Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup raw "B").bind
    (fun value => instantiateValue? value 1 1 [.fvar "b"]) =
    some (selected.parsed.occurrenceReadback namedArgument) := by
  convert selected.instantiateValue?_stored namedArgument using 1
  decide +kernel

/-- A well-typed map may still swap the two external name slots. -/
private def swappedNames : Sub (signatureOf language) [t, t, t, t] [t, t, t, t] :=
  fun _ position => match position with
    | .zero => .var .zero
    | .succ .zero => .var (.succ .zero)
    | .succ (.succ .zero) => .var (.succ (.succ (.succ .zero)))
    | .succ (.succ (.succ .zero)) => .var (.succ (.succ .zero))
    | .succ (.succ (.succ (.succ impossible))) => nomatch impossible
private def swappedReadback : Pattern :=
  NamedFreeContext.openContext 2 entries (erase (bind swappedNames captured.body.term))

private def checks : List (String × Bool) := [
  ("original-argument-source-order", openedArguments entries [t, t] (eraseArguments localArgument) == [.bvar 0]),
  ("named-argument-source-readback", openedArguments entries [t, t] (eraseArguments namedArgument) == [.fvar "b"]),
  ("actual-original-local-run", instantiateValue? source 1 1 [.bvar 0] == some (captured.occurrenceReadback localArgument)),
  ("actual-original-named-run", instantiateValue? source 1 1 [.fvar "b"] == some (captured.occurrenceReadback namedArgument)),
  ("local-result-exact", captured.occurrenceReadback localArgument == .subst (.fvar "a") (.bvar 0)),
  ("named-result-exact", captured.occurrenceReadback namedArgument == .subst (.fvar "a") (.fvar "b")),
  ("raw-substitution-is-retained", captured.occurrenceReadback namedArgument != .fvar "a"),
  ("changing-arguments-changes-readback", captured.occurrenceReadback localArgument != captured.occurrenceReadback namedArgument),
  ("nested-capture-avoiding-result", nestedCaptured.occurrenceReadback namedArgument ==
    .lambda none (.subst (.fvar "b") (.fvar "a"))),
  ("nested-original-run", instantiateValue? nestedSource 1 1 [.fvar "b"] ==
    some (nestedCaptured.occurrenceReadback namedArgument)),
  ("ambient-is-not-dependency", ambientCaptured.occurrenceReadback namedArgument == .bvar 1),
  ("zero-dependency-retains-free-ambient", zeroCaptured.occurrenceReadback noArguments == .fvar "a"),
  ("zero-dependency-original-run", instantiateValue? zeroSource 1 1 [] == some (zeroCaptured.occurrenceReadback noArguments)),
  ("missing-dependency-refuses", (instantiateValue? source 1 1 []).isNone),
  ("extra-dependency-refuses", (instantiateValue? source 1 1 [.bvar 0, .bvar 0]).isNone),
  ("wrong-original-ambient-refuses", (instantiateValue? source 0 1 [.bvar 0]).isNone),
  ("out-of-scope-argument-refuses", (instantiateValue? source 1 1 [.bvar 2]).isNone),
  ("declared-selected-source-lookup", selected.original == source),
  ("unused-declaration-not-fabricated", (selectCapture? language rule spec .right entries [t] raw unused).isNone),
  ("stored-native-source-call", (Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup raw "B").bind
      (fun value => instantiateValue? value 1 1 [.fvar "b"]) ==
      some (selected.parsed.occurrenceReadback namedArgument)),
  ("typed-name-swap-really-changes-result", swappedReadback == .subst (.fvar "b") (.bvar 0)),
  ("typed-map-does-not-authorize-name-swap", instantiateValue? source 1 1 [.bvar 0] != some swappedReadback)
]

#guard checks.all Prod.snd

def main : IO Unit := do
  for (label, okay) in checks do
    unless okay do throw <| IO.userError ("FAILED " ++ label)
  IO.println s!"{checks.length} named source-operation controls PASS"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies.OperationControls



namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

/-- Explicit finite source evidence retains its exact original operator,
sort, binding arity and declaration descriptors, as well as the raw body. -/
structure EvidenceParsed (language : LanguageDef) (entries : List (String × TypeExpr))
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) (evidence : Data)
    extends Parsed language entries bound source sort where
  encoded : (Wire.termCodec language (bound ++ NamedFreeContext.contextSorts entries) sort).put term = evidence

/-- The automatic source parser is optional. An explicit original binding
term is also checked against its actual closed raw body and finite names. -/
def parseEvidence? (language : LanguageDef) (entries : List (String × TypeExpr))
    (bound : List TypeExpr) (source : Pattern) (sort : TypeExpr) (evidence : Data) :
    Option (EvidenceParsed language entries bound source sort evidence) :=
  match decoded : (Wire.termCodec language (bound ++ NamedFreeContext.contextSorts entries) sort).canonicalGet evidence with
  | none => none
  | some term =>
      if unique : (entries.map Prod.fst).Nodup then
        if scopeProof : source.isWellScopedAt bound.length = true then
          if sourceRead : erase term = NamedFreeContext.closeContext bound.length entries source then
            some {
              term := term
              closed_readback := sourceRead
              source_scope := scopeProof
              names_unique := unique
              encoded := Codec.put_of_canonicalGet _ _ _ decoded }
          else none
        else none
      else none

/-- Every actual represented body has finite explicit evidence. This
includes source operators beyond the automatic parser's search profile. -/
theorem parseEvidence?_put {language : LanguageDef} {entries : List (String × TypeExpr)}
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (parsed : Parsed language entries bound source sort) :
    parseEvidence? language entries bound source sort
      ((Wire.termCodec language (bound ++ NamedFreeContext.contextSorts entries) sort).put parsed.term) =
        some { toParsed := parsed, encoded := rfl } := by
  unfold parseEvidence?
  split
  · rename_i decoded
    have accepted := Codec.canonicalGet_put
      (Wire.termCodec language (bound ++ NamedFreeContext.contextSorts entries) sort) parsed.term
    rw [decoded] at accepted
    cases accepted
  · rename_i term decoded
    have accepted := Codec.canonicalGet_put
      (Wire.termCodec language (bound ++ NamedFreeContext.contextSorts entries) sort) parsed.term
    have same : term = parsed.term := Option.some.inj (decoded.symm.trans accepted)
    cases same
    simp only [parsed.names_unique, parsed.source_scope, parsed.closed_readback, dite_true]


/-- Original capture metadata and explicit source evidence are checked
independently. The packet retains both the actual intrinsic body and code. -/
structure EvidenceCaptured (language : LanguageDef) (entries : List (String × TypeExpr))
    (dependencies ambient : List TypeExpr) (source : ContextualValue) (sort : TypeExpr)
    (evidence : Data) extends Captured language entries dependencies ambient source sort where
  encoded : (Wire.termCodec language
    ((dependencies ++ ambient) ++ NamedFreeContext.contextSorts entries) sort).put body.term = evidence

def captureEvidence? (language : LanguageDef) (entries : List (String × TypeExpr))
    (dependencies ambient : List TypeExpr) (source : ContextualValue) (sort : TypeExpr)
    (evidence : Data) : Option (EvidenceCaptured language entries dependencies ambient source sort evidence) :=
  if dependenciesEq : source.dependencies = dependencies then
    if ambientEq : source.ambient = ambient.length then do
      let body ← parseEvidence? language entries (dependencies ++ ambient) source.body sort evidence
      pure {
        body := body.toParsed
        dependencies_eq := dependenciesEq
        ambient_eq := ambientEq
        encoded := body.encoded }
    else none
  else none

/-- Every represented original contextual value has finite source evidence;
its dependency types and ambient length are not guessed from body erasure. -/
theorem captureEvidence?_put {language : LanguageDef} {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort) :
    captureEvidence? language entries dependencies ambient source sort
      ((Wire.termCodec language ((dependencies ++ ambient) ++ NamedFreeContext.contextSorts entries)
        sort).put captured.body.term) = some { toCaptured := captured, encoded := rfl } := by
  unfold captureEvidence?
  simp only [captured.dependencies_eq, captured.ambient_eq, dite_true,
    parseEvidence?_put, Bind.bind, Option.bind, pure]

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies



namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Every original well-sorted open object has an exactly represented body
over its admitted finite free-name context. This derives representation from
the original source judgment, not from the automatic parser's profile. -/
theorem Parsed.exists_of_openTyped {language : LanguageDef}
    {entries : List (String × TypeExpr)} {bound : List TypeExpr}
    {source : Pattern} {sort : TypeExpr}
    (unique : (entries.map Prod.fst).Nodup)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList entries) bound sort source) :
    Nonempty (Parsed language entries bound source sort) := by
  have closedTyped := NamedFreeContext.closeContext_typed entries typed.1
  have closedCanonical :
      (NamedFreeContext.closeContext bound.length entries source).hasCanonicalBinderMetadata = true :=
    (NamedFreeContext.closeNames_metadata bound.length (entries.map Prod.fst) source).trans typed.2.1
  have closedObject : isObjectPattern (NamedFreeContext.closeContext bound.length entries source) = true :=
    (NamedFreeContext.closeNames_object bound.length (entries.map Prod.fst) source).trans typed.2.2.1
  obtain ⟨term, readback⟩ := typedObject_exists closedTyped closedCanonical closedObject
  exact ⟨⟨term, readback, typed.2.2.2, unique⟩⟩

/-- The runnable explicit-evidence checker is complete for the independently
stated source object judgment, including arbitrary binding headers and all
collection kinds. Its finite evidence retains the real constructor rows. -/
theorem parseEvidence?_complete {language : LanguageDef}
    {entries : List (String × TypeExpr)} {bound : List TypeExpr}
    {source : Pattern} {sort : TypeExpr}
    (unique : (entries.map Prod.fst).Nodup)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList entries) bound sort source) :
    ∃ (evidence : Data) (parsed : EvidenceParsed language entries bound source sort evidence),
      parseEvidence? language entries bound source sort evidence = some parsed := by
  obtain ⟨parsed⟩ := Parsed.exists_of_openTyped unique typed
  exact ⟨_, { toParsed := parsed, encoded := rfl }, parseEvidence?_put parsed⟩

/-- Source typing, the original ambient count and dependency types earn
finite accepted contextual evidence without any body-inference assumption. -/
theorem captureEvidence?_complete {language : LanguageDef}
    {entries : List (String × TypeExpr)} {dependencies ambient : List TypeExpr}
    {source : ContextualValue} {sort : TypeExpr}
    (unique : (entries.map Prod.fst).Nodup)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList entries)
      (dependencies ++ ambient) sort source.body)
    (dependenciesEq : source.dependencies = dependencies)
    (ambientEq : source.ambient = ambient.length) :
    ∃ (evidence : Data) (captured : EvidenceCaptured language entries dependencies ambient source sort evidence),
      captureEvidence? language entries dependencies ambient source sort evidence = some captured := by
  obtain ⟨body⟩ := Parsed.exists_of_openTyped unique typed
  let captured : Captured language entries dependencies ambient source sort :=
    ⟨body, dependenciesEq, ambientEq⟩
  exact ⟨_, { toCaptured := captured, encoded := rfl }, captureEvidence?_put captured⟩


/-- On the original canonical object profile, finite accepted wire evidence
exists exactly when the original source object judgment holds. -/
theorem parseEvidence?_exists_iff_openTyped {language : LanguageDef}
    {entries : List (String × TypeExpr)} {bound : List TypeExpr}
    {source : Pattern} {sort : TypeExpr}
    (unique : (entries.map Prod.fst).Nodup)
    (canonical : source.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern source = true) :
    (∃ evidence, (parseEvidence? language entries bound source sort evidence).isSome = true) ↔
      OpenPatternWellSorted language (FreeTypeContext.ofList entries) bound sort source := by
  constructor
  · rintro ⟨evidence, accepted⟩
    cases decoded : parseEvidence? language entries bound source sort evidence with
    | none => simp only [decoded, Option.isSome_none, Bool.false_eq_true] at accepted
    | some parsed => exact ⟨parsed.toParsed.typed, canonical, object, parsed.source_scope⟩
  · intro typed
    obtain ⟨evidence, parsed, decoded⟩ := parseEvidence?_complete unique typed
    exact ⟨evidence, by rw [decoded]; rfl⟩

/-- The same coverage theorem uses the original snapshot's admitted names
and actual first-match free typing context. -/
theorem parseEvidence?_snapshot_complete
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (admitted : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.checkFreeContext snapshot = true)
    {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (typed : OpenPatternWellSorted snapshot.language snapshot.free bound sort source) :
    ∃ evidence, (parseEvidence? snapshot.language snapshot.freeTypes bound source sort evidence).isSome = true := by
  rw [snapshot_free_eq_ofList] at typed
  exact (parseEvidence?_exists_iff_openTyped (snapshot_names_unique admitted)
    typed.2.1 typed.2.2.1).mpr typed
end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies

#print axioms Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.InputRecovery.recovered_body_of_instance
#print axioms Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.InputRecovery.recoverValue?_typed_instance
