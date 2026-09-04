import Mettapedia.Languages.OpenTheory.CoreTerm
import Mettapedia.Languages.OpenTheory.Substitution

/-!
# Canonical binding operations for OpenTheory terms

This module isolates the de Bruijn operations needed by OpenTheory's
primitive `abs` and `betaConv` rules.  Free typed variables and bound indices
remain distinct:

* `closeFreeAt` turns occurrences of one exact typed free variable into the
  binder at a specified depth;
* `instantiateAt` replaces one binder by a closed canonical term;
* both operations have direct type-preservation theorems.

The operations are stated independently of theorem construction.  In
particular, `closeFreeAt` does not impose the `abs` rule's freshness condition
on hypotheses; that belongs to the inference rule using this syntax.
-/

namespace Mettapedia.Languages.OpenTheory

namespace DBTerm

/-! ## Exact free-variable occurrence -/

/-- A structural occurrence of one exact typed free variable. -/
inductive FreeOccurrence (needle : SourceVar) : DBTerm → Prop where
  | here : FreeOccurrence needle (.free needle)
  | appFunction : FreeOccurrence needle function →
      FreeOccurrence needle (.app function argument)
  | appArgument : FreeOccurrence needle argument →
      FreeOccurrence needle (.app function argument)
  | absBody : FreeOccurrence needle body →
      FreeOccurrence needle (.abs domain body)

/-- Executable recognition of exact typed free-variable occurrence. -/
def hasFree (needle : SourceVar) : DBTerm → Bool
  | .const _ _ => false
  | .free sourceVar => sourceVarSame needle sourceVar
  | .bound _ => false
  | .app function argument =>
      hasFree needle function || hasFree needle argument
  | .abs _ body => hasFree needle body
termination_by term => sizeOf term

/-- The executable occurrence test is exact. -/
theorem hasFree_eq_true_iff (needle : SourceVar) (term : DBTerm) :
    hasFree needle term = true ↔ FreeOccurrence needle term := by
  induction term with
  | const constant ty =>
      constructor
      · intro impossible
        simp [hasFree] at impossible
      · intro occurrence
        cases occurrence
  | free sourceVar =>
      constructor
      · intro hsame
        simp only [hasFree] at hsame
        have equality := (sourceVarSame_eq_true_iff needle sourceVar).mp hsame
        subst sourceVar
        exact FreeOccurrence.here
      · intro occurrence
        cases occurrence
        simp only [hasFree]
        exact (sourceVarSame_eq_true_iff needle needle).mpr rfl
  | bound index =>
      constructor
      · intro impossible
        simp [hasFree] at impossible
      · intro occurrence
        cases occurrence
  | app function argument functionIH argumentIH =>
      constructor
      · intro hoccurs
        rw [hasFree, Bool.or_eq_true, functionIH, argumentIH] at hoccurs
        exact hoccurs.elim FreeOccurrence.appFunction
          FreeOccurrence.appArgument
      · intro occurrence
        cases occurrence with
        | appFunction found =>
            simp [hasFree, functionIH, argumentIH, found]
        | appArgument found =>
            simp [hasFree, functionIH, argumentIH, found]
  | abs domain body bodyIH =>
      constructor
      · intro hoccurs
        simp only [hasFree] at hoccurs
        exact FreeOccurrence.absBody (bodyIH.mp hoccurs)
      · intro occurrence
        cases occurrence with
        | absBody found =>
            simp only [hasFree]
            exact bodyIH.mpr found

/-! ## Closing one free variable -/

/--
Replace one exact typed free variable by the binder at `depth`.  Entering a
lambda increments the depth, so unrelated binders retain their indices.
-/
def closeFreeAt (needle : SourceVar) (depth : Nat) : DBTerm → DBTerm
  | .const constant ty => .const constant ty
  | .free sourceVar =>
      if sourceVarSame needle sourceVar then .bound depth else .free sourceVar
  | .bound index => .bound index
  | .app function argument =>
      .app (closeFreeAt needle depth function)
        (closeFreeAt needle depth argument)
  | .abs domain body => .abs domain (closeFreeAt needle (depth + 1) body)
termination_by term => sizeOf term

@[simp] theorem closeFreeAt_exact (needle : SourceVar) (depth : Nat) :
    closeFreeAt needle depth (.free needle) = .bound depth := by
  simp [closeFreeAt]

theorem closeFreeAt_other (needle sourceVar : SourceVar) (depth : Nat)
    (different : needle ≠ sourceVar) :
    closeFreeAt needle depth (.free sourceVar) = .free sourceVar := by
  simp [closeFreeAt, different]

/--
Closing a free variable appends its type after all already-active binders.
This general form is what makes the abstraction case compose under nested
lambdas.
-/
theorem inferType_closeFreeAt
    (needle : SourceVar) (term : DBTerm) (context : List Ty) {ty : Ty}
    (checked : term.inferType context = some ty) :
    (closeFreeAt needle context.length term).inferType
        (context ++ [needle.ty]) = some ty := by
  induction term generalizing context ty with
  | const constant annotation =>
      simp only [inferType] at checked
      simp only [closeFreeAt, inferType] at ⊢
      exact checked
  | free sourceVar =>
      simp only [inferType] at checked
      have typeEquality : sourceVar.ty = ty := Option.some.inj checked
      subst ty
      by_cases same : needle = sourceVar
      · subst sourceVar
        simp
      · simp [closeFreeAt, same]
  | bound index =>
      simp only [inferType] at checked
      simp only [closeFreeAt, inferType]
      obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp checked
      rw [List.getElem?_append_left inRange]
      exact checked
  | app function argument functionIH argumentIH =>
      simp only [inferType] at checked
      simp only [closeFreeAt, inferType]
      cases functionTypeEq : function.inferType context with
      | none => simp [functionTypeEq] at checked
      | some functionType =>
          cases argumentTypeEq : argument.inferType context with
          | none => simp [functionTypeEq, argumentTypeEq] at checked
          | some argumentType =>
              have functionChecked := functionIH context functionTypeEq
              have argumentChecked := argumentIH context argumentTypeEq
              simpa [functionTypeEq, argumentTypeEq, functionChecked,
                argumentChecked] using checked
  | abs domain body bodyIH =>
      simp only [inferType] at checked
      simp only [closeFreeAt, inferType]
      cases bodyTypeEq : body.inferType (domain :: context) with
      | none => simp [bodyTypeEq] at checked
      | some codomain =>
          have resultType : Ty.function domain codomain = ty := by
            simpa [bodyTypeEq] using checked
          subst ty
          have bodyChecked := bodyIH (domain :: context) bodyTypeEq
          have bodyChecked' :
              (closeFreeAt needle (context.length + 1) body).inferType
                  (domain :: (context ++ [needle.ty])) =
                some codomain := by
            simpa using bodyChecked
          rw [bodyChecked']
          rfl

/-! ## Instantiating one binder by a closed term -/

/--
Replace the binder at `depth` by `replacement`.  This operation is used only
with a closed, checked replacement.  Indices greater than `depth` are left
unchanged: for a well-typed closed beta body there are no such dangling
indices, because the discharged binder is the outermost entry in the active
context.
-/
def instantiateAt (replacement : DBTerm) (depth : Nat) : DBTerm → DBTerm
  | .const constant ty => .const constant ty
  | .free sourceVar => .free sourceVar
  | .bound index => if index = depth then replacement else .bound index
  | .app function argument =>
      .app (instantiateAt replacement depth function)
        (instantiateAt replacement depth argument)
  | .abs domain body =>
      .abs domain (instantiateAt replacement (depth + 1) body)
termination_by term => sizeOf term

@[simp] theorem instantiateAt_target (replacement : DBTerm) (depth : Nat) :
    instantiateAt replacement depth (.bound depth) = replacement := by
  simp [instantiateAt]

theorem instantiateAt_other (replacement : DBTerm) (depth index : Nat)
    (different : index ≠ depth) :
    instantiateAt replacement depth (.bound index) = .bound index := by
  simp [instantiateAt, different]

/--
Substituting a closed term for the final entry of a binder context preserves
typing and removes exactly that context entry.
-/
theorem inferType_instantiateAt
    (replacement term : DBTerm) (targetTy : Ty)
    (replacementChecked : replacement.inferType [] = some targetTy)
    (context : List Ty) {ty : Ty}
    (checked : term.inferType (context ++ [targetTy]) = some ty) :
    (instantiateAt replacement context.length term).inferType context = some ty := by
  induction term generalizing context ty with
  | const constant annotation =>
      simp only [inferType] at checked
      simp only [instantiateAt, inferType] at ⊢
      exact checked
  | free sourceVar =>
      simp only [inferType] at checked
      simp only [instantiateAt, inferType] at ⊢
      exact checked
  | bound index =>
      simp only [inferType] at checked ⊢
      by_cases target : index = context.length
      · subst index
        rw [List.getElem?_concat_length] at checked
        have typeEquality : targetTy = ty := Option.some.inj checked
        subst ty
        simp only [instantiateAt]
        exact DBTerm.inferType_weaken_empty replacementChecked context
      · have inExtendedRange : index < (context ++ [targetTy]).length :=
          (List.getElem?_eq_some_iff.mp checked).1
        have inContext : index < context.length := by
          simp only [List.length_append, List.length_singleton] at inExtendedRange
          omega
        simp only [instantiateAt, if_neg target, inferType]
        rw [← checked, List.getElem?_append_left inContext]
  | app function argument functionIH argumentIH =>
      simp only [inferType] at checked
      simp only [instantiateAt, inferType]
      cases functionTypeEq : function.inferType (context ++ [targetTy]) with
      | none => simp [functionTypeEq] at checked
      | some functionType =>
          cases argumentTypeEq : argument.inferType (context ++ [targetTy]) with
          | none => simp [functionTypeEq, argumentTypeEq] at checked
          | some argumentType =>
              have functionChecked := functionIH context functionTypeEq
              have argumentChecked := argumentIH context argumentTypeEq
              simpa [functionTypeEq, argumentTypeEq, functionChecked,
                argumentChecked] using checked
  | abs domain body bodyIH =>
      simp only [inferType] at checked
      simp only [instantiateAt, inferType]
      cases bodyTypeEq : body.inferType (domain :: (context ++ [targetTy])) with
      | none => simp [bodyTypeEq] at checked
      | some codomain =>
          have resultType : Ty.function domain codomain = ty := by
            simpa [bodyTypeEq] using checked
          subst ty
          have bodyTypeEq' :
              body.inferType ((domain :: context) ++ [targetTy]) =
                some codomain := by
            simpa using bodyTypeEq
          have bodyChecked := bodyIH (domain :: context) bodyTypeEq'
          have bodyChecked' :
              (instantiateAt replacement (context.length + 1) body).inferType
                  (domain :: context) =
                some codomain := by
            simpa using bodyChecked
          rw [bodyChecked']
          rfl

end DBTerm

namespace CanonicalTerm

/-! ## Checked wrappers -/

/-- Bind one exact typed free variable in a checked canonical term. -/
def abstractFree (sourceVar : SourceVar) (body : CanonicalTerm) : CanonicalTerm :=
  ⟨.abs sourceVar.ty (DBTerm.closeFreeAt sourceVar 0 body.term),
    .function sourceVar.ty body.ty, by
      simp only [DBTerm.inferType]
      have bodyChecked :=
        DBTerm.inferType_closeFreeAt sourceVar body.term [] body.checked
      have bodyChecked' :
          DBTerm.inferType [sourceVar.ty]
              (DBTerm.closeFreeAt sourceVar 0 body.term) = some body.ty := by
        simpa using bodyChecked
      simp [bodyChecked']⟩

/-- Independent graph of checked abstraction. -/
def AbstractionSemantics
    (sourceVar : SourceVar) (body abstraction : CanonicalTerm) : Prop :=
  abstraction.term =
    .abs sourceVar.ty (DBTerm.closeFreeAt sourceVar 0 body.term)

theorem abstractFree_eq_iff
    (sourceVar : SourceVar) (body abstraction : CanonicalTerm) :
    body.abstractFree sourceVar = abstraction ↔
      AbstractionSemantics sourceVar body abstraction := by
  constructor
  · intro equality
    rw [← equality]
    rfl
  · intro semantics
    apply CanonicalTerm.ext_term
    exact semantics.symm

/-- Structural abstraction semantics determines its checked result uniquely. -/
@[simp] theorem abstractionSemantics_iff_eq
    (sourceVar : SourceVar) (body abstraction : CanonicalTerm) :
    AbstractionSemantics sourceVar body abstraction ↔
      abstraction = body.abstractFree sourceVar := by
  rw [← abstractFree_eq_iff]
  exact eq_comm

/-- Recognize and contract one canonical beta redex. -/
def betaReduce? (whole : CanonicalTerm) : Option CanonicalTerm :=
  match whole.term with
  | .app (.abs _ body) argumentDB => do
      let argument ← CanonicalTerm.ofDB? argumentDB
      CanonicalTerm.ofDB? (DBTerm.instantiateAt argument.term 0 body)
  | _ => none

/-- Independent structural graph of one root beta contraction. -/
def BetaReductionSemantics
    (whole reduced : CanonicalTerm) : Prop :=
  ∃ (domain : Ty) (body : DBTerm) (argument : CanonicalTerm),
    whole.term = .app (.abs domain body) argument.term ∧
      reduced.term = DBTerm.instantiateAt argument.term 0 body

/-- Root beta recognition and contraction is exactly its structural graph. -/
theorem betaReduce?_eq_some_iff
    (whole reduced : CanonicalTerm) :
    whole.betaReduce? = some reduced ↔
      BetaReductionSemantics whole reduced := by
  constructor
  · intro accepted
    unfold betaReduce? at accepted
    cases shape : whole.term <;> simp [shape] at accepted
    rename_i functionDB argumentDB
    cases functionShape : functionDB <;>
      simp [functionShape] at accepted
    rename_i domain body
    cases argumentResult : CanonicalTerm.ofDB? argumentDB with
    | none => simp [argumentResult] at accepted
    | some argument =>
        cases reducedResult : CanonicalTerm.ofDB?
            (DBTerm.instantiateAt argument.term 0 body) with
        | none => simp [argumentResult, reducedResult] at accepted
        | some candidate =>
            simp [argumentResult, reducedResult] at accepted
            subst candidate
            exact ⟨domain, body, argument, by
              simpa [shape, functionShape] using
                (CanonicalTerm.ofDB?_eq_some_iff argumentDB argument).mp
                  argumentResult |>.symm,
              (CanonicalTerm.ofDB?_eq_some_iff _ reduced).mp reducedResult⟩
  · rintro ⟨domain, body, argument, wholeShape, reducedShape⟩
    unfold betaReduce?
    rw [wholeShape]
    simp only
    rw [CanonicalTerm.ofDB?_term]
    apply (CanonicalTerm.ofDB?_eq_some_iff _ _).mpr
    exact reducedShape

/-- Every checked root beta redex has a checked contractum of the same type. -/
theorem betaReduce?_isSome_of_shape
    (whole : CanonicalTerm) {domain : Ty} {body argument : DBTerm}
    (shape : whole.term = .app (.abs domain body) argument) :
    whole.betaReduce?.isSome = true := by
  have wholeChecked := whole.checked
  rw [shape] at wholeChecked
  simp only [DBTerm.inferType] at wholeChecked
  cases bodyTypeEq : body.inferType [domain] with
  | none => simp [bodyTypeEq] at wholeChecked
  | some codomain =>
      cases argumentTypeEq : argument.inferType [] with
      | none => simp [bodyTypeEq, argumentTypeEq] at wholeChecked
      | some argumentTy =>
          have domainMatch : Ty.same domain argumentTy = true := by
            have normalized :
                (if Ty.same domain argumentTy then some codomain else none) =
                  some whole.ty := by
              simpa [bodyTypeEq, argumentTypeEq] using wholeChecked
            by_cases same : Ty.same domain argumentTy = true
            · exact same
            · simp [same] at normalized
          have argumentTyEq : argumentTy = domain :=
            (Ty.same_eq_true_iff domain argumentTy).mp domainMatch |>.symm
          subst argumentTy
          let checkedArgument : CanonicalTerm :=
            ⟨argument, domain, argumentTypeEq⟩
          have reducedChecked :
              (DBTerm.instantiateAt checkedArgument.term 0 body).inferType [] =
                some codomain := by
            exact DBTerm.inferType_instantiateAt checkedArgument.term body domain
              checkedArgument.checked [] (by simpa using bodyTypeEq)
          let checkedReduced : CanonicalTerm :=
            ⟨DBTerm.instantiateAt checkedArgument.term 0 body,
              codomain, reducedChecked⟩
          have accepted : whole.betaReduce? = some checkedReduced := by
            apply (betaReduce?_eq_some_iff whole checkedReduced).mpr
            exact ⟨domain, body, checkedArgument, shape, rfl⟩
          simp [accepted]

end CanonicalTerm

/-! ## Positive and negative binding controls -/

namespace BindingExamples

open SequentExamples

def xIndividual : SourceVar := ⟨Name.global "x", Examples.individual⟩
def yIndividual : SourceVar := ⟨Name.global "y", Examples.individual⟩

def freeX : CanonicalTerm :=
  ⟨.free xIndividual, Examples.individual, by simp [xIndividual]⟩

def freeY : CanonicalTerm :=
  ⟨.free yIndividual, Examples.individual, by simp [yIndividual]⟩

/-- Closing binds the selected exact variable. -/
example : (freeX.abstractFree xIndividual).term =
    .abs Examples.individual (.bound 0) := by
  simp [CanonicalTerm.abstractFree, freeX, xIndividual]

/-- Closing does not capture a different free variable. -/
example : (freeY.abstractFree xIndividual).term =
    .abs Examples.individual (.free yIndividual) := by
  have different : xIndividual ≠ yIndividual := by
    simp [xIndividual, yIndividual, Name.global]
  simp only [CanonicalTerm.abstractFree, freeY, xIndividual]
  congr 1
  exact DBTerm.closeFreeAt_other xIndividual yIndividual 0 different

def identityAppliedToY : CanonicalTerm :=
  ⟨.app (.abs Examples.individual (.bound 0)) (.free yIndividual),
    Examples.individual, by simp [yIndividual]⟩

/-- Canonical beta contraction substitutes the checked argument. -/
example : identityAppliedToY.betaReduce? = some freeY := by
  apply (CanonicalTerm.betaReduce?_eq_some_iff _ _).mpr
  exact ⟨Examples.individual, .bound 0, freeY, by
    simp [identityAppliedToY, freeY], by
    simp [freeY]⟩

/-- A non-redex is rejected rather than treated as an identity reduction. -/
example : freeY.betaReduce? = none := by
  rfl

end BindingExamples

end Mettapedia.Languages.OpenTheory
