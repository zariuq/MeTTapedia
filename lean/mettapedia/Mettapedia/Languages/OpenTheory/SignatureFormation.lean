import Mettapedia.Languages.OpenTheory.Definitions
import Mettapedia.Languages.OpenTheory.Substitution
import Mettapedia.Languages.OpenTheory.CanonicalTyping

/-!
# Signature formation for shared HOL source terms

The raw term checker verifies applications and binding. This layer additionally
checks a constant's displayed type and a type operator's displayed arity against
an explicit declaration context.
Polymorphic occurrences supply a type-substitution certificate; its result is
checked against the declaration rather than against the occurrence's name.

Definitions retain their provenance in the registered symbol. Consequently a
different body with the same printed name is not the registered declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.SignatureFormation

open Mettapedia.Languages.OpenTheory

structure Signature where
  typeOperators : TypeOp → Option Nat
  constants : Const → Option Ty

namespace Signature

/-- An inclusion preserves actual declarations, including their provenance. -/
def Includes (source target : Signature) : Prop :=
  (∀ operator arity, source.typeOperators operator = some arity →
    target.typeOperators operator = some arity) ∧
  (∀ constant schema, source.constants constant = some schema →
    target.constants constant = some schema)

theorem Includes.refl (signature : Signature) : Includes signature signature :=
  ⟨fun _ _ found => found, fun _ _ found => found⟩

theorem Includes.trans {first second third : Signature}
    (left : Includes first second) (right : Includes second third) :
    Includes first third :=
  ⟨fun operator arity found => right.1 operator arity (left.1 operator arity found),
    fun constant schema found => right.2 constant schema (left.2 constant schema found)⟩

def addConstant (signature : Signature) (constant : Const) (schema : Ty) : Signature :=
  { signature with constants := fun candidate =>
      let sameSymbol := sharedComparison Const.same (fun symbol =>
        (Const.same_eq_true_iff symbol symbol).mpr rfl) candidate constant
      if sameSymbol then some schema else signature.constants candidate }

def addTypeOperator (signature : Signature) (operator : TypeOp) (arity : Nat) : Signature :=
  { signature with typeOperators := fun candidate =>
      let sameSymbol := sharedComparison TypeOp.same (fun symbol =>
        (TypeOp.same_eq_true_iff symbol symbol).mpr rfl) candidate operator
      if sameSymbol then some arity else signature.typeOperators candidate }

theorem includes_addConstant (signature : Signature) (constant : Const) (schema : Ty)
    (fresh : signature.constants constant = none) :
    Includes signature (signature.addConstant constant schema) := by
  refine ⟨fun _ _ found => found, ?_⟩
  intro candidate oldSchema found
  have different : candidate ≠ constant := by
    intro equal
    subst candidate
    rw [fresh] at found
    cases found
  simp [addConstant, Const.same_eq_true_iff, different, found]

theorem includes_addTypeOperator (signature : Signature) (operator : TypeOp) (arity : Nat)
    (fresh : signature.typeOperators operator = none) :
    Includes signature (signature.addTypeOperator operator arity) := by
  refine ⟨?_, fun _ _ found => found⟩
  intro candidate oldArity found
  have different : candidate ≠ operator := by
    intro equal
    subst candidate
    rw [fresh] at found
    cases found
  simp [addTypeOperator, TypeOp.same_eq_true_iff, different, found]

end Signature

/-- Type variables are the formal parameters of a HOL declaration. An operator
occurrence must instead name a registered operator at exactly its arity. -/
def TypeFormed (signature : Signature) : Ty → Prop
  | .var _ => True
  | .op operator arguments =>
      signature.typeOperators operator = some arguments.length ∧
        ∀ argument ∈ arguments, TypeFormed signature argument
termination_by type => sizeOf type

def typeFormedB (signature : Signature) : Ty → Bool
  | .var _ => true
  | .op operator arguments =>
      decide (signature.typeOperators operator = some arguments.length) &&
        arguments.attach.all (fun argument => typeFormedB signature argument.val)
termination_by type => sizeOf type
decreasing_by
  simp_wf
  have smaller := List.sizeOf_lt_of_mem argument.property
  omega

theorem typeFormedB_eq_true_iff (signature : Signature) (type : Ty) :
    typeFormedB signature type = true ↔ TypeFormed signature type := by
  cases type with
  | var name => simp [typeFormedB, TypeFormed]
  | op operator arguments =>
      simp only [typeFormedB, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, TypeFormed]
      constructor
      · rintro ⟨arity, children⟩
        exact ⟨arity, fun argument member =>
          (typeFormedB_eq_true_iff signature argument).mp
            (children ⟨argument, member⟩ (List.mem_attach ..))⟩
      · rintro ⟨arity, children⟩
        exact ⟨arity, fun argument _ =>
          (typeFormedB_eq_true_iff signature argument.val).mpr
            (children argument.val argument.property)⟩
termination_by sizeOf type
decreasing_by
  all_goals
    simp_wf
    first
    | have smaller := List.sizeOf_lt_of_mem argument.property
      omega
    | have smaller := List.sizeOf_lt_of_mem member
      omega

theorem TypeFormed.mono {source target : Signature} (included : source.Includes target)
    {type : Ty} (formed : TypeFormed source type) : TypeFormed target type := by
  fun_induction TypeFormed source type with
  | case1 => simp [TypeFormed]
  | case2 operator arguments ih =>
      simp only [TypeFormed] at formed ⊢
      exact ⟨included.1 operator arguments.length formed.1,
        fun argument member => ih argument member (formed.2 argument member)⟩

/-- Substitution preserves formation when its actual replacement carriers are
formed. Inhabitation is a separate semantic obligation of a HOL profile. -/
theorem TypeFormed.substitute (signature : Signature) (substitution : TypeSubst)
    (replacements : ∀ name replacement, substitution.lookup name = some replacement →
      TypeFormed signature replacement) {type : Ty} (formed : TypeFormed signature type) :
    TypeFormed signature (substitution.apply type) := by
  fun_induction TypeSubst.apply with
  | case1 name =>
      cases found : substitution.lookup name with
      | none => simp [TypeFormed]
      | some replacement => exact replacements name replacement found
  | case2 operator arguments ih =>
      simp only [TypeFormed, List.length_map] at formed ⊢
      refine ⟨by simpa using formed.1, ?_⟩
      intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (formed.2 original originalMember)

def ContextFormed (signature : Signature) (context : List Ty) : Prop :=
  ∀ type ∈ context, TypeFormed signature type

theorem ContextFormed.nil (signature : Signature) : ContextFormed signature [] := by simp [ContextFormed]

theorem ContextFormed.cons (signature : Signature) {context : List Ty} {type : Ty}
    (head : TypeFormed signature type) (tail : ContextFormed signature context) :
    ContextFormed signature (type :: context) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail candidate member

theorem ContextFormed.lookup (signature : Signature) {context : List Ty}
    (formed : ContextFormed signature context) {index : Nat} {type : Ty}
    (found : context[index]? = some type) : TypeFormed signature type := by
  induction context generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          have equal : head = type := by simpa using found
          subst type
          exact formed head (by simp)
      | succ index =>
          exact ih (fun candidate member => formed candidate (by simp [member]))
            (by simpa using found)

theorem ContextFormed.substitute (signature : Signature) (substitution : TypeSubst)
    (replacements : ∀ name replacement, substitution.lookup name = some replacement →
      TypeFormed signature replacement) {context : List Ty} (formed : ContextFormed signature context) :
    ContextFormed signature (context.map substitution.apply) := by
  intro type member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact (formed original originalMember).substitute signature substitution replacements

theorem TypeFormed.function (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    {domain codomain : Ty} (domainFormed : TypeFormed signature domain)
    (codomainFormed : TypeFormed signature codomain) :
    TypeFormed signature (.function domain codomain) := by
  simp only [Ty.function, TypeFormed]
  exact ⟨functionArity, by simp [domainFormed, codomainFormed]⟩

theorem TypeFormed.function_components (signature : Signature) {domain codomain : Ty}
    (formed : TypeFormed signature (.function domain codomain)) :
    TypeFormed signature domain ∧ TypeFormed signature codomain := by
  simp only [Ty.function, TypeFormed] at formed
  exact ⟨formed.2 domain (by simp), formed.2 codomain (by simp)⟩

/-- The declaration schema is instantiated simultaneously, using the shared
type-substitution operation. -/
def ConstantInstance (signature : Signature) (constant : Const) (annotation : Ty) : Prop :=
  ∃ (schema : Ty) (substitution : TypeSubst), signature.constants constant = some schema ∧
    substitution.apply schema = annotation

abbrev InstanceWitnesses := Const → Ty → TypeSubst

/-- The supplied certificate is checked against the actual declaration. -/
def constantInstanceB (signature : Signature) (witnesses : InstanceWitnesses)
    (constant : Const) (annotation : Ty) : Bool :=
  match signature.constants constant with
  | none => false
  | some schema => Ty.same ((witnesses constant annotation).apply schema) annotation

theorem constantInstanceB_sound (signature : Signature) (witnesses : InstanceWitnesses)
    (constant : Const) (annotation : Ty)
    (accepted : constantInstanceB signature witnesses constant annotation = true) :
    ConstantInstance signature constant annotation := by
  cases found : signature.constants constant with
  | none => simp [constantInstanceB, found] at accepted
  | some schema =>
      exact ⟨schema, witnesses constant annotation, found,
        by simpa [constantInstanceB, found] using accepted⟩

theorem ConstantInstance.mono {source target : Signature}
    (included : source.Includes target) {constant : Const} {annotation : Ty}
    (instanceProof : ConstantInstance source constant annotation) :
    ConstantInstance target constant annotation := by
  obtain ⟨schema, substitution, found, equal⟩ := instanceProof
  exact ⟨schema, substitution, included.2 constant schema found, equal⟩

theorem ConstantInstance.substitute (signature : Signature) (substitution : TypeSubst)
    {constant : Const} {annotation : Ty}
    (instanceProof : ConstantInstance signature constant annotation) :
    ConstantInstance signature constant (substitution.apply annotation) := by
  obtain ⟨schema, first, found, equal⟩ := instanceProof
  refine ⟨schema, first.compose substitution, found, ?_⟩
  rw [TypeSubst.apply_compose, equal]

theorem mem_typeVariablesList (name : Name) (arguments : List Ty) :
    name ∈ Ty.typeVariablesList arguments ↔
      ∃ argument ∈ arguments, name ∈ argument.typeVariables := by
  induction arguments with
  | nil => simp [Ty.typeVariablesList]
  | cons head tail ih =>
      simp only [Ty.typeVariablesList, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (member | ⟨argument, inTail, member⟩)
        · exact ⟨head, Or.inl rfl, member⟩
        · exact ⟨argument, Or.inr inTail, member⟩
      · rintro ⟨argument, rfl | inTail, member⟩
        · exact Or.inl member
        · exact Or.inr ⟨argument, inTail, member⟩

private theorem map_images_equal {A B : Type} (first second : A → B) (arguments : List A)
    (equal : arguments.map first = arguments.map second) :
    ∀ argument ∈ arguments, first argument = second argument := by
  induction arguments with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨headEqual, tailEqual⟩ := List.cons.inj equal
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact headEqual
      · exact ih tailEqual argument member

/-- A schema's instantiated result determines every parameter that actually
occurs in it, including parameters repeated in several argument positions. -/
theorem schema_parameters_determined (first second : TypeSubst) (schema : Ty)
    (equal : first.apply schema = second.apply schema) :
    ∀ name ∈ schema.typeVariables, first.apply (.var name) = second.apply (.var name) := by
  cases shape : schema with
  | var parameter =>
      rw [shape] at equal
      intro name member
      have nameEqual : name = parameter := by simpa [Ty.typeVariables] using member
      simpa [nameEqual] using equal
  | op operator arguments =>
      rw [shape] at equal
      have mapped : arguments.map first.apply = arguments.map second.apply := by
        simpa only [TypeSubst.apply_op, Ty.op.injEq, true_and] using equal
      intro name member
      obtain ⟨argument, argumentMember, parameterMember⟩ :=
        (mem_typeVariablesList name arguments).mp member
      exact schema_parameters_determined first second argument
        (map_images_equal _ _ arguments mapped argument argumentMember) name parameterMember
termination_by sizeOf schema
decreasing_by
  rw [shape]
  simp only [Ty.op.sizeOf_spec]
  have smaller := List.sizeOf_lt_of_mem argumentMember
  omega

/-- Type substitution depends exactly on the parameters in the type, rather
than on unused entries of its certificate. -/
theorem apply_equal_of_parameter_agreement (first second : TypeSubst) (type : Ty)
    (agree : ∀ name ∈ type.typeVariables, first.apply (.var name) = second.apply (.var name)) :
    first.apply type = second.apply type := by
  cases shape : type with
  | var parameter =>
      rw [shape] at agree
      exact agree parameter (by simp [Ty.typeVariables])
  | op operator arguments =>
      rw [shape] at agree
      rw [TypeSubst.apply_op, TypeSubst.apply_op]
      congr 1
      apply List.map_congr_left
      intro argument member
      apply apply_equal_of_parameter_agreement first second argument
      intro name parameterMember
      exact agree name ((mem_typeVariablesList name arguments).mpr ⟨argument, member, parameterMember⟩)
termination_by sizeOf type
decreasing_by
  rw [shape]
  simp only [Ty.op.sizeOf_spec]
  have smaller := List.sizeOf_lt_of_mem member
  omega

theorem term_type_instantiation_equal (first second : TypeSubst) (term : DBTerm)
    (agree : ∀ name ∈ term.typeVariables, first.apply (.var name) = second.apply (.var name)) :
    (TermSubst.mk first []).applyDB term = (TermSubst.mk second []).applyDB term := by
  induction term with
  | const constant annotation =>
      simp only [DBTerm.typeVariables] at agree
      simp only [TermSubst.applyDB_const]
      rw [apply_equal_of_parameter_agreement first second annotation agree]
  | free sourceVar =>
      simp only [DBTerm.typeVariables] at agree
      have typeEqual := apply_equal_of_parameter_agreement first second sourceVar.ty agree
      simp [TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar, typeEqual]
  | bound index => simp
  | app function argument functionIH argumentIH =>
      simp only [DBTerm.typeVariables] at agree
      simp only [TermSubst.applyDB_app]
      rw [functionIH (fun name member => agree name (Finset.mem_union_left _ member)),
        argumentIH (fun name member => agree name (Finset.mem_union_right _ member))]
  | abs domain body bodyIH =>
      simp only [DBTerm.typeVariables] at agree
      simp only [TermSubst.applyDB_abs]
      rw [apply_equal_of_parameter_agreement first second domain
          (fun name member => agree name (Finset.mem_union_left _ member)),
        bodyIH (fun name member => agree name (Finset.mem_union_right _ member))]

/-- The source definition guard excludes hidden type parameters. Consequently
two valid certificates for the same declaration instance yield the same
instantiated body, which is required for a well-defined interpretation. -/
theorem definition_instance_independent (first second : TypeSubst)
    (schema : Ty) (body : DBTerm) (bounded : body.typeVariables ⊆ schema.typeVariables)
    (sameInstance : first.apply schema = second.apply schema) :
    (TermSubst.mk first []).applyDB body = (TermSubst.mk second []).applyDB body :=
  term_type_instantiation_equal first second body
    (fun name member => schema_parameters_determined first second schema sameInstance name (bounded member))

/-- Absence of one complete constant identity from displayed term syntax.
Definition provenance is part of that identity, rather than a printed name. -/
def _root_.Mettapedia.Languages.OpenTheory.DBTerm.OmitsConstant (constant : Const) : DBTerm → Prop
  | .const actual _ => actual ≠ constant
  | .free _ => True
  | .bound _ => True
  | .app function argument =>
      OmitsConstant constant function ∧ OmitsConstant constant argument
  | .abs _ body => OmitsConstant constant body

theorem _root_.Mettapedia.Languages.OpenTheory.DBTerm.OmitsConstant.typeInstance
    {constant : Const} {term : DBTerm}
    (omitted : term.OmitsConstant constant) (substitution : TypeSubst) :
    ((TermSubst.mk substitution []).applyDB term).OmitsConstant constant := by
  induction term with
  | const actual annotation => simpa only [TermSubst.applyDB_const, DBTerm.OmitsConstant] using omitted
  | free sourceVar => simp [TermSubst.applyDB, TermSubst.lookup, DBTerm.OmitsConstant]
  | bound index => simp only [TermSubst.applyDB_bound, DBTerm.OmitsConstant]
  | app function argument functionIH argumentIH =>
      simpa only [TermSubst.applyDB_app, DBTerm.OmitsConstant] using
        And.intro (functionIH omitted.1) (argumentIH omitted.2)
  | abs domain body bodyIH =>
      simpa only [TermSubst.applyDB_abs, DBTerm.OmitsConstant] using bodyIH omitted

/-- Binding and application typing remain the existing raw checker's job.
This relation records precisely the additional declaration obligations. -/
inductive AnnotationsFormed (signature : Signature) : DBTerm → Prop where
  | constant {constant : Const} {annotation : Ty}
      (formed : TypeFormed signature annotation)
      (declared : ConstantInstance signature constant annotation) :
      AnnotationsFormed signature (.const constant annotation)
  | free {sourceVar : SourceVar} (formed : TypeFormed signature sourceVar.ty) :
      AnnotationsFormed signature (.free sourceVar)
  | bound (index : Nat) : AnnotationsFormed signature (.bound index)
  | app {function argument : DBTerm}
      (functionFormed : AnnotationsFormed signature function)
      (argumentFormed : AnnotationsFormed signature argument) :
      AnnotationsFormed signature (.app function argument)
  | abs {domain : Ty} {body : DBTerm} (domainFormed : TypeFormed signature domain)
      (bodyFormed : AnnotationsFormed signature body) :
      AnnotationsFormed signature (.abs domain body)

/-- An admitted old-language term cannot mention an unregistered identity. -/
theorem AnnotationsFormed.omits_unregistered {signature : Signature}
    {constant : Const} (fresh : signature.constants constant = none)
    {term : DBTerm} (formed : AnnotationsFormed signature term) :
    term.OmitsConstant constant := by
  induction formed with
  | constant _ declared =>
      obtain ⟨schema, _, registered, _⟩ := declared
      intro same
      rw [same, fresh] at registered
      cases registered
  | free _ => trivial
  | bound _ => trivial
  | app _ _ functionIH argumentIH => exact ⟨functionIH, argumentIH⟩
  | abs _ _ bodyIH => exact bodyIH

/-- The resulting type is formed as well as the term's written annotations.
The function operator is the source kernel's declared binary constructor. -/
theorem AnnotationsFormed.inferredType (signature : Signature)
    (functionArity : signature.typeOperators TypeOp.function = some 2)
    {term : DBTerm} (annotations : AnnotationsFormed signature term)
    {context : List Ty} (contextFormed : ContextFormed signature context)
    {type : Ty} (typed : term.inferType context = some type) : TypeFormed signature type := by
  induction annotations generalizing context type with
  | @constant constant annotation formed _ =>
      have equal : annotation = type := by simpa [DBTerm.inferType] using typed
      simpa [← equal] using formed
  | @free sourceVar formed =>
      have equal : sourceVar.ty = type := by simpa [DBTerm.inferType] using typed
      simpa [← equal] using formed
  | bound index =>
      exact contextFormed.lookup signature (by simpa only [DBTerm.inferType] using typed)
  | app _ _ functionIH _ =>
      obtain ⟨domain, functionTyped, _⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
      exact ((functionIH contextFormed functionTyped).function_components signature).2
  | @abs domain body domainFormed _ bodyIH =>
      obtain ⟨codomain, bodyTyped, equal⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed
      rw [equal]
      exact TypeFormed.function signature functionArity domainFormed
        (bodyIH (contextFormed.cons signature domainFormed) bodyTyped)

def annotationsFormedB (signature : Signature) (witnesses : InstanceWitnesses) : DBTerm → Bool
  | .const constant annotation =>
      typeFormedB signature annotation && constantInstanceB signature witnesses constant annotation
  | .free sourceVar => typeFormedB signature sourceVar.ty
  | .bound _ => true
  | .app function argument =>
      annotationsFormedB signature witnesses function &&
        annotationsFormedB signature witnesses argument
  | .abs domain body =>
      typeFormedB signature domain && annotationsFormedB signature witnesses body
termination_by term => sizeOf term

theorem annotationsFormedB_sound (signature : Signature) (witnesses : InstanceWitnesses)
    {term : DBTerm} (accepted : annotationsFormedB signature witnesses term = true) :
    AnnotationsFormed signature term := by
  induction term with
  | const constant annotation =>
      simp only [annotationsFormedB, Bool.and_eq_true] at accepted
      exact .constant ((typeFormedB_eq_true_iff signature annotation).mp accepted.1)
        (constantInstanceB_sound signature witnesses constant annotation accepted.2)
  | free sourceVar =>
      exact .free ((typeFormedB_eq_true_iff signature sourceVar.ty).mp
        (by simpa only [annotationsFormedB] using accepted))
  | bound index => exact .bound index
  | app function argument functionIH argumentIH =>
      simp only [annotationsFormedB, Bool.and_eq_true] at accepted
      exact .app (functionIH accepted.1) (argumentIH accepted.2)
  | abs domain body bodyIH =>
      simp only [annotationsFormedB, Bool.and_eq_true] at accepted
      exact .abs ((typeFormedB_eq_true_iff signature domain).mp accepted.1) (bodyIH accepted.2)

theorem AnnotationsFormed.mono {source target : Signature} (included : source.Includes target)
    {term : DBTerm} (formed : AnnotationsFormed source term) :
    AnnotationsFormed target term := by
  induction formed with
  | constant typeFormed declared =>
      exact .constant (typeFormed.mono included) (declared.mono included)
  | free typeFormed => exact .free (typeFormed.mono included)
  | bound index => exact .bound index
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH
  | abs typeFormed _ bodyIH => exact .abs (typeFormed.mono included) bodyIH

theorem AnnotationsFormed.substitute (signature : Signature) (substitution : TermSubst)
    (typesFormed : ∀ name replacement, substitution.types.lookup name = some replacement →
      TypeFormed signature replacement)
    (termsFormed : ∀ sourceVar replacement, substitution.lookup sourceVar = some replacement →
      AnnotationsFormed signature replacement.canonical.term)
    {term : DBTerm} (formed : AnnotationsFormed signature term) :
    AnnotationsFormed signature (substitution.applyDB term) := by
  induction formed with
  | constant annotationFormed declared =>
      simp only [TermSubst.applyDB]
      exact .constant (annotationFormed.substitute signature substitution.types typesFormed)
        (declared.substitute signature substitution.types)
  | @free sourceVar annotationFormed =>
      cases found : substitution.lookup (substitution.types.applyVar sourceVar) with
      | none =>
          simp only [TermSubst.applyDB, found]
          exact .free (annotationFormed.substitute signature substitution.types typesFormed)
      | some replacement =>
          simp only [TermSubst.applyDB, found]
          exact termsFormed _ _ found
  | bound index => simpa only [TermSubst.applyDB] using AnnotationsFormed.bound (signature := signature) index
  | app _ _ functionIH argumentIH =>
      simpa only [TermSubst.applyDB] using AnnotationsFormed.app functionIH argumentIH
  | abs domainFormed _ bodyIH =>
      simp only [TermSubst.applyDB]
      exact .abs (domainFormed.substitute signature substitution.types typesFormed) bodyIH

/-- Certificate existence is a logical completeness result. It does not
provide a native procedure for selecting an instantiation certificate. -/
theorem exists_instanceWitnesses (signature : Signature) :
    ∃ witnesses : InstanceWitnesses, ∀ constant annotation,
      ConstantInstance signature constant annotation →
        constantInstanceB signature witnesses constant annotation = true := by
  classical
  have choices (constant : Const) (annotation : Ty) :
      ∃ substitution : TypeSubst, ∀ schema,
        signature.constants constant = some schema →
          ConstantInstance signature constant annotation → substitution.apply schema = annotation := by
    by_cases available : ConstantInstance signature constant annotation
    · obtain ⟨schema, substitution, found, equal⟩ := available
      refine ⟨substitution, ?_⟩
      intro otherSchema otherFound _
      have same : schema = otherSchema := Option.some.inj (found.symm.trans otherFound)
      simpa [← same] using equal
    · exact ⟨TypeSubst.empty, fun _ _ impossible => False.elim (available impossible)⟩
  choose witnesses realizes using choices
  refine ⟨witnesses, ?_⟩
  intro constant annotation instanceProof
  have kept := instanceProof
  obtain ⟨schema, _, found, _⟩ := kept
  simp [constantInstanceB, found, realizes constant annotation schema found instanceProof]

theorem annotationsFormedB_complete (signature : Signature) (witnesses : InstanceWitnesses)
    (realizes : ∀ constant annotation, ConstantInstance signature constant annotation →
      constantInstanceB signature witnesses constant annotation = true)
    {term : DBTerm} (formed : AnnotationsFormed signature term) :
    annotationsFormedB signature witnesses term = true := by
  induction formed with
  | constant annotationFormed declared =>
      simp only [annotationsFormedB, Bool.and_eq_true]
      exact ⟨(typeFormedB_eq_true_iff _ _).mpr annotationFormed, realizes _ _ declared⟩
  | free annotationFormed =>
      simpa only [annotationsFormedB] using (typeFormedB_eq_true_iff _ _).mpr annotationFormed
  | bound index => simp only [annotationsFormedB]
  | app _ _ functionIH argumentIH =>
      simp only [annotationsFormedB, Bool.and_eq_true]
      exact ⟨functionIH, argumentIH⟩
  | abs domainFormed _ bodyIH =>
      simp only [annotationsFormedB, Bool.and_eq_true]
      exact ⟨(typeFormedB_eq_true_iff _ _).mpr domainFormed, bodyIH⟩

/-- Source terms become admissible only after both the binding/type check and
the independent declaration-annotation check succeed. -/
def checkSource (signature : Signature) (witnesses : InstanceWitnesses)
    (source : SourceTerm) : Option CanonicalTerm := do
  let canonical ← source.check
  if annotationsFormedB signature witnesses canonical.term then some canonical else none

theorem checkSource_sound (signature : Signature) (witnesses : InstanceWitnesses)
    {source : SourceTerm} {canonical : CanonicalTerm}
    (accepted : checkSource signature witnesses source = some canonical) :
    source.check = some canonical ∧ AnnotationsFormed signature canonical.term := by
  unfold checkSource at accepted
  simp only [bind, Option.bind] at accepted
  cases checked : source.check with
  | none => simp [checked] at accepted
  | some result =>
      simp only [checked] at accepted
      split at accepted
      · rename_i formed
        have equal : result = canonical := Option.some.inj accepted
        subst result
        exact ⟨rfl, annotationsFormedB_sound signature witnesses formed⟩
      · cases accepted

theorem checkSource_complete (signature : Signature) {source : SourceTerm}
    {canonical : CanonicalTerm} (checked : source.check = some canonical)
    (formed : AnnotationsFormed signature canonical.term) :
    ∃ witnesses, checkSource signature witnesses source = some canonical := by
  obtain ⟨witnesses, realizes⟩ := exists_instanceWitnesses signature
  exact ⟨witnesses, by
    simp [checkSource, checked, annotationsFormedB_complete signature witnesses realizes formed]⟩

theorem checkSource_alpha (signature : Signature) (witnesses : InstanceWitnesses)
    {left right : SourceTerm} (alpha : left.AlphaEq right) :
    checkSource signature witnesses left = checkSource signature witnesses right := by
  have canonical := (SourceTerm.alphaEq_iff_toDB_eq left right).mp alpha
  unfold checkSource SourceTerm.check
  rw [canonical]

theorem checkSource_admission_iff (signature : Signature) (source : SourceTerm)
    (canonical : CanonicalTerm) :
    (∃ witnesses, checkSource signature witnesses source = some canonical) ↔
      source.check = some canonical ∧ AnnotationsFormed signature canonical.term := by
  constructor
  · rintro ⟨witnesses, accepted⟩
    exact checkSource_sound signature witnesses accepted
  · rintro ⟨checked, formed⟩
    exact checkSource_complete signature checked formed

namespace Controls

def individual : Ty := .op (.mk (Name.global "ind") .undefined) []
def alpha : Ty := .var (Name.global "A")
def identity : Const := .mk (Name.global "identity") .undefined

def signature : Signature :=
  { typeOperators := fun operator =>
      if TypeOp.same operator TypeOp.function then some 2 else
      if TypeOp.same operator TypeOp.bool then some 0 else
      if TypeOp.same operator (.mk (Name.global "ind") .undefined) then some 0 else none
    constants := fun constant =>
      if Const.same constant identity then some (.function alpha alpha) else none }

def booleanWitnesses : InstanceWitnesses := fun _ _ =>
  ⟨[(Name.global "A", Ty.bool)]⟩

theorem boolean_identity_instance :
    annotationsFormedB signature booleanWitnesses
      (.const identity (.function Ty.bool Ty.bool)) = true := by
  simp [annotationsFormedB, typeFormedB, signature, booleanWitnesses,
    constantInstanceB, identity, alpha, TypeSubst.lookup, Name.global,
    Ty.function, Ty.bool, TypeOp.function, TypeOp.bool, Const.same, TypeOp.same]

theorem false_identity_annotation_refused :
    annotationsFormedB signature booleanWitnesses
      (.const identity (.function Ty.bool individual)) = false := by
  simp [annotationsFormedB, typeFormedB, signature, booleanWitnesses,
    constantInstanceB, identity, individual, alpha, TypeSubst.lookup, Name.global,
    Ty.function, Ty.bool, TypeOp.function, TypeOp.bool, Const.same, TypeOp.same,
    Ty.same, Ty.listSame]

/-- No alternative instantiation certificate can repair this false annotation:
the same type parameter cannot simultaneously become two distinct carriers. -/
theorem false_identity_has_no_certificate :
    ¬ ConstantInstance signature identity (.function Ty.bool individual) := by
  rintro ⟨schema, substitution, found, equal⟩
  have schemaEqual : schema = .function alpha alpha := by
    simpa [signature, Const.same_eq_true_iff] using found.symm
  subst schema
  rw [TypeSubst.apply_function] at equal
  obtain ⟨left, right⟩ := Ty.function_inj equal
  have impossible : Ty.bool = individual := left.symm.trans right
  simp [Ty.bool, individual, TypeOp.bool, Name.global] at impossible

theorem malformed_boolean_arity_refused :
    typeFormedB signature (.op TypeOp.bool [Ty.bool]) = false := by
  simp [typeFormedB, signature, TypeOp.bool, TypeOp.function, TypeOp.same, Name.global]

theorem absent_constant_refused :
    constantInstanceB signature booleanWitnesses
      (.mk (Name.global "unregistered") .undefined) Ty.bool = false := by
  simp [constantInstanceB, signature, identity, Const.same, Name.global]

def parameterIdentity : CanonicalTerm :=
  ⟨.abs alpha (.bound 0), .function alpha alpha, by simp [DBTerm.inferType]⟩

/-- This closed Boolean term mentions A internally but its result type does
not. It is a genuine typed counterexample to omitting the definition guard. -/
def hiddenParameterBody : CanonicalTerm :=
  CanonicalTerm.equalityOfSameType parameterIdentity parameterIdentity rfl

theorem hidden_parameter_body_closed : hiddenParameterBody.term.HasNoFreeVariables :=
  .app (.app .const (.abs .bound)) (.abs .bound)

theorem hidden_parameter_guard_refused :
    ¬ hiddenParameterBody.term.typeVariables ⊆ hiddenParameterBody.ty.typeVariables := by
  intro bounded
  have impossible := bounded (x := Name.global "A")
    (by simp [hiddenParameterBody, parameterIdentity, CanonicalTerm.equalityOfSameType,
      CanonicalTerm.equalityDB, DBTerm.typeVariables, Ty.typeVariables,
      Ty.typeVariablesList, Ty.equality, Ty.function, Ty.bool, alpha])
  simp [hiddenParameterBody, CanonicalTerm.equalityOfSameType,
    Ty.bool, Ty.typeVariables, Ty.typeVariablesList] at impossible

def individualWitness : TypeSubst := ⟨[(Name.global "A", individual)]⟩

theorem hidden_parameter_same_result_type :
    (booleanWitnesses identity Ty.bool).apply hiddenParameterBody.ty =
      individualWitness.apply hiddenParameterBody.ty := by
  simp [hiddenParameterBody, CanonicalTerm.equalityOfSameType, Ty.bool]

/-- Matching the result type alone does not determine a body that hides an
extra parameter. The source guard is precisely what rules this out. -/
theorem hidden_parameter_different_bodies :
    (TermSubst.mk (booleanWitnesses identity Ty.bool) []).applyDB hiddenParameterBody.term ≠
      (TermSubst.mk individualWitness []).applyDB hiddenParameterBody.term := by
  intro equal
  simp [hiddenParameterBody, parameterIdentity, CanonicalTerm.equalityOfSameType,
    CanonicalTerm.equalityDB, booleanWitnesses, individualWitness,
    alpha, individual, TypeSubst.lookup, Ty.equality, Ty.function, Ty.bool,
    TypeOp.bool, Name.global] at equal

end Controls

end Mettapedia.Languages.OpenTheory.SignatureFormation
