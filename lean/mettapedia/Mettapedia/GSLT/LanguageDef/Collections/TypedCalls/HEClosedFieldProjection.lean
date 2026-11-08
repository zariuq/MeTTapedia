import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFormals
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorDeclarationGuard
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Closed field evidence from a constructor's actual range unifier

The static projection uses the constructor row that the equation pattern
matched. Its range is unified with the caller's closed formal, and that
same returned substitution is applied to the field declaration. If the
result is closed, every runtime solution of the range equation gives that
field the same type. The result uses the existing total unifier's proved
most-generality, not an assumed unifier certificate.

The constructor inversion corollary uses the existing checked constructor
typing derivation, including its shared row-variable assignment. It does
not turn a nominal annotation on an arbitrary expression into field typing.
The source binding corollary keeps the full annotated field, not its erased
syntax. Native wildcard, space-class and primitive-normalization matching
remain separate from the ordinary syntactic-unification fragment here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Logic.LP (Term Subst Unifies unifyTotal unifyTotal_mgu)
open ShapeTyping StaticEvidence OpenFormals InferredTypeSets RecognizedFolds
open Spec.Eval Spec.Eval.Completed
open Spec.Type.Presentation
open Spec.Bindings.ScopeObservation

theorem encode_substitution (assignment : String → Atom) (atom : Atom) :
    UnifyAtoms.encode (substA assignment atom) =
      Subst.applyTerm (fun name => UnifyAtoms.encode (assignment name) : Subst UnifyAtoms.sig)
        (UnifyAtoms.encode atom) := by
  have decoded := UnifyAtoms.decode_applyTerm
    (fun name => UnifyAtoms.encode (assignment name) : Subst UnifyAtoms.sig) atom
  simp only [UnifyAtoms.decode_encode] at decoded
  exact (congrArg UnifyAtoms.encode decoded).symm.trans
    (TypeScopeRenaming.encode_decode _)

mutual
theorem substitution_closed (assignment : String → Atom) : ∀ atom,
    TypeSubst.typeVars atom = [] → substA assignment atom = atom
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .var _, closed => by simp [TypeSubst.typeVars] at closed
  | .expression children, closed =>
      congrArg Atom.expression (substitution_list_closed assignment children closed)
theorem substitution_list_closed (assignment : String → Atom) : ∀ atoms,
    TypeSubst.typeVarsList atoms = [] → substL assignment atoms = atoms
  | [], _ => rfl
  | atom :: atoms, closed => by
      have parts := List.append_eq_nil_iff.mp closed
      rw [substL, substitution_closed assignment atom parts.1,
        substitution_list_closed assignment atoms parts.2]
end

/-- Closing a field with the actual returned atom unifier fixes it under
every solution of the range equation, including later caller refinements. -/
theorem atom_closed_field (rowRange formal field result : Atom)
    (theta : Subst UnifyAtoms.sig)
    (matched : UnifyAtoms.unify rowRange formal = some theta)
    (projected : substA (UnifyAtoms.readBack theta) field = result)
    (closed : TypeSubst.typeVars result = [])
    (assignment : String → Atom)
    (compatible : substA assignment rowRange = substA assignment formal) :
    substA assignment field = result := by
  let candidate : Subst UnifyAtoms.sig := fun name => UnifyAtoms.encode (assignment name)
  have solved : Unifies candidate [(UnifyAtoms.encode rowRange, UnifyAtoms.encode formal)] := by
    intro pair member
    have same := List.mem_singleton.mp member
    subst pair
    simpa only [candidate, ← encode_substitution] using congrArg UnifyAtoms.encode compatible
  obtain ⟨after, factor⟩ := unifyTotal_mgu _ theta matched candidate solved
  have factorEq : candidate = after.comp theta := funext factor
  have fieldEq := congrArg (fun substitution : Subst UnifyAtoms.sig =>
      UnifyAtoms.decode (substitution.applyTerm (UnifyAtoms.encode field))) factorEq
  rw [Subst.applyTerm_comp] at fieldEq
  rw [← TypeScopeRenaming.encode_decode (theta.applyTerm (UnifyAtoms.encode field)),
    UnifyAtoms.decode_applyTerm, UnifyAtoms.decode_applyTerm] at fieldEq
  have chosen : UnifyAtoms.decode (theta.applyTerm (UnifyAtoms.encode field)) = result := by
    rw [UnifyAtoms.decode_applyTerm]
    exact projected
  simp only [candidate, UnifyAtoms.decode_encode] at fieldEq
  rw [chosen, substitution_closed _ result closed] at fieldEq
  exact fieldEq

/-- The existing symbolic-type codec gives the same closed-field law,
so checked constructor inversion can consume an executable result. -/
theorem type_closed_field {V : Type} [DecidableEq V]
    (rowRange field : Ty V) (formal result : Ty Empty)
    (theta : Subst (TypeEquationSolver.signature V))
    (matched : unifyTotal [(TypeEquationSolver.encode rowRange,
      TypeEquationSolver.encode (formal.lift : Ty V))] = some theta)
    (projected : field.bind (fun name => TypeEquationSolver.decode (theta name)) =
      (result.lift : Ty V))
    (assignment : V → Ty Empty) (compatible : rowRange.bind assignment = formal) :
    field.bind assignment = result := by
  let lifted : V → Ty V := fun name => (assignment name).lift
  let candidate : Subst (TypeEquationSolver.signature V) :=
    fun name => TypeEquationSolver.encode (lifted name)
  have liftBind (type : Ty V) : type.bind lifted = (type.bind assignment).lift := by
    simp only [lifted, Ty.lift, Ty.map, Ty.bind_bind]
  have solved : Unifies candidate [(TypeEquationSolver.encode rowRange,
      TypeEquationSolver.encode (formal.lift : Ty V))] := by
    intro pair member
    have same := List.mem_singleton.mp member
    subst pair
    simp only [candidate, ← TypeEquationSolver.encode_bind, liftBind,
      Ty.lift_bind_ground, compatible]
  obtain ⟨after, factor⟩ := unifyTotal_mgu _ theta matched candidate solved
  have factorEq : candidate = after.comp theta := funext factor
  have fieldEq := congrArg (fun substitution : Subst (TypeEquationSolver.signature V) =>
      TypeEquationSolver.decode (substitution.applyTerm (TypeEquationSolver.encode field))) factorEq
  rw [Subst.applyTerm_comp] at fieldEq
  rw [← TypeEquationSolver.encode_decode (theta.applyTerm (TypeEquationSolver.encode field)),
    TypeEquationSolver.decode_apply, TypeEquationSolver.decode_apply] at fieldEq
  have chosen : TypeEquationSolver.decode (theta.applyTerm (TypeEquationSolver.encode field)) =
      (result.lift : Ty V) := by
    rw [TypeEquationSolver.decode_apply]
    exact projected
  simp only [candidate, TypeEquationSolver.decode_encode] at fieldEq
  rw [chosen] at fieldEq
  have grounded := congrArg (fun type : Ty V => type.bind (fun _ => (default : Ty Empty))) fieldEq
  simpa only [lifted, Ty.bind_bind, Ty.lift_bind_ground] using grounded

/-- The closed symbolic branch of static field recovery, using the existing
solver and codec. No nominal row is used as a replacement for this check. -/
def inferClosedField (range : Ty String) (formal : Ty Empty) (field : Ty String) : Option (Ty String) :=
  (unifyTotal [(TypeEquationSolver.encode range,
    TypeEquationSolver.encode (formal.lift : Ty String))]).bind fun theta =>
      let projected := field.bind (fun name => TypeEquationSolver.decode (theta name))
      if projected.vars.isEmpty then some projected else none

theorem inferred_field_fixed (range field : Ty String) (formal result : Ty Empty)
    (inferred : inferClosedField range formal field = some result.lift)
    (assignment : String → Ty Empty) (compatible : range.bind assignment = formal) :
    field.bind assignment = result := by
  simp only [inferClosedField, Option.bind_eq_some_iff] at inferred
  obtain ⟨theta, matched, projected⟩ := inferred
  split at projected
  · exact type_closed_field range field formal result theta matched (Option.some.inj projected) assignment compatible
  · contradiction

/-- The same runtime assignment checks every field. The declared field may
be open even though the statically recovered field type is closed. -/
theorem constructor_field (Γ : Decls) (head : String) (whole : Ty String)
    (formals : List (Ty String)) (range fieldType : Ty String)
    (callerType resultType : Ty Empty)
    (row : ctorRow Γ head = some (whole, formals, range))
    (arguments : List Atom) (index : Nat) (field : Atom)
    (formalAt : formals[index]? = some fieldType)
    (fieldAt : arguments[index]? = some field)
    (checked : CheckedTy fieldType)
    (theta : Subst (TypeEquationSolver.signature String))
    (matched : unifyTotal [(TypeEquationSolver.encode range,
      TypeEquationSolver.encode (callerType.lift : Ty String))] = some theta)
    (projected : fieldType.bind (fun name => TypeEquationSolver.decode (theta name)) =
      (resultType.lift : Ty String))
    (typed : Typable (stamp Γ (.expression (.symbol head :: arguments))) callerType) :
    StaticAt (stamp Γ field) resultType := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  obtain ⟨types, present, selected⟩ := typed
  rw [stamp_ctor Γ head whole formals range rows split] at present
  by_cases length : formals.length = arguments.length
  swap
  · simp [if_neg length] at present
  simp only [if_pos length] at present
  obtain ⟨assignments, _, _, ranges, each⟩ :=
    semCheck_ok_inv whole range formals _ Set.univ types ⟨fun _ => default, trivial⟩ present
  subst ranges
  obtain ⟨assignment, allowed, rangeEq⟩ := selected
  have fieldStamp : (arguments.map (stamp Γ))[index]? = some (stamp Γ field) := by simp [fieldAt]
  rcases forall₂_getElem? each formalAt fieldStamp with absent | unchecked | ⟨fieldTypes, fieldPresent, satisfies⟩
  · exact .inl absent
  · rw [checked_stamp checked Γ field] at unchecked
    cases unchecked
  · refine .inr ⟨fieldTypes, fieldPresent, ?_⟩
    have fixed := type_closed_field range fieldType callerType resultType theta matched projected assignment rangeEq
    rw [← fixed]
    exact satisfies assignment allowed

theorem inferred_constructor_field (Γ : Decls) (head : String) (whole : Ty String)
    (formals : List (Ty String)) (range fieldType : Ty String)
    (callerType resultType : Ty Empty)
    (row : ctorRow Γ head = some (whole, formals, range))
    (arguments : List Atom) (index : Nat) (field : Atom)
    (formalAt : formals[index]? = some fieldType)
    (fieldAt : arguments[index]? = some field)
    (checked : CheckedTy fieldType)
    (inferred : inferClosedField range callerType fieldType = some resultType.lift)
    (typed : Typable (stamp Γ (.expression (.symbol head :: arguments))) callerType) :
    StaticAt (stamp Γ field) resultType := by
  simp only [inferClosedField, Option.bind_eq_some_iff] at inferred
  obtain ⟨theta, matched, projected⟩ := inferred
  split at projected
  · exact constructor_field Γ head whole formals range fieldType callerType resultType row arguments index field
      formalAt fieldAt checked theta matched (Option.some.inj projected) typed
  · contradiction

/-- Literal parts of an equation pattern compare erased syntax without
discarding the annotations of the value they match. -/
theorem literal_source_match (policy : Policy) (environment : Entry.Value.Environment)
    (value : Entry.Value) :
    Entry.Value.UnifyRel policy.rebuilding environment value (Entry.Value.ofAtom value.erase) environment := by
  apply Entry.Value.UnifyRel.ordinary
  apply Entry.Value.AppliedUnifyRel.identical
  rw [Entry.Value.erase_substitute_environment, Entry.Value.erase_substitute_environment,
    Entry.Value.erase_ofAtom]

theorem literal_source_matches (policy : Policy) (environment : Entry.Value.Environment) :
    ∀ values : List Entry.Value,
      Entry.Value.UnifyListRel policy.rebuilding environment values
        (values.map fun value => Entry.Value.ofAtom value.erase) environment
  | [] => .nil _
  | value :: values => .cons (literal_source_match policy environment value)
      (literal_source_matches policy environment values)

/-- An arbitrary field position, not only a unary constructor, uses the
actual contextual source matcher. The prefix and suffix are literal parts
of the pattern; the selected field is bound fresh. -/
theorem source_field_capture (policy : Policy) (before : Frame) (name : String)
    (field : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (closed : TypeSubst.typeVars field.erase = []) :
    ∀ preceding following : List Entry.Value,
      Entry.Value.UnifyListRel policy.rebuilding before.environment
        (preceding ++ field :: following)
        ((preceding.map fun value => Entry.Value.ofAtom value.erase) ++
          .var name :: following.map fun value => Entry.Value.ofAtom value.erase)
        (HEFreshSyntaxBinding.bindFrame policy before name field fresh (by simp [closed])).environment
  | [], following => .cons (HEFreshSyntaxBinding.source_binding policy before name field fresh closed)
      (literal_source_matches policy _ following)
  | value :: preceding, following => .cons (literal_source_match policy before.environment value)
      (source_field_capture policy before name field fresh closed preceding following)

/-- Source capture returns the exact annotated field and its static evidence.
Neither the field's status nor any nested status is reconstructed from syntax. -/
theorem captured_field_evidence (policy readingPolicy : Policy) (before : Frame) (name : String)
    (field : Entry.Value) (fresh : name ∉ specBindingVars before.bindings)
    (closed : TypeSubst.typeVars field.erase = []) (Γ : Decls) (type : Ty Empty)
    (checked : StaticAt (stamp Γ field.erase) type) :
    let after := HEFreshSyntaxBinding.bindFrame policy before name field fresh (by simp [closed])
    after.read readingPolicy (.var name) = field ∧
      StaticAt (stamp Γ (after.read readingPolicy (.var name)).erase) type ∧
      after.bindings = HEFreshRangeFrame.extend before.bindings name field.erase := by
  dsimp only
  have retained := HEFreshSyntaxBinding.bound_read policy before name field fresh closed readingPolicy
  refine ⟨retained, ?_, HEFreshSyntaxBinding.binding_keeps_caller policy before name field fresh _⟩
  rw [retained]
  exact checked

/-- The selected slot keeps the constructor check's inferred field evidence
and the source matcher's complete annotated field at the same time. -/
theorem checked_constructor_capture (policy : Policy) (before : Frame) (name head : String)
    (preceding following : List Entry.Value) (field : Entry.Value)
    (fresh : name ∉ specBindingVars before.bindings)
    (closed : TypeSubst.typeVars field.erase = [])
    (Γ : Decls) (whole range fieldType : Ty String) (formals : List (Ty String))
    (callerType resultType : Ty Empty)
    (row : ctorRow Γ head = some (whole, formals, range))
    (formalAt : formals[preceding.length]? = some fieldType)
    (checked : CheckedTy fieldType)
    (inferred : inferClosedField range callerType fieldType = some resultType.lift)
    (typed : Typable (stamp Γ (.expression (.symbol head ::
      (preceding ++ field :: following).map Entry.Value.erase))) callerType) :
    ∃ after : Frame,
      Entry.Value.UnifyListRel policy.rebuilding before.environment
        ((.symbol head :: preceding) ++ field :: following)
        (((.symbol head :: preceding).map fun value => Entry.Value.ofAtom value.erase) ++
          .var name :: following.map fun value => Entry.Value.ofAtom value.erase) after.environment ∧
      (∀ readingPolicy, after.read readingPolicy (.var name) = field ∧
        StaticAt (stamp Γ (after.read readingPolicy (.var name)).erase) resultType) ∧
      after.bindings = HEFreshRangeFrame.extend before.bindings name field.erase := by
  have fieldAt : ((preceding ++ field :: following).map Entry.Value.erase)[preceding.length]? =
      some field.erase := by simp
  have static := inferred_constructor_field Γ head whole formals range fieldType callerType resultType row
    _ preceding.length field.erase formalAt fieldAt checked inferred typed
  let after := HEFreshSyntaxBinding.bindFrame policy before name field fresh (by simp [closed])
  refine ⟨after, source_field_capture policy before name field fresh closed (.symbol head :: preceding) following,
    ?_, HEFreshSyntaxBinding.binding_keeps_caller policy before name field fresh _⟩
  intro readingPolicy
  exact ⟨(captured_field_evidence policy readingPolicy before name field fresh closed Γ resultType static).1,
    (captured_field_evidence policy readingPolicy before name field fresh closed Γ resultType static).2.1⟩

/-! ## The actual ordered argument checker at a projected position -/

/-- The field is checked at its reached state, not at an independently
chosen assignment. The ordinary branch retains the exact first selected
typing and the rejected prefix. -/
def FieldStep {Value TypeAtom Bind Kind : Type}
    (ops : NativeTypeViews.Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (formal : TypeAtom) (value : Value) (before after : Bind) : Prop :=
  (ops.metaCheck (ops.apply before formal) (reads.kind value) = some true ∧ after = before) ∨
  (ops.metaCheck (ops.apply before formal) (reads.kind value) = none ∧
    ∃ preceding actual following,
      reads.inferred value = preceding ++ actual :: following ∧
      (∀ prior ∈ preceding, ops.unify before prior (ops.apply before formal) = none) ∧
      ops.unify before actual (ops.apply before formal) = some after)

theorem source_argument_step {Value TypeAtom Bind Kind : Type}
    (ops : NativeTypeViews.Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind)
    (formal : TypeAtom) (value : Value) (formals : List TypeAtom) (values : List Value)
    (before final : Bind)
    (checked : NativeTypeViews.sourceArgs ops reads (formal :: formals) (value :: values) before = some final) :
    ∃ after, FieldStep ops reads formal value before after ∧
      NativeTypeViews.sourceArgs ops reads formals values after = some final := by
  simp only [NativeTypeViews.sourceArgs] at checked
  split at checked
  next accepted => exact ⟨before, .inl ⟨accepted, rfl⟩, checked⟩
  next rejected => contradiction
  next ordinary =>
    split at checked
    next failed => contradiction
    next after selected =>
      obtain ⟨preceding, actual, following, shape, rejected, matched⟩ :=
        (StampInference.firstResult_some_iff _ _ _).mp selected
      exact ⟨after, .inr ⟨ordinary, preceding, actual, following, shape, rejected, matched⟩, checked⟩

/-- Successful checking exposes the selected field's exact entry/exit
states together with its remaining run. Earlier fields are actually run;
their shared type bindings cannot be replaced by independent field checks. -/
theorem source_argument_at {Value TypeAtom Bind Kind : Type}
    (ops : NativeTypeViews.Ops TypeAtom Bind Kind)
    (reads : NativeTypeViews.Reads Value TypeAtom Kind) :
    ∀ (formals : List TypeAtom) (values : List Value) (index : Nat)
      (formal : TypeAtom) (value : Value) (before final : Bind),
      formals[index]? = some formal → values[index]? = some value →
      NativeTypeViews.sourceArgs ops reads formals values before = some final →
      ∃ reached after,
        NativeTypeViews.sourceArgs ops reads (formals.take index) (values.take index) before = some reached ∧
        FieldStep ops reads formal value reached after ∧
        NativeTypeViews.sourceArgs ops reads (formals.drop (index + 1)) (values.drop (index + 1)) after = some final
  | [], _, _, _, _, _, _, formalAt, _, _ => by simp at formalAt
  | _ :: _, [], _, _, _, _, _, _, valueAt, _ => by simp at valueAt
  | param :: params, arg :: args, 0, formal, value, before, final, formalAt, valueAt, checked => by
      have fp := Option.some.inj formalAt
      have vp := Option.some.inj valueAt
      subst formal
      subst value
      obtain ⟨after, step, tail⟩ := source_argument_step ops reads param arg params args before final checked
      exact ⟨before, after, rfl, step, tail⟩
  | param :: params, arg :: args, index + 1, formal, value, before, final, formalAt, valueAt, checked => by
      obtain ⟨middle, step, tail⟩ := source_argument_step ops reads param arg params args before final checked
      obtain ⟨reached, after, start, fieldStep, rest⟩ :=
        source_argument_at ops reads params args index formal value middle final formalAt valueAt tail
      refine ⟨reached, after, ?_, fieldStep, rest⟩
      simp only [List.take_succ_cons, NativeTypeViews.sourceArgs]
      rcases step with ⟨accepted, rfl⟩ | ⟨ordinary, preceding, actual, following, shape, rejected, matched⟩
      · simpa only [accepted] using start
      · have selected : StampInference.firstResult
            (fun candidate => ops.unify before candidate (ops.apply before param)) (reads.inferred arg) = some middle :=
          (StampInference.firstResult_some_iff _ _ _).mpr ⟨preceding, actual, following, shape, rejected, matched⟩
        simpa only [ordinary, selected] using start

/-- The declaration-only gate and actual constructor inference jointly earn
the field's reached check. A positive nominal parent annotation would not
be enough to establish this conclusion. -/
theorem guarded_node_field {Bind Kind : Type}
    (ops : NativeTypeViews.Ops Atom Bind Kind) (reads : NativeTypeViews.Reads Atom Atom Kind)
    (rows : List Atom) (head : String) (values : List Atom)
    (accepted : HEConstructorDeclarationGuard.accepts rows head = true)
    (annotationRead : reads.annotations (.symbol head) values =
      getAnnotatedTypes ⟨rows⟩ (.expression (.symbol head :: values)))
    (ordinary : reads.classify (.symbol head) values = .ordinary)
    (row range : Atom) (formals : List Atom)
    (headRead : reads.headRows (.symbol head) = [row])
    (arrow : ops.arrow row = some (formals, range))
    (positive : NativeTypeViews.sourceNode ops reads true (.symbol head) values ≠ [])
    (index : Nat) (formal value : Atom)
    (formalAt : formals[index]? = some formal) (valueAt : values[index]? = some value) :
    ∃ final reached after,
      NativeTypeViews.sourceNode ops reads true (.symbol head) values =
        [ops.normalize (ops.apply final range)] ∧
      NativeTypeViews.sourceArgs ops reads (formals.take index) (values.take index) ops.initial = some reached ∧
      FieldStep ops reads formal value reached after ∧
      NativeTypeViews.sourceArgs ops reads (formals.drop (index + 1)) (values.drop (index + 1)) after = some final := by
  obtain ⟨final, checked, result⟩ :=
    HEConstructorDeclarationGuard.positive_count_earns_argument_check ops reads rows head values accepted
      annotationRead ordinary row range formals headRead arrow positive
  obtain ⟨reached, after, start, step, finish⟩ :=
    source_argument_at ops reads formals values index formal value ops.initial final formalAt valueAt checked
  exact ⟨final, reached, after, result, start, step, finish⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection
