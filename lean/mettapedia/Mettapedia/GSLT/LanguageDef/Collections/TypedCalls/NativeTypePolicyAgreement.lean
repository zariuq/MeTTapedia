import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeAnnotationPolicy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

/-!
# Annotation-policy agreement on actual source reads

When the source has no expression-subject declarations, changing the
application-annotation policy preserves the entire occurrence-scoped query:
answers, unfinished reads and the final private-name supply. Symbol typing,
polymorphic arrow rows and subtype queries remain available. This is not an
agreement claim for sources containing expression-subject declarations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicyAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts NativeTypeViews
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

variable {State : Type}

theorem node_run (ops : Ops Atom TypeScopeMatcher.State Atom) (policy : AnnotationPolicy Atom)
    (service : State → Question → Option Reply × State)
    (empty : ∀ state head values,
      (service state (.inl (.annotations (.expression (head :: values))))).1 = some (.types []))
    (direct : Bool) (head : Atom) (values : List Atom) (state : State) :
    QueryState.run service (ReadOnlyQueryDemand.demand
      (node { ops with annotationPolicy := policy } direct head values)) state =
    QueryState.run service (ReadOnlyQueryDemand.demand (node ops direct head values)) state := by
  simp only [node, ReadOnlyQueryDemand.demand, QueryState.run]
  cases response : (service state (.inl (.classify head values))).1 with
  | none => rfl
  | some reply =>
      cases reply with
      | types _ | kind _ => rfl
      | class_ kind =>
          cases kind with
          | nativeMork | listValue => rfl
          | ordinary =>
              cases direct <;>
                simp [typesRead, ReadOnlyQueryDemand.demand, QueryState.run, empty,
                  NativeTypeAnnotationPolicy.ordinary_policy]

theorem body_run (ops : Ops Atom TypeScopeMatcher.State Atom) (policy : AnnotationPolicy Atom)
    (service : State → Question → Option Reply × State)
    (empty : ∀ state head values,
      (service state (.inl (.annotations (.expression (head :: values))))).1 = some (.types []))
    (call : Call) (state : State) :
    QueryState.run service (ReadOnlyQueryDemand.demand
      (body { ops with annotationPolicy := policy } call)) state =
    QueryState.run service (ReadOnlyQueryDemand.demand (body ops call)) state := by
  cases call with
  | infer direct atom =>
      cases atom with
      | symbol _ | grounded _ | var _ => rfl
      | expression children =>
          cases children with
          | nil => rfl
          | cons head values => exact node_run ops policy service empty direct head values state
  | tuplePart atHead atom => rfl
  | operatorRows atom => rfl

/-- Local source-side condition; it is checked before private freshening. -/
def NoExpressionRows (rows : List Atom) : Prop :=
  ∀ children type_, .expression [.symbol ":", .expression children, type_] ∉ rows

theorem annotated_empty {rows : List Atom} (absent : NoExpressionRows rows) (children : List Atom) :
    getAnnotatedTypes ⟨rows⟩ (.expression children) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro type_ present
  obtain ⟨row, member, selected⟩ := List.mem_filterMap.mp present
  split at selected
  next _ subject type_ =>
    split at selected
    next same =>
      have subjects := (beq_iff_eq.mp same)
      subst subject
      exact absent children type_ member
    next => cases selected
  next => cases selected

theorem raw_empty (source : Source) (world : ExternalView)
    (safe : TypeDependencyAdmission.resourceFreeList source.rows = true)
    (absent : NoExpressionRows source.rows) (children : List Atom) :
    rawDeclarations source world (.expression children) = [] := by
  simp only [rawDeclarations, TypeDependencyAdmission.observedSpace,
    TypeDependencyAdmission.observeList_resourceFree world source.rows safe]
  exact annotated_empty absent children

theorem evaluate_policy (ops : Ops Atom TypeScopeMatcher.State Atom) (policy : AnnotationPolicy Atom)
    (source : Source) (world : ExternalView)
    (empty : ∀ children, rawDeclarations source world (.expression children) = [])
    (depth : Nat) : ∀ call supply,
    NativeTypeScopedReads.evaluate { ops with annotationPolicy := policy } source world depth call supply =
      NativeTypeScopedReads.evaluate ops source world depth call supply := by
  induction depth with
  | zero => intro call supply; rfl
  | succ depth ih =>
      intro call supply
      dsimp only [NativeTypeScopedReads.evaluate]
      simp only [ih]
      have agreement := body_run ops policy
        (fun current => fun
          | Sum.inl key => NativeTypeScopedReads.primitive source world current key
          | Sum.inr child => NativeTypeScopedReads.evaluate ops source world depth child current)
        (fun current head values => by
          simp [NativeTypeScopedReads.primitive, empty, TypeReadSupply.freshList]) call supply
      exact congrArg (fun result =>
        let answer := NativeTypeRecursiveDriver.completed result.answer
        (answer, NativeTypeScopedReads.retain result.state answer)) agreement

theorem evaluate_policy_of_rows (ops : Ops Atom TypeScopeMatcher.State Atom)
    (policy : AnnotationPolicy Atom) (source : Source) (world : ExternalView)
    (safe : TypeDependencyAdmission.resourceFreeList source.rows = true)
    (absent : NoExpressionRows source.rows) (depth : Nat) (call : Call) (supply : Supply) :
    NativeTypeScopedReads.evaluate { ops with annotationPolicy := policy } source world depth call supply =
      NativeTypeScopedReads.evaluate ops source world depth call supply :=
  evaluate_policy ops policy source world (raw_empty source world safe absent) depth call supply

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicyAgreement
