import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety
import Mettapedia.Machines.ReadOnlyQueryRelation

/-!
# Continuation-wise world relation for adaptive type plans

The relation follows every resource-safe reply, not a fixed store indexed
by query keys. Consequently it can be interpreted by an occurrence-scoped
service whose repeated reads allocate different type-variable instances.
Unification is compared at each reached formal with its actual accumulated
substitution; normalization is compared only on resource-free returned types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePlanRelated

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQuerySafety (OnSuccess)
open Mettapedia.Machines.ReadOnlyQueryRelation
open TypeDependencyAdmission TypeScopeMatcher NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView)

theorem native_typesRead {Result : Type} (key : NativeTypeDemand.Question Atom)
    (first second : List Atom → NativeTypeDemand.CheckedPlan Atom Atom Atom Result)
    (good : Result → Prop)
    (later : ∀ types, resourceFreeList types = true →
      Related (fun _ => True) ReplySafe (OnSuccess good) (first types) (second types)) :
    Related (fun _ => True) ReplySafe (OnSuccess good)
      (NativeTypeDemand.typesRead key first) (NativeTypeDemand.typesRead key second) := by
  apply Related.read trivial
  intro reply safe
  cases reply with
  | types types => exact later types safe
  | class_ _ | kind _ => exact .pure trivial

theorem argsPlan (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) :
    ∀ (formals values : List Atom) (state : TypeScopeMatcher.State),
      resourceFreeList formals = true → SafeState state →
      Related (fun _ => True) ReplySafe (OnSuccess BindingSafe)
        (NativeTypeDemand.argsPlan (ops first normalizeFirst subtypesFirst) formals values state)
        (NativeTypeDemand.argsPlan (ops second normalizeSecond subtypesSecond) formals values state)
  | [], [], _, _, safe => .pure safe
  | [], _ :: _, _, _, _ => .pure trivial
  | _ :: _, [], _, _, _ => .pure trivial
  | formal :: formals, value :: values, state, formalsSafe, stateSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      apply Related.read trivial
      intro reply replySafe
      cases reply with
      | class_ _ | types _ => exact .pure trivial
      | kind kind =>
          simp only [ops]
          cases metaReply : metaCheckAtom (substA state formal) kind with
          | some answer =>
              cases answer with
              | false => exact .pure trivial
              | true =>
                  exact argsPlan first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
                    formals values state formalsSafe.2 stateSafe
          | none =>
              apply native_typesRead
              intro actuals actualsSafe
              have chosenEq := firstResult_congr_on
                (fun actual => unify first state actual (substA state formal))
                (fun actual => unify second state actual (substA state formal)) actuals
                (fun actual present => unify_world first second state stateSafe actual (substA state formal)
                  ((resourceFreeList_iff _).mp actualsSafe actual present) expectedSafe)
              rw [chosenEq]
              cases chosen : StampInference.firstResult
                  (fun actual => unify second state actual (substA state formal)) actuals with
              | none => exact .pure trivial
              | some next =>
                  exact argsPlan first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
                    formals values next formalsSafe.2
                    (firstResult_preserves second state stateSafe (substA state formal)
                      expectedSafe actuals actualsSafe next chosen)

theorem rowsPlan (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (values : List Atom) :
    ∀ rows, resourceFreeList rows = true →
      Related (fun _ => True) ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
        (NativeTypeDemand.rowsPlan (ops first normalizeFirst subtypesFirst) values rows)
        (NativeTypeDemand.rowsPlan (ops second normalizeSecond subtypesSecond) values rows)
  | [], _ => .pure rfl
  | row :: rows, rowsSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at rowsSafe
      have rest := rowsPlan first second normalizeFirst normalizeSecond normalizeSafe normalizers
        subtypesFirst subtypesSecond values rows rowsSafe.2
      have arrowEq : (ops first normalizeFirst subtypesFirst).arrow row =
          (ops second normalizeSecond subtypesSecond).arrow row := rfl
      simp only [NativeTypeDemand.rowsPlan, ← arrowEq]
      cases arrow : (ops first normalizeFirst subtypesFirst).arrow row with
      | none => exact rest
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          have parts := arrow_resourceFree first normalizeFirst subtypesFirst rowsSafe.1 arrow
          apply bind_related (fun _ => True) ReplySafe (OnSuccess BindingSafe) _
            (argsPlan first second normalizeFirst normalizeSecond subtypesFirst subtypesSecond
              formals values Atom.var parts.1 (fun _ => rfl))
          intro answer safe
          cases answer with
          | error _ => exact .pure trivial
          | ok selected =>
              cases selected with
              | none => exact rest
              | some state =>
                  have rangeSafe := substitute_resourceFree state safe range parts.2
                  apply map_related_of_agree (fun _ => True) ReplySafe
                    (OnSuccess (fun types => resourceFreeList types = true)) _ rest
                  · intro result _
                    simp only [ops, normalizers _ rangeSafe]
                  · intro result good
                    cases result with
                    | error _ => trivial
                    | ok types =>
                        exact Bool.and_eq_true_iff.mpr ⟨normalizeSafe _ rangeSafe, good⟩

theorem liftViews {Result : Type} (good : Result → Prop)
    (first second : Program (NativeTypeDemand.Question Atom) NativeTypeCallGraph.Reply Result)
    (related : Related (fun _ => True) ReplySafe good first second) :
    Related KeySafe ReplySafe good (NativeTypeCallGraph.liftViews first) (NativeTypeCallGraph.liftViews second) := by
  induction related with
  | pure valid => exact .pure valid
  | @read key left right keyGood children ih =>
      exact .read (viewQuestion_safe key) (fun reply safe => ih reply safe)

theorem typesRead {Result : Type} (key : NativeTypeCallGraph.Question) (safeKey : KeySafe key)
    (first second : List Atom → NativeTypeCallGraph.Plan Result) (good : Result → Prop)
    (later : ∀ types, resourceFreeList types = true →
      Related KeySafe ReplySafe (OnSuccess good) (first types) (second types)) :
    Related KeySafe ReplySafe (OnSuccess good)
      (NativeTypeCallGraph.typesRead key first) (NativeTypeCallGraph.typesRead key second) := by
  apply Related.read safeKey
  intro reply safe
  cases reply with
  | types types => exact later types safe
  | class_ _ | kind _ => exact .pure trivial

theorem ordinary (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (head : Atom) (values : List Atom) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.ordinary (ops first normalizeFirst subtypesFirst) head values)
      (NativeTypeCallGraph.ordinary (ops second normalizeSecond subtypesSecond) head values) := by
  apply typesRead (.inr (.operatorRows head)) trivial
  intro rows safe
  have arrowEq : (rows.any fun row => ((ops first normalizeFirst subtypesFirst).arrow row).isSome) =
      (rows.any fun row => ((ops second normalizeSecond subtypesSecond).arrow row).isSome) := rfl
  simp only [← arrowEq]
  split
  · apply map_related KeySafe ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
    · exact liftViews _ _ _ (rowsPlan first second normalizeFirst normalizeSecond normalizeSafe normalizers
        subtypesFirst subtypesSecond values rows safe)
    · intro result good
      cases result <;> exact good
  · apply refl_of_guarantees
    apply Mettapedia.Machines.ReadOnlyQuerySafety.bind_guarantees KeySafe ReplySafe (OnSuccess ProductSafe)
    · exact NativeTypeCallGraphSafety.liftViews _ _ (NativeTypeCallGraphSafety.productPlan _)
    · intro result good
      cases result with
      | error _ => exact .pure trivial
      | ok products =>
          simp only
          split
          · exact NativeTypeCallGraphSafety.finishTypes _ rfl
          · exact NativeTypeCallGraphSafety.closeTypes _ (tuple_product_safe products good)

theorem node (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (direct : Bool) (head : Atom) (values : List Atom) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.node (ops first normalizeFirst subtypesFirst) direct head values)
      (NativeTypeCallGraph.node (ops second normalizeSecond subtypesSecond) direct head values) := by
  apply Related.read trivial
  intro reply safe
  cases reply with
  | types _ | kind _ => exact .pure trivial
  | class_ kind =>
      cases kind with
      | nativeMork | listValue => exact .pure rfl
      | ordinary =>
          cases direct with
          | false =>
              exact ordinary first second normalizeFirst normalizeSecond normalizeSafe normalizers
                subtypesFirst subtypesSecond head values
          | true =>
              apply typesRead (.inl (.annotations (.expression (head :: values)))) trivial
              intro types typesSafe
              split
              · exact ordinary first second normalizeFirst normalizeSecond normalizeSafe normalizers
                  subtypesFirst subtypesSecond head values
              · exact refl_of_guarantees _ _ _ _ (NativeTypeCallGraphSafety.closeTypes _ typesSafe)

theorem body (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (call : NativeTypeCallGraph.Call) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.body (ops first normalizeFirst subtypesFirst) call)
      (NativeTypeCallGraph.body (ops second normalizeSecond subtypesSecond) call) := by
  cases call with
  | infer direct atom =>
      cases atom with
      | var name => exact .pure rfl
      | symbol name =>
          exact refl_of_guarantees _ _ _ _
            (NativeTypeCallGraphSafety.body first normalizeFirst normalizeSafe subtypesFirst (.infer direct (.symbol name)))
      | grounded value =>
          exact refl_of_guarantees _ _ _ _
            (NativeTypeCallGraphSafety.body first normalizeFirst normalizeSafe subtypesFirst (.infer direct (.grounded value)))
      | expression children =>
          cases children with
          | nil => exact .pure rfl
          | cons head values =>
              exact node first second normalizeFirst normalizeSecond normalizeSafe normalizers
                subtypesFirst subtypesSecond direct head values
  | tuplePart atHead atom =>
      exact refl_of_guarantees _ _ _ _
        (NativeTypeCallGraphSafety.body first normalizeFirst normalizeSafe subtypesFirst (.tuplePart atHead atom))
  | operatorRows atom =>
      exact refl_of_guarantees _ _ _ _
        (NativeTypeCallGraphSafety.body first normalizeFirst normalizeSafe subtypesFirst (.operatorRows atom))

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePlanRelated
