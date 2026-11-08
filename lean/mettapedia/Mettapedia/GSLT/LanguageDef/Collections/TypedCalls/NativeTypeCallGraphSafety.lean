import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph
import Mettapedia.Machines.ReadOnlyQuerySafety

/-! # Resource closure of the actual adaptive type plans -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQuerySafety
open TypeDependencyAdmission TypeScopeMatcher NativeTypeCallGraph NativeTypeViews

def ReplySafe : Reply → Prop
  | .types types => resourceFreeList types = true
  | _ => True

def BindingSafe : Option TypeScopeMatcher.State → Prop
  | none => True
  | some state => SafeState state

theorem native_typesRead {Result : Type} (key : NativeTypeDemand.Question Atom)
    (next : List Atom → NativeTypeDemand.CheckedPlan Atom Atom Atom Result) (good : Result → Prop)
    (later : ∀ types, resourceFreeList types = true → Guarantees (fun _ => True) ReplySafe (OnSuccess good) (next types)) :
    Guarantees (fun _ => True) ReplySafe (OnSuccess good) (NativeTypeDemand.typesRead key next) := by
  apply Guarantees.read trivial
  intro reply safe
  cases reply with
  | types types => exact later types safe
  | class_ _ => exact .pure trivial
  | kind _ => exact .pure trivial

theorem argsPlan (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) : ∀ (formals values : List Atom) (state : TypeScopeMatcher.State),
    resourceFreeList formals = true → SafeState state →
      Guarantees (fun _ => True) ReplySafe (OnSuccess BindingSafe)
        (NativeTypeDemand.argsPlan (TypeScopeMatcher.ops world normalize subtypes) formals values state)
  | [], [], state, _, safe => .pure safe
  | [], _ :: _, _, _, _ => .pure trivial
  | _ :: _, [], _, _, _ => .pure trivial
  | formal :: formals, value :: values, state, formalsSafe, stateSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at formalsSafe
      have expectedSafe := substitute_resourceFree state stateSafe formal formalsSafe.1
      apply Guarantees.read trivial
      intro reply replySafe
      cases reply with
      | class_ _ => exact .pure trivial
      | types _ => exact .pure trivial
      | kind kind =>
          simp only [TypeScopeMatcher.ops]
          split
          · exact argsPlan world normalize subtypes formals values state formalsSafe.2 stateSafe
          · exact .pure trivial
          · apply native_typesRead
            intro actuals actualsSafe
            split
            · exact .pure trivial
            · rename_i next found
              exact argsPlan world normalize subtypes formals values next formalsSafe.2
                (firstResult_preserves world state stateSafe (substA state formal) expectedSafe
                  actuals actualsSafe next found)

theorem rowsPlan (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (values : List Atom) : ∀ rows,
    resourceFreeList rows = true →
      Guarantees (fun _ => True) ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
        (NativeTypeDemand.rowsPlan (TypeScopeMatcher.ops world normalize subtypes) values rows)
  | [], _ => .pure rfl
  | row :: rows, rowsSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at rowsSafe
      simp only [NativeTypeDemand.rowsPlan]
      cases arrow : (TypeScopeMatcher.ops world normalize subtypes).arrow row with
      | none => exact rowsPlan world normalize normalizeSafe subtypes values rows rowsSafe.2
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          have parts := arrow_resourceFree world normalize subtypes rowsSafe.1 arrow
          apply bind_guarantees (fun _ => True) ReplySafe (OnSuccess BindingSafe)
          · exact argsPlan world normalize subtypes formals values Atom.var parts.1 (fun _ => rfl)
          · intro result safe
            cases result with
            | error _ => exact .pure trivial
            | ok selected =>
                cases selected with
                | none => exact rowsPlan world normalize normalizeSafe subtypes values rows rowsSafe.2
                | some state =>
                    have rangeSafe := normalizeSafe _ (substitute_resourceFree state safe range parts.2)
                    apply map_guarantees (fun _ => True) ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
                    · exact rowsPlan world normalize normalizeSafe subtypes values rows rowsSafe.2
                    · intro result safe
                      cases result with
                      | error _ => trivial
                      | ok types => exact Bool.and_eq_true_iff.mpr ⟨rangeSafe, safe⟩

def ProductSafe (products : List (List Atom)) : Prop :=
  ∀ product ∈ products, resourceFreeList product = true

theorem productPlan : ∀ keys : List (NativeTypeDemand.Question Atom),
    Guarantees (fun _ => True) ReplySafe (OnSuccess ProductSafe) (NativeTypeDemand.productPlan keys)
  | [] => .pure (by intro product member; have same := List.mem_singleton.mp member; subst product; rfl)
  | key :: keys => by
      apply native_typesRead
      intro types typesSafe
      split
      · exact .pure (by intro product member; cases member)
      · apply map_guarantees (fun _ => True) ReplySafe (OnSuccess ProductSafe)
        · exact productPlan keys
        · intro result safe
          cases result with
          | error _ => trivial
          | ok tails =>
              intro product member
              obtain ⟨type_, inTypes, selected⟩ := List.mem_flatMap.mp member
              obtain ⟨tail, inTails, rfl⟩ := List.mem_map.mp selected
              exact Bool.and_eq_true_iff.mpr
                ⟨(resourceFreeList_iff _).mp typesSafe type_ inTypes, safe tail inTails⟩

def KeySafe : Question → Prop
  | .inl (.closure seeds) => resourceFreeList seeds = true
  | _ => True

theorem viewQuestion_safe (key : NativeTypeDemand.Question Atom) : KeySafe (viewQuestion key) := by
  cases key <;> trivial

theorem liftViews {Result : Type} (good : Result → Prop)
    (program : Program (NativeTypeDemand.Question Atom) Reply Result)
    (safe : Guarantees (fun _ => True) ReplySafe good program) :
    Guarantees KeySafe ReplySafe good (NativeTypeCallGraph.liftViews program) := by
  induction safe with
  | pure valid => exact .pure valid
  | @read key next keyGood children ih => exact .read (viewQuestion_safe key) (fun reply good => ih reply good)

theorem typesRead {Result : Type} (key : Question) (keySafe : KeySafe key) (next : List Atom → Plan Result) (good : Result → Prop)
    (later : ∀ types, resourceFreeList types = true → Guarantees KeySafe ReplySafe (OnSuccess good) (next types)) :
    Guarantees KeySafe ReplySafe (OnSuccess good) (NativeTypeCallGraph.typesRead key next) := by
  apply Guarantees.read keySafe
  intro reply safe
  cases reply with
  | types types => exact later types safe
  | class_ _ => exact .pure trivial
  | kind _ => exact .pure trivial

theorem finishTypes (types : List Atom) (safe : resourceFreeList types = true) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe) (NativeTypeCallGraph.finishTypes types) := .pure safe

theorem closeTypes (types : List Atom) (safe : resourceFreeList types = true) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe) (NativeTypeCallGraph.closeTypes types) :=
  typesRead (.inl (.closure types)) safe _ ReplySafe finishTypes

theorem filter_safe (predicate : Atom → Bool) (types : List Atom) (safe : resourceFreeList types = true) :
    resourceFreeList (types.filter predicate) = true := by
  apply (resourceFreeList_iff _).mpr
  intro type_ member
  exact (resourceFreeList_iff _).mp safe type_ (List.mem_of_mem_filter member)

theorem tuple_product_safe (products : List (List Atom)) (safe : ProductSafe products) :
    resourceFreeList (products.map Atom.expression) = true := by
  apply (resourceFreeList_iff _).mpr
  intro type_ member
  obtain ⟨product, present, rfl⟩ := List.mem_map.mp member
  exact safe product present

theorem ordinary (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (head : Atom) (values : List Atom) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.ordinary (TypeScopeMatcher.ops world normalize subtypes) head values) := by
  apply typesRead <;> try trivial
  intro rows rowsSafe
  split
  · apply map_guarantees KeySafe ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
    · exact liftViews _ _ (rowsPlan world normalize normalizeSafe subtypes values rows rowsSafe)
    · intro result safe
      cases result <;> exact safe
  · apply bind_guarantees KeySafe ReplySafe (OnSuccess ProductSafe)
    · exact liftViews _ _ (productPlan _)
    · intro result safe
      cases result with
      | error _ => exact .pure trivial
      | ok products =>
          simp only
          split
          · exact finishTypes _ rfl
          · exact closeTypes _ (tuple_product_safe products safe)

theorem node (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (direct : Bool) (head : Atom) (values : List Atom) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.node (TypeScopeMatcher.ops world normalize subtypes) direct head values) := by
  apply Guarantees.read trivial
  intro reply safe
  cases reply with
  | types _ => exact .pure trivial
  | kind _ => exact .pure trivial
  | class_ kind =>
      cases kind with
      | nativeMork => exact finishTypes _ rfl
      | listValue => exact finishTypes _ rfl
      | ordinary =>
          cases direct with
          | false => exact ordinary world normalize normalizeSafe subtypes head values
          | true =>
              apply typesRead <;> try trivial
              intro types typesSafe
              split
              · exact ordinary world normalize normalizeSafe subtypes head values
              · exact closeTypes _ typesSafe

theorem body (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (call : Call) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.body (TypeScopeMatcher.ops world normalize subtypes) call) := by
  cases call with
  | infer direct atom =>
      cases atom with
      | var _ => exact finishTypes _ rfl
      | grounded value =>
          apply typesRead <;> try trivial
          intro types typesSafe
          split
          · exact finishTypes _ rfl
          · exact finishTypes _ typesSafe
      | symbol _ =>
          cases direct with
          | false => exact finishTypes _ rfl
          | true =>
              apply typesRead <;> try trivial
              intro types typesSafe
              split
              · exact finishTypes _ rfl
              · exact closeTypes _ typesSafe
      | expression children =>
          cases children with
          | nil => exact finishTypes _ rfl
          | cons head values => exact node world normalize normalizeSafe subtypes direct head values
  | tuplePart atHead atom =>
      cases atom with
      | var _ => exact finishTypes [] rfl
      | symbol _ | grounded _ | expression _ =>
          apply typesRead <;> try trivial
          intro types typesSafe
          exact finishTypes _ (filter_safe _ _ typesSafe)
  | operatorRows atom =>
      apply typesRead <;> try trivial
      intro rows rowsSafe
      split
      · cases atom with
        | symbol _ | var _ | grounded _ => exact finishTypes [] rfl
        | expression _ =>
            apply typesRead <;> try trivial
            intro types typesSafe
            exact finishTypes _ (filter_safe _ _ typesSafe)
      · exact finishTypes _ rowsSafe

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety
