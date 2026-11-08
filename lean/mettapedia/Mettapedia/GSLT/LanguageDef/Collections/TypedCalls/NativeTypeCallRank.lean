import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph
import Mettapedia.Machines.ReadOnlyQueryRelation

/-!
# Structural rank of the actual adaptive inference call graph

Tuple/operator wrappers may request inference of the same term; their phase
therefore contributes one rank unit. An inference node requests wrappers or
inference only on its proper expression children. Type replies, instantiated
signatures and normalized output sizes do not alter that input-side descent.

The query invariant restricts keys only. Every possible reply is covered,
including malformed replies, so this is not a completed-oracle assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallRank

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQuerySafety
open NativeTypeCallGraph

noncomputable def rank : Call → Nat
  | .infer _ atom => 2 * sizeOf atom
  | .tuplePart _ atom | .operatorRows atom => 2 * sizeOf atom + 1

def KeyBelow (bound : Nat) : Question → Prop
  | .inl _ => True
  | .inr child => rank child < bound

abbrev KeysBelow {Answer : Type} (bound : Nat) (program : Program Question Reply Answer) : Prop :=
  Guarantees (KeyBelow bound) (fun _ => True) (fun _ => True) program

abbrev ViewKeysBelow {Answer : Type} (bound : Nat)
    (program : Program (NativeTypeDemand.Question Atom) Reply Answer) : Prop :=
  Guarantees (fun key => KeyBelow bound (viewQuestion key)) (fun _ => True) (fun _ => True) program

theorem child_size (atoms : List Atom) (atom : Atom) (member : atom ∈ atoms) :
    sizeOf atom < sizeOf (Atom.expression atoms) := by
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Atom.expression.sizeOf_spec]
  omega

theorem inferred_child (direct : Bool) (head atom : Atom) (values : List Atom)
    (member : atom ∈ head :: values) : rank (.infer true atom) < rank (.infer direct (.expression (head :: values))) := by
  have smaller := child_size (head :: values) atom member
  simp only [rank]
  omega

theorem wrapped_child (direct atHead : Bool) (head atom : Atom) (values : List Atom)
    (member : atom ∈ head :: values) :
    rank (.tuplePart atHead atom) < rank (.infer direct (.expression (head :: values))) ∧
    rank (.operatorRows atom) < rank (.infer direct (.expression (head :: values))) := by
  have smaller := child_size (head :: values) atom member
  simp only [rank]
  omega

theorem map_keys {Answer Other : Type} (bound : Nat) (program : Program Question Reply Answer)
    (safe : KeysBelow bound program) (convert : Answer → Other) : KeysBelow bound (map convert program) :=
  map_guarantees _ _ _ _ program safe convert (fun _ _ => trivial)

theorem view_map_keys {Answer Other : Type} (bound : Nat)
    (program : Program (NativeTypeDemand.Question Atom) Reply Answer)
    (safe : ViewKeysBelow bound program) (convert : Answer → Other) : ViewKeysBelow bound (map convert program) :=
  map_guarantees _ _ _ _ program safe convert (fun _ _ => trivial)

theorem lift_keys {Answer : Type} (bound : Nat)
    (program : Program (NativeTypeDemand.Question Atom) Reply Answer) (safe : ViewKeysBelow bound program) :
    KeysBelow bound (liftViews program) := by
  induction safe with
  | pure _ => exact .pure trivial
  | read keySafe children ih => exact .read keySafe ih

theorem types_keys {Answer : Type} (bound : Nat) (key : Question) (safeKey : KeyBelow bound key)
    (next : List Atom → Plan Answer) (safe : ∀ types, KeysBelow bound (next types)) :
    KeysBelow bound (typesRead key next) := by
  exact .read safeKey (fun reply _ => by cases reply with
    | types types => exact safe types
    | class_ _ | kind _ => exact .pure trivial)

theorem view_types_keys {Answer : Type} (bound : Nat) (key : NativeTypeDemand.Question Atom)
    (safeKey : KeyBelow bound (viewQuestion key))
    (next : List Atom → NativeTypeDemand.CheckedPlan Atom Atom Atom Answer)
    (safe : ∀ types, ViewKeysBelow bound (next types)) :
    ViewKeysBelow bound (NativeTypeDemand.typesRead key next) := by
  exact .read safeKey (fun reply _ => by cases reply with
    | types types => exact safe types
    | class_ _ | kind _ => exact .pure trivial)

theorem args_keys (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (bound : Nat) :
    ∀ (formals values : List Atom) (state : TypeScopeMatcher.State),
      (∀ atom ∈ values, rank (.infer true atom) < bound) →
      ViewKeysBelow bound (NativeTypeDemand.argsPlan ops formals values state)
  | [], [], _, _ => .pure trivial
  | [], _ :: _, _, _ => .pure trivial
  | _ :: _, [], _, _ => .pure trivial
  | formal :: formals, value :: values, state, smaller => by
      have tail := fun atom member => smaller atom (List.mem_cons_of_mem value member)
      apply Guarantees.read (by trivial)
      intro reply _
      cases reply with
      | class_ _ | types _ => exact .pure trivial
      | kind kind =>
          dsimp only
          cases metatype : ops.metaCheck (ops.apply state formal) kind with
          | some result =>
              cases result with
              | false => exact .pure trivial
              | true => exact args_keys ops bound formals values state tail
          | none =>
              apply view_types_keys bound (.inferred value) (smaller value (by simp))
              intro types
              cases selected : StampInference.firstResult
                  (fun actual => ops.unify state actual (ops.apply state formal)) types with
              | none => exact .pure trivial
              | some next => exact args_keys ops bound formals values next tail

theorem rows_keys (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (bound : Nat)
    (values : List Atom) (smaller : ∀ atom ∈ values, rank (.infer true atom) < bound) :
    ∀ rows, ViewKeysBelow bound (NativeTypeDemand.rowsPlan ops values rows)
  | [] => .pure trivial
  | row :: rows => by
      simp only [NativeTypeDemand.rowsPlan]
      cases arrow : ops.arrow row with
      | none => exact rows_keys ops bound values smaller rows
      | some signature =>
          obtain ⟨formals, range⟩ := signature
          apply bind_guarantees _ _ (fun _ => True) (fun _ => True)
            _ (args_keys ops bound formals values ops.initial smaller)
          intro answer _
          cases answer with
          | error _ => exact .pure trivial
          | ok selected =>
              cases selected with
              | none => exact rows_keys ops bound values smaller rows
              | some state => exact view_map_keys bound _ (rows_keys ops bound values smaller rows) _

theorem product_keys (bound : Nat) : ∀ keys : List (NativeTypeDemand.Question Atom),
    (∀ key ∈ keys, KeyBelow bound (viewQuestion key)) →
    ViewKeysBelow bound (NativeTypeDemand.productPlan keys)
  | [], _ => .pure trivial
  | key :: keys, safe => by
      apply view_types_keys bound key (safe key (by simp))
      intro types
      split
      · exact .pure trivial
      · exact view_map_keys bound _ (product_keys bound keys
          (fun key member => safe key (List.mem_cons_of_mem _ member))) _

theorem close_keys (bound : Nat) (types : List Atom) : KeysBelow bound (closeTypes types) :=
  types_keys bound (.inl (.closure types)) trivial _ (fun _ => .pure trivial)

theorem ordinary_keys (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (direct : Bool) (head : Atom) (values : List Atom) :
    KeysBelow (rank (.infer direct (.expression (head :: values)))) (ordinary ops head values) := by
  let bound := rank (.infer direct (.expression (head :: values)))
  have children : ∀ atom ∈ values, rank (.infer true atom) < bound :=
    fun atom member => inferred_child direct head atom values (List.mem_cons_of_mem _ member)
  apply types_keys bound (.inr (.operatorRows head)) ((wrapped_child direct true head head values (by simp)).2)
  intro rows
  split
  · exact map_keys bound _ (lift_keys bound _ (rows_keys ops bound values children rows)) _
  · apply bind_guarantees _ _ (fun _ => True) (fun _ => True)
    · apply lift_keys bound
      apply product_keys bound
      intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact (wrapped_child direct true head head values (by simp)).1
      · obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
        exact (wrapped_child direct false head atom values (List.mem_cons_of_mem _ present)).1
    · intro answer _
      cases answer with
      | error _ => exact .pure trivial
      | ok products =>
          simp only
          split
          · exact .pure trivial
          · exact close_keys bound _

theorem annotated_keys (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (direct : Bool) (head : Atom) (values annotations : List Atom) :
    KeysBelow (rank (.infer direct (.expression (head :: values)))) (annotated ops head values annotations) := by
  let bound := rank (.infer direct (.expression (head :: values)))
  cases policy : ops.annotationPolicy with
  | historicalOverride => simpa only [annotated, policy] using close_keys bound annotations
  | supplement same =>
      simp only [annotated, policy]
      apply types_keys bound (.inl (.closure annotations)) trivial
      intro closed
      apply types_keys bound (.inr (.operatorRows head)) ((wrapped_child direct true head head values (by simp)).2)
      intro rows
      split
      · exact map_keys bound _ (lift_keys bound _ (rows_keys ops bound values
          (fun atom member => inferred_child direct head atom values (List.mem_cons_of_mem _ member)) rows)) _
      · exact .pure trivial

theorem node_keys (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (direct : Bool) (head : Atom) (values : List Atom) :
    KeysBelow (rank (.infer direct (.expression (head :: values)))) (node ops direct head values) := by
  apply Guarantees.read trivial
  intro reply _
  cases reply with
  | types _ | kind _ => exact .pure trivial
  | class_ kind =>
      cases kind with
      | nativeMork | listValue => exact .pure trivial
      | ordinary =>
          cases direct with
          | false => exact ordinary_keys ops false head values
          | true =>
              apply types_keys _ (.inl (.annotations (.expression (head :: values)))) trivial
              intro annotations
              split
              · exact ordinary_keys ops true head values
              · exact annotated_keys ops true head values annotations

theorem body_keys_below (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (call : Call) :
    KeysBelow (rank call) (body ops call) := by
  cases call with
  | infer direct atom =>
      cases atom with
      | var _ => exact .pure trivial
      | grounded value =>
          apply types_keys _ (.inl (.intrinsic (.grounded value))) trivial
          intro types
          split <;> exact .pure trivial
      | symbol name =>
          cases direct with
          | false => exact .pure trivial
          | true =>
              apply types_keys _ (.inl (.annotations (.symbol name))) trivial
              intro types
              split
              · exact .pure trivial
              · exact close_keys _ types
      | expression atoms =>
          cases atoms with
          | nil => exact .pure trivial
          | cons head values => exact node_keys ops direct head values
  | tuplePart atHead atom =>
      cases atom with
      | var _ => exact .pure trivial
      | symbol name => exact types_keys _ (.inl (.annotations (.symbol name))) trivial _ (fun _ => .pure trivial)
      | grounded value => exact types_keys _ (.inl (.intrinsic (.grounded value))) trivial _ (fun _ => .pure trivial)
      | expression atoms =>
          exact types_keys _ (.inr (.infer true (.expression atoms)))
            (by simp [KeyBelow, rank]) _ (fun _ => .pure trivial)
  | operatorRows atom =>
      apply types_keys _ (.inl (.annotations atom)) trivial
      intro rows
      split
      · cases atom with
        | var _ | symbol _ | grounded _ => exact .pure trivial
        | expression atoms =>
            exact types_keys _ (.inr (.infer true (.expression atoms)))
              (by simp [KeyBelow, rank]) _ (fun _ => .pure trivial)
      · exact .pure trivial

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallRank
