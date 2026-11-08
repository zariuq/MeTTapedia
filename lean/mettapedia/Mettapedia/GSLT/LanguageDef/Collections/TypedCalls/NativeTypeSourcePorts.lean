import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety

/-!
# Source-derived primitive ports for recursive type inference

The ports use the actual annotation reader, explicit declaration freshening,
and completed subtype-closure rounds. Intrinsic symbol declarations take
precedence over user rows when present. The represented scalar codec covers
integers, Booleans and strings; other native grounded representations remain
outside this codec and decline rather than receive an invented type.

Closure inputs are justified by the adaptive plan's key invariant. The port
does not replace an unfinished closure with an empty answer or assume every
finite source has terminating subtype closure. Native intrinsic-table and
fresh-name representation correspondence remain explicit adapter obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSourcePorts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open TypeDependencyAdmission NativeTypeCallGraph NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView)

structure Source where
  rows : List Atom
  intrinsicRows : List Atom
  rename : Atom → Nat → String → String
  subtypeBudget : Nat
  subtypeFresh : String
  alpha : Atom → Atom → Bool

def Safe (source : Source) : Prop :=
  resourceFreeList source.rows = true ∧ resourceFreeList source.intrinsicRows = true

def rawDeclarations (source : Source) (world : ExternalView) (atom : Atom) : List Atom :=
  let user := getAnnotatedTypes (observedSpace world source.rows) atom
  match atom with
  | .symbol _ =>
      let intrinsic := getAnnotatedTypes (observedSpace world source.intrinsicRows) atom
      if intrinsic.isEmpty then user else intrinsic
  | _ => user

def declarations (source : Source) (world : ExternalView) (atom : Atom) : List Atom :=
  (rawDeclarations source world atom).zipIdx.map fun (type_, index) =>
    renameAtom (source.rename atom index) type_

theorem rawDeclarations_safe (source : Source) (safe : Safe source) (world : ExternalView) (atom : Atom) :
    resourceFreeList (rawDeclarations source world atom) = true := by
  have userSafe : resourceFreeList (getAnnotatedTypes (observedSpace world source.rows) atom) = true := by
    apply (resourceFreeList_iff _).mpr
    intro type_ member
    simp only [observedSpace, observeList_resourceFree world _ safe.1] at member
    exact annotation_resourceFree safe.1 atom member
  have intrinsicSafe : resourceFreeList (getAnnotatedTypes (observedSpace world source.intrinsicRows) atom) = true := by
    apply (resourceFreeList_iff _).mpr
    intro type_ member
    simp only [observedSpace, observeList_resourceFree world _ safe.2] at member
    exact annotation_resourceFree safe.2 atom member
  cases atom <;> simp only [rawDeclarations]
  · split <;> assumption
  · exact userSafe
  · exact userSafe
  · exact userSafe

theorem declarations_safe (source : Source) (safe : Safe source) (world : ExternalView) (atom : Atom) :
    resourceFreeList (declarations source world atom) = true := by
  apply (resourceFreeList_iff _).mpr
  intro type_ member
  obtain ⟨⟨original, index⟩, present, rfl⟩ := List.mem_map.mp member
  rw [rename_resourceFree]
  exact (resourceFreeList_iff _).mp (rawDeclarations_safe source safe world atom) original
    (List.fst_mem_of_mem_zipIdx present)

theorem declarations_world (source : Source) (safe : Safe source) (first second : ExternalView) (atom : Atom) :
    declarations source first atom = declarations source second atom := by
  simp only [declarations, rawDeclarations, observedSpace,
    observeList_resourceFree first _ safe.1, observeList_resourceFree second _ safe.1,
    observeList_resourceFree first _ safe.2, observeList_resourceFree second _ safe.2]

def nativeClassify (head : Atom) (values : List Atom) : NativeTypeViews.HeadClass :=
  if head == .symbol "NativeHandle" then
    match values with
    | [kind, _] =>
        if kind == .symbol "mork-space" || kind == .grounded (.string "mork-space") then .nativeMork
        else .ordinary
    | _ => .ordinary
  else .ordinary

def primitive (source : Source) (world : ExternalView) : Primitive → Option Reply
  | .annotations atom => some (.types (declarations source world atom))
  | .intrinsic (.grounded (.int value)) => some (.types [getGroundedType (.int value)])
  | .intrinsic (.grounded (.bool value)) => some (.types [getGroundedType (.bool value)])
  | .intrinsic (.grounded (.string value)) => some (.types [getGroundedType (.string value)])
  | .intrinsic _ => none
  | .kind atom => some (.kind (getMetaType atom))
  | .classify head values => some (.class_ (nativeClassify head values))
  | .closure seeds =>
      (SubtypeClosureRounds.completeTypes source.alpha
        (fun type_ => TypeScopeClosure.subtypeQuery world type_ source.subtypeFresh source.rows)
        source.subtypeBudget seeds).map (fun types => .types types)

theorem primitive_safe (source : Source) (safe : Safe source) (world : ExternalView)
    (key : Primitive) (keySafe : KeySafe (.inl key)) (reply : Reply)
    (returned : primitive source world key = some reply) : ReplySafe reply := by
  cases key with
  | annotations atom =>
      cases Option.some.inj returned
      exact declarations_safe source safe world atom
  | kind atom => cases Option.some.inj returned; trivial
  | classify head values => cases Option.some.inj returned; trivial
  | intrinsic atom =>
      cases atom with
      | symbol _ | var _ | expression _ => cases returned
      | grounded value =>
          cases value with
          | int _ => cases Option.some.inj returned; rfl
          | bool _ => cases Option.some.inj returned; rfl
          | string _ => cases Option.some.inj returned; rfl
          | custom _ _ => cases returned
  | closure seeds =>
      simp only [primitive, Option.map_eq_some_iff] at returned
      obtain ⟨types, completed, rfl⟩ := returned
      exact SubtypeClosureRounds.completeTypes_source_safe source.alpha world source.rows safe.1
        source.subtypeFresh source.subtypeBudget seeds keySafe types completed

theorem primitive_world (source : Source) (safe : Safe source) (first second : ExternalView)
    (key : Primitive) (keySafe : KeySafe (.inl key)) :
    primitive source first key = primitive source second key := by
  cases key with
  | annotations atom => simp only [primitive, declarations_world source safe first second atom]
  | intrinsic atom =>
      cases atom with
      | symbol _ | var _ | expression _ => rfl
      | grounded value => cases value <;> rfl
  | kind atom => rfl
  | classify head values => rfl
  | closure seeds =>
      simp only [primitive]
      rw [SubtypeClosureRounds.completeTypes_source_world source.alpha first second source.rows safe.1
        source.subtypeFresh source.subtypeBudget seeds keySafe]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSourcePorts
