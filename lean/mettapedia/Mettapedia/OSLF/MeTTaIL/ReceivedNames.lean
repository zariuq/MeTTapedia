import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Received names: the whole-name law and name resolution

Binder elimination for a reflective presentation is the transparent
simultaneous substitution of `QuoteEnvironment.lean` together with one law at
the declared drop: a drop whose payload is, through units and nesting of the
declared parallel composition, exactly a variable that the substitution
replaces with a quotation runs the quoted process.  A literal dropped
quotation stays inert; the law is sensitive to provenance.

Name resolution is a separate pass: it orients the declared quote/drop
equation through units of the parallel composition.  Elimination is applied
to resolved terms.

Main results:

* `eliminate_isWellScopedAt`: scope.
* `eliminate_eliminate`: successive eliminations compose when every
  substituted value is a name (variable, metavariable or quotation) and
  every drop in the term receives a name.  `composition_needs_named_drops`
  shows the second condition cannot be dropped on one carrier.
* `resolve_quote_drop`, `resolve_quote_parallel_drop`: the declared name
  equations.
* `coherent_parallel_unit_right`, `coherent_unit_parallel`,
  `coherent_drop_payload_unit`: elimination after resolution respects
  parallel-unit re-spelling up to `canonicalEquivalent`.
* `eliminate_closure`: on a contextual quotation with a sealed body,
  elimination acts on the environment only.
* `realize_contextual_one`: realizing a one-entry environment commutes with
  elimination.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReceivedNames

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

variable (decl : ReflectivePresentationDecl)

/-! ## Leaves of the declared parallel composition -/

mutual
  /-- The non-unit leaves of the declared parallel composition, flattening
  nested compositions. -/
  def leaves : Pattern → List Pattern
    | .bvar index => [.bvar index]
    | .fvar name => [.fvar name]
    | .apply constructor [] =>
        if constructor = decl.parallelUnitConstructor then [] else [.apply constructor []]
    | .apply constructor (argument :: arguments) =>
        [.apply constructor (argument :: arguments)]
    | .lambda name body => [.lambda name body]
    | .multiLambda arity names body => [.multiLambda arity names body]
    | .subst body value => [.subst body value]
    | .collection kind elements none =>
        if kind = decl.parallelCollection then leavesList elements
        else [.collection kind elements none]
    | .collection kind elements (some rest) => [.collection kind elements (some rest)]

  def leavesList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => leaves pattern ++ leavesList patterns
end

theorem leavesList_eq_flatMap :
    ∀ patterns : List Pattern, leavesList decl patterns = patterns.flatMap (leaves decl)
  | [] => rfl
  | pattern :: patterns => by
      simp [leavesList, leavesList_eq_flatMap patterns]

/-- A name: a variable, a metavariable, or a quotation. -/
def isName : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply constructor [_] => decide (constructor = decl.quoteConstructor)
  | _ => false

/-- The variable a drop receives, seen through units of the parallel
composition. -/
def receivedIndex? (payload : Pattern) : Option Nat :=
  match leaves decl payload with
  | [.bvar index] => some index
  | _ => none

/-- The process held by a quotation. -/
def quotedProcess? : Pattern → Option Pattern
  | .apply constructor [process] =>
      if constructor = decl.quoteConstructor then some process else none
  | _ => none

/-- The whole-name law: the process run by a drop of a variable that the
assignment replaces with a quotation. -/
def activation? (σ : Assignment) (constructor : String) (arguments : List Pattern) :
    Option Pattern :=
  if constructor = decl.dropConstructor then
    match arguments with
    | [payload] => (receivedIndex? decl payload).bind fun index => quotedProcess? decl (σ index)
    | _ => none
  else none

mutual
  /-- Simultaneous binder elimination with the whole-name law. -/
  def eliminate (σ : Assignment) : Pattern → Pattern
    | .bvar index => σ index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        (activation? decl σ constructor arguments).getD
          (.apply constructor (eliminateList σ arguments))
    | .lambda name body => .lambda name (eliminate (lift 1 σ) body)
    | .multiLambda arity names body =>
        .multiLambda arity names (eliminate (lift arity σ) body)
    | .subst body value => .subst (eliminate (lift 1 σ) body) (eliminate σ value)
    | .collection kind elements rest => .collection kind (eliminateList σ elements) rest

  def eliminateList (σ : Assignment) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => eliminate σ pattern :: eliminateList σ patterns
end

@[simp] theorem eliminateList_eq_map (σ : Assignment) :
    ∀ patterns : List Pattern, eliminateList decl σ patterns = patterns.map (eliminate decl σ)
  | [] => rfl
  | pattern :: patterns => by
      simp only [eliminateList, List.map_cons, eliminateList_eq_map σ patterns]

theorem activation?_eq_some {σ : Assignment} {constructor : String}
    {arguments : List Pattern} {process : Pattern}
    (h : activation? decl σ constructor arguments = some process) :
    ∃ payload index, constructor = decl.dropConstructor ∧ arguments = [payload] ∧
      leaves decl payload = [.bvar index] ∧
      σ index = .apply decl.quoteConstructor [process] := by
  unfold activation? at h
  split at h
  · rename_i dropped
    split at h
    · rename_i payload
      unfold receivedIndex? at h
      split at h
      · rename_i index hleaves
        refine ⟨payload, index, dropped, rfl, hleaves, ?_⟩
        simp only [Option.bind_some] at h
        unfold quotedProcess? at h
        split at h
        · rename_i quote process'
          split at h
          · rename_i isQuote
            cases h
            rw [‹σ index = _›, isQuote]
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem activation?_of_ne {σ : Assignment} {constructor : String}
    (ne : constructor ≠ decl.dropConstructor) (arguments : List Pattern) :
    activation? decl σ constructor arguments = none := by
  simp [activation?, ne]

theorem eliminate_apply_of_ne {σ : Assignment} {constructor : String}
    (ne : constructor ≠ decl.dropConstructor) (arguments : List Pattern) :
    eliminate decl σ (.apply constructor arguments) =
      .apply constructor (arguments.map (eliminate decl σ)) := by
  simp [eliminate, activation?_of_ne decl ne]

/-! ## Scope -/

theorem mem_leaves_isWellScopedAt {depth : Nat} {pattern : Pattern}
    (inScope : pattern.isWellScopedAt depth = true) :
    ∀ leaf ∈ leaves decl pattern, leaf.isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simpa [leaves] using inScope
  | hfvar name => simp [leaves, Pattern.isWellScopedAt]
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          intro leaf member
          simp only [leaves] at member
          split at member
          · simp at member
          · simp only [List.mem_singleton] at member
            subst member
            exact inScope
      | cons argument arguments =>
          intro leaf member
          simp only [leaves, List.mem_singleton] at member
          subst member
          exact inScope
  | hlambda name body ih =>
      intro leaf member
      simp only [leaves, List.mem_singleton] at member
      subst member
      exact inScope
  | hmultiLambda arity names body ih =>
      intro leaf member
      simp only [leaves, List.mem_singleton] at member
      subst member
      exact inScope
  | hsubst body value ihBody ihValue =>
      intro leaf member
      simp only [leaves, List.mem_singleton] at member
      subst member
      exact inScope
  | hcollection kind elements rest ih =>
      intro leaf member
      cases rest with
      | none =>
          simp only [leaves] at member
          split at member
          · rw [leavesList_eq_flatMap, List.mem_flatMap] at member
            obtain ⟨element, elementMember, leafMember⟩ := member
            simp only [Pattern.isWellScopedAt] at inScope
            exact ih element elementMember
              ((isWellScopedListAt_eq_true_iff _ _).mp inScope element elementMember)
              leaf leafMember
          · simp only [List.mem_singleton] at member
            subst member
            exact inScope
      | some rest =>
          simp only [leaves, List.mem_singleton] at member
          subst member
          exact inScope

/-- **Scope.** -/
theorem eliminate_isWellScopedAt {source target : Nat} {σ : Assignment}
    (wellScoped : WellScopedAssignment source target σ) {pattern : Pattern}
    (inScope : pattern.isWellScopedAt source = true) :
    (eliminate decl σ pattern).isWellScopedAt target = true := by
  induction pattern using Pattern.inductionOn generalizing source target σ with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
      exact wellScoped index inScope
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      have each := (isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [eliminate]
      cases h : activation? decl σ constructor arguments with
      | some process =>
          obtain ⟨payload, index, -, rfl, hleaves, hquote⟩ := activation?_eq_some decl h
          have indexScoped := mem_leaves_isWellScopedAt decl (each payload (by simp))
            (.bvar index) (by simp [hleaves])
          simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at indexScoped
          have := wellScoped index indexScoped
          rw [hquote] at this
          simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using this
      | none =>
          simp only [Option.getD_none, Pattern.isWellScopedAt, eliminateList_eq_map]
          rw [isWellScopedListAt_eq_true_iff]
          intro element member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember wellScoped (each original originalMember)
  | hlambda name body ih =>
      simp only [Pattern.isWellScopedAt] at inScope ⊢
      exact ih (wellScoped.lift 1) inScope
  | hmultiLambda arity names body ih =>
      simp only [Pattern.isWellScopedAt] at inScope ⊢
      exact ih (wellScoped.lift arity) inScope
  | hsubst body value ihBody ihValue =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
      simp only [eliminate, Pattern.isWellScopedAt, Bool.and_eq_true]
      exact ⟨ihBody (wellScoped.lift 1) inScope.1, ihValue wellScoped inScope.2⟩
  | hcollection kind elements rest ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      have each := (isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [eliminate, Pattern.isWellScopedAt, eliminateList_eq_map]
      rw [isWellScopedListAt_eq_true_iff]
      intro element member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember wellScoped (each original originalMember)

/-- **Scope of one elimination.** -/
theorem eliminate_single_isWellScopedAt {depth : Nat} {replacement body : Pattern}
    (bodyScoped : body.isWellScopedAt (depth + 1) = true)
    (replacementScoped : replacement.isWellScopedAt depth = true) :
    (eliminate decl (single replacement) body).isWellScopedAt depth = true := by
  refine eliminate_isWellScopedAt decl ?_ bodyScoped
  intro index below
  cases index with
  | zero => exact replacementScoped
  | succ index =>
      simp only [single, Pattern.isWellScopedAt]
      exact decide_eq_true (by omega)

/-! ## Lifting -/

/-- The image of an index under `liftBVars cutoff amount`. -/
def shiftIndex (cutoff amount index : Nat) : Nat :=
  if index ≥ cutoff then index + amount else index

theorem liftBVars_bvar (cutoff amount index : Nat) :
    liftBVars cutoff amount (.bvar index) = .bvar (shiftIndex cutoff amount index) := by
  simp only [liftBVars, shiftIndex]
  split <;> rfl

theorem leaves_liftBVars (cutoff amount : Nat) (pattern : Pattern) :
    leaves decl (liftBVars cutoff amount pattern) =
      (leaves decl pattern).map (liftBVars cutoff amount) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index => simp [liftBVars_bvar, leaves]
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          simp only [liftBVars, liftBVarsList, leaves]
          split <;> simp [liftBVars, liftBVarsList]
      | cons argument arguments => simp [liftBVars, liftBVarsList_eq_map, leaves]
  | hlambda _ _ _ => simp [liftBVars, leaves]
  | hmultiLambda _ _ _ _ => simp [liftBVars, leaves]
  | hsubst _ _ _ _ => simp [liftBVars, leaves]
  | hcollection kind elements rest ih =>
      cases rest with
      | none =>
          simp only [liftBVars, liftBVarsList_eq_map, leaves]
          split
          · rw [leavesList_eq_flatMap, leavesList_eq_flatMap, List.flatMap_map, List.map_flatMap]
            exact List.flatMap_congr fun element member => ih element member cutoff
          · simp [liftBVars, liftBVarsList_eq_map]
      | some _ => simp [liftBVars, liftBVarsList_eq_map, leaves]

theorem receivedIndex?_congr {left right : Pattern}
    (same : leaves decl left = leaves decl right) :
    receivedIndex? decl left = receivedIndex? decl right := by
  unfold receivedIndex?
  rw [same]

theorem receivedIndex?_liftBVars (cutoff amount : Nat) (pattern : Pattern) :
    receivedIndex? decl (liftBVars cutoff amount pattern) =
      (receivedIndex? decl pattern).map (shiftIndex cutoff amount) := by
  unfold receivedIndex?
  rw [leaves_liftBVars]
  generalize leaves decl pattern = found
  rcases found with _ | ⟨leaf, _ | ⟨second, rest⟩⟩
  · rfl
  · cases leaf <;> simp only [List.map_cons, List.map_nil, liftBVars_bvar] <;> rfl
  · simp only [List.map_cons]
    split <;> simp_all

theorem quotedProcess?_liftBVars (cutoff amount : Nat) (pattern : Pattern) :
    quotedProcess? decl (liftBVars cutoff amount pattern) =
      (quotedProcess? decl pattern).map (liftBVars cutoff amount) := by
  cases pattern with
  | apply constructor arguments =>
      rcases arguments with _ | ⟨process, _ | ⟨second, rest⟩⟩
      · rfl
      · simp only [liftBVars, liftBVarsList, quotedProcess?]
        split <;> rfl
      · rfl
  | bvar index => simp [liftBVars_bvar, quotedProcess?]
  | _ => rfl

theorem lift_shiftIndex (τ : Assignment) (cutoff amount index : Nat) :
    lift (cutoff + amount) τ (shiftIndex cutoff amount index) =
      liftBVars cutoff amount (lift cutoff τ index) := by
  have h := substitute_liftBVars τ (.bvar index) cutoff amount
  rw [liftBVars_bvar] at h
  exact h

theorem activation?_liftBVars (τ : Assignment) (cutoff amount : Nat) (constructor : String)
    (arguments : List Pattern) :
    activation? decl (lift (cutoff + amount) τ) constructor
        (arguments.map (liftBVars cutoff amount)) =
      (activation? decl (lift cutoff τ) constructor arguments).map
        (liftBVars cutoff amount) := by
  unfold activation?
  split
  · rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
    · rfl
    · simp only [List.map_cons, List.map_nil, receivedIndex?_liftBVars]
      cases receivedIndex? decl payload with
      | none => rfl
      | some index => simp [lift_shiftIndex, quotedProcess?_liftBVars]
    · rfl
  · rfl

/-- Elimination commutes with inserting an untouched context prefix. -/
theorem eliminate_liftBVars (τ : Assignment) (pattern : Pattern) (cutoff amount : Nat) :
    eliminate decl (lift (cutoff + amount) τ) (liftBVars cutoff amount pattern) =
      liftBVars cutoff amount (eliminate decl (lift cutoff τ) pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      rw [liftBVars_bvar]
      exact lift_shiftIndex τ cutoff amount index
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [liftBVars, liftBVarsList_eq_map, eliminate, eliminateList_eq_map,
        activation?_liftBVars]
      cases activation? decl (lift cutoff τ) constructor arguments with
      | some process => rfl
      | none =>
          simp only [Option.map_none, Option.getD_none, liftBVars, liftBVarsList_eq_map,
            List.map_map]
          congr 1
          exact List.map_congr_left fun p hp => ih p hp cutoff
  | hlambda name body ih =>
      simp only [liftBVars, eliminate, lift_lift]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + 1)
  | hmultiLambda arity names body ih =>
      simp only [liftBVars, eliminate, lift_lift]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + arity)
  | hsubst body value ihBody ihValue =>
      simp only [liftBVars, eliminate, lift_lift]
      congr 1
      · simpa only [Nat.add_right_comm] using ihBody (cutoff + 1)
      · exact ihValue cutoff
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, eliminate, eliminateList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun p hp => ih p hp cutoff

theorem eliminate_lift_comp (σ τ : Assignment) (arity : Nat) :
    (fun index => eliminate decl (lift arity τ) (lift arity σ index)) =
      lift arity (fun index => eliminate decl τ (σ index)) := by
  funext index
  by_cases below : index < arity
  · simp [lift, below, eliminate]
  · simp only [lift, below, ite_false]
    simpa only [Nat.zero_add, lift_zero] using
      eliminate_liftBVars decl τ (σ (index - arity)) 0 arity

/-! ## Composition -/

theorem activation?_nil (σ : Assignment) (constructor : String) :
    activation? decl σ constructor [] = none := by
  unfold activation?
  split <;> rfl

theorem leaves_eliminate (σ : Assignment) (pattern : Pattern) :
    leaves decl (eliminate decl σ pattern) =
      (leaves decl pattern).flatMap fun leaf => leaves decl (eliminate decl σ leaf) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [leaves]
  | hfvar _ => simp [leaves]
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          simp only [eliminate, activation?_nil, Option.getD_none, eliminateList]
          simp only [leaves]
          split <;> simp [eliminate, activation?_nil, leaves, *]
      | cons argument arguments => simp [leaves]
  | hlambda _ _ _ => simp [leaves]
  | hmultiLambda _ _ _ _ => simp [leaves]
  | hsubst _ _ _ _ => simp [leaves]
  | hcollection kind elements rest ih =>
      cases rest with
      | none =>
          simp only [eliminate, eliminateList_eq_map, leaves]
          split
          · rw [leavesList_eq_flatMap, leavesList_eq_flatMap, List.flatMap_map,
              List.flatMap_assoc]
            exact List.flatMap_congr fun element member => ih element member
          · next notParallel => simp [eliminate, leaves, notParallel]
      | some _ => simp [leaves]

theorem isName_cases {pattern : Pattern} (named : isName decl pattern = true) :
    (∃ index, pattern = .bvar index) ∨ (∃ name, pattern = .fvar name) ∨
      ∃ process, pattern = .apply decl.quoteConstructor [process] := by
  cases pattern with
  | bvar index => exact Or.inl ⟨index, rfl⟩
  | fvar name => exact Or.inr (Or.inl ⟨name, rfl⟩)
  | apply constructor arguments =>
      rcases arguments with _ | ⟨process, _ | ⟨second, rest⟩⟩
      · simp [isName] at named
      · simp only [isName, decide_eq_true_eq] at named
        exact Or.inr (Or.inr ⟨process, by rw [named]⟩)
      · simp [isName] at named
  | _ => simp [isName] at named

theorem isName_liftBVars (cutoff amount : Nat) {pattern : Pattern}
    (named : isName decl pattern = true) :
    isName decl (liftBVars cutoff amount pattern) = true := by
  rcases isName_cases decl named with ⟨index, rfl⟩ | ⟨name, rfl⟩ | ⟨process, rfl⟩
  · simp [liftBVars_bvar, isName]
  · rfl
  · simp [liftBVars, liftBVarsList, isName]

theorem isName_lift {σ : Assignment} (names : ∀ index, isName decl (σ index) = true)
    (arity : Nat) : ∀ index, isName decl (lift arity σ index) = true := by
  intro index
  simp only [lift]
  split
  · rfl
  · exact isName_liftBVars decl 0 arity (names _)

/-- A drop payload whose only leaf is a name. -/
def dropReceivesName : List Pattern → Bool
  | [payload] =>
      match leaves decl payload with
      | [leaf] => isName decl leaf
      | _ => false
  | _ => true

mutual
  /-- Every drop receives a name: rho's sorting of drop payloads, read on one
  carrier through units of the parallel composition. -/
  def namesAtDrops : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply constructor arguments =>
        (!(decide (constructor = decl.dropConstructor)) || dropReceivesName decl arguments) &&
          namesAtDropsList arguments
    | .lambda _ body => namesAtDrops body
    | .multiLambda _ _ body => namesAtDrops body
    | .subst body value => namesAtDrops body && namesAtDrops value
    | .collection _ elements _ => namesAtDropsList elements

  def namesAtDropsList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => namesAtDrops pattern && namesAtDropsList patterns
end

theorem namesAtDropsList_iff (patterns : List Pattern) :
    namesAtDropsList decl patterns = true ↔ ∀ p ∈ patterns, namesAtDrops decl p = true := by
  induction patterns with
  | nil => simp [namesAtDropsList]
  | cons head tail ih => simp [namesAtDropsList, ih]

theorem eliminate_quote (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (σ : Assignment) (process : Pattern) :
    eliminate decl σ (.apply decl.quoteConstructor [process]) =
      .apply decl.quoteConstructor [eliminate decl σ process] := by
  rw [eliminate_apply_of_ne decl distinct]
  rfl

theorem eliminate_drop (σ : Assignment) (payload : Pattern) :
    eliminate decl σ (.apply decl.dropConstructor [payload]) =
      ((receivedIndex? decl payload).bind fun index => quotedProcess? decl (σ index)).getD
        (.apply decl.dropConstructor [eliminate decl σ payload]) := by
  simp [eliminate, activation?]

theorem receivedIndex?_name_ne_bvar (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (σ : Assignment) {payload leaf : Pattern} (only : leaves decl payload = [leaf])
    (unreceived : ∀ index, leaf ≠ .bvar index) (named : isName decl leaf = true) :
    receivedIndex? decl payload = none ∧ receivedIndex? decl (eliminate decl σ payload) = none := by
  have elimLeaves : leaves decl (eliminate decl σ payload) = leaves decl (eliminate decl σ leaf) := by
    rw [leaves_eliminate, only]
    simp
  rcases isName_cases decl named with ⟨index, rfl⟩ | ⟨name, rfl⟩ | ⟨process, rfl⟩
  · exact absurd rfl (unreceived index)
  · constructor
    · simp [receivedIndex?, only]
    · rw [receivedIndex?_congr decl elimLeaves]
      rfl
  · constructor
    · simp [receivedIndex?, only]
    · rw [receivedIndex?_congr decl elimLeaves, eliminate_quote decl distinct]
      rfl

/-- **Composition.** Successive eliminations compose when every value of the
first assignment is a name and every drop of the term receives a name. -/
theorem eliminate_eliminate (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (pattern : Pattern) (dropsNamed : namesAtDrops decl pattern = true)
    (σ : Assignment) (names : ∀ index, isName decl (σ index) = true) (τ : Assignment) :
    eliminate decl τ (eliminate decl σ pattern) =
      eliminate decl (fun index => eliminate decl τ (σ index)) pattern := by
  induction pattern using Pattern.inductionOn generalizing σ τ with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [namesAtDrops, Bool.and_eq_true] at dropsNamed
      obtain ⟨dropOk, argumentsOk⟩ := dropsNamed
      have each := (namesAtDropsList_iff decl arguments).mp argumentsOk
      by_cases dropped : constructor = decl.dropConstructor
      · subst dropped
        have receives : dropReceivesName decl arguments = true := by simpa using dropOk
        rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
        · simp [eliminate, activation?_nil]
        · have payloadIh := ih payload (by simp) (each payload (by simp)) σ names τ
          obtain ⟨leaf, only, named⟩ : ∃ leaf, leaves decl payload = [leaf] ∧
              isName decl leaf = true := by
            simp only [dropReceivesName] at receives
            split at receives
            · next leaf found => exact ⟨leaf, found, receives⟩
            · cases receives
          rw [eliminate_drop, eliminate_drop]
          by_cases received : ∃ index, leaf = .bvar index
          · obtain ⟨index, rfl⟩ := received
            have atIndex : receivedIndex? decl payload = some index := by
              simp [receivedIndex?, only]
            have elimLeaves : leaves decl (eliminate decl σ payload) =
                leaves decl (σ index) := by
              rw [leaves_eliminate, only]
              simp [eliminate]
            rw [atIndex]
            simp only [Option.bind_some]
            rcases isName_cases decl (names index) with
              ⟨target, hσ⟩ | ⟨name, hσ⟩ | ⟨process, hσ⟩
            · rw [hσ]
              have atTarget : receivedIndex? decl (eliminate decl σ payload) = some target := by
                rw [receivedIndex?_congr decl elimLeaves, hσ]
                rfl
              simp only [quotedProcess?, Option.getD_none, eliminate_drop, atTarget,
                Option.bind_some, payloadIh]
              rfl
            · rw [hσ]
              have atName : receivedIndex? decl (eliminate decl σ payload) = none := by
                rw [receivedIndex?_congr decl elimLeaves, hσ]
                rfl
              simp only [quotedProcess?, Option.getD_none, eliminate_drop, atName,
                Option.bind_none, payloadIh]
              rfl
            · rw [hσ, eliminate_quote decl distinct]
              simp [quotedProcess?]
          · have unreceived : ∀ index, leaf ≠ .bvar index := fun index h => received ⟨index, h⟩
            obtain ⟨none₁, none₂⟩ :=
              receivedIndex?_name_ne_bvar decl distinct σ only unreceived named
            rw [none₁]
            simp only [Option.bind_none, Option.getD_none]
            rw [eliminate_drop, none₂]
            simp only [Option.bind_none, Option.getD_none, payloadIh]
        · have long : ∀ (σ' : Assignment) (xs : List Pattern), 2 ≤ xs.length →
              eliminate decl σ' (.apply decl.dropConstructor xs) =
                .apply decl.dropConstructor (xs.map (eliminate decl σ')) := by
            intro σ' xs atLeastTwo
            rcases xs with _ | ⟨a, _ | ⟨b, xs⟩⟩
            · simp at atLeastTwo
            · simp at atLeastTwo
            · simp [eliminate, activation?]
          rw [long σ _ (by simp), long τ _ (by simp), long _ _ (by simp), List.map_map]
          congr 1
          exact List.map_congr_left fun p hp => ih p hp (each p hp) σ names τ
      · rw [eliminate_apply_of_ne decl dropped, eliminate_apply_of_ne decl dropped,
          eliminate_apply_of_ne decl dropped, List.map_map]
        congr 1
        exact List.map_congr_left fun p hp => ih p hp (each p hp) σ names τ
  | hlambda name body ih =>
      simp only [namesAtDrops] at dropsNamed
      simp only [eliminate, ih dropsNamed _ (isName_lift decl names 1), eliminate_lift_comp]
  | hmultiLambda arity names' body ih =>
      simp only [namesAtDrops] at dropsNamed
      simp only [eliminate, ih dropsNamed _ (isName_lift decl names arity), eliminate_lift_comp]
  | hsubst body value ihBody ihValue =>
      simp only [namesAtDrops, Bool.and_eq_true] at dropsNamed
      simp only [eliminate, ihBody dropsNamed.1 _ (isName_lift decl names 1),
        ihValue dropsNamed.2 σ names, eliminate_lift_comp]
  | hcollection kind elements rest ih =>
      simp only [namesAtDrops] at dropsNamed
      have each := (namesAtDropsList_iff decl elements).mp dropsNamed
      simp only [eliminate, eliminateList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun p hp => ih p hp (each p hp) σ names τ

theorem lift_single_shiftIndex (value : Pattern) (cutoff index : Nat) :
    lift cutoff (single value) (shiftIndex cutoff 1 index) = .bvar index := by
  unfold shiftIndex
  by_cases above : index ≥ cutoff
  · simp only [above, ite_true, lift, show ¬ index + 1 < cutoff by omega, ite_false]
    rw [show index + 1 - cutoff = (index - cutoff) + 1 by omega]
    simp only [single, liftBVars, Nat.zero_le, ite_true]
    congr 1
    omega
  · simp [above, lift, show index < cutoff by omega]

/-- Eliminating a variable that does not occur. -/
theorem eliminate_lift_single_liftBVars (value pattern : Pattern) (cutoff : Nat) :
    eliminate decl (lift cutoff (single value)) (liftBVars cutoff 1 pattern) = pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      rw [liftBVars_bvar]
      exact lift_single_shiftIndex value cutoff index
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      have inert : activation? decl (lift cutoff (single value)) constructor
          (arguments.map (liftBVars cutoff 1)) = none := by
        unfold activation?
        split
        · rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
          · rfl
          · simp only [List.map_cons, List.map_nil, receivedIndex?_liftBVars]
            cases receivedIndex? decl payload with
            | none => rfl
            | some index => simp [lift_single_shiftIndex, quotedProcess?]
          · rfl
        · rfl
      simp only [liftBVars, liftBVarsList_eq_map, eliminate, eliminateList_eq_map, inert,
        Option.getD_none, List.map_map]
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun p hp => ih p hp cutoff
  | hlambda name body ih =>
      simp only [liftBVars, eliminate, lift_lift]
      exact congrArg (Pattern.lambda name) (ih (cutoff + 1))
  | hmultiLambda arity names body ih =>
      simp only [liftBVars, eliminate, lift_lift]
      exact congrArg (Pattern.multiLambda arity names) (ih (cutoff + arity))
  | hsubst body value' ihBody ihValue =>
      simp only [liftBVars, eliminate, lift_lift]
      exact congrArg₂ Pattern.subst (ihBody (cutoff + 1)) (ihValue cutoff)
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, eliminate, eliminateList_eq_map, List.map_map]
      congr 1
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun p hp => ih p hp cutoff

theorem isName_single {value : Pattern} (named : isName decl value = true) :
    ∀ index, isName decl (single value index) = true
  | 0 => named
  | _ + 1 => rfl

/-- **Successive eliminations.** With names as replacements:
`t[x := a][y := b] = t[y := b][x := a[y := b]]`. -/
theorem eliminate_single_single (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    {inner outer body : Pattern} (innerName : isName decl inner = true)
    (outerName : isName decl outer = true) (dropsNamed : namesAtDrops decl body = true) :
    eliminate decl (single outer) (eliminate decl (single inner) body) =
      eliminate decl (single (eliminate decl (single outer) inner))
        (eliminate decl (lift 1 (single outer)) body) := by
  rw [eliminate_eliminate decl distinct body dropsNamed (single inner)
      (isName_single decl innerName) (single outer),
    eliminate_eliminate decl distinct body dropsNamed (lift 1 (single outer))
      (isName_lift decl (isName_single decl outerName) 1) _]
  congr 1
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      have h := eliminate_lift_single_liftBVars decl
        (eliminate decl (single outer) inner) (single outer index) 0
      simp only [lift_zero] at h
      simp only [lift, show ¬ index + 1 < 1 by omega, ite_false, Nat.add_sub_cancel, h]
      rfl

/-! ## The drop condition is necessary on one carrier -/

section Necessity

/-- A reflective presentation on one carrier. -/
def oneCarrier : ReflectivePresentationDecl where
  name := "one"
  processSort := "Term"
  nameSort := "Term"
  quoteConstructor := "Quote"
  dropConstructor := "Drop"
  parallelCollection := .hashBag
  parallelUnitConstructor := "Nil"
  quoteDropEquation := "QuoteDrop"
  -- Closed: received names act only at exposed drops; quoted code stays opaque.
  quoteScope := .closed

/-- `**x`: a drop whose payload is a process, not a name. -/
def doubleDrop : Pattern := .apply "Drop" [.apply "Drop" [.bvar 0]]

/-- First `x := @y`, then `y := @0`. -/
def quotedVariable : Pattern := .apply "Quote" [.bvar 0]
def receivedNil : Pattern := .apply "Quote" [.apply "Nil" []]

/-- Every replacement is a name, but the drop of `*x` does not receive one.
Successive elimination runs `0`; the composed elimination leaves the
literal `*@0`, which is not equivalent to `0`. -/
theorem composition_needs_named_drops :
    namesAtDrops oneCarrier doubleDrop = false ∧
      (∀ index, isName oneCarrier (single quotedVariable index) = true) ∧
      eliminate oneCarrier (single receivedNil)
          (eliminate oneCarrier (single quotedVariable) doubleDrop) = .apply "Nil" [] ∧
      eliminate oneCarrier
          (fun index => eliminate oneCarrier (single receivedNil) (single quotedVariable index))
          doubleDrop = .apply "Drop" [receivedNil] ∧
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalEquivalent oneCarrier
          (.apply "Nil" []) (.apply "Drop" [receivedNil]) = false := by
  refine ⟨by decide, isName_single oneCarrier (by decide), by decide, by decide, by decide⟩

end Necessity

/-! ## Name resolution -/

/-- The declared quote/drop equation on resolved arguments, seen through
units and nesting of the parallel composition. -/
def finishResolve (constructor : String) (arguments : List Pattern) : Pattern :=
  if constructor = decl.quoteConstructor then
    match arguments with
    | [argument] =>
        match leaves decl argument with
        | [.apply drop [name]] =>
            if drop = decl.dropConstructor then name else .apply constructor arguments
        | _ => .apply constructor arguments
    | _ => .apply constructor arguments
  else .apply constructor arguments

mutual
  /-- Resolve every quoted drop `@(*n | 0 | …)` to the name `n`, bottom-up. -/
  def resolve : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments => finishResolve decl constructor (resolveList arguments)
    | .lambda name body => .lambda name (resolve body)
    | .multiLambda arity names body => .multiLambda arity names (resolve body)
    | .subst body value => .subst (resolve body) (resolve value)
    | .collection kind elements rest => .collection kind (resolveList elements) rest

  def resolveList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => resolve pattern :: resolveList patterns
end

theorem resolve_unit :
    resolve decl (.apply decl.parallelUnitConstructor []) =
      .apply decl.parallelUnitConstructor [] := by
  simp only [resolve, resolveList, finishResolve]
  split <;> rfl

theorem resolve_drop (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (term : Pattern) :
    resolve decl (.apply decl.dropConstructor [term]) =
      .apply decl.dropConstructor [resolve decl term] := by
  simp [resolve, resolveList, finishResolve, Ne.symm distinct]

/-- **Quote/drop law.** `@*t` resolves as `t`. -/
theorem resolve_quote_drop (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (term : Pattern) :
    resolve decl (.apply decl.quoteConstructor [.apply decl.dropConstructor [term]]) =
      resolve decl term := by
  rw [show resolve decl (.apply decl.quoteConstructor [.apply decl.dropConstructor [term]]) =
      finishResolve decl decl.quoteConstructor
        [resolve decl (.apply decl.dropConstructor [term])] from rfl, resolve_drop decl distinct]
  simp [finishResolve, leaves]

/-- The law seen through a parallel unit: `@(*t | 0)` resolves as `t`. -/
theorem resolve_quote_parallel_drop (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (term : Pattern) :
    resolve decl (.apply decl.quoteConstructor
        [.collection decl.parallelCollection
          [.apply decl.dropConstructor [term], .apply decl.parallelUnitConstructor []] none]) =
      resolve decl term := by
  rw [show resolve decl (.apply decl.quoteConstructor
        [.collection decl.parallelCollection
          [.apply decl.dropConstructor [term], .apply decl.parallelUnitConstructor []] none]) =
      finishResolve decl decl.quoteConstructor
        [.collection decl.parallelCollection
          [resolve decl (.apply decl.dropConstructor [term]),
            resolve decl (.apply decl.parallelUnitConstructor [])] none] from rfl,
    resolve_drop decl distinct, resolve_unit]
  simp [finishResolve, leaves, leavesList]

/-! ## Coherence with the parallel unit -/

section Coherence

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

theorem canonicalize_unit_parallel (term : Pattern) :
    canonicalize decl (.collection decl.parallelCollection
        [.apply decl.parallelUnitConstructor [], term] none) = canonicalize decl term := by
  rw [← canonicalize_parallel_singleton decl term]
  simp only [canonicalize, beq_self_eq_true, if_true]
  change collapseParallel decl (normalizeParallelElements decl
      (canonicalize decl (.apply decl.parallelUnitConstructor []) ::
        canonicalizeList decl [term])) =
    collapseParallel decl (normalizeParallelElements decl (canonicalizeList decl [term]))
  rw [canonicalize_parallel_unit, normalizeParallelElements_unit_cons]

theorem canonicalize_parallel_unit_right (term : Pattern) :
    canonicalize decl (.collection decl.parallelCollection
        [term, .apply decl.parallelUnitConstructor []] none) = canonicalize decl term := by
  rw [canonicalize_parallel_permutation decl (List.Perm.swap _ _ _)]
  exact canonicalize_unit_parallel decl term

theorem eliminate_unit (σ : Assignment) :
    eliminate decl σ (.apply decl.parallelUnitConstructor []) =
      .apply decl.parallelUnitConstructor [] := by
  simp [eliminate, activation?_nil]

/-- **Coherence (root).** Elimination after resolution sends `t | 0` and `t`
to equivalent results. -/
theorem coherent_parallel_unit_right (σ : Assignment) (term : Pattern) :
    canonicalEquivalent decl
      (eliminate decl σ (resolve decl (.collection decl.parallelCollection
        [term, .apply decl.parallelUnitConstructor []] none)))
      (eliminate decl σ (resolve decl term)) = true := by
  rw [canonicalEquivalent_eq_true_iff]
  rw [show resolve decl (.collection decl.parallelCollection
        [term, .apply decl.parallelUnitConstructor []] none) =
      .collection decl.parallelCollection
        [resolve decl term, resolve decl (.apply decl.parallelUnitConstructor [])] none from rfl,
    resolve_unit]
  simp only [eliminate, eliminateList_eq_map, List.map_cons, List.map_nil, activation?_nil,
    Option.getD_none]
  exact canonicalize_parallel_unit_right decl _

theorem coherent_unit_parallel (σ : Assignment) (term : Pattern) :
    canonicalEquivalent decl
      (eliminate decl σ (resolve decl (.collection decl.parallelCollection
        [.apply decl.parallelUnitConstructor [], term] none)))
      (eliminate decl σ (resolve decl term)) = true := by
  rw [canonicalEquivalent_eq_true_iff]
  rw [show resolve decl (.collection decl.parallelCollection
        [.apply decl.parallelUnitConstructor [], term] none) =
      .collection decl.parallelCollection
        [resolve decl (.apply decl.parallelUnitConstructor []), resolve decl term] none from rfl,
    resolve_unit]
  simp only [eliminate, eliminateList_eq_map, List.map_cons, List.map_nil, activation?_nil,
    Option.getD_none]
  exact canonicalize_unit_parallel decl _

/-- **Coherence (root).** Elimination after resolution sends `@*t` and `t`
to the same result. -/
theorem coherent_quote_drop (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (σ : Assignment) (term : Pattern) :
    eliminate decl σ (resolve decl
        (.apply decl.quoteConstructor [.apply decl.dropConstructor [term]])) =
      eliminate decl σ (resolve decl term) := by
  rw [resolve_quote_drop decl distinct]

theorem canonicalize_apply_single_congr (constructor : String) {left right : Pattern}
    (same : canonicalize decl left = canonicalize decl right) :
    canonicalize decl (.apply constructor [left]) = canonicalize decl (.apply constructor [right]) := by
  show Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply decl
      constructor (canonicalizeList decl [left]) =
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply decl
      constructor (canonicalizeList decl [right])
  simp only [canonicalizeList, same]

theorem receivedIndex?_unit_right (payload : Pattern) :
    receivedIndex? decl (.collection decl.parallelCollection
        [payload, .apply decl.parallelUnitConstructor []] none) =
      receivedIndex? decl payload := by
  apply receivedIndex?_congr
  simp [leaves, leavesList]

/-- **Coherence inside a drop.** The whole-name law sees through a parallel
unit in the payload, so `*(p | 0)` and `*p` eliminate to equivalent results. -/
theorem coherent_drop_payload_unit (σ : Assignment) (payload : Pattern) :
    canonicalEquivalent decl
      (eliminate decl σ (.apply decl.dropConstructor
        [.collection decl.parallelCollection [payload, .apply decl.parallelUnitConstructor []] none]))
      (eliminate decl σ (.apply decl.dropConstructor [payload])) = true := by
  rw [canonicalEquivalent_eq_true_iff, eliminate_drop, eliminate_drop,
    receivedIndex?_unit_right]
  cases (receivedIndex? decl payload).bind fun index => quotedProcess? decl (σ index) with
  | some process => rfl
  | none =>
      simp only [Option.getD_none, eliminate, eliminateList_eq_map, List.map_cons, List.map_nil,
        activation?_nil]
      exact canonicalize_apply_single_congr decl _ (canonicalize_parallel_unit_right decl _)

end Coherence

/-! ## Controls -/

section Controls

/-- Under the binder `x`: `*@(*x | 0)`. -/
def wholeName : Pattern :=
  .apply "Drop" [.apply "Quote"
    [.collection .hashBag [.apply "Drop" [.bvar 0], .apply "Nil" []] none]]

def receivedProcess : Pattern := .apply "App" [.fvar "g"]
def receivedCode : Pattern := .apply "Quote" [receivedProcess]

/-- **Whole-name law.** `*@(*x | 0)` resolves to `*x`, which runs the
received process. The tree's operation agrees. -/
theorem wholeName_activates :
    resolve oneCarrier wholeName = .apply "Drop" [.bvar 0] ∧
      eliminate oneCarrier (single receivedCode) (resolve oneCarrier wholeName) =
        receivedProcess ∧
      Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation.instantiate oneCarrier 0 receivedCode
        wholeName = receivedProcess := by
  decide +kernel

/-- Through a unit in the payload: `*(x | 0)` also runs the received process. -/
theorem drop_through_unit_activates :
    eliminate oneCarrier (single receivedCode)
        (.apply "Drop" [.collection .hashBag [.bvar 0, .apply "Nil" []] none]) =
      receivedProcess := by decide

/-- Negative: a literal dropped quotation is inert. -/
theorem literal_drop_inert :
    eliminate oneCarrier (single receivedCode) (.apply "Drop" [receivedCode]) =
      .apply "Drop" [receivedCode] := by decide

/-- Negative: a drop of a different variable does not run. -/
theorem other_drop_inert :
    eliminate oneCarrier (single receivedCode) (.apply "Drop" [.bvar 1]) =
      .apply "Drop" [.bvar 0] := by decide

end Controls

/-! ## Metavariable holes and declared dependencies -/

section Metavariables

open Mettapedia.OSLF.MeTTaIL.RuleBinding

/-- Code `F(x)` that uses the binder `x` introduced at the occurrence. -/
def usesBinder : Pattern := .apply "F" [.bvar 0]

/-- Code `F(0)` that does not use it. -/
def ignoresBinder : Pattern := .apply "F" [.apply "Nil" []]

/-- `?B[]` under a new binder `x`: filling with code that uses `x` fails, in
both the filling and the matching direction. -/
theorem hole_without_dependency_rejects :
    instantiateValue? { dependencies := [], ambient := 0, body := usesBinder } 0 1 [] = none ∧
      recoverValue? [] 0 1 [] usesBinder = none := by decide

/-- `?B[x]`: the declared dependency accepts the same code. -/
theorem hole_with_dependency_accepts :
    instantiateValue? { dependencies := [TypeExpr.name], ambient := 0, body := usesBinder }
        0 1 [.bvar 0] = some usesBinder ∧
      recoverValue? [TypeExpr.name] 0 1 [.bvar 0] usesBinder =
        some { dependencies := [TypeExpr.name], ambient := 0, body := usesBinder } := by
  decide

/-- Positive control: code that ignores `x` fills `?B[]`. -/
theorem hole_without_dependency_accepts_independent_code :
    instantiateValue? { dependencies := [], ambient := 0, body := ignoresBinder } 0 1 [] =
        some ignoresBinder ∧
      recoverValue? [] 0 1 [] ignoresBinder =
        some { dependencies := [], ambient := 0, body := ignoresBinder } := by decide

end Metavariables

/-! ## Contextual quotations under the whole-name law -/

theorem activation?_congr {arity : Nat} {σ τ : Assignment}
    (agree : ∀ index, index < arity → σ index = τ index) (constructor : String)
    {arguments : List Pattern} (inScope : ∀ p ∈ arguments, p.isWellScopedAt arity = true) :
    activation? decl σ constructor arguments = activation? decl τ constructor arguments := by
  unfold activation?
  split
  · rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
    · rfl
    · simp only
      cases found : receivedIndex? decl payload with
      | none => rfl
      | some index =>
          have only : leaves decl payload = [.bvar index] := by
            unfold receivedIndex? at found
            split at found
            · cases found
              assumption
            · cases found
          have indexScoped := mem_leaves_isWellScopedAt decl (inScope payload (by simp))
            (.bvar index) (by simp [only])
          simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at indexScoped
          simp [agree index indexScoped]
    · rfl
  · rfl

theorem lift_agree {arity : Nat} {σ τ : Assignment}
    (agree : ∀ index, index < arity → σ index = τ index) (count : Nat) :
    ∀ index, index < arity + count → lift count σ index = lift count τ index := by
  intro index below
  simp only [lift]
  split
  · rfl
  · rw [agree (index - count) (by omega)]

/-- Elimination reads only the variables in scope. -/
theorem eliminate_congr {arity : Nat} {σ τ : Assignment}
    (agree : ∀ index, index < arity → σ index = τ index) {pattern : Pattern}
    (inScope : pattern.isWellScopedAt arity = true) :
    eliminate decl σ pattern = eliminate decl τ pattern := by
  induction pattern using Pattern.inductionOn generalizing arity σ τ with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
      exact agree index inScope
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      have each := (isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [eliminate, eliminateList_eq_map, activation?_congr decl agree constructor each]
      congr 2
      exact List.map_congr_left fun p hp => ih p hp agree (each p hp)
  | hlambda name body ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [eliminate]
      exact congrArg (Pattern.lambda name) (ih (lift_agree agree 1) inScope)
  | hmultiLambda count names body ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      simp only [eliminate]
      exact congrArg (Pattern.multiLambda count names) (ih (lift_agree agree count) inScope)
  | hsubst body value ihBody ihValue =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
      simp only [eliminate]
      exact congrArg₂ Pattern.subst (ihBody (lift_agree agree 1) inScope.1)
        (ihValue agree inScope.2)
  | hcollection kind elements rest ih =>
      simp only [Pattern.isWellScopedAt] at inScope
      have each := (isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [eliminate, eliminateList_eq_map]
      congr 1
      exact List.map_congr_left fun p hp => ih p hp agree (each p hp)

theorem eliminate_id (pattern : Pattern) : eliminate decl Pattern.bvar pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      have inert : activation? decl Pattern.bvar constructor arguments = none := by
        unfold activation?
        split
        · rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
          · rfl
          · simp only
            cases receivedIndex? decl payload <;> rfl
          · rfl
        · rfl
      simp only [eliminate, eliminateList_eq_map, inert, Option.getD_none]
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun p hp => ih p hp
  | hlambda name body ih => simp only [eliminate, lift_identity, ih]
  | hmultiLambda arity names body ih => simp only [eliminate, lift_identity, ih]
  | hsubst body value ihBody ihValue => simp only [eliminate, lift_identity, ihBody, ihValue]
  | hcollection kind elements rest ih =>
      simp only [eliminate, eliminateList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun p hp => ih p hp

/-- `closure body [v₀, …, vₙ₋₁]` is `.subst (… (.subst body vₙ₋₁) …) v₀`
(the same telescope as in `QuoteEnvironment.lean`). -/
def closure (body : Pattern) : List Pattern → Pattern
  | [] => body
  | value :: environment => .subst (closure body environment) value

/-- How an outer elimination acts on an environment telescope. -/
def eliminateEnvironment (σ : Assignment) : List Pattern → List Pattern
  | [] => []
  | value :: environment =>
      eliminate decl σ value :: eliminateEnvironment (lift 1 σ) environment

/-- **Contextual elimination under the whole-name law.** On a closure whose
body is scoped by its own environment, elimination acts on the environment
only; the body is neither substituted nor run. -/
theorem eliminate_closure (σ : Assignment) {body : Pattern} (environment : List Pattern)
    (sealed : body.isWellScopedAt environment.length = true) :
    eliminate decl σ (closure body environment) =
      closure body (eliminateEnvironment decl σ environment) := by
  suffices general : ∀ (environment : List Pattern) (layers : Nat) (σ : Assignment),
      body.isWellScopedAt (layers + environment.length) = true →
      eliminate decl (lift layers σ) (closure body environment) =
        closure body (eliminateEnvironment decl (lift layers σ) environment) by
    simpa using general environment 0 σ (by simpa using sealed)
  intro environment
  induction environment with
  | nil =>
      intro layers σ inScope
      have fixes : ∀ index, index < layers → lift layers σ index = Pattern.bvar index := by
        intro index below
        simp [lift, below]
      rw [closure, eliminate_congr decl fixes (by simpa using inScope), eliminate_id]
      rfl
  | cons value environment ih =>
      intro layers σ inScope
      simp only [closure, eliminate, eliminateEnvironment, lift_lift]
      congr 1
      exact ih (layers + 1) σ (by simpa [Nat.add_assoc, Nat.add_comm 1] using inScope)

/-- **Observation under the whole-name law.** For a contextual quotation with
a one-entry environment holding a name: eliminating after realizing the
environment equals realizing after contextual elimination. -/
theorem realize_contextual_one (distinct : decl.quoteConstructor ≠ decl.dropConstructor)
    (σ : Assignment) {body value : Pattern} (sealed : body.isWellScopedAt 1 = true)
    (valueName : isName decl value = true) (dropsNamed : namesAtDrops decl body = true) :
    eliminate decl σ (.apply decl.quoteConstructor [.subst body value]) =
        .apply decl.quoteConstructor [.subst body (eliminate decl σ value)] ∧
      eliminate decl σ (.apply decl.quoteConstructor [eliminate decl (single value) body]) =
        .apply decl.quoteConstructor [eliminate decl (single (eliminate decl σ value)) body] := by
  constructor
  · rw [eliminate_quote decl distinct]
    have h := eliminate_closure decl σ (body := body) [value] sealed
    simpa [closure, eliminateEnvironment] using congrArg (fun x => Pattern.apply decl.quoteConstructor [x]) h
  · rw [eliminate_quote decl distinct,
      eliminate_eliminate decl distinct body dropsNamed (single value)
        (isName_single decl valueName) σ]
    congr 2
    refine eliminate_congr decl (arity := 1) ?_ sealed
    intro index below
    have : index = 0 := by omega
    subst this
    rfl

end Mettapedia.OSLF.MeTTaIL.ReceivedNames

#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.leavesList_eq_flatMap
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.activation?_eq_some
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.activation?_of_ne
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_apply_of_ne
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.mem_leaves_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_single_isWellScopedAt
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.liftBVars_bvar
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.leaves_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.receivedIndex?_congr
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.receivedIndex?_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.quotedProcess?_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.lift_shiftIndex
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.activation?_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_lift_comp
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.activation?_nil
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.leaves_eliminate
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.isName_cases
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.isName_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.isName_lift
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.namesAtDropsList_iff
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_quote
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_drop
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.receivedIndex?_name_ne_bvar
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_eliminate
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.lift_single_shiftIndex
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_lift_single_liftBVars
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.isName_single
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_single_single
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.composition_needs_named_drops
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.resolve_unit
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.resolve_drop
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.resolve_quote_drop
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.resolve_quote_parallel_drop
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.canonicalize_unit_parallel
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.canonicalize_parallel_unit_right
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_unit
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.coherent_parallel_unit_right
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.coherent_unit_parallel
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.coherent_quote_drop
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.canonicalize_apply_single_congr
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.receivedIndex?_unit_right
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.coherent_drop_payload_unit
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.wholeName_activates
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.drop_through_unit_activates
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.literal_drop_inert
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.other_drop_inert
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.hole_without_dependency_rejects
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.hole_with_dependency_accepts
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.hole_without_dependency_accepts_independent_code
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.activation?_congr
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.lift_agree
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_congr
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_id
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.eliminate_closure
#print axioms Mettapedia.OSLF.MeTTaIL.ReceivedNames.realize_contextual_one
