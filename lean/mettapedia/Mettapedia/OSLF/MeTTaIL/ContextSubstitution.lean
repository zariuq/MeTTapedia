import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Simultaneous substitution of pattern context variables

An occurrence substitution supplies a term for every variable in a
metavariable's declared dependency context.  This module gives its executable
action on the existing `Pattern` carrier.  It substitutes de Bruijn context
variables, leaving named metavariables and collection-rest names unchanged.

The binder lift fixes newly bound variables and weakens every supplied term.
Binder names, collection kinds, and explicit-substitution nodes remain syntax.
The action satisfies identity and composition. A one-variable assignment is
provided for later comparison with the existing binder-eliminating operation.
-/

namespace Mettapedia.OSLF.MeTTaIL.ContextSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

/-- An assignment to de Bruijn context variables.  Finite-domain consumers
check their source context before applying this total action. -/
abbrev Assignment := Nat → Pattern

/-- Extend an assignment under `arity` binders.  The new prefix is fixed;
images of ambient variables move below that prefix without capture. -/
def lift (arity : Nat) (assignment : Assignment) : Assignment :=
  fun index => if index < arity then .bvar index
    else liftBVars 0 arity (assignment (index - arity))

mutual
/-- Simultaneously substitute context variables, preserving syntax and all
non-variable metadata.  The explicit list traversal reduces in the kernel. -/
def substitute (assignment : Assignment) : Pattern → Pattern
  | .bvar index => assignment index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply constructor (substituteList assignment arguments)
  | .lambda name body => .lambda name (substitute (lift 1 assignment) body)
  | .multiLambda arity names body =>
      .multiLambda arity names (substitute (lift arity assignment) body)
  | .subst body replacement =>
      .subst (substitute (lift 1 assignment) body) (substitute assignment replacement)
  | .collection kind elements rest =>
      .collection kind (substituteList assignment elements) rest

/-- Ordered traversal for constructor arguments and collection elements. -/
def substituteList (assignment : Assignment) : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => substitute assignment pattern :: substituteList assignment patterns
end

@[simp] theorem substituteList_eq_map (assignment : Assignment) :
    ∀ patterns, substituteList assignment patterns = patterns.map (substitute assignment)
  | [] => rfl
  | pattern :: patterns => by
      simp only [substituteList, List.map_cons, substituteList_eq_map assignment patterns]

@[simp] theorem lift_zero (assignment : Assignment) : lift 0 assignment = assignment := by
  funext index
  simp [lift, liftBVars_zero]

@[simp] theorem lift_identity (arity : Nat) : lift arity Pattern.bvar = Pattern.bvar := by
  funext index
  simp only [lift]
  split
  · rfl
  · next h => simp only [liftBVars, Nat.zero_le, ite_true]; congr 1; omega

private theorem liftBVars_comp (first second : Nat) (pattern : Pattern) (cutoff : Nat) :
    liftBVars cutoff first (liftBVars cutoff second pattern) =
      liftBVars cutoff (first + second) pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp only [liftBVars]
      split <;> simp only [liftBVars] <;> split <;> first | rfl | (congr 1; omega)
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor) (List.map_congr_left fun p hp => ih p hp cutoff)
  | hlambda name body ih => simp only [liftBVars, ih]
  | hmultiLambda arity names body ih => simp only [liftBVars, ih]
  | hsubst body replacement ihBody ihReplacement => simp only [liftBVars, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp cutoff)

/-- Successive binder extensions add their arities. -/
theorem lift_lift (outer inner : Nat) (assignment : Assignment) :
    lift outer (lift inner assignment) = lift (inner + outer) assignment := by
  funext index
  by_cases hOuter : index < outer
  · have hTotal : index < inner + outer := by omega
    simp [lift, hOuter, hTotal]
  · by_cases hInner : index - outer < inner
    · have hTotal : index < inner + outer := by omega
      simp only [lift, hOuter, hInner, hTotal, ite_false, ite_true,
        liftBVars, Nat.zero_le]
      congr 1
      omega
    · have hTotal : ¬ index < inner + outer := by omega
      simp only [lift, hOuter, hInner, hTotal, ite_false, liftBVars_comp]
      rw [show outer + inner = inner + outer by omega,
        show index - outer - inner = index - (inner + outer) by omega]

/-- An assignment between finite de Bruijn contexts supplies an image in the
target context for every variable of the source context. -/
def WellScopedAssignment (source target : Nat)
    (assignment : Assignment) : Prop :=
  ∀ index, index < source →
    (assignment index).isWellScopedAt target = true

/-- Lifting a well-scoped assignment fixes every new binder and places each
ambient image below the binder prefix without capture. -/
theorem WellScopedAssignment.lift {source target : Nat}
    {assignment : Assignment}
    (wellScoped : WellScopedAssignment source target assignment)
    (arity : Nat) :
    WellScopedAssignment (source + arity) (target + arity)
      (ContextSubstitution.lift arity assignment) := by
  intro index inSource
  by_cases hlocal : index < arity
  · simp only [ContextSubstitution.lift, hlocal, ite_true,
      Pattern.isWellScopedAt]
    exact decide_eq_true (by omega)
  · have oldIndex : index - arity < source := by omega
    simp only [ContextSubstitution.lift, hlocal, ite_false]
    have shifted := Substitution.liftBVars_isWellScopedAt
      (ambient := target) (cutoff := 0) (shift := arity)
      (pattern := assignment (index - arity))
      (by simpa only [Nat.add_zero] using wellScoped (index - arity) oldIndex)
    simpa only [Nat.add_zero, Nat.zero_add] using shifted

private theorem isWellScopedListAt_map_of_forall
    {depth : Nat} {patterns : List Pattern} {f : Pattern → Pattern}
    (all : ∀ pattern ∈ patterns,
      (f pattern).isWellScopedAt depth = true) :
    Pattern.isWellScopedListAt depth (patterns.map f) = true := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, Pattern.isWellScopedListAt,
        Bool.and_eq_true]
      exact ⟨all head (by simp),
        inductionHypothesis (by
          intro pattern membership
          exact all pattern (by simp [membership]))⟩

private theorem isWellScopedListAt_mem
    {depth : Nat} {patterns : List Pattern} {pattern : Pattern}
    (all : Pattern.isWellScopedListAt depth patterns = true)
    (member : pattern ∈ patterns) :
    pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at all
      cases List.mem_cons.mp member with
      | inl same => simpa only [same] using all.1
      | inr tailMember => exact inductionHypothesis all.2 tailMember

/-- Simultaneous substitution sends a scoped source term to a scoped target
term whenever each source variable has a scoped target image. -/
theorem substitute_wellScoped {source target : Nat}
    {assignment : Assignment}
    (wellScoped : WellScopedAssignment source target assignment)
    {pattern : Pattern}
    (termScoped : pattern.isWellScopedAt source = true) :
    (substitute assignment pattern).isWellScopedAt target = true := by
  induction pattern using Pattern.inductionOn
    generalizing source target assignment with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt] at termScoped
      simpa only [substitute] using
        wellScoped index (of_decide_eq_true termScoped)
  | hfvar name =>
      simp only [substitute, Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      simp only [substitute, substituteList_eq_map,
        Pattern.isWellScopedAt] at termScoped ⊢
      exact isWellScopedListAt_map_of_forall fun argument membership =>
        inductionHypothesis argument membership wellScoped
          (isWellScopedListAt_mem termScoped membership)
  | hlambda binder body inductionHypothesis =>
      simp only [substitute, Pattern.isWellScopedAt] at termScoped ⊢
      exact inductionHypothesis (wellScoped.lift 1) termScoped
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [substitute, Pattern.isWellScopedAt] at termScoped ⊢
      exact inductionHypothesis (wellScoped.lift arity) termScoped
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [substitute, Pattern.isWellScopedAt,
        Bool.and_eq_true] at termScoped ⊢
      exact ⟨bodyInduction (wellScoped.lift 1) termScoped.1,
        replacementInduction wellScoped termScoped.2⟩
  | hcollection kind elements rest inductionHypothesis =>
      simp only [substitute, substituteList_eq_map,
        Pattern.isWellScopedAt] at termScoped ⊢
      exact isWellScopedListAt_map_of_forall fun element membership =>
        inductionHypothesis element membership wellScoped
          (isWellScopedListAt_mem termScoped membership)

@[simp] theorem substitute_id (pattern : Pattern) :
    substitute Pattern.bvar pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [substitute, substituteList_eq_map]
      exact congrArg (Pattern.apply constructor)
        (by simpa only [List.map_id] using
          (List.map_congr_left (l := arguments)
            (f := substitute Pattern.bvar) (g := id)
            (fun p hp => ih p hp)))
  | hlambda name body ih => simp only [substitute, lift_identity, ih]
  | hmultiLambda arity names body ih => simp only [substitute, lift_identity, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [substitute, lift_identity, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [substitute, substituteList_eq_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (by simpa only [List.map_id] using
          (List.map_congr_left (l := elements)
            (f := substitute Pattern.bvar) (g := id)
            (fun p hp => ih p hp)))

/-- Insert a second prefix after an inserted prefix at the same boundary. -/
theorem liftBVars_after_insert (pattern : Pattern) (cutoff first second : Nat) :
    liftBVars (cutoff + first) second (liftBVars cutoff first pattern) =
      liftBVars cutoff (first + second) pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp only [liftBVars]
      split <;> simp only [liftBVars] <;> split <;> first | rfl | (congr 1; omega)
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor) (List.map_congr_left fun p hp => ih p hp cutoff)
  | hlambda name body ih =>
      simp only [liftBVars]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + 1)
  | hmultiLambda arity names body ih =>
      simp only [liftBVars]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + arity)
  | hsubst body replacement ihBody ihReplacement =>
      simp only [liftBVars]
      congr 1
      · simpa only [Nat.add_right_comm] using ihBody (cutoff + 1)
      · exact ihReplacement cutoff
  | hcollection kind elements rest ih =>
      simp only [liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp cutoff)

/-- Ambient substitution commutes with inserting an untouched context prefix,
also below an existing local prefix. -/
theorem substitute_liftBVars (assignment : Assignment) (pattern : Pattern)
    (cutoff amount : Nat) :
    substitute (lift (cutoff + amount) assignment) (liftBVars cutoff amount pattern) =
      liftBVars cutoff amount (substitute (lift cutoff assignment) pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases h : index < cutoff
      · have hge : ¬ index ≥ cutoff := by omega
        have hTotal : index < cutoff + amount := by omega
        simp [liftBVars, substitute, lift, h, hge, hTotal]
      · have hge : index ≥ cutoff := by omega
        have hTotal : ¬ index + amount < cutoff + amount := by omega
        have hSub : index + amount - (cutoff + amount) = index - cutoff := by omega
        simp only [liftBVars, hge, ite_true, substitute, lift, hTotal, h,
          ite_false, hSub]
        simpa only [Nat.zero_add] using
          (liftBVars_after_insert (assignment (index - cutoff)) 0 cutoff amount).symm
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [substitute, substituteList_eq_map, liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor) (List.map_congr_left fun p hp => ih p hp cutoff)
  | hlambda name body ih =>
      simp only [substitute, liftBVars, lift_lift]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + 1)
  | hmultiLambda arity names body ih =>
      simp only [substitute, liftBVars, lift_lift]
      congr 1
      simpa only [Nat.add_right_comm] using ih (cutoff + arity)
  | hsubst body replacement ihBody ihReplacement =>
      simp only [substitute, liftBVars, lift_lift]
      congr 1
      · simpa only [Nat.add_right_comm] using ihBody (cutoff + 1)
      · exact ihReplacement cutoff
  | hcollection kind elements rest ih =>
      simp only [substitute, substituteList_eq_map, liftBVars, liftBVarsList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp cutoff)

/-- Lifting respects substitution composition. -/
theorem lift_comp (first second : Assignment) (arity : Nat) :
    (fun index => substitute (lift arity second) (lift arity first index)) =
      lift arity (fun index => substitute second (first index)) := by
  funext index
  by_cases h : index < arity
  · simp [lift, h, substitute]
  · simp only [lift, h, ite_false]
    simpa only [Nat.zero_add, lift_zero] using
      substitute_liftBVars second (first (index - arity)) 0 arity

/-- Successive occurrence substitutions compose by substituting their images. -/
theorem substitute_comp (first second : Assignment) (pattern : Pattern) :
    substitute second (substitute first pattern) =
      substitute (fun index => substitute second (first index)) pattern := by
  induction pattern using Pattern.inductionOn generalizing first second with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
      simp only [substitute, substituteList_eq_map, List.map_map]
      exact congrArg (Pattern.apply constructor) (List.map_congr_left fun p hp => ih p hp first second)
  | hlambda name body ih =>
      simp only [substitute, ih, lift_comp]
  | hmultiLambda arity names body ih =>
      simp only [substitute, ih, lift_comp]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [substitute, ihBody, ihReplacement, lift_comp]
  | hcollection kind elements rest ih =>
      simp only [substitute, substituteList_eq_map, List.map_map]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp first second)

/-- Eliminate the first context variable using `replacement`. -/
def single (replacement : Pattern) : Assignment
  | 0 => replacement
  | index + 1 => .bvar index

/-- A singleton simultaneous assignment agrees with elimination of the
selected de Bruijn level, including under every binder and collection. -/
theorem substitute_lift_single (replacement : Pattern) (pattern : Pattern) :
    ∀ depth,
      substitute (lift depth (single replacement)) pattern =
        instantiateBVarAt depth replacement pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth
      by_cases below : index < depth
      · simp [substitute, instantiateBVarAt, lift, below]
      · by_cases equal : index = depth
        · subst index
          simp [substitute, instantiateBVarAt, lift, single]
        · have above : depth < index := by omega
          have hdiff : index - depth = Nat.succ (index - depth - 1) := by omega
          have hsingle : single replacement (index - depth) =
              .bvar (index - depth - 1) := by rw [hdiff]; rfl
          simp only [substitute, instantiateBVarAt, below, ite_false, equal,
            lift, hsingle, liftBVars, Nat.zero_le, ite_true]
          congr 1
          omega
  | hfvar name => intro depth; simp [substitute, instantiateBVarAt]
  | happly constructor arguments ih =>
      intro depth
      simp only [substitute, substituteList_eq_map, instantiateBVarAt]
      exact congrArg (Pattern.apply constructor)
        (List.map_congr_left fun p hp => ih p hp depth)
  | hlambda name body ih =>
      intro depth
      simp only [substitute, instantiateBVarAt, lift_lift]
      exact congrArg (Pattern.lambda name) (ih (depth + 1))
  | hmultiLambda arity names body ih =>
      intro depth
      simp only [substitute, instantiateBVarAt, lift_lift]
      exact congrArg (Pattern.multiLambda arity names) (ih (depth + arity))
  | hsubst body nestedReplacement ihBody ihReplacement =>
      intro depth
      simp only [substitute, instantiateBVarAt, lift_lift]
      exact congrArg₂ Pattern.subst (ihBody (depth + 1)) (ihReplacement depth)
  | hcollection kind elements rest ih =>
      intro depth
      simp only [substitute, substituteList_eq_map, instantiateBVarAt]
      exact congrArg (fun xs => Pattern.collection kind xs rest)
        (List.map_congr_left fun p hp => ih p hp depth)

/-- The root case compares the simultaneous occurrence action with the
existing binder-eliminating operation. -/
theorem substitute_single_eq_instantiateBVar (replacement pattern : Pattern) :
    substitute (single replacement) pattern =
      instantiateBVar replacement pattern := by
  simpa only [lift_zero, instantiateBVar] using
    substitute_lift_single replacement pattern 0

end Mettapedia.OSLF.MeTTaIL.ContextSubstitution
