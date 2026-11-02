import Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSubstitution
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ScopedApplication
import Mettapedia.OSLF.MeTTaIL.ScopedStepPremise

/-!
# Authored patterns on the common ABT carrier

The existing source ABT and the common signature-indexed ABT have the same
field/binder structure. Their explicit carrier isomorphism connects authored
scope and substitution to the shared term operations. Raw lowering retains
display metadata; canonical lowering erases it using the source's existing
alpha-equivalence relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PatternABTCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open InferenceSupportIndexedABTLowering
open SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open ContextualPatterns (underBinders_eq underBinders_zero)

deriving instance DecidableEq for PatternABTHead

mutual
def toTerm : PatternABT → Term PatternABTHead
  | .idx i => .idx i
  | .node h fs => .node h (toFields fs)

def toFields : PatternABTFields → Fields PatternABTHead
  | .nil => .nil
  | .cons d t rest => .cons d (toTerm t) (toFields rest)
end

mutual
def fromTerm : Term PatternABTHead → PatternABT
  | .idx i => .idx i
  | .node h fs => .node h (fromFields fs)

def fromFields : Fields PatternABTHead → PatternABTFields
  | .nil => .nil
  | .cons d t rest => .cons d (fromTerm t) (fromFields rest)
end

mutual
@[simp] theorem from_toTerm (t : PatternABT) : fromTerm (toTerm t) = t := by
  cases t with
  | idx i => rfl
  | node h fs => simp [toTerm, fromTerm, from_toFields fs]

@[simp] theorem from_toFields (fs : PatternABTFields) : fromFields (toFields fs) = fs := by
  cases fs with
  | nil => rfl
  | cons d t rest => simp [toFields, fromFields, from_toTerm t, from_toFields rest]
end

mutual
@[simp] theorem to_fromTerm (t : Term PatternABTHead) : toTerm (fromTerm t) = t := by
  cases t with
  | idx i => rfl
  | node h fs => simp [toTerm, fromTerm, to_fromFields fs]

@[simp] theorem to_fromFields (fs : Fields PatternABTHead) : toFields (fromFields fs) = fs := by
  cases fs with
  | nil => rfl
  | cons d t rest => simp [toFields, fromFields, to_fromTerm t, to_fromFields rest]
end

theorem toTerm_injective : Function.Injective toTerm :=
  Function.LeftInverse.injective from_toTerm

def lowerRaw (pattern : Pattern) : Term PatternABTHead := toTerm (PatternABT.encode pattern)

theorem lowerRaw_injective : Function.Injective lowerRaw := by
  intro a b same
  have encoded := toTerm_injective same
  have decoded := congrArg PatternABT.decode? encoded
  simpa only [PatternABT.decode_encode, Option.some.injEq] using decoded

def lower (pattern : Pattern) : Term PatternABTHead := lowerRaw pattern.eraseBinderMetadata

theorem lower_eq_iff_alpha (a b : Pattern) : lower a = lower b ↔ a.AlphaEquiv b := by
  exact ⟨fun same => lowerRaw_injective same, congrArg lowerRaw⟩

mutual
theorem lowerRaw_scope (depth : Nat) (pattern : Pattern) :
    Term.supportedAt depth (lowerRaw pattern) = pattern.isWellScopedAt depth := by
  cases pattern with
  | bvar i => rfl
  | fvar name => rfl
  | apply constructor arguments => exact lowerRawFields_scope depth arguments
  | lambda name body =>
    simpa only [lowerRaw, PatternABT.encode, toTerm, toFields, Term.supportedAt,
      Term.Fields.supportedAt, Bool.and_true, Pattern.isWellScopedAt] using lowerRaw_scope (depth + 1) body
  | multiLambda arity names body =>
    simpa only [lowerRaw, PatternABT.encode, toTerm, toFields, Term.supportedAt,
      Term.Fields.supportedAt, Bool.and_true, Pattern.isWellScopedAt] using lowerRaw_scope (depth + arity) body
  | subst body replacement =>
    simp only [lowerRaw, PatternABT.encode, toTerm, toFields, Term.supportedAt,
      Term.Fields.supportedAt, Bool.and_true, Pattern.isWellScopedAt, Nat.add_zero]
    rw [show Term.supportedAt (depth + 1) (toTerm (PatternABT.encode body)) = _ from lowerRaw_scope (depth + 1) body,
      show Term.supportedAt depth (toTerm (PatternABT.encode replacement)) = _ from lowerRaw_scope depth replacement]
  | collection kind elements rest => exact lowerRawFields_scope depth elements

theorem lowerRawFields_scope (depth : Nat) (patterns : List Pattern) :
    Term.Fields.supportedAt depth (toFields (PatternABT.encodeFields 0 patterns)) =
      Pattern.isWellScopedListAt depth patterns := by
  cases patterns with
  | nil => rfl
  | cons p rest =>
    simp only [PatternABT.encodeFields, toFields, Term.Fields.supportedAt, Nat.add_zero,
      Pattern.isWellScopedListAt]
    rw [show Term.supportedAt depth (toTerm (PatternABT.encode p)) = _ from lowerRaw_scope depth p,
      lowerRawFields_scope depth rest]
end

theorem lower_scope (depth : Nat) (pattern : Pattern) :
    Term.supportedAt depth (lower pattern) = pattern.isWellScopedAt depth := by
  rw [lower, lowerRaw_scope, Mettapedia.OSLF.MeTTaIL.Syntax.eraseBinderMetadata_isWellScopedAt]

mutual
theorem lift_toTerm (cutoff shift : Nat) (term : PatternABT) :
    toTerm (PatternABT.lift cutoff shift term) = Term.lift cutoff shift (toTerm term) := by
  cases term with
  | idx i =>
    by_cases below : i < cutoff
    · simp [PatternABT.lift, toTerm, Term.lift, below, Nat.not_le.mpr below]
    · simp [PatternABT.lift, toTerm, Term.lift, below, Nat.le_of_not_gt below]
  | node h fs => simp [PatternABT.lift, toTerm, Term.lift, lift_toFields cutoff shift fs]

theorem lift_toFields (cutoff shift : Nat) (fs : PatternABTFields) :
    toFields (PatternABT.liftFields cutoff shift fs) = Term.Fields.lift cutoff shift (toFields fs) := by
  cases fs with
  | nil => rfl
  | cons d t rest =>
    simp [PatternABT.liftFields, toFields, Term.Fields.lift,
      lift_toTerm (cutoff + d) shift t, lift_toFields cutoff shift rest]
end

theorem lowerRaw_lift (cutoff shift : Nat) (pattern : Pattern) :
    lowerRaw (Substitution.liftBVars cutoff shift pattern) =
      Term.lift cutoff shift (lowerRaw pattern) := by
  rw [lowerRaw, PatternABT.encode_liftBVars, lift_toTerm]
  rfl


theorem lowerRaw_lift_assignment (depth : Nat) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) :
    (fun i => lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift depth assignment i)) =
      ContextualPatterns.underBinders depth (fun i => lowerRaw (assignment i)) := by
  funext i
  rw [underBinders_eq]
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split
  · rfl
  · exact lowerRaw_lift 0 depth (assignment (i - depth))

def lowerFields (patterns : List Pattern) : Fields PatternABTHead :=
  toFields (PatternABT.encodeFields 0 patterns)

mutual
theorem lowerRaw_substitute (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (pattern : Pattern) :
    lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment pattern) =
      Term.substituteMany (fun i => lowerRaw (assignment i)) (lowerRaw pattern) := by
  cases pattern with
  | bvar i => simp [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm]
  | fvar name => rfl
  | apply constructor arguments =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm,
      ContextualPatterns.substitute_node]
    exact congrArg (Term.node (.apply constructor)) (lowerFields_substitute assignment arguments)
  | lambda name body =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm, toFields,
      ContextualPatterns.substitute_node, ContextualPatterns.substitute_fields_cons,
      ContextualPatterns.substitute_fields_nil]
    change Term.node _ (.cons 1 (lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute _ body)) .nil) = _
    rw [lowerRaw_substitute, lowerRaw_lift_assignment]
    rfl
  | multiLambda arity names body =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm, toFields,
      ContextualPatterns.substitute_node, ContextualPatterns.substitute_fields_cons,
      ContextualPatterns.substitute_fields_nil]
    change Term.node _ (.cons arity (lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute _ body)) .nil) = _
    rw [lowerRaw_substitute, lowerRaw_lift_assignment]
    rfl
  | subst body replacement =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm, toFields,
      ContextualPatterns.substitute_node, ContextualPatterns.substitute_fields_cons,
      ContextualPatterns.substitute_fields_nil]
    change Term.node _ (.cons 1 (lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute _ body))
      (.cons 0 (lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment replacement)) .nil)) = _
    rw [lowerRaw_substitute, lowerRaw_substitute, lowerRaw_lift_assignment]
    simp only [underBinders_zero]
    rfl
  | collection kind elements rest =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, lowerRaw, PatternABT.encode, toTerm,
      ContextualPatterns.substitute_node]
    exact congrArg (Term.node (.collection kind rest)) (lowerFields_substitute assignment elements)

theorem lowerFields_substitute (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (patterns : List Pattern) :
    lowerFields (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList assignment patterns) =
      ContextualPatterns.substituteFields (fun i => lowerRaw (assignment i)) (lowerFields patterns) := by
  cases patterns with
  | nil => rfl
  | cons p rest =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList, lowerFields, PatternABT.encodeFields, toFields,
      ContextualPatterns.substitute_fields_cons]
    change Fields.cons 0 (lowerRaw (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment p))
      (lowerFields (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList assignment rest)) = _
    rw [lowerRaw_substitute, lowerFields_substitute]
    simp only [underBinders_zero]
    rfl
end

/-- Canonical lowering transports the actual source substitution modulo binder display names. -/
theorem lower_substitute (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (pattern : Pattern) :
    lower (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment pattern) =
      Term.substituteMany (fun i => lower (assignment i)) (lower pattern) := by
  unfold lower
  rw [Mettapedia.OSLF.MeTTaIL.Syntax.eraseBinderMetadata_substitute, lowerRaw_substitute]

end Mettapedia.GSLT.LanguageDef.PatternABTCarrier
