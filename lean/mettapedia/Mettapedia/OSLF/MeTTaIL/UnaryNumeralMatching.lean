import Mettapedia.OSLF.MeTTaIL.UnaryNumerals
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Unary numerals under matching and instantiation

A unary numeral contains no binder, no metavariable and no collection.  It is
therefore matched exactly, left unchanged by every instantiation, and needs
no binder metadata.  These facts let a rule generated from a table entry,
which mentions numerals of unknown size, be analysed like a rule written out
literally.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Match

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A numeral binds nothing. -/
@[simp] theorem binderFree_unary (zero succ : String) (count : Nat) :
    binderFree (Pattern.unary zero succ count) = true := by
  induction count with
  | zero => simp [binderFree, binderFreeList]
  | succ count recurse => simp [binderFree, binderFreeList, recurse]

/-- A numeral is matched exactly. -/
@[simp] theorem isMatchCorrectAux_unary (zero succ : String) (count : Nat) :
    isMatchCorrectAux (Pattern.unary zero succ count) = true := by
  induction count with
  | zero => simp [isMatchCorrectAux, isMatchCorrectListAux]
  | succ count recurse => simp [isMatchCorrectAux, isMatchCorrectListAux, recurse]

/-- An instantiation leaves a numeral unchanged. -/
@[simp] theorem applyBindings_unary (bindings : Bindings) (zero succ : String) (count : Nat) :
    applyBindings bindings (Pattern.unary zero succ count) = Pattern.unary zero succ count := by
  induction count with
  | zero => simp [applyBindings]
  | succ count recurse => simp [applyBindings, recurse]

/-- A numeral has no free variable. -/
@[simp] theorem freeVars_unary (zero succ : String) (count : Nat) :
    Substitution.freeVars (Pattern.unary zero succ count) = [] := by
  induction count with
  | zero => simp [Substitution.freeVars]
  | succ count recurse => simp [Substitution.freeVars, recurse]

end Mettapedia.OSLF.MeTTaIL.Match

namespace Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- A numeral carries no binder metadata. -/
@[simp] theorem hasCanonicalBinderMetadata_unary (zero succ : String) (count : Nat) :
    (unary zero succ count).hasCanonicalBinderMetadata = true := by
  induction count with
  | zero => simp [hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList]
  | succ count recurse =>
      simp [hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList, recurse]

end Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
