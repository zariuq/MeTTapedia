import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveControls

/-!
# Repeated polymorphic reads need distinct instantiation scopes

World stability of a fixed read service is not a proof that its declaration
freshener implements per-occurrence instantiation. The existing source port
is keyed by subject and row index. Repeating the same polymorphic subject
therefore repeats its chosen variable names. The native annotation reader
instead allocates a new frame identity for every variable-bearing read.

These controls isolate that remaining source-adapter obligation. They do not
claim a native regression, and do not authorize replacing the full problem
by closed declarations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeFreshReadControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeRecursiveDriver NativeTypeSourcePorts
open NativeTypeRecursiveControls (sym expr row arrow world ops)

def list (type_ : Atom) : Atom := expr [sym "PolyList", type_]

def source : Source where
  rows := [row "ScopeNil" (list (.var "element")),
    row "cross-inst" (NativeTypeRecursiveControls.arrow [list (sym "Number"), list (sym "String")] (sym "R"))]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 2
  subtypeFresh := "%fresh-read-subtype"
  alpha := (· == ·)

def call : Call := .infer true (expr [sym "cross-inst", sym "ScopeNil", sym "ScopeNil"])

theorem resource_safety_does_not_supply_freshness : NativeTypeSourcePorts.Safe source := by
  unfold NativeTypeSourcePorts.Safe
  decide

theorem fixed_subject_read_couples_polymorphic_occurrences :
    publishTypes (evaluate ops (primitive source world) 4 call) = some [] := by cbv

def separated : Source :=
  { source with rows :=
    [row "ScopeLeft" (list (.var "left-element")),
     row "ScopeRight" (list (.var "right-element")),
     row "cross-inst" (NativeTypeRecursiveControls.arrow [list (sym "Number"), list (sym "String")] (sym "R"))] }

theorem separated_instantiation_variables_allow_both_formals :
    publishTypes (evaluate ops (primitive separated world) 4
      (.infer true (expr [sym "cross-inst", sym "ScopeLeft", sym "ScopeRight"]))) = some [sym "R"] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeFreshReadControls
