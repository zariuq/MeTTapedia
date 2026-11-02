import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody
import Mettapedia.Machines.TypedScalarEquality

/-!
# Semantics-preserving normalization of extracted scalar bodies

Normalization removes constant Boolean choices and orients greater-than tests
as swapped less-than tests. It preserves partial evaluation, result sorts and
the live tuple-head check. Source extraction happens first: a discarded branch
cannot conceal an unsupported effect from the extractor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody

open Mettapedia.Machines.TypedScalar

deriving instance DecidableEq for Body

def canonicalBinary {Slot : Type} : {a b c : Kind} → Binary a b c →
    Expr Slot a → Expr Slot b → Expr Slot c
  | _, _, _, .gt, left, right => .binary .lt right left
  | _, _, _, .ge, left, right => .binary .le right left
  | _, _, _, op, left, right => .binary op left right

theorem canonicalBinary_eval {Slot : Type} {a b c : Kind} (op : Binary a b c)
    (left : Expr Slot a) (right : Expr Slot b) (locals : Slot → Data) :
    (canonicalBinary op left right).eval locals = (Expr.binary op left right).eval locals := by
  cases op <;> try rfl
  all_goals
    cases first : left.eval locals <;> cases second : right.eval locals <;>
      simp only [canonicalBinary, Expr.eval, first, second]
    all_goals first | rfl | (rename_i x y; cases x <;> cases y <;> rfl)

def canonicalExpr {Slot : Type} : {kind : Kind} → Expr Slot kind → Expr Slot kind
  | _, .literal value => .literal value
  | _, .boolean value => .boolean value
  | _, .read slot => .read slot
  | _, .binary op left right => canonicalBinary op (canonicalExpr left) (canonicalExpr right)
  | _, .branch test yes no =>
      match canonicalExpr test with
      | .boolean true => canonicalExpr yes
      | .boolean false => canonicalExpr no
      | other => .branch other (canonicalExpr yes) (canonicalExpr no)

theorem canonicalExpr_eval {Slot : Type} {kind : Kind} (expression : Expr Slot kind) (locals : Slot → Data) :
    (canonicalExpr expression).eval locals = expression.eval locals := by
  induction expression with
  | literal | boolean | read => rfl
  | binary op left right ihl ihr =>
      rw [canonicalExpr, canonicalBinary_eval]
      simp only [Expr.eval, ihl, ihr]
  | branch test yes no iht ihy ihn =>
      unfold canonicalExpr
      split
      next flag =>
        have tested : test.eval locals = some true := by rw [← iht, flag]; rfl
        simp [Expr.eval, tested, ihy]
      next flag =>
        have tested : test.eval locals = some false := by rw [← iht, flag]; rfl
        simp [Expr.eval, tested, ihn]
      next => simp only [Expr.eval, iht, ihy, ihn]

def canonicalField {Slot : Type} (field : Packed Slot) : Packed Slot := ⟨field.1, canonicalExpr field.2⟩

theorem canonicalField_eval {Slot : Type} (field : Packed Slot) (locals : Slot → Data) :
    evalField locals (canonicalField field) = evalField locals field := by
  simp only [evalField, canonicalField, canonicalExpr_eval]

theorem canonicalFields_eval {Slot : Type} (fields : List (Packed Slot)) (locals : Slot → Data) :
    evalFields locals (fields.map canonicalField) = evalFields locals fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp only [List.map_cons, evalFields, canonicalField_eval, ih]

def canonical {Slot : Type} : Body Slot → Body Slot
  | .scalar field => .scalar (canonicalField field)
  | .tuple fields => .tuple (fields.map canonicalField)
  | .branch test yes no =>
      match canonicalExpr test with
      | .boolean true => canonical yes
      | .boolean false => canonical no
      | other => .branch other (canonical yes) (canonical no)

theorem canonical_eval {Slot : Type} (body : Body Slot) (program : SpaceSemantics.Program)
    (locals : Slot → Data) : (canonical body).eval program locals = body.eval program locals := by
  induction body with
  | scalar field => exact canonicalField_eval field locals
  | tuple fields => simp only [canonical, Body.eval, canonicalFields_eval]
  | branch test yes no ihy ihn =>
      unfold canonical
      split
      next flag =>
        have tested : test.eval locals = some true := by rw [← canonicalExpr_eval test locals, flag]; rfl
        simp [Body.eval, tested, ihy]
      next flag =>
        have tested : test.eval locals = some false := by rw [← canonicalExpr_eval test locals, flag]; rfl
        simp [Body.eval, tested, ihn]
      next => simp only [Body.eval, canonicalExpr_eval, ihy, ihn]

theorem canonical_equal_eval {Slot : Type} (left right : Body Slot)
    (same : canonical left = canonical right) (program : SpaceSemantics.Program) (locals : Slot → Data) :
    left.eval program locals = right.eval program locals := by
  rw [← canonical_eval left, ← canonical_eval right, same]

/-- A source-indexed certificate for a supplied typed schema. A downstream
algebra proves what the schema means uniformly over its admitted inputs. -/
structure Recognized {Slot : Type} (program : SpaceSemantics.Program)
    (environment : ScalarSource.Environment Slot) (source : OSLFCore.Atom) (schema : Body Slot) where
  body : Body Slot
  compiled : Compiles program environment source body
  normalized : canonical body = canonical schema

def recognize {Slot : Type} [DecidableEq Slot] (program : SpaceSemantics.Program)
    (environment : ScalarSource.Environment Slot) (source : OSLFCore.Atom) (schema : Body Slot) :
    Option (Recognized program environment source schema) := do
  let compiled ← elaborate program environment source
  if same : canonical compiled.val = canonical schema then
    return ⟨compiled.val, compiled.property, same⟩
  else none

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarBody
