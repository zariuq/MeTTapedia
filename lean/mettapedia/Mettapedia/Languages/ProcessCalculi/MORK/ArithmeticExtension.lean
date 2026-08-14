import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseRefinement

/-!
# MORK Arithmetic / Comparison Extension Interface

Packages the currently live arithmetic sink and comparison-source extension lane
around the existing core MORK formalization.

## What this file IS

- A theorem-backed interface for the current Rust extension heads:
  - integer sinks: `i+`, `i-`, `i*`, `ieq`
  - float sinks: `f+`, `f-`, `f*`, `f/`, `fgt`, `flt`, `feq`
  - comparison sources: `==`, `!=`
- An honest lowering story:
  - arithmetic sinks are extension operators which, after decoding/evaluating
    their numeric arguments, lower to a single core `.add` sink
  - comparison sources are already represented by the core `SourceFactor`
    constructors `eqConstraint` / `neqConstraint`

## What this file is NOT

- Not a redesign of core `Sink`
- Not a claim that Lean's native float printer is the Rust `format!` contract
- Not a claim that `<`, `<=`, `#=` or other source comparators already exist
- Not a direct formalization of write-side PathMap byte plumbing

Positive example:
- once `i* (product) 6 7` has decoded its integer arguments, the effect is just
  adding `(product 42)` to the current space

Negative example:
- this file does not pretend `Float.toString` is the exact runtime rendering that
  Rust uses for `f64`
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance

/-- Append a result symbol to the current prefix focus.

For an expression prefix, this appends a new child.
For a non-expression prefix, this wraps it into a two-child expression.

This matches the Rust sink shape:
- expression prefix: bump arity and append result child
- bare symbol/atom prefix: wrap as `(prefix result)` -/
def appendSymbolToPrefix (pfx : Atom) (result : String) : Atom :=
  match pfx with
  | .expression es => .expression (es ++ [.symbol result])
  | a => .expression [a, .symbol result]

private theorem groundList_append_symbol (xs : List Atom) (s : String)
    (h : isGroundAtom.isGroundList xs = true) :
    isGroundAtom.isGroundList (xs ++ [.symbol s]) = true := by
  induction xs with
  | nil =>
      simp [isGroundAtom.isGroundList, isGroundAtom]
  | cons x xs ih =>
      simp [isGroundAtom.isGroundList, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩

/-- Appending a result symbol to a ground prefix stays ground. -/
theorem appendSymbolToPrefix_ground (pfx : Atom) (result : String)
    (hground : isGroundAtom pfx = true) :
    isGroundAtom (appendSymbolToPrefix pfx result) = true := by
  cases pfx with
  | var v =>
      simp [isGroundAtom] at hground
  | symbol s =>
      simp [appendSymbolToPrefix, isGroundAtom, isGroundAtom.isGroundList]
  | grounded g =>
      simp [appendSymbolToPrefix, isGroundAtom, isGroundAtom.isGroundList]
  | expression es =>
      simp only [appendSymbolToPrefix, isGroundAtom] at hground ⊢
      exact groundList_append_symbol es result hground

/-- Single ground add-template acts as plain union on the spec space. -/
theorem applySinks_single_add_ground (s : Space) (a : Atom)
    (hg : isGroundAtom a = true) :
    applySinks s [] (mkTemplate [mkAdd a]) = s ∪ {a} := by
  simp [applySinks, mkTemplate, mkAdd, applySink]
  rw [applySubst_nil]
  simp [hg]

/-! ## Integer arithmetic sinks -/

/-- Integer arithmetic extension heads currently supported by Rust `IntArithSink`. -/
inductive IntArithOp where
  | add
  | sub
  | mul
  | eq
  deriving Repr, DecidableEq

namespace IntArithOp

/-- Source head string used by the runtime dispatcher. -/
def head : IntArithOp → String
  | .add => "i+"
  | .sub => "i-"
  | .mul => "i*"
  | .eq => "ieq"

/-- Current runtime arity for all integer arithmetic sinks:
`(op prefix arg1 arg2)`. -/
def arity (_ : IntArithOp) : Nat := 4

/-- Runtime head decoder for the integer arithmetic sink family. -/
def ofHead? : String → Option IntArithOp
  | "i+" => some .add
  | "i-" => some .sub
  | "i*" => some .mul
  | "ieq" => some .eq
  | _ => none

/-- Integer-valued arithmetic result, matching Rust `IntArithSink`.

Equality returns `1` or `0`, not a boolean atom. -/
def eval : IntArithOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .eq, a, b => if a = b then 1 else 0

theorem ofHead?_head (op : IntArithOp) : ofHead? op.head = some op := by
  cases op <;> rfl

theorem eval_eq_true (a b : Int) (h : a = b) :
    eval .eq a b = 1 := by
  simp [eval, h]

theorem eval_eq_false (a b : Int) (h : a ≠ b) :
    eval .eq a b = 0 := by
  simp [eval, h]

end IntArithOp

/-- Result atom produced by the integer arithmetic extension after decoding its
arguments and evaluating them. -/
def intArithResultAtom (op : IntArithOp) (pfx : Atom) (a b : Int) : Atom :=
  appendSymbolToPrefix pfx (toString (op.eval a b))

/-- Core-template lowering of the integer arithmetic extension:
after decoding/evaluation it becomes a single `.add` sink. -/
def intArithTemplate (op : IntArithOp) (pfx : Atom) (a b : Int) : Template :=
  mkTemplate [mkAdd (intArithResultAtom op pfx a b)]

/-- Integer arithmetic lowering agrees with the core `applySinks` semantics. -/
theorem applySinks_intArithTemplate (s : Space) (op : IntArithOp)
    (pfx : Atom) (a b : Int) (hprefix : isGroundAtom pfx = true) :
    applySinks s [] (intArithTemplate op pfx a b) =
      s ∪ {intArithResultAtom op pfx a b} := by
  apply applySinks_single_add_ground
  exact appendSymbolToPrefix_ground pfx (toString (op.eval a b)) hprefix

example : IntArithOp.ofHead? "i+" = some .add := rfl
example : IntArithOp.ofHead? "i/" = none := rfl

example :
    intArithResultAtom .mul (.expression [.symbol "product"]) 6 7 =
      .expression [.symbol "product", .symbol "42"] := by
  decide

example :
    intArithResultAtom .eq (.expression [.symbol "equal"]) 5 4 =
      .expression [.symbol "equal", .symbol "0"] := by
  decide

/-! ## Float arithmetic sinks -/

/-- Float arithmetic extension heads currently supported by Rust `FloatArithSink`. -/
inductive FloatArithOp where
  | add
  | sub
  | mul
  | div
  | gt
  | lt
  | eq
  deriving Repr, DecidableEq

namespace FloatArithOp

/-- Source head string used by the runtime dispatcher. -/
def head : FloatArithOp → String
  | .add => "f+"
  | .sub => "f-"
  | .mul => "f*"
  | .div => "f/"
  | .gt => "fgt"
  | .lt => "flt"
  | .eq => "feq"

/-- Current runtime arity for all float arithmetic sinks:
`(op prefix arg1 arg2)`. -/
def arity (_ : FloatArithOp) : Nat := 4

/-- Runtime head decoder for the float arithmetic sink family. -/
def ofHead? : String → Option FloatArithOp
  | "f+" => some .add
  | "f-" => some .sub
  | "f*" => some .mul
  | "f/" => some .div
  | "fgt" => some .gt
  | "flt" => some .lt
  | "feq" => some .eq
  | _ => none

/-- Tolerance used by the runtime `feq` predicate. -/
def eqTol : Float := 1e-12

/-- Numeric float result, matching Rust `FloatArithSink`.

Division-by-zero follows the Rust branch and deliberately yields `NaN`
via the `0.0 / 0.0` branch rather than Lean's default `a / 0.0 = inf`
behaviour. -/
def eval : FloatArithOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => if b != 0.0 then a / b else 0.0 / 0.0
  | .gt, a, b => if a > b then 1.0 else 0.0
  | .lt, a, b => if a < b then 1.0 else 0.0
  | .eq, a, b => if Float.abs (a - b) < eqTol then 1.0 else 0.0

theorem ofHead?_head (op : FloatArithOp) : ofHead? op.head = some op := by
  cases op <;> rfl

theorem eval_gt_true (a b : Float) (h : a > b) :
    eval .gt a b = 1.0 := by
  simp [eval, h]

theorem eval_gt_false (a b : Float) (h : ¬ a > b) :
    eval .gt a b = 0.0 := by
  simp [eval, h]

theorem eval_lt_true (a b : Float) (h : a < b) :
    eval .lt a b = 1.0 := by
  simp [eval, h]

theorem eval_lt_false (a b : Float) (h : ¬ a < b) :
    eval .lt a b = 0.0 := by
  simp [eval, h]

theorem eval_eq_true_of_close (a b : Float)
    (h : Float.abs (a - b) < eqTol) :
    eval .eq a b = 1.0 := by
  simp [eval, h]

theorem eval_eq_false_of_separated (a b : Float)
    (h : ¬ Float.abs (a - b) < eqTol) :
    eval .eq a b = 0.0 := by
  simp [eval, h]

/-- The division provider takes its zero branch whenever the host float
comparison classifies the divisor as zero.  Lean's built-in `Float.beq` is an
opaque runtime primitive, so its concrete classification is kept as the
provider premise instead of being discharged by native evaluation. -/
theorem eval_div_zero_branch (a : Float)
    (hzero : ((0.0 : Float) != 0.0) = false) :
    eval .div a 0.0 = 0.0 / 0.0 := by
  simp [eval, hzero]

end FloatArithOp

/-- Runtime float rendering is intentionally a parameter here.

This keeps the theorem family honest: Rust uses `format!("{}", f64)`, which is
not Lean's default `Float.toString`. The arithmetic semantics are settled here;
the exact printer remains a runtime rendering choice. -/
abbrev FloatRenderer := Float → String

/-- Result atom produced by the float arithmetic extension after decoding its
arguments, evaluating them, and rendering the result. -/
def floatArithResultAtom (render : FloatRenderer) (op : FloatArithOp)
    (pfx : Atom) (a b : Float) : Atom :=
  appendSymbolToPrefix pfx (render (op.eval a b))

/-- Core-template lowering of the float arithmetic extension:
after decoding/evaluation/rendering it becomes a single `.add` sink. -/
def floatArithTemplate (render : FloatRenderer) (op : FloatArithOp)
    (pfx : Atom) (a b : Float) : Template :=
  mkTemplate [mkAdd (floatArithResultAtom render op pfx a b)]

/-- Float arithmetic lowering agrees with the core `applySinks` semantics. -/
theorem applySinks_floatArithTemplate (s : Space) (render : FloatRenderer)
    (op : FloatArithOp) (pfx : Atom) (a b : Float)
    (hprefix : isGroundAtom pfx = true) :
    applySinks s [] (floatArithTemplate render op pfx a b) =
      s ∪ {floatArithResultAtom render op pfx a b} := by
  apply applySinks_single_add_ground
  exact appendSymbolToPrefix_ground pfx (render (op.eval a b)) hprefix

example : FloatArithOp.ofHead? "fgt" = some .gt := rfl
example : FloatArithOp.ofHead? "fsin" = none := rfl

/-! ## Comparison sources (`CmpSource`) -/

/-- Currently supported comparison-source modes in Rust `CmpSource`. -/
inductive CmpMode where
  | eq
  | neq
  deriving Repr, DecidableEq

namespace CmpMode

/-- Source head string used by the runtime source dispatcher. -/
def head : CmpMode → String
  | .eq => "=="
  | .neq => "!="

/-- Current runtime arity for comparison sources:
`(== pat witness)` / `(!= pat witness)`. -/
def arity (_ : CmpMode) : Nat := 3

/-- Runtime head decoder for the comparison source family. -/
def ofHead? : String → Option CmpMode
  | "==" => some .eq
  | "!=" => some .neq
  | _ => none

theorem ofHead?_head (mode : CmpMode) : ofHead? mode.head = some mode := by
  cases mode <;> rfl

end CmpMode

/-- Comparison-source lowering into the existing core `SourceFactor` language. -/
def cmpSourceFactor (mode : CmpMode) (pat witness : Atom) : SourceFactor :=
  match mode with
  | .eq => .eqConstraint pat witness
  | .neq => .neqConstraint pat witness

/-- Singleton explicit input spec for a comparison source. -/
def cmpSourceInput (mode : CmpMode) (pat witness : Atom) : InputSpec :=
  .explicit [cmpSourceFactor mode pat witness]

/-- Source-rule constructor for a single comparison factor plus a template. -/
def cmpSourceRule (priority : ℕ) (name : String)
    (mode : CmpMode) (pat witness : Atom) (tmpl : Template) : SourceExecRule :=
  { priority := priority
    name := name
    input := cmpSourceInput mode pat witness
    guards := []
    tmpl := tmpl }

theorem matchSourceFactor_cmpSourceFactor (σ : Subst) (s : Space)
    (mode : CmpMode) (pat witness : Atom) :
    matchSourceFactor σ s (cmpSourceFactor mode pat witness) =
      match mode with
      | .eq => matchSourceFactor σ s (.eqConstraint pat witness)
      | .neq => matchSourceFactor σ s (.neqConstraint pat witness) := by
  cases mode <;> rfl

theorem cmatchSourceFactor_cmpSourceFactor (σ : Subst) (s : Computable.CSpace)
    (mode : CmpMode) (pat witness : Atom) :
    Computable.cmatchSourceFactor σ s (cmpSourceFactor mode pat witness) =
      match mode with
      | .eq => Computable.cmatchSourceFactor σ s (.eqConstraint pat witness)
      | .neq => Computable.cmatchSourceFactor σ s (.neqConstraint pat witness) := by
  cases mode <;> rfl

theorem matchInputSpec_cmpSourceInput (σ : Subst) (s : Space)
    (mode : CmpMode) (pat witness : Atom) :
    matchInputSpec σ s (cmpSourceInput mode pat witness) =
      matchSourceFactors σ s [cmpSourceFactor mode pat witness] := by
  rfl

theorem cmatchInputSpec_cmpSourceInput (σ : Subst) (s : Computable.CSpace)
    (mode : CmpMode) (pat witness : Atom) :
    Computable.cmatchInputSpec σ s (cmpSourceInput mode pat witness) =
      Computable.cmatchSourceFactors σ s [cmpSourceFactor mode pat witness] := by
  rfl

theorem fireSourceRule_cmpSourceRule_noGuards (s : Space)
    (priority : ℕ) (name : String) (mode : CmpMode)
    (pat witness : Atom) (tmpl : Template) :
    fireSourceRule s (cmpSourceRule priority name mode pat witness tmpl) =
      (matchInputSpec [] s (cmpSourceInput mode pat witness)).map
        (fun (σ, _consumed) => applySinks s σ tmpl) := by
  exact fireSourceRule_no_guards s (cmpSourceRule priority name mode pat witness tmpl) rfl

private theorem cfilter_matchSourceGuards_nil {l : List (Subst × List Atom)} :
    l.filter (fun (σ, _) => matchSourceGuards σ []) = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      cases hd with
      | mk σ consumed =>
          simp [matchSourceGuards]

theorem cfireSourceRule_cmpSourceRule_noGuards (s : Computable.CSpace)
    (priority : ℕ) (name : String) (mode : CmpMode)
    (pat witness : Atom) (tmpl : Template) :
    Computable.cfireSourceRule s (cmpSourceRule priority name mode pat witness tmpl) =
      (Computable.cmatchInputSpec [] s (cmpSourceInput mode pat witness)).map
        (fun (σ, _consumed) => Computable.capplySinks s σ tmpl) := by
  simp [Computable.cfireSourceRule, cmpSourceRule, cfilter_matchSourceGuards_nil]

example : CmpMode.ofHead? "==" = some .eq := rfl
example : CmpMode.ofHead? "<" = none := rfl

/-! ## Canaries -/

section Canaries
#check @appendSymbolToPrefix_ground
#check @applySinks_intArithTemplate
#check @applySinks_floatArithTemplate
#check @matchInputSpec_cmpSourceInput
#check @cfireSourceRule_cmpSourceRule_noGuards
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms applySinks_intArithTemplate
#print axioms applySinks_floatArithTemplate
#print axioms fireSourceRule_cmpSourceRule_noGuards
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK
