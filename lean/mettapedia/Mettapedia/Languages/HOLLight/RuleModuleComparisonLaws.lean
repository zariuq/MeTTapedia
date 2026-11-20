import Mettapedia.Languages.HOLLight.RuleModulePrimitives

/-!
# Reflexivity of the structural comparisons of the HOL Light kernel rule module

The HOL Light kernel is stated as a rule module: big-step rewrite rules over constructor data.
Its syntax layer compares types and terms as OCaml's `compare` compares HOL Light's `hol_type` and
`term`: first by constructor (`Tyvar` before `Tyapp`; `Var`, `Const`, `Comb`, `Abs` in this
order), then field by field, names by `"cmp-str"`, lists with the empty list first.  Equality of
types, of terms and of term lists (`"ty-eq"`, `"tm-eq"`, `"tms-eq"`) asks whether the comparison
answers `eq`.

A rule compiler may answer at once, without running the rules, when both arguments of one of the
judgments `"cmp-type"`, `"cmp-types"`, `"ty-eq"`, `"cmp-term"`, `"tm-eq"`, `"tms-eq"` are the same
object: `eq`, or `yes` for the three equalities.  This file transcribes the rules of these
judgments and of the judgments they call, one Lean equation per rule (each equation is labelled
with the name of its rule), and proves that the shortcut gives the answer of the rules.

* Totality.  Each judgment is a Lean function whose arms are its rules, with no catch-all arm:
  Lean's coverage check is a check that the rules cover every input, and structural recursion a
  check that every call terminates.
* Continuations.  A continuation `"…-k"` that calls back into the recursive judgment calling it
  is unfolded in place, as `"cmp-str"` unfolds `"cmp-str-k"`.  `cmpType_Tyapp_Tyapp`,
  `cmpTypes_tycons_tycons`, `cmpTerm_Comb_Comb`, `cmpTerm_Abs_Abs` and `tmsEq_tmcons_tmcons`
  restate the calling rules as the module writes them, through the continuation.
* Reflexivity, for all arguments and with no hypothesis: `cmpStr_refl`, `cmpType_refl`,
  `cmpTypes_refl`, `tyEq_refl`, `cmpLeaf_refl`, `cmpTerm_refl`, `tmEq_refl`, `tmsEq_refl`.
* The shortcut.  `fastPath_sound`: if a test holds only of equal arguments (pointer equality on
  immutable data is one), the function that answers `eq` (resp. `yes`) where the test holds and
  the answer of the rules elsewhere is the function of the rules.  `cmpType_fastPath`,
  `cmpTypes_fastPath`, `tyEq_fastPath`, `cmpTerm_fastPath`, `tmEq_fastPath` and
  `tmsEq_fastPath` are its instances.

The comparisons are structural, not up to renaming of bound variables: the identity functions
`λx. x` and `λy. y` are not `"tm-eq"` (see the examples).  Comparison up to renaming (`"orda"`,
`"alphaorder"`) is not treated here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws

open Mettapedia.Languages.HOLLight.RuleModulePrimitives

/-! ## The module's syntax -/

mutual

/-- Sort `Type` of the module: a type variable, or a type constructor applied to a list of
types. -/
inductive Ty
  | Tyvar (n : Str)
  | Tyapp (n : Str) (args : Tys)
  deriving DecidableEq, Repr

/-- Sort `Tys`: a list of types. -/
inductive Tys
  | tynil
  | tycons (x : Ty) (xs : Tys)
  deriving DecidableEq, Repr

end

/-- Sort `Term`: a variable or a constant (a name and a type), an application, an
abstraction. -/
inductive Term
  | Var (n : Str) (ty : Ty)
  | Const (n : Str) (ty : Ty)
  | Comb (f x : Term)
  | Abs (v b : Term)
  deriving DecidableEq, Repr

/-- Sort `Tms`: a list of terms. -/
inductive Tms
  | tmnil
  | tmcons (x : Term) (xs : Tms)
  deriving DecidableEq, Repr

/-! ## The rules

A rule's premises are calls evaluated left to right.  Below, each premise but the last is a
`let`, in the written order and named as in the rule; in every rule here the last premise
computes the rule's result, and it appears as the result. -/

/-! ### Types -/

mutual

/-- `"cmp-type-vv"`, `"cmp-type-va"`, `"cmp-type-av"`, and `"cmp-type-aa"` with its continuation
`"cmp-type-k-*"` unfolded in place; `cmpType_Tyapp_Tyapp` restates `"cmp-type-aa"` as the module
writes it, through `cmpTypeK`. -/
def cmpType : Ty → Ty → Ord
  | .Tyvar a, .Tyvar b => cmpStr a b  -- "cmp-type-vv"
  | .Tyvar _, .Tyapp _ _ => .lt       -- "cmp-type-va"
  | .Tyapp _ _, .Tyvar _ => .gt       -- "cmp-type-av"
  | .Tyapp n1 a1, .Tyapp n2 a2 =>     -- "cmp-type-aa"
    match cmpStr n1 n2 with
    | .lt => .lt                      -- "cmp-type-k-lt"
    | .gt => .gt                      -- "cmp-type-k-gt"
    | .eq => cmpTypes a1 a2           -- "cmp-type-k-eq"
termination_by structural t _ => t

/-- `"cmp-types-nn"`, `"cmp-types-nc"`, `"cmp-types-cn"`, and `"cmp-types-cc"` with its
continuation `"cmp-types-k-*"` unfolded in place; `cmpTypes_tycons_tycons` restates
`"cmp-types-cc"` as the module writes it, through `cmpTypesK`. -/
def cmpTypes : Tys → Tys → Ord
  | .tynil, .tynil => .eq             -- "cmp-types-nn"
  | .tynil, .tycons _ _ => .lt        -- "cmp-types-nc"
  | .tycons _ _, .tynil => .gt        -- "cmp-types-cn"
  | .tycons x xs, .tycons y ys =>     -- "cmp-types-cc"
    match cmpType x y with
    | .lt => .lt                      -- "cmp-types-k-lt"
    | .gt => .gt                      -- "cmp-types-k-gt"
    | .eq => cmpTypes xs ys           -- "cmp-types-k-eq"
termination_by structural l _ => l

end

/-- `"cmp-type-k-*"`. -/
def cmpTypeK : Ord → Tys → Tys → Ord
  | .lt, _, _ => .lt                  -- "cmp-type-k-lt"
  | .gt, _, _ => .gt                  -- "cmp-type-k-gt"
  | .eq, a1, a2 => cmpTypes a1 a2     -- "cmp-type-k-eq"

/-- `"cmp-types-k-*"`. -/
def cmpTypesK : Ord → Tys → Tys → Ord
  | .lt, _, _ => .lt                  -- "cmp-types-k-lt"
  | .gt, _, _ => .gt                  -- "cmp-types-k-gt"
  | .eq, xs, ys => cmpTypes xs ys     -- "cmp-types-k-eq"

/-- `"cmp-type-aa"` as the module states it. -/
theorem cmpType_Tyapp_Tyapp (n1 : Str) (a1 : Tys) (n2 : Str) (a2 : Tys) :
    cmpType (.Tyapp n1 a1) (.Tyapp n2 a2) = cmpTypeK (cmpStr n1 n2) a1 a2 := by
  simp only [cmpType]
  cases cmpStr n1 n2 <;> rfl

/-- `"cmp-types-cc"` as the module states it. -/
theorem cmpTypes_tycons_tycons (x : Ty) (xs : Tys) (y : Ty) (ys : Tys) :
    cmpTypes (.tycons x xs) (.tycons y ys) = cmpTypesK (cmpType x y) xs ys := by
  simp only [cmpTypes]
  cases cmpType x y <;> rfl

/-- `"ty-eq"`. -/
def tyEq (a b : Ty) : Flag :=
  let o := cmpType a b
  ordIsEq o

/-! ### Terms -/

/-- `"cmp-leaf-k-*"`. -/
def cmpLeafK : Ord → Ty → Ty → Ord
  | .lt, _, _ => .lt                  -- "cmp-leaf-k-lt"
  | .gt, _, _ => .gt                  -- "cmp-leaf-k-gt"
  | .eq, t1, t2 => cmpType t1 t2      -- "cmp-leaf-k-eq"

/-- `"cmp-leaf"`: the names, then the types. -/
def cmpLeaf (n1 : Str) (t1 : Ty) (n2 : Str) (t2 : Ty) : Ord :=
  let o := cmpStr n1 n2
  cmpLeafK o t1 t2

/-- `"cmp-term-*"`, one rule for each pair of constructors, with the continuation
`"cmp-term-k-*"` of `"cmp-term-mm"` and `"cmp-term-aa"` unfolded in place; `cmpTerm_Comb_Comb`
and `cmpTerm_Abs_Abs` restate these two rules as the module writes them, through `cmpTermK`. -/
def cmpTerm : Term → Term → Ord
  | .Var n1 t1, .Var n2 t2 => cmpLeaf n1 t1 n2 t2      -- "cmp-term-vv"
  | .Var _ _, .Const _ _ => .lt                        -- "cmp-term-vc"
  | .Var _ _, .Comb _ _ => .lt                         -- "cmp-term-vm"
  | .Var _ _, .Abs _ _ => .lt                          -- "cmp-term-va"
  | .Const _ _, .Var _ _ => .gt                        -- "cmp-term-cv"
  | .Const n1 t1, .Const n2 t2 => cmpLeaf n1 t1 n2 t2  -- "cmp-term-cc"
  | .Const _ _, .Comb _ _ => .lt                       -- "cmp-term-cm"
  | .Const _ _, .Abs _ _ => .lt                        -- "cmp-term-ca"
  | .Comb _ _, .Var _ _ => .gt                         -- "cmp-term-mv"
  | .Comb _ _, .Const _ _ => .gt                       -- "cmp-term-mc"
  | .Comb f1 x1, .Comb f2 x2 =>                        -- "cmp-term-mm"
    match cmpTerm f1 f2 with
    | .lt => .lt                                       -- "cmp-term-k-lt"
    | .gt => .gt                                       -- "cmp-term-k-gt"
    | .eq => cmpTerm x1 x2                             -- "cmp-term-k-eq"
  | .Comb _ _, .Abs _ _ => .lt                         -- "cmp-term-ma"
  | .Abs _ _, .Var _ _ => .gt                          -- "cmp-term-av"
  | .Abs _ _, .Const _ _ => .gt                        -- "cmp-term-ac"
  | .Abs _ _, .Comb _ _ => .gt                         -- "cmp-term-am"
  | .Abs v1 b1, .Abs v2 b2 =>                          -- "cmp-term-aa"
    match cmpTerm v1 v2 with
    | .lt => .lt                                       -- "cmp-term-k-lt"
    | .gt => .gt                                       -- "cmp-term-k-gt"
    | .eq => cmpTerm b1 b2                             -- "cmp-term-k-eq"
termination_by structural t _ => t

/-- `"cmp-term-k-*"`. -/
def cmpTermK : Ord → Term → Term → Ord
  | .lt, _, _ => .lt                  -- "cmp-term-k-lt"
  | .gt, _, _ => .gt                  -- "cmp-term-k-gt"
  | .eq, a, b => cmpTerm a b          -- "cmp-term-k-eq"

/-- `"cmp-term-mm"` as the module states it. -/
theorem cmpTerm_Comb_Comb (f1 x1 f2 x2 : Term) :
    cmpTerm (.Comb f1 x1) (.Comb f2 x2) = cmpTermK (cmpTerm f1 f2) x1 x2 := by
  simp only [cmpTerm]
  cases cmpTerm f1 f2 <;> rfl

/-- `"cmp-term-aa"` as the module states it. -/
theorem cmpTerm_Abs_Abs (v1 b1 v2 b2 : Term) :
    cmpTerm (.Abs v1 b1) (.Abs v2 b2) = cmpTermK (cmpTerm v1 v2) b1 b2 := by
  simp only [cmpTerm]
  cases cmpTerm v1 v2 <;> rfl

/-- `"tm-eq"`. -/
def tmEq (a b : Term) : Flag :=
  let o := cmpTerm a b
  ordIsEq o

/-- `"tms-eq-nn"`, `"tms-eq-nc"`, `"tms-eq-cn"`, and `"tms-eq-cc"` with its continuation
`"tms-eq-k-*"` unfolded in place; `tmsEq_tmcons_tmcons` restates `"tms-eq-cc"` as the module
writes it, through `tmsEqK`. -/
def tmsEq : Tms → Tms → Flag
  | .tmnil, .tmnil => .yes            -- "tms-eq-nn"
  | .tmnil, .tmcons _ _ => .no        -- "tms-eq-nc"
  | .tmcons _ _, .tmnil => .no        -- "tms-eq-cn"
  | .tmcons x xs, .tmcons y ys =>     -- "tms-eq-cc"
    match tmEq x y with
    | .no => .no                      -- "tms-eq-k-no"
    | .yes => tmsEq xs ys             -- "tms-eq-k-yes"
termination_by structural l _ => l

/-- `"tms-eq-k-*"`. -/
def tmsEqK : Flag → Tms → Tms → Flag
  | .no, _, _ => .no                  -- "tms-eq-k-no"
  | .yes, xs, ys => tmsEq xs ys       -- "tms-eq-k-yes"

/-- `"tms-eq-cc"` as the module states it. -/
theorem tmsEq_tmcons_tmcons (x : Term) (xs : Tms) (y : Term) (ys : Tms) :
    tmsEq (.tmcons x xs) (.tmcons y ys) = tmsEqK (tmEq x y) xs ys := by
  simp only [tmsEq]
  cases tmEq x y <;> rfl

/-! ## Reflexivity -/

/-- `"cmp-nib"` answers `eq` on equal digits. -/
theorem cmpNib_refl (a : Nib) : cmpNib a a = .eq := by
  cases a <;> rfl

/-- `"cmp-byte"` answers `eq` on equal bytes. -/
theorem cmpByte_refl : ∀ b : Byte, cmpByte b b = .eq
  | .byte hi lo => by
    show (cmpNib hi hi).then (cmpNib lo lo) = .eq
    rw [cmpNib_refl, cmpNib_refl]
    rfl

/-- `"cmp-str"` answers `eq` on equal names. -/
theorem cmpStr_refl : ∀ s : Str, cmpStr s s = .eq
  | .nnil => rfl
  | .ncons x xs => by
    rw [cmpStr_ncons_ncons, cmpByte_refl]
    exact cmpStr_refl xs

mutual

/-- `"cmp-type"` answers `eq` on equal types. -/
theorem cmpType_refl : ∀ t : Ty, cmpType t t = .eq
  | .Tyvar a => cmpStr_refl a
  | .Tyapp n args => by
    rw [cmpType_Tyapp_Tyapp, cmpStr_refl]
    exact cmpTypes_refl args
termination_by structural t => t

/-- `"cmp-types"` answers `eq` on equal lists of types. -/
theorem cmpTypes_refl : ∀ l : Tys, cmpTypes l l = .eq
  | .tynil => rfl
  | .tycons x xs => by
    rw [cmpTypes_tycons_tycons, cmpType_refl x]
    exact cmpTypes_refl xs
termination_by structural l => l

end

/-- `"ty-eq"` answers `yes` on equal types. -/
theorem tyEq_refl (t : Ty) : tyEq t t = .yes :=
  congrArg ordIsEq (cmpType_refl t)

/-- `"cmp-leaf"` answers `eq` on an equal name and an equal type. -/
theorem cmpLeaf_refl (n : Str) (t : Ty) : cmpLeaf n t n t = .eq := by
  show cmpLeafK (cmpStr n n) t t = .eq
  rw [cmpStr_refl]
  exact cmpType_refl t

/-- `"cmp-term"` answers `eq` on equal terms. -/
theorem cmpTerm_refl : ∀ t : Term, cmpTerm t t = .eq
  | .Var n ty => cmpLeaf_refl n ty
  | .Const n ty => cmpLeaf_refl n ty
  | .Comb f x => by
    rw [cmpTerm_Comb_Comb, cmpTerm_refl f]
    exact cmpTerm_refl x
  | .Abs v b => by
    rw [cmpTerm_Abs_Abs, cmpTerm_refl v]
    exact cmpTerm_refl b
termination_by structural t => t

/-- `"tm-eq"` answers `yes` on equal terms. -/
theorem tmEq_refl (t : Term) : tmEq t t = .yes :=
  congrArg ordIsEq (cmpTerm_refl t)

/-- `"tms-eq"` answers `yes` on equal lists of terms. -/
theorem tmsEq_refl : ∀ l : Tms, tmsEq l l = .yes
  | .tmnil => rfl
  | .tmcons x xs => by
    rw [tmsEq_tmcons_tmcons, tmEq_refl]
    exact tmsEq_refl xs
termination_by structural l => l

/-! ## The shortcut -/

universe u v

/-- A shortcut that answers `v` whenever a test `same` holds, and otherwise computes `f`, gives
the value of `f`, provided `same` holds only of equal arguments and `f` takes the value `v` on
equal arguments. -/
theorem fastPath_sound {α : Sort u} {β : Sort v} (f : α → α → β) (v : β)
    (hrefl : ∀ a, f a a = v) (same : α → α → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : α) : (if same a b then v else f a b) = f a b := by
  cases h : same a b with
  | false => rfl
  | true =>
    show v = f a b
    rw [hsame a b h, hrefl]

/-- The shortcut for `"cmp-type"`. -/
theorem cmpType_fastPath (same : Ty → Ty → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Ty) : (if same a b then .eq else cmpType a b) = cmpType a b :=
  fastPath_sound cmpType .eq cmpType_refl same hsame a b

/-- The shortcut for `"cmp-types"`. -/
theorem cmpTypes_fastPath (same : Tys → Tys → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Tys) : (if same a b then .eq else cmpTypes a b) = cmpTypes a b :=
  fastPath_sound cmpTypes .eq cmpTypes_refl same hsame a b

/-- The shortcut for `"ty-eq"`. -/
theorem tyEq_fastPath (same : Ty → Ty → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Ty) : (if same a b then .yes else tyEq a b) = tyEq a b :=
  fastPath_sound tyEq .yes tyEq_refl same hsame a b

/-- The shortcut for `"cmp-term"`. -/
theorem cmpTerm_fastPath (same : Term → Term → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Term) : (if same a b then .eq else cmpTerm a b) = cmpTerm a b :=
  fastPath_sound cmpTerm .eq cmpTerm_refl same hsame a b

/-- The shortcut for `"tm-eq"`. -/
theorem tmEq_fastPath (same : Term → Term → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Term) : (if same a b then .yes else tmEq a b) = tmEq a b :=
  fastPath_sound tmEq .yes tmEq_refl same hsame a b

/-- The shortcut for `"tms-eq"`. -/
theorem tmsEq_fastPath (same : Tms → Tms → Bool) (hsame : ∀ a b, same a b = true → a = b)
    (a b : Tms) : (if same a b then .yes else tmsEq a b) = tmsEq a b :=
  fastPath_sound tmsEq .yes tmsEq_refl same hsame a b

/-! ## Examples -/

namespace Examples

open RuleModulePrimitives.Examples (nameBool nameFun nameX)

/-- The name `A`: byte `41`. -/
def nameA : Str := .ncons (.byte .x4 .x1) .nnil

/-- The name `B`: byte `42`. -/
def nameB : Str := .ncons (.byte .x4 .x2) .nnil

/-- The name `y`: byte `79`. -/
def nameY : Str := .ncons (.byte .x7 .x9) .nnil

/-- The type variable `A`. -/
def tyA : Ty := .Tyvar nameA

/-- The type variable `B`. -/
def tyB : Ty := .Tyvar nameB

/-- The type `bool`. -/
def tyBool : Ty := .Tyapp nameBool .tynil

/-- The function type `d -> r`, as `"mk-fun-ty"` builds it. -/
def funTy (d r : Ty) : Ty := .Tyapp nameFun (.tycons d (.tycons r .tynil))

/-- The variable `x:A`. -/
def varXA : Term := .Var nameX tyA

/-- The variable `y:A`. -/
def varYA : Term := .Var nameY tyA

/-- The variable `x:B`: the name of `x:A`, another type. -/
def varXB : Term := .Var nameX tyB

-- Names.
example : cmpStr nameA nameA = .eq := by decide
example : cmpStr nameA nameB = .lt := by decide

-- Types: `A -> bool` against itself, and against `B -> bool`.
example : cmpType (funTy tyA tyBool) (funTy tyA tyBool) = .eq := by decide
example : tyEq (funTy tyA tyBool) (funTy tyA tyBool) = .yes := by decide
example : cmpTypes (.tycons tyA (.tycons tyBool .tynil)) (.tycons tyA (.tycons tyBool .tynil))
    = .eq := by decide
example : cmpType (funTy tyA tyBool) (funTy tyB tyBool) = .lt := by decide
example : tyEq (funTy tyA tyBool) (funTy tyB tyBool) = .no := by decide
-- The laws are about equal arguments: the distinct `A` and `B` compare `lt` one way and `gt`
-- the other.
example : tyA ≠ tyB ∧ cmpType tyA tyB = .lt ∧ cmpType tyB tyA = .gt := by decide
example : tyEq tyA tyB = .no := by decide
-- A type variable comes before a type constructor application; `[]` before a nonempty list.
example : cmpType tyA tyBool = .lt := by decide
example : cmpTypes .tynil (.tycons tyA .tynil) = .lt := by decide

-- Terms.
example : cmpTerm varXA varXA = .eq := by decide
example : tmEq varXA varXA = .yes := by decide
example : cmpLeaf nameX tyA nameX tyA = .eq := by decide
-- Two different variables `x:A` and `y:A` are not equal ...
example : tmEq varXA varYA = .no := by decide
example : cmpTerm varXA varYA = .lt := by decide
-- ... nor are `x:A` and `x:B`, which differ only in their types.
example : tmEq varXA varXB = .no := by decide
example : cmpLeaf nameX tyA nameX tyB = .lt := by decide
-- Structural, not up to renaming: `λx. x` equals itself, not `λy. y`.
example : tmEq (.Abs varXA varXA) (.Abs varXA varXA) = .yes := by decide
example : tmEq (.Abs varXA varXA) (.Abs varYA varYA) = .no := by decide
-- `Var`, `Const`, `Comb`, `Abs` in this order.
example : cmpTerm (.Const nameX tyA) varXA = .gt := by decide
example : cmpTerm (.Comb varXA varXA) (.Abs varXA varXA) = .lt := by decide

-- Lists of terms.
example : tmsEq (.tmcons varXA (.tmcons varYA .tmnil)) (.tmcons varXA (.tmcons varYA .tmnil))
    = .yes := by decide
example : tmsEq (.tmcons varXA (.tmcons varYA .tmnil)) (.tmcons varXA (.tmcons varXB .tmnil))
    = .no := by decide
example : tmsEq (.tmcons varXA .tmnil) .tmnil = .no := by decide

-- The shortcut with a test that holds only of equal arguments: structural equality is one.
example (a b : Term) : (if decide (a = b) then .eq else cmpTerm a b) = cmpTerm a b :=
  cmpTerm_fastPath (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h) a b

/-- A test that compares the names of two variables and ignores their types. -/
def sameName : Term → Term → Bool
  | .Var n _, .Var m _ => decide (n = m)
  | _, _ => false

-- `sameName` holds of `x:A` and `x:B`, which are not equal, and the shortcut built on it answers
-- `eq` where the rules answer `lt`.
example : sameName varXA varXB = true ∧ varXA ≠ varXB := by decide
example : (if sameName varXA varXB then .eq else cmpTerm varXA varXB) ≠ cmpTerm varXA varXB := by
  decide

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws

#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpStr_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpType_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTypes_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tyEq_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpLeaf_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTerm_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tmEq_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tmsEq_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpType_Tyapp_Tyapp
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTypes_tycons_tycons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTerm_Comb_Comb
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTerm_Abs_Abs
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tmsEq_tmcons_tmcons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.fastPath_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpType_fastPath
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTypes_fastPath
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tyEq_fastPath
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.cmpTerm_fastPath
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tmEq_fastPath
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws.tmsEq_fastPath
