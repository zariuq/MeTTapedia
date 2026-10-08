import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh
import Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces

/-!
# Lexical fresh: three faces of a clause with a fresh local

The lexical-fresh clause `(= (f $x) (let $y (succ $x) (succ $y)))` has a fresh
local `$y` and the parameter `$x`.  Its three faces place the local's
quantifier alike, inside the parameter's:

* **operational**: the local is a slot of the clause's frame, made afresh at
  each call: a closure called twice binds two slots and answers both calls; if
  the local is shared instead (`{$y}`, one slot for every call), the second
  call's binding conflicts and there is no answer;
* **type**: `f a ≡ (λy. succ y) (succ a)`: the local is a β-redex under the
  application, one per call;
* **set** (the definitional extension of the standard model of the numerals,
  `DefinitionFaces.NatExample`): `∀x. ∃y. y = succ x ∧ f x = succ y` holds,
  while the persistent placement `∃y. ∀x. y = succ x ∧ f x = succ y` fails.

`three_faces_quantifier_placement` states the three together.  A shared name,
by contrast, is a parameter: lambda lifting passes it as a leading argument
(`run_lifted_call`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshFaces

open Mettapedia.Logic.HOL
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces
open Mettapedia.GSLT.LanguageDef.TemplateScope.DefinitionFaces.NatExample

/-! ## The operational face -/

/-- Symbols of the clause's program. -/
inductive FSy where
  | zero | succ | f | Pair | unit
  deriving DecidableEq, Repr

/-- Spellings of the clause's program. -/
inductive FSp where
  | x | y | g | u
  deriving DecidableEq, Repr

abbrev FA := Src FSy FSp

/-- The clause `(= (f) (lam x (let $y (succ x) (succ $y))))`, its local written
with the crossing set `xs`: `none` makes it fresh (lexical fresh's default),
`some [y]` shares it with the clause's root. -/
def clauseF (xs : Option (List FSp)) : FA :=
  .lam .x none (.letS (.sv .y) (.app (.sym .succ) (.par .x)) (.app (.sym .succ) (.sv .y)) xs)

/-- The equations: `f` only. -/
def clF (xs : Option (List FSp)) : FSy → Option FA := fun F => if F = .f then some (clauseF xs) else none

/-- One closure of `f`, called on `0` and on `1`:
`(let $g (f) (Pair ($g 0) ($g 1)))`. -/
def twoCalls : FA :=
  .letS (.sv .g) (.fn .f)
    (.app (.app (.sym .Pair) (.app (.sv .g) (.sym .zero)))
      (.app (.sv .g) (.app (.sym .succ) (.sym .zero)))) none

/-- Answers under lexical fresh with binder identities. -/
def ansF (xs : Option (List FSp)) : Option (List (Tm FSy (BId FSp))) :=
  answers .static (progLF .u .unit (clF xs)) 60 (elabLFFormAt [] twoCalls)

def nI : ℕ → Tm FSy (BId FSp)
  | 0 => .sym .zero
  | n + 1 => .app (.sym .succ) (nI n)

/-- **Operational face.**  Fresh per call, the closure answers both calls:
`(Pair 2 3)`.  Shared by all calls, the two bindings of the one slot
conflict: no answer. -/
theorem op_quantifier_placement :
    ansF none = some [.app (.app (.sym .Pair) (nI 2)) (nI 3)] ∧ ansF (some [.y]) = some [] := by
  constructor <;> decide +kernel

/-! ## The type face -/

/-- `succ` in the extended signature. -/
def succE {Γ : Ctx Unit} : Term (Ext NatC ι ι) Γ (ι ⇒ ι) := .const (.old .succ)

/-- `(λy. succ y) (succ zero)`: the clause's body at `zero`, its local a
β-redex. -/
def letAtZero : Term (Ext NatC ι ι) [] ι :=
  .app (.lam (.app succE (.var .vz))) (.app succE (.const (.old .zero)))

/-- **Type face.**  `f zero ≡ (λy. succ y) (succ zero)`: the local is bound by a
β-redex under the call. -/
theorem type_quantifier_placement : DefEq (lamBody body) (call (τ := ι) zeroG) letAtZero := by
  have hβ : DefEq (lamBody body) letAtZero
      (instantiate (Base := Unit) (.app succE (.const (.old .zero))) (.app succE (.var .vz))) :=
    DefEq.beta _ _
  have hβ' : instantiate (Base := Unit) (.app succE (.const (.old .zero)) : Term (Ext NatC ι ι) [] ι)
      (.app succE (.var .vz)) =
      DefinedConst.embed (target := ι ⇒ ι)
        (Term.app (Term.const NatC.succ) (Term.app (Term.const NatC.succ) (Term.const NatC.zero)) :
          Term NatC [] ι) := rfl
  rw [hβ'] at hβ
  exact .trans type_f_zero (.symm hβ)

/-! ## The set face -/

/-- `f` in the extended signature. -/
def fE {Γ : Ctx Unit} : Term (Ext NatC ι ι) Γ (ι ⇒ ι) := .const .defined

/-- `∀x. ∃y. y = succ x ∧ f x = succ y`: the local inside the parameter. -/
def perCallSentence : ClosedFormula (Ext NatC ι ι) :=
  .all (.ex (.and (.eq (.var .vz) (.app succE (.var (.vs .vz))))
    (.eq (.app fE (.var (.vs .vz))) (.app succE (.var .vz)))))

/-- `∃y. ∀x. y = succ x ∧ f x = succ y`: one local for every argument. -/
def persistentSentence : ClosedFormula (Ext NatC ι ι) :=
  .ex (.all (.and (.eq (.var (.vs .vz)) (.app succE (.var .vz)))
    (.eq (.app fE (.var .vz)) (.app succE (.var (.vs .vz))))))

/-- The definitional extension of the standard model of the numerals. -/
abbrev Mf := Mℕ.definitionExtension (lamBody body)

/-- **Set face.**  The per-call placement holds, the persistent one fails. -/
theorem set_quantifier_placement :
    (Mf.denote perCallSentence (emptyVal Mf)).down ∧ ¬ (Mf.denote persistentSentence (emptyVal Mf)).down := by
  constructor
  · intro x _
    refine ⟨ULift.up (x.down + 1), trivial, ?_, ?_⟩
    · rfl
    · rfl
  · rintro ⟨y, -, hy⟩
    have h0 := (hy (ULift.up 0) trivial).1
    have h1 := (hy (ULift.up 1) trivial).1
    have e0 : y.down = 1 := congrArg ULift.down h0
    have e1 : y.down = 2 := congrArg ULift.down h1
    omega

/-- **The three faces agree on quantifier placement** for the lexical-fresh
clause `(= (f $x) (let $y (succ $x) (succ $y)))`: operationally the local is
fresh per call (a closure answers two calls; one shared local has no answer),
by definitional equality it is a β-redex under each application, and in the
standard model the sentence with the local inside the parameter holds while
the one with the local outside fails. -/
theorem three_faces_quantifier_placement :
    (ansF none = some [.app (.app (.sym .Pair) (nI 2)) (nI 3)] ∧ ansF (some [.y]) = some []) ∧
      DefEq (lamBody body) (call (τ := ι) zeroG) letAtZero ∧
      ((Mf.denote perCallSentence (emptyVal Mf)).down ∧
        ¬ (Mf.denote persistentSentence (emptyVal Mf)).down) :=
  ⟨op_quantifier_placement, type_quantifier_placement, set_quantifier_placement⟩

end Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshFaces
