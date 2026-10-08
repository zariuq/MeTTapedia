import Mettapedia.TypeTheory.Calculi.SealedCode.Boundary
import Mettapedia.TypeTheory.Calculi.ContextualCode.Confluence

/-!
# Controls: three ways to break a quotation

Each control sets a variant beside the calculus and shows that it gives one
program two results.

* **A `let` that enters quotations.** In the Prime draft `((lam $x @$x) 5)`
  gives `(quote $x)` but `(let $x 5 @$x)` gives `(quote 5)`. With names read
  as the draft reads them, `let` substitution that enters a quotation disagrees
  with β (`leakyLet_disagrees`), and one program reaches two different names
  depending on whether the `let` under a `lam` fires first
  (`leakyLet_incoherent`). In the calculus `let` is β, and the same program has
  one name (`letAsBeta_name`).
* **A quotation that substitution enters.** A program that writes such a
  quotation itself (the sealed-code control `FTerm.frozen`) has two names:
  `(λx. ⌜x⌝) ((λy. y) a)` (`leakyQuote_incoherent`).
* **A bracket that fills as written.** Adding a rule that fills a template as
  written beside the `lift` derivation gives the bracket two meanings
  (`bothBrackets_incoherent`). The derived bracket alone names the normal form
  (`instAll_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-! ## A `let` that enters quotations -/

/-- Terms with names, read as the Prime draft reads them: a name is bound by
`lam` and by `let`, and a quotation keeps the names in it. -/
inductive NTerm : Type where
  | atom : String → NTerm
  | lam : String → NTerm → NTerm
  | app : NTerm → NTerm → NTerm
  | quote : NTerm → NTerm
  | letIn : String → NTerm → NTerm → NTerm
  deriving DecidableEq

namespace NTerm

/-- Substitution for `lam`: it stops at a quotation and at a binder of the same
name. -/
def substLam (x : String) (v : NTerm) : NTerm → NTerm
  | atom y => if y = x then v else atom y
  | lam y b => if y = x then lam y b else lam y (substLam x v b)
  | app f a => app (substLam x v f) (substLam x v a)
  | quote M => quote M
  | letIn y V B => letIn y (substLam x v V) (if y = x then B else substLam x v B)

/-- Substitution for the draft's `let`: it also enters quotations. -/
def substLet (x : String) (v : NTerm) : NTerm → NTerm
  | atom y => if y = x then v else atom y
  | lam y b => if y = x then lam y b else lam y (substLet x v b)
  | app f a => app (substLet x v f) (substLet x v a)
  | quote M => quote (substLet x v M)
  | letIn y V B => letIn y (substLet x v V) (if y = x then B else substLet x v B)

/-- Values: names, abstractions and quotations. -/
inductive IsValue : NTerm → Prop where
  | atom (s : String) : IsValue (atom s)
  | lam (x : String) (b : NTerm) : IsValue (lam x b)
  | quote (M : NTerm) : IsValue (quote M)

end NTerm

open NTerm in
/-- β substitutes with `substLam`; the draft's `let` substitutes a value with
`substLet`. -/
inductive LeakyStep : NTerm → NTerm → Prop where
  | beta (x : String) (b a : NTerm) : LeakyStep (.app (.lam x b) a) (substLam x a b)
  | letIn (x : String) (V B : NTerm) : IsValue V → LeakyStep (.letIn x V B) (substLet x V B)
  | lam {x : String} {b b' : NTerm} : LeakyStep b b' → LeakyStep (.lam x b) (.lam x b')
  | appL {f f' a : NTerm} : LeakyStep f f' → LeakyStep (.app f a) (.app f' a)
  | appR {f a a' : NTerm} : LeakyStep a a' → LeakyStep (.app f a) (.app f a')
  | letV {x : String} {V V' B : NTerm} : LeakyStep V V' → LeakyStep (.letIn x V B) (.letIn x V' B)
  | letB {x : String} {V B B' : NTerm} : LeakyStep B B' → LeakyStep (.letIn x V B) (.letIn x V B')

theorem leakyStep_quote_irreducible (M N : NTerm) : ¬ LeakyStep (.quote M) N := by
  intro h
  cases h

/-- **The draft's `let` disagrees with β.** `(let y 5 @y)` names `5`, while
`((lam y @y) 5)` names `y`. -/
theorem leakyLet_disagrees :
    LeakyStep (.letIn "y" (.atom "5") (.quote (.atom "y"))) (.quote (.atom "5")) ∧
      LeakyStep (.app (.lam "y" (.quote (.atom "y"))) (.atom "5")) (.quote (.atom "y")) :=
  ⟨.letIn _ _ _ (.atom _), .beta _ _ _⟩

/-- `((lam x (let y x @y)) 5)`. -/
def leakyLetProgram : NTerm :=
  .app (.lam "x" (.letIn "y" (.atom "x") (.quote (.atom "y")))) (.atom "5")

/-- **The draft's `let` makes names depend on the route.** Reducing β first
names `5`; reducing the `let` under the `lam` first names `x`. -/
theorem leakyLet_incoherent : SealedCode.Incoherent LeakyStep :=
  ⟨leakyLetProgram, .quote (.atom "5"), .quote (.atom "x"),
    (Relation.ReflTransGen.single (.beta _ _ _)).tail (.letIn _ _ _ (.atom _)),
    (Relation.ReflTransGen.single (.appL (.lam (.letIn _ _ _ (.atom _))))).tail (.beta _ _ _),
    leakyStep_quote_irreducible _, leakyStep_quote_irreducible _, by decide⟩

/-- **In the calculus `let` is β**, and the same program,
`(λx. (λy. ⌜y⌝) x) 5`, names `y` by every route. -/
theorem letAsBeta_name :
    Steps (.app (.lam (.app (.lam (.cquote 0 (.sym "y"))) (.var 0))) (.sym "5") : Term 0)
      (.cquote 0 (.sym "y")) :=
  (Relation.ReflTransGen.single (.beta _ _)).tail (.beta _ _)

theorem letAsBeta_name_unique {W : Term 0}
    (h : Steps (.app (.lam (.app (.lam (.cquote 0 (.sym "y"))) (.var 0))) (.sym "5") : Term 0)
      (.cquote 0 W)) : W = .sym "y" :=
  name_unique h letAsBeta_name

/-! ## A quotation that substitution enters -/

open SealedCode in
/-- `(λx. ⌜x⌝) ((λy. y) a)`, with a quotation that substitution enters. -/
def leakyQuoteProgram : FTerm 0 := .app (.lam (.frozen (.var 0))) (.app (.lam (.var 0)) (.sym "a"))

open SealedCode in
/-- **A quotation that substitution enters gives one program two names**,
`⌜(λy. y) a⌝` and `⌜a⌝`, depending on whether the argument is reduced before
it is substituted. -/
theorem leakyQuote_incoherent : Incoherent (@Premature 0) :=
  ⟨leakyQuoteProgram, .frozen (.app (.lam (.var 0)) (.sym "a")), .frozen (.sym "a"),
    .single (.beta _ _),
    (Relation.ReflTransGen.single (.appR (.beta _ _))).tail (.beta _ _),
    premature_frozen_irreducible _, premature_frozen_irreducible _, by decide⟩

/-! ## A bracket that fills as written -/

/-- Contextual code with an extra rule that fills a template as written. -/
inductive BothBrackets : {n : Nat} → Term n → Term n → Prop where
  | step {n : Nat} {M N : Term n} : Step M N → BothBrackets M N
  | asWritten {n k : Nat} (M : Term k) (V : Fin k → Term 0) :
      BothBrackets (instAll (.cquote k M : Term n) (fun i => .cquote 0 (V i)))
        (.cquote 0 (M.subst (fillSub V)))

theorem bothBrackets_cquote_irreducible {n k : Nat} (M : Term k) (N : Term n) :
    ¬ BothBrackets (.cquote k M) N := by
  intro h
  cases h with
  | step inner => exact cquote_no_step M N inner

/-- The template `(quote ($x a) ($x))` and the name `@(λy. y)`. -/
def applyTemplate : Term 1 := .app (.var 0) (.sym "a")
def identityCode : Term 0 := .lam (.var 0)

/-- **Two meanings for the bracket give one program two names**: filling as
written names the redex `(λy. y) a`, the derived bracket names `a`. -/
theorem bothBrackets_incoherent : SealedCode.Incoherent (@BothBrackets 0) := by
  refine ⟨instAll (.cquote 1 applyTemplate) (fun _ : Fin 1 => .cquote 0 identityCode),
    .cquote 0 (.app identityCode (.sym "a")), .cquote 0 (.sym "a"),
    .single (.asWritten applyTemplate (fun _ : Fin 1 => identityCode)), ?_,
    bothBrackets_cquote_irreducible _, bothBrackets_cquote_irreducible _, by decide⟩
  have derived := instAll_name (n := 0) applyTemplate (fun _ : Fin 1 => identityCode)
    (W := .sym "a") (.single (.beta _ _)) (.sym "a")
  exact Relation.ReflTransGen.mono (fun _ _ h => BothBrackets.step h) _ _ derived

/-- The derived bracket names `a`, never the redex. -/
theorem derivedBracket_names_normal_form :
    Steps (instAll (.cquote 1 applyTemplate : Term 0) (fun _ : Fin 1 => .cquote 0 identityCode))
      (.cquote 0 (.sym "a")) :=
  instAll_name applyTemplate (fun _ : Fin 1 => identityCode) (.single (.beta _ _)) (.sym "a")

theorem derivedBracket_not_asWritten :
    ¬ Steps (instAll (.cquote 1 applyTemplate : Term 0) (fun _ : Fin 1 => .cquote 0 identityCode))
      (.cquote 0 (.app identityCode (.sym "a"))) := by
  intro h
  have := name_unique h derivedBracket_names_normal_form
  cases this

end Mettapedia.TypeTheory.Calculi.ContextualCode
