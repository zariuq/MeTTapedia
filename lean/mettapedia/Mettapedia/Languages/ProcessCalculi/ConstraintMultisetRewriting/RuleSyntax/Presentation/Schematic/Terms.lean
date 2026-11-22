import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Language
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.OSLF.MeTTaIL.DecimalNames

/-!
# Rows with unknowns, as first-order terms and as patterns of the presented language

The rows of a rule with unknowns are first-order terms of the tree's logic-programming term type
(`Mettapedia.Logic.LP.Term`) over the signature of rows (`rowSig`): the constants `sym k` and `name n`,
the binary former `app` and the unary former `code`, and unknowns numbered by `ℕ`. The step is then the
step of `RuleSyntax` at one frame over the existing first-order action (`FirstOrder.action rowSig`, equal
means identical), as in `RuleSyntax.Examples`.

* **Ground rows** (`toTerm`): every row of the ground presentation is a term without unknowns.
* **The code of a term** (`termCode`): its row formers as constructors, and each unknown `x` as the
  metavariable `unknownName x`. On ground rows it is the ground code (`termCode_toTerm`). Unknown names,
  the names of the rests of reads (`readRestName`) and the rest `"rest"` are pairwise distinct.
* **Instances** (`inst`): a ground instantiation `θ : ℕ → Expr` of the unknowns sends a term to a row;
  as a substitution it is `lift θ` (`applyTerm_lift`). A substitution that sends a term to a ground row
  sends each of its unknowns to a ground row (`inst_groundPart`), and two substitutions that agree on a
  term agree on its unknowns (`agree_of_applyTerm_eq`).

## The framework's bindings read as an instantiation

The framework's matcher returns bindings: lists of metavariable names and patterns, read by `find?`.

* `mergeBindings_find`: a merge reads as the concatenation of its arguments;
  `merge_exists`: two binding lists that agree with one partial assignment merge, into a list with the
  same entries.
* `applyBindings_termCode_eq_rowCode`: **if bindings send the code of a term to a row, the instantiation
  they determine (`groundOf`) sends the term to that row**, and they bind every unknown of the term to the
  code of its value. Conversely `applyBindings_termCode_of_lookup`.
* `matchRel_termCode`: **the code of a term matches the code of each of its instances**, with bindings
  that are exactly the instantiation on the term's unknowns: the framework's matcher handles an unknown
  that occurs twice by its agreement check (`mergeBindings`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open NamesOnTheStep (Expr)

/-! ## The signature of rows -/

/-- The constants of rows. -/
inductive RowConstant where
  | sym (k : ℕ)
  | name (n : ℕ)
  deriving DecidableEq

/-- The formers of rows. -/
inductive RowFunction where
  | app
  | code
  deriving DecidableEq

/-- The arity of a former. -/
def rowArity : RowFunction → ℕ
  | .app => 2
  | .code => 1

/-- **The signature of rows**: constants, formers, and unknowns numbered by `ℕ`. -/
abbrev rowSig : LPSignature where
  constants := RowConstant
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := RowFunction
  functionArity := rowArity

/-- **Rows with unknowns**: first-order terms over the signature of rows. -/
abbrev Tm := Term rowSig

/-- The first argument of an application. -/
def head : Fin (rowArity .app) := ⟨0, by decide⟩

/-- The second argument of an application. -/
def tail : Fin (rowArity .app) := ⟨1, by decide⟩

/-- The argument of a code. -/
def body : Fin (rowArity .code) := ⟨0, by decide⟩

theorem fin_app (i : Fin (rowArity .app)) : i = head ∨ i = tail := by
  rcases i with ⟨_ | _ | n, bound⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd bound (by simp [rowArity])

theorem fin_code (i : Fin (rowArity .code)) : i = body := by
  rcases i with ⟨_ | n, bound⟩
  · rfl
  · exact absurd bound (by simp [rowArity])

/-- Two arguments of an application, as a function of the position. -/
def args2 (f a : Tm) : Fin (rowArity .app) → Tm := ![f, a]

/-- One argument of a code. -/
def args1 (e : Tm) : Fin (rowArity .code) → Tm := ![e]

/-! ## Unknowns of terms -/

theorem mem_vars_var {x y : ℕ} : x ∈ (Term.var y : Tm).freeVars ↔ x = y := Term.mem_freeVars_var

theorem not_mem_vars_const {c : RowConstant} {x : ℕ} : x ∉ (Term.const c : Tm).freeVars :=
  Term.not_mem_freeVars_const

theorem mem_vars_app {f : RowFunction} {ts : Fin (rowArity f) → Tm} {x : ℕ} :
    x ∈ (Term.app f ts : Tm).freeVars ↔ ∃ i, x ∈ (ts i).freeVars :=
  Term.mem_freeVars_app

theorem mem_vars_head {ts : Fin (rowArity .app) → Tm} {x : ℕ} (member : x ∈ (ts head).freeVars) :
    x ∈ (Term.app RowFunction.app ts : Tm).freeVars :=
  mem_vars_app.mpr ⟨head, member⟩

theorem mem_vars_tail {ts : Fin (rowArity .app) → Tm} {x : ℕ} (member : x ∈ (ts tail).freeVars) :
    x ∈ (Term.app RowFunction.app ts : Tm).freeVars :=
  mem_vars_app.mpr ⟨tail, member⟩

theorem mem_vars_body {ts : Fin (rowArity .code) → Tm} {x : ℕ} (member : x ∈ (ts body).freeVars) :
    x ∈ (Term.app RowFunction.code ts : Tm).freeVars :=
  mem_vars_app.mpr ⟨body, member⟩

theorem mem_vars_app_cases {ts : Fin (rowArity .app) → Tm} {x : ℕ}
    (member : x ∈ (Term.app RowFunction.app ts : Tm).freeVars) :
    x ∈ (ts head).freeVars ∨ x ∈ (ts tail).freeVars := by
  obtain ⟨i, inside⟩ := mem_vars_app.mp member
  rcases fin_app i with rfl | rfl
  · exact Or.inl inside
  · exact Or.inr inside

theorem mem_vars_code_cases {ts : Fin (rowArity .code) → Tm} {x : ℕ}
    (member : x ∈ (Term.app RowFunction.code ts : Tm).freeVars) : x ∈ (ts body).freeVars := by
  obtain ⟨i, inside⟩ := mem_vars_app.mp member
  rwa [fin_code i] at inside

/-! ## Ground rows -/

/-- **A ground row as a term**. -/
def toTerm : Expr → Tm
  | .sym k => .const (.sym k)
  | .app f a => .app .app (args2 (toTerm f) (toTerm a))
  | .name n => .const (.name n)
  | .code e => .app .code (args1 (toTerm e))

theorem app_inj {ts us : Fin (rowArity .app) → Tm}
    (same : (Term.app RowFunction.app ts : Tm) = Term.app RowFunction.app us) : ts = us :=
  eq_of_heq (Term.app.inj same).2

theorem code_inj {ts us : Fin (rowArity .code) → Tm}
    (same : (Term.app RowFunction.code ts : Tm) = Term.app RowFunction.code us) : ts = us :=
  eq_of_heq (Term.app.inj same).2

theorem toTerm_injective : Function.Injective toTerm := by
  intro first
  induction first with
  | sym k =>
      intro second same
      cases second with
      | sym _ => exact congrArg Expr.sym (RowConstant.sym.inj (Term.const.inj same))
      | app _ _ => cases same
      | name _ => cases (Term.const.inj same)
      | code _ => cases same
  | app f a ihf iha =>
      intro second same
      cases second with
      | sym _ => cases same
      | app g b =>
          have args := app_inj same
          rw [ihf (congrFun args head), iha (congrFun args tail)]
      | name _ => cases same
      | code _ => cases (Term.app.inj same).1
  | name n =>
      intro second same
      cases second with
      | sym _ => cases (Term.const.inj same)
      | app _ _ => cases same
      | name _ => exact congrArg Expr.name (RowConstant.name.inj (Term.const.inj same))
      | code _ => cases same
  | code e ih =>
      intro second same
      cases second with
      | sym _ => cases same
      | app _ _ => cases (Term.app.inj same).1
      | name _ => cases same
      | code g => rw [ih (congrFun (code_inj same) body)]

/-- A ground row is fixed by every substitution. -/
theorem applyTerm_toTerm (τ : Subst rowSig) : ∀ e : Expr, τ.applyTerm (toTerm e) = toTerm e
  | .sym _ => rfl
  | .app f a => by
      rw [toTerm, Subst.applyTerm_app]
      refine congrArg (Term.app (σ := rowSig) RowFunction.app) (funext fun i => ?_)
      rcases fin_app i with rfl | rfl
      · exact applyTerm_toTerm τ f
      · exact applyTerm_toTerm τ a
  | .name _ => rfl
  | .code e => by
      rw [toTerm, Subst.applyTerm_app]
      refine congrArg (Term.app (σ := rowSig) RowFunction.code) (funext fun i => ?_)
      rw [fin_code i]
      exact applyTerm_toTerm τ e

/-- A ground row has no unknowns. -/
theorem vars_toTerm : ∀ (e : Expr) (x : ℕ), x ∉ (toTerm e).freeVars
  | .sym _, _, member => not_mem_vars_const member
  | .app f a, x, member => by
      rcases mem_vars_app_cases member with inside | inside
      · exact vars_toTerm f x inside
      · exact vars_toTerm a x inside
  | .name _, _, member => not_mem_vars_const member
  | .code e, x, member => vars_toTerm e x (mem_vars_code_cases member)

/-! ## Names -/

/-- **The metavariable of an unknown.** -/
def unknownName (x : ℕ) : String := "x" ++ toString x

/-- The metavariable of the rest of the `j`-th read. -/
def readRestName (j : ℕ) : String := "q" ++ toString j

theorem unknownName_injective : Function.Injective unknownName :=
  fun _ _ same => Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_injective "x" same

theorem readRestName_injective : Function.Injective readRestName :=
  fun _ _ same => Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_injective "q" same

theorem unknownName_ne_rest (x : ℕ) : unknownName x ≠ "rest" :=
  Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_ne_literal "x" "rest" (toString x) fun tail => by
    have left : "x".toList = ['x'] := by decide
    have right : "rest".toList = ['r', 'e', 's', 't'] := by decide
    rw [left, right]
    simp

theorem readRestName_ne_rest (j : ℕ) : readRestName j ≠ "rest" :=
  Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_ne_literal "q" "rest" (toString j) fun tail => by
    have left : "q".toList = ['q'] := by decide
    have right : "rest".toList = ['r', 'e', 's', 't'] := by decide
    rw [left, right]
    simp

theorem unknownName_ne_readRestName (x j : ℕ) : unknownName x ≠ readRestName j :=
  Mettapedia.OSLF.MeTTaIL.DecimalNames.literal_ne (leftChars := ['x']) (rightChars := ['q'])
    (by decide) (by decide) (fun _ _ same => by simp at same) _ _

/-! ## The code of a term -/

/-- **The code of a term**: its formers as constructors, each unknown as its metavariable. -/
def termCode : Tm → Pattern
  | .var x => .fvar (unknownName x)
  | .const (.sym k) => .apply "Sym" [Pattern.unary "Zero" "Succ" k]
  | .const (.name n) => .apply "Name" [Pattern.unary "Zero" "Succ" n]
  | .app .app ts => .apply "App" [termCode (ts head), termCode (ts tail)]
  | .app .code ts => .apply "Code" [termCode (ts body)]

/-- **On ground rows the code is the ground code.** -/
theorem termCode_toTerm : ∀ e : Expr, termCode (toTerm e) = rowCode e
  | .sym _ => rfl
  | .app f a => by
      show Pattern.apply "App" [termCode (toTerm f), termCode (toTerm a)] = _
      rw [termCode_toTerm f, termCode_toTerm a]
      rfl
  | .name _ => rfl
  | .code e => by
      show Pattern.apply "Code" [termCode (toTerm e)] = _
      rw [termCode_toTerm e]
      rfl

theorem unaryCorrect : ∀ k : ℕ, isMatchCorrectAux (Pattern.unary "Zero" "Succ" k) = true
  | 0 => rfl
  | k + 1 => by simp [isMatchCorrectAux, isMatchCorrectListAux, unaryCorrect k]

/-- The code of a term is matched exactly by the framework's matcher. -/
theorem isMatchCorrect_termCode : ∀ p : Tm, Pattern.isMatchCorrect (termCode p) = true
  | .var _ => rfl
  | .const (.sym k) => by
      have numeral := unaryCorrect k
      simp [termCode, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux, numeral]
  | .const (.name n) => by
      have numeral := unaryCorrect n
      simp [termCode, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux, numeral]
  | .app .app ts => by
      have first := isMatchCorrect_termCode (ts head)
      have second := isMatchCorrect_termCode (ts tail)
      simp only [Pattern.isMatchCorrect] at first second
      simp [termCode, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux, first, second]
  | .app .code ts => by
      have only := isMatchCorrect_termCode (ts body)
      simp only [Pattern.isMatchCorrect] at only
      simp [termCode, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux, only]

/-! ## Instances -/

/-- **The instance of a term** at a ground instantiation of its unknowns. -/
def inst (θ : ℕ → Expr) : Tm → Expr
  | .var x => θ x
  | .const (.sym k) => .sym k
  | .const (.name n) => .name n
  | .app .app ts => .app (inst θ (ts head)) (inst θ (ts tail))
  | .app .code ts => .code (inst θ (ts body))

theorem inst_toTerm (θ : ℕ → Expr) : ∀ e : Expr, inst θ (toTerm e) = e
  | .sym _ => rfl
  | .app f a => by
      show Expr.app (inst θ (toTerm f)) (inst θ (toTerm a)) = _
      rw [inst_toTerm θ f, inst_toTerm θ a]
  | .name _ => rfl
  | .code e => by
      show Expr.code (inst θ (toTerm e)) = _
      rw [inst_toTerm θ e]

/-- A ground instantiation as a substitution. -/
def lift (θ : ℕ → Expr) : Subst rowSig := fun x => toTerm (θ x)

/-- **The instance is the substitution's result.** -/
theorem applyTerm_lift (θ : ℕ → Expr) : ∀ p : Tm, (lift θ).applyTerm p = toTerm (inst θ p)
  | .var _ => rfl
  | .const (.sym _) => rfl
  | .const (.name _) => rfl
  | .app .app ts => by
      rw [Subst.applyTerm_app]
      refine congrArg (Term.app (σ := rowSig) RowFunction.app) (funext fun i => ?_)
      rcases fin_app i with rfl | rfl
      · exact applyTerm_lift θ (ts head)
      · exact applyTerm_lift θ (ts tail)
  | .app .code ts => by
      rw [Subst.applyTerm_app]
      refine congrArg (Term.app (σ := rowSig) RowFunction.code) (funext fun i => ?_)
      rw [fin_code i]
      exact applyTerm_lift θ (ts body)

/-- Instances agree where the instantiations agree on the unknowns. -/
theorem inst_congr {θ θ' : ℕ → Expr} : ∀ (p : Tm), (∀ x ∈ p.freeVars, θ x = θ' x) → inst θ p = inst θ' p
  | .var x, agree => agree x (mem_vars_var.mpr rfl)
  | .const (.sym _), _ => rfl
  | .const (.name _), _ => rfl
  | .app .app ts, agree => by
      show Expr.app (inst θ (ts head)) (inst θ (ts tail)) = Expr.app (inst θ' (ts head)) (inst θ' (ts tail))
      rw [inst_congr (ts head) fun x member => agree x (mem_vars_head member),
        inst_congr (ts tail) fun x member => agree x (mem_vars_tail member)]
  | .app .code ts, agree => by
      show Expr.code (inst θ (ts body)) = Expr.code (inst θ' (ts body))
      rw [inst_congr (ts body) fun x member => agree x (mem_vars_body member)]

/-- Equal instances agree on the unknowns. -/
theorem agree_of_inst_eq {θ θ' : ℕ → Expr} : ∀ (p : Tm), inst θ p = inst θ' p → ∀ x ∈ p.freeVars, θ x = θ' x
  | .var x, same, y, member => by
      rw [mem_vars_var.mp member]
      exact same
  | .const _, _, _, member => absurd member not_mem_vars_const
  | .app .app ts, same, y, member => by
      have pair : Expr.app (inst θ (ts head)) (inst θ (ts tail)) =
          Expr.app (inst θ' (ts head)) (inst θ' (ts tail)) := same
      rcases mem_vars_app_cases member with inside | inside
      · exact agree_of_inst_eq (ts head) (Expr.app.inj pair).1 y inside
      · exact agree_of_inst_eq (ts tail) (Expr.app.inj pair).2 y inside
  | .app .code ts, same, y, member => by
      have one : Expr.code (inst θ (ts body)) = Expr.code (inst θ' (ts body)) := same
      exact agree_of_inst_eq (ts body) (Expr.code.inj one) y (mem_vars_code_cases member)

/-! ## Substitutions that ground a term -/

/-- The ground row a substitution assigns an unknown, when it assigns one. -/
noncomputable def groundPart (τ : Subst rowSig) (x : ℕ) : Expr := by
  classical
  exact if found : ∃ e, τ x = toTerm e then found.choose else .sym 0

theorem groundPart_spec {τ : Subst rowSig} {x : ℕ} {e : Expr} (assigned : τ x = toTerm e) :
    groundPart τ x = e := by
  classical
  have found : ∃ e, τ x = toTerm e := ⟨e, assigned⟩
  unfold groundPart
  rw [dif_pos found]
  exact toTerm_injective (found.choose_spec.symm.trans assigned)

/-- **A substitution that sends a term to a ground row sends each of its unknowns to a ground row**, and
the instance at those rows is the row. -/
theorem inst_groundPart (τ : Subst rowSig) : ∀ (p : Tm) (e : Expr), τ.applyTerm p = toTerm e →
    inst (groundPart τ) p = e ∧ ∀ x ∈ p.freeVars, τ x = toTerm (groundPart τ x)
  | .var x, e, assigned => by
      refine ⟨groundPart_spec assigned, fun y member => ?_⟩
      rw [mem_vars_var.mp member, groundPart_spec assigned]
      exact assigned
  | .const (.sym k), e, assigned => by
      refine ⟨?_, fun _ member => absurd member not_mem_vars_const⟩
      cases e with
      | sym j => exact congrArg Expr.sym (RowConstant.sym.inj (Term.const.inj assigned))
      | app _ _ => cases assigned
      | name _ => cases (Term.const.inj assigned)
      | code _ => cases assigned
  | .const (.name n), e, assigned => by
      refine ⟨?_, fun _ member => absurd member not_mem_vars_const⟩
      cases e with
      | sym _ => cases (Term.const.inj assigned)
      | app _ _ => cases assigned
      | name j => exact congrArg Expr.name (RowConstant.name.inj (Term.const.inj assigned))
      | code _ => cases assigned
  | .app .app ts, e, assigned => by
      rw [Subst.applyTerm_app] at assigned
      cases e with
      | sym _ => cases assigned
      | app f a =>
          have args := app_inj assigned
          obtain ⟨headInst, headVars⟩ := inst_groundPart τ (ts head) f (congrFun args head)
          obtain ⟨tailInst, tailVars⟩ := inst_groundPart τ (ts tail) a (congrFun args tail)
          refine ⟨by show Expr.app _ _ = _; rw [headInst, tailInst], fun x member => ?_⟩
          rcases mem_vars_app_cases member with inside | inside
          · exact headVars x inside
          · exact tailVars x inside
      | name _ => cases assigned
      | code _ => cases (Term.app.inj assigned).1
  | .app .code ts, e, assigned => by
      rw [Subst.applyTerm_app] at assigned
      cases e with
      | sym _ => cases assigned
      | app _ _ => cases (Term.app.inj assigned).1
      | name _ => cases assigned
      | code g =>
          obtain ⟨bodyInst, bodyVars⟩ := inst_groundPart τ (ts body) g (congrFun (code_inj assigned) body)
          exact ⟨by show Expr.code _ = _; rw [bodyInst], fun x member => bodyVars x (mem_vars_code_cases member)⟩

/-- **Two substitutions that agree on a term agree on its unknowns.** -/
theorem agree_of_applyTerm_eq {τ τ' : Subst rowSig} : ∀ (p : Tm), τ.applyTerm p = τ'.applyTerm p →
    ∀ x ∈ p.freeVars, τ x = τ' x
  | .var x, same, y, member => by
      rw [mem_vars_var.mp member]
      exact same
  | .const _, _, _, member => absurd member not_mem_vars_const
  | .app .app ts, same, y, member => by
      rw [Subst.applyTerm_app, Subst.applyTerm_app] at same
      have args := app_inj same
      rcases mem_vars_app_cases member with inside | inside
      · exact agree_of_applyTerm_eq (ts head) (congrFun args head) y inside
      · exact agree_of_applyTerm_eq (ts tail) (congrFun args tail) y inside
  | .app .code ts, same, y, member => by
      rw [Subst.applyTerm_app, Subst.applyTerm_app] at same
      exact agree_of_applyTerm_eq (ts body) (congrFun (code_inj same) body) y (mem_vars_code_cases member)

/-! ## Bindings -/

/-- A list of bindings agrees with a partial assignment of patterns to names. -/
def Agrees (f : String → Option Pattern) (b : Bindings) : Prop := ∀ e ∈ b, f e.1 = some e.2

theorem find?_spec {b : Bindings} {n : String} {e : String × Pattern} (found : b.find? (·.1 == n) = some e) :
    e.1 = n ∧ e ∈ b := by
  have holds := List.find?_some found
  exact ⟨beq_iff_eq.mp holds, List.mem_of_find?_eq_some found⟩

theorem mergeBindings_nil (b : Bindings) : mergeBindings b [] = some b := rfl

theorem mergeBindings_cons_none {b : Bindings} {n : String} {v : Pattern} (rest : Bindings)
    (absent : b.find? (·.1 == n) = none) :
    mergeBindings b ((n, v) :: rest) = mergeBindings ((n, v) :: b) rest := by
  unfold mergeBindings
  rw [List.foldlM_cons]
  simp [absent]

theorem mergeBindings_cons_some {b : Bindings} {n m : String} {v w : Pattern} (rest : Bindings)
    (found : b.find? (·.1 == n) = some (m, w)) (same : w = v) :
    mergeBindings b ((n, v) :: rest) = mergeBindings b rest := by
  subst same
  unfold mergeBindings
  rw [List.foldlM_cons]
  simp [found]

theorem mergeBindings_cons_clash {b : Bindings} {n m : String} {v w : Pattern} (rest : Bindings)
    (found : b.find? (·.1 == n) = some (m, w)) (different : w ≠ v) :
    mergeBindings b ((n, v) :: rest) = none := by
  unfold mergeBindings
  rw [List.foldlM_cons]
  simp [found, beq_iff_eq, different]

/-- **A merge reads as the concatenation of its arguments.** -/
theorem mergeBindings_find : ∀ {b2 b1 b : Bindings}, mergeBindings b1 b2 = some b →
    ∀ n, b.find? (·.1 == n) = (b1 ++ b2).find? (·.1 == n)
  | [], b1, b, merged, n => by
      rw [mergeBindings_nil] at merged
      cases merged
      rw [List.append_nil]
  | (m, v) :: rest, b1, b, merged, n => by
      cases found : b1.find? (·.1 == m) with
      | none =>
          rw [mergeBindings_cons_none rest found] at merged
          rw [mergeBindings_find merged n]
          by_cases same : m = n
          · subst same
            simp [List.find?_append, found]
          · have other : (m == n) = false := beq_eq_false_iff_ne.mpr same
            simp [List.find?_append, other]
      | some entry =>
          obtain ⟨name, w⟩ := entry
          by_cases agree : w = v
          · rw [mergeBindings_cons_some rest found agree] at merged
            rw [mergeBindings_find merged n]
            by_cases same : m = n
            · subst same
              simp [List.find?_append, found]
            · have other : (m == n) = false := beq_eq_false_iff_ne.mpr same
              simp [List.find?_append, other]
          · rw [mergeBindings_cons_clash rest found agree] at merged
            cases merged

/-- A merge extends both of its arguments. -/
theorem extends_left {b1 b2 b : Bindings} (merged : mergeBindings b1 b2 = some b) : BindingsExtends b1 b :=
  fun _ _ found => mergeBindings_subsumed_left merged found

theorem extends_right {b1 b2 b : Bindings} (merged : mergeBindings b1 b2 = some b) : BindingsExtends b2 b :=
  fun _ _ found => mergeBindings_subsumed_right merged found

theorem extends_refl (b : Bindings) : BindingsExtends b b := fun _ _ found => found

theorem extends_trans {b1 b2 b3 : Bindings} (first : BindingsExtends b1 b2) (second : BindingsExtends b2 b3) :
    BindingsExtends b1 b3 :=
  fun x v found => second x v (first x v found)

/-- **Two binding lists that agree with one partial assignment merge**, into a list of the same entries. -/
theorem merge_exists (f : String → Option Pattern) : ∀ (b2 b1 : Bindings), Agrees f b1 → Agrees f b2 →
    ∃ b, mergeBindings b1 b2 = some b ∧ Agrees f b ∧ (∀ e ∈ b, e ∈ b1 ∨ e ∈ b2) ∧ ∀ e ∈ b1 ++ b2, e ∈ b
  | [], b1, agrees1, _ => ⟨b1, rfl, agrees1, fun e member => Or.inl member,
      fun e member => by rwa [List.append_nil] at member⟩
  | (m, v) :: rest, b1, agrees1, agrees2 => by
      have headAgrees : f m = some v := agrees2 (m, v) List.mem_cons_self
      have restAgrees : Agrees f rest := fun e member => agrees2 e (List.mem_cons_of_mem _ member)
      cases found : b1.find? (·.1 == m) with
      | none =>
          have consAgrees : Agrees f ((m, v) :: b1) := by
            intro e member
            rcases List.mem_cons.mp member with rfl | member
            · exact headAgrees
            · exact agrees1 e member
          obtain ⟨b, merged, agrees, sub, super⟩ := merge_exists f rest ((m, v) :: b1) consAgrees restAgrees
          refine ⟨b, by rw [mergeBindings_cons_none rest found]; exact merged, agrees, ?_, ?_⟩
          · intro e member
            rcases sub e member with inside | inside
            · rcases List.mem_cons.mp inside with rfl | inside
              · exact Or.inr List.mem_cons_self
              · exact Or.inl inside
            · exact Or.inr (List.mem_cons_of_mem _ inside)
          · intro e member
            rcases List.mem_append.mp member with inside | inside
            · exact super e (List.mem_append_left _ (List.mem_cons_of_mem _ inside))
            · rcases List.mem_cons.mp inside with rfl | inside
              · exact super _ (List.mem_append_left _ List.mem_cons_self)
              · exact super e (List.mem_append_right _ inside)
      | some entry =>
          obtain ⟨name, w⟩ := entry
          obtain ⟨named, present⟩ := find?_spec found
          have known := agrees1 _ present
          have agree : w = v := by
            have named' : name = m := named
            rw [named'] at known
            exact Option.some.inj (known.symm.trans headAgrees)
          obtain ⟨b, merged, agrees, sub, super⟩ := merge_exists f rest b1 agrees1 restAgrees
          refine ⟨b, by rw [mergeBindings_cons_some rest found agree]; exact merged, agrees, ?_, ?_⟩
          · intro e member
            rcases sub e member with inside | inside
            · exact Or.inl inside
            · exact Or.inr (List.mem_cons_of_mem _ inside)
          · intro e member
            rcases List.mem_append.mp member with inside | inside
            · exact super e (List.mem_append_left _ inside)
            · rcases List.mem_cons.mp inside with rfl | inside
              · have named' : name = m := named
                rw [← named', ← agree]
                exact super _ (List.mem_append_left _ present)
              · exact super e (List.mem_append_right _ inside)

/-- In a list that agrees with an assignment, an entry is what `find?` reads. -/
theorem find?_of_agrees {f : String → Option Pattern} {b : Bindings} (agrees : Agrees f b) {n : String}
    {v : Pattern} (member : (n, v) ∈ b) : b.find? (·.1 == n) = some (n, v) := by
  cases found : b.find? (·.1 == n) with
  | none =>
      have absent := List.find?_eq_none.mp found (n, v) member
      simp at absent
  | some entry =>
      obtain ⟨name, w⟩ := entry
      obtain ⟨named, present⟩ := find?_spec found
      have named' : name = n := named
      have first := agrees _ present
      have second := agrees _ member
      rw [named'] at first
      have same : w = v := Option.some.inj (first.symm.trans second)
      rw [named', same]

/-! ## Instantiating a code -/

theorem applyBindings_fvar_some {b : Bindings} {n m : String} {v : Pattern}
    (found : b.find? (·.1 == n) = some (m, v)) : applyBindings b (.fvar n) = v := by
  simp [applyBindings, found]

theorem applyBindings_fvar_none {b : Bindings} {n : String} (absent : b.find? (·.1 == n) = none) :
    applyBindings b (.fvar n) = .fvar n := by
  simp [applyBindings, absent]

theorem applyBindings_app (b : Bindings) (ts : Fin (rowArity .app) → Tm) :
    applyBindings b (termCode (.app .app ts)) =
      .apply "App" [applyBindings b (termCode (ts head)), applyBindings b (termCode (ts tail))] := by
  simp [termCode, applyBindings]

theorem applyBindings_code (b : Bindings) (ts : Fin (rowArity .code) → Tm) :
    applyBindings b (termCode (.app .code ts)) = .apply "Code" [applyBindings b (termCode (ts body))] := by
  simp [termCode, applyBindings]

/-- The ground row bindings assign an unknown, when they assign a row. -/
noncomputable def groundOf (b : Bindings) (x : ℕ) : Expr := by
  classical
  exact if found : ∃ e, b.find? (·.1 == unknownName x) = some (unknownName x, rowCode e) then found.choose
    else .sym 0

theorem groundOf_spec {b : Bindings} {x : ℕ} {e : Expr}
    (found : b.find? (·.1 == unknownName x) = some (unknownName x, rowCode e)) : groundOf b x = e := by
  classical
  have exists' : ∃ e, b.find? (·.1 == unknownName x) = some (unknownName x, rowCode e) := ⟨e, found⟩
  unfold groundOf
  rw [dif_pos exists']
  have same := exists'.choose_spec.symm.trans found
  exact rowCode_injective (Prod.ext_iff.mp (Option.some.inj same)).2

/-- **If bindings send the code of a term to a row, the instantiation they determine sends the term to
that row**, and they bind every unknown of the term to the code of its value. -/
theorem applyBindings_termCode_eq_rowCode (b : Bindings) : ∀ (p : Tm) (e : Expr),
    applyBindings b (termCode p) = rowCode e →
      inst (groundOf b) p = e ∧ ∀ x ∈ p.freeVars,
        b.find? (·.1 == unknownName x) = some (unknownName x, rowCode (groundOf b x))
  | .var x, e, instantiated => by
      have code : termCode (.var x) = .fvar (unknownName x) := rfl
      rw [code] at instantiated
      cases found : b.find? (·.1 == unknownName x) with
      | none =>
          rw [applyBindings_fvar_none found] at instantiated
          cases e <;> cases instantiated
      | some entry =>
          obtain ⟨name, v⟩ := entry
          rw [applyBindings_fvar_some found] at instantiated
          obtain ⟨named, -⟩ := find?_spec found
          have named' : name = unknownName x := named
          rw [named', instantiated] at found
          have spec := groundOf_spec found
          refine ⟨spec, fun y member => ?_⟩
          rw [mem_vars_var.mp member, spec]
          exact found
  | .const (.sym k), e, instantiated => by
      refine ⟨?_, fun _ member => absurd member not_mem_vars_const⟩
      have fixed : applyBindings b (termCode (.const (.sym k))) = rowCode (.sym k) :=
        applyBindings_rowCode b (.sym k)
      exact rowCode_injective (fixed.symm.trans instantiated)
  | .const (.name n), e, instantiated => by
      refine ⟨?_, fun _ member => absurd member not_mem_vars_const⟩
      have fixed : applyBindings b (termCode (.const (.name n))) = rowCode (.name n) :=
        applyBindings_rowCode b (.name n)
      exact rowCode_injective (fixed.symm.trans instantiated)
  | .app .app ts, e, instantiated => by
      rw [applyBindings_app] at instantiated
      cases e with
      | app f a =>
          have parts := List.cons.inj (Pattern.apply.inj instantiated).2
          obtain ⟨headInst, headVars⟩ := applyBindings_termCode_eq_rowCode b (ts head) f parts.1
          obtain ⟨tailInst, tailVars⟩ := applyBindings_termCode_eq_rowCode b (ts tail) a
            (List.cons.inj parts.2).1
          refine ⟨by show Expr.app _ _ = _; rw [headInst, tailInst], fun x member => ?_⟩
          rcases mem_vars_app_cases member with inside | inside
          · exact headVars x inside
          · exact tailVars x inside
      | sym _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)
      | name _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)
      | code _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)
  | .app .code ts, e, instantiated => by
      rw [applyBindings_code] at instantiated
      cases e with
      | code g =>
          obtain ⟨bodyInst, bodyVars⟩ := applyBindings_termCode_eq_rowCode b (ts body) g
            (List.cons.inj (Pattern.apply.inj instantiated).2).1
          exact ⟨by show Expr.code _ = _; rw [bodyInst], fun x member => bodyVars x (mem_vars_code_cases member)⟩
      | sym _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)
      | name _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)
      | app _ _ => exact absurd (Pattern.apply.inj instantiated).1 (by decide)

/-- **Conversely, bindings that send every unknown of a term to the code of its value send the code of the
term to the code of its instance.** -/
theorem applyBindings_termCode_of_lookup (b : Bindings) (θ : ℕ → Expr) : ∀ p : Tm,
    (∀ x ∈ p.freeVars, b.find? (·.1 == unknownName x) = some (unknownName x, rowCode (θ x))) →
      applyBindings b (termCode p) = rowCode (inst θ p)
  | .var x, bound => applyBindings_fvar_some (bound x (mem_vars_var.mpr rfl))
  | .const (.sym k), _ => applyBindings_rowCode b (.sym k)
  | .const (.name n), _ => applyBindings_rowCode b (.name n)
  | .app .app ts, bound => by
      rw [applyBindings_app, applyBindings_termCode_of_lookup b θ (ts head)
          (fun x member => bound x (mem_vars_head member)),
        applyBindings_termCode_of_lookup b θ (ts tail)
          (fun x member => bound x (mem_vars_tail member))]
      rfl
  | .app .code ts, bound => by
      rw [applyBindings_code, applyBindings_termCode_of_lookup b θ (ts body)
          (fun x member => bound x (mem_vars_body member))]
      rfl

/-! ## The framework's matcher on codes -/

/-- The assignment of an instantiation: each unknown's name to the code of its value. -/
noncomputable def assignment (θ : ℕ → Expr) (n : String) : Option Pattern := by
  classical
  exact if found : ∃ x, unknownName x = n then some (rowCode (θ found.choose)) else none

theorem assignment_unknown (θ : ℕ → Expr) (x : ℕ) : assignment θ (unknownName x) = some (rowCode (θ x)) := by
  classical
  have found : ∃ y, unknownName y = unknownName x := ⟨x, rfl⟩
  unfold assignment
  rw [dif_pos found, unknownName_injective found.choose_spec]

/-- **The code of a term matches the code of each of its instances**, with bindings that are exactly the
instantiation on the term's unknowns. -/
theorem matchRel_termCode (θ : ℕ → Expr) : ∀ p : Tm, ∃ hb, MatchRel (termCode p) (rowCode (inst θ p)) hb ∧
    (∀ e ∈ hb, ∃ x ∈ p.freeVars, e = (unknownName x, rowCode (θ x))) ∧
    ∀ x ∈ p.freeVars, (unknownName x, rowCode (θ x)) ∈ hb
  | .var x => ⟨[(unknownName x, rowCode (θ x))], .fvar, fun e member => by
      rw [List.mem_singleton.mp member]
      exact ⟨x, mem_vars_var.mpr rfl, rfl⟩, fun y member => by
      rw [mem_vars_var.mp member]
      exact List.mem_singleton_self _⟩
  | .const (.sym k) => ⟨[], matchRel_self_rowCode (.sym k), fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member not_mem_vars_const⟩
  | .const (.name n) => ⟨[], matchRel_self_rowCode (.name n), fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member not_mem_vars_const⟩
  | .app .app ts => by
      obtain ⟨h0, match0, sub0, all0⟩ := matchRel_termCode θ (ts head)
      obtain ⟨h1, match1, sub1, all1⟩ := matchRel_termCode θ (ts tail)
      have agrees0 : Agrees (assignment θ) h0 := fun e member => by
        obtain ⟨x, -, rfl⟩ := sub0 e member
        exact assignment_unknown θ x
      have agrees1 : Agrees (assignment θ) h1 := fun e member => by
        obtain ⟨x, -, rfl⟩ := sub1 e member
        exact assignment_unknown θ x
      obtain ⟨b, merged, -, sub, super⟩ := merge_exists (assignment θ) h1 h0 agrees0 agrees1
      refine ⟨b, ?_, ?_, ?_⟩
      · show MatchRel (.apply "App" [termCode (ts head), termCode (ts tail)])
          (.apply "App" [rowCode (inst θ (ts head)), rowCode (inst θ (ts tail))]) b
        exact .apply (.cons match0 (.cons match1 .nil (mergeBindings_nil h1)) merged) rfl
      · intro e member
        rcases sub e member with inside | inside
        · obtain ⟨x, vars, rfl⟩ := sub0 e inside
          exact ⟨x, mem_vars_head vars, rfl⟩
        · obtain ⟨x, vars, rfl⟩ := sub1 e inside
          exact ⟨x, mem_vars_tail vars, rfl⟩
      · intro x member
        rcases mem_vars_app_cases member with inside | inside
        · exact super _ (List.mem_append_left _ (all0 x inside))
        · exact super _ (List.mem_append_right _ (all1 x inside))
  | .app .code ts => by
      obtain ⟨h0, match0, sub0, all0⟩ := matchRel_termCode θ (ts body)
      refine ⟨h0, ?_, fun e member => ?_, fun x member => all0 x (mem_vars_code_cases member)⟩
      · show MatchRel (.apply "Code" [termCode (ts body)]) (.apply "Code" [rowCode (inst θ (ts body))]) h0
        exact .apply (.cons match0 .nil (mergeBindings_nil h0)) rfl
      · obtain ⟨x, vars, rfl⟩ := sub0 e member
        exact ⟨x, mem_vars_body vars, rfl⟩

#print axioms toTerm_injective
#print axioms applyTerm_toTerm
#print axioms termCode_toTerm
#print axioms isMatchCorrect_termCode
#print axioms applyTerm_lift
#print axioms inst_groundPart
#print axioms agree_of_applyTerm_eq
#print axioms mergeBindings_find
#print axioms merge_exists
#print axioms find?_of_agrees
#print axioms applyBindings_termCode_eq_rowCode
#print axioms applyBindings_termCode_of_lookup
#print axioms matchRel_termCode

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
