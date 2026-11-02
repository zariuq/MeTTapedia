import Mettapedia.GSLT.Readers.Rho.Record
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# Reading the binders of an mrho process: locally nameless terms of Mettapedia's rho calculus

The reader's tree of a process keeps every variable as a token: the variable of a receive at its
binder position, every other occurrence under the `name_var` row. `MrhoSyntax.module` declares the
binding structure as data (`Scopes`): the variable `x` of `proc_recv` binds in its body `p`,
`name_var` is an occurrence, and `name_quote` seals (`scopeProfile_eq`, `scope_kids`). This file
reads that structure: `RProc.resolve` turns a process into a locally nameless term of Mettapedia's
authored rho calculus (`rhoCalc`: `PZero`, the `hashBag` collection, `POutput`, `PInput` over a
`lambda`, `PDrop`, `NQuote`), where an occurrence bound by the I-th enclosing receive is `.bvar I`,
counted outward to the innermost receive of that spelling and never across a quote, and an
occurrence no receive binds is the free name `.fvar x`. This is the reference's own rule
(`rho_elab_atom` in `rhocalc_syntax.c`: the innermost binder of the spelling; a literal quote clears
the binder stack).

Results:
* `resolve_wellSorted`: the term is well sorted for Mettapedia's rho presentation, with every free
  name a name, whatever the binder names;
* `resolve_safe`: it is safe in Mettapedia's quote-aware sense (`binderSafeAt "NQuote"`): no index
  points past its own binders or out of a quote;
* `resolve_closed`: a process with no free name is a term of the established closed process carrier
  (`RhoClosedTermWellSorted rhoProc`), on which Mettapedia's rho reduction is defined;
* controls: renaming a binder changes nothing; the inner of two receives of one spelling binds;
  a quote seals; a free name and a receive of the same spelling stay apart; the reference's
  capture-avoiding residual reads as expected.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Rho.Record

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.ConstructorCategory (rhoProc)
open Mettapedia.GSLT.Readers.Rho

/-! ## The binding structure the `.module` declares -/

inductive ScopeEntry where
  | binder (row var body : String)
  | occurrence (row var : String)
  | seal (row : String)
  deriving DecidableEq, Repr

def scopeEntry? : Pattern → Option ScopeEntry
  | .apply "Binder" [.apply row [], .apply x [], .apply body []] => some (.binder row x body)
  | .apply "Occurrence" [.apply row [], .apply x []] => some (.occurrence row x)
  | .apply "Seal" [.apply row []] => some (.seal row)
  | _ => none

/-- The reply of the `ReturnScopeProfile` message, decoded. -/
def scopeProfile? : Option (List ScopeEntry) := do
  match ← reply? "Scopes" "GetScopeProfile" with
  | .apply "ScopeProfile" entries => entries.mapM scopeEntry?
  | _ => none

theorem scopeProfile_eq :
    scopeProfile? = some [.binder "proc_recv" "x" "p", .occurrence "name_var" "x", .seal "name_quote"] := by
  decide +kernel

/-- The position, among a row's children in the reader's tree, of the child a parameter names. -/
def kidIndex (row param : String) : Option Nat := do
  let r ← grammar.terms.find? (·.label == row)
  let kids := r.syntaxPattern.filterMap fun item => match item with
    | .nonTerminal n => some n
    | _ => none
  kids.findIdx? (· == param)

/-- The declared structure, at the reader's tree positions: the binder of `proc_recv` is its child 1
and its body child 2; the variable of `name_var` is its child 0. `RProc.tree` puts them there. -/
theorem scope_kids :
    kidIndex "proc_recv" "x" = some 1 ∧ kidIndex "proc_recv" "p" = some 2 ∧
      kidIndex "name_var" "x" = some 0 := by
  decide +kernel

theorem recv_tree (m : RName) (x : String) (p : RProc) :
    (RProc.recv m x p).tree = .node "proc_recv" [m.tree, .leaf "var_tok" ("$" ++ x), p.tree] := by
  simp [RProc.tree]

/-! ## Resolution -/

/-- The position of the innermost binder of a spelling, innermost first. -/
def lookupIdx (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if y = x then some 0 else (lookupIdx x ys).map (· + 1)

theorem lookupIdx_lt (x : String) : ∀ (env : List String) (i : Nat), lookupIdx x env = some i → i < env.length
  | [], i, h => by simp [lookupIdx] at h
  | y :: ys, i, h => by
    simp only [lookupIdx] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · cases hx : lookupIdx x ys with
      | none => rw [hx] at h; simp at h
      | some j =>
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have := lookupIdx_lt x ys j hx
        simp; omega

mutual
  /-- A name: a quote resolves its process with no binder in scope (a quote seals); a variable is
  the index of its innermost binder, or a free name. -/
  def RName.resolve (env : List String) : RName → Pattern
    | .quote p => .apply "NQuote" [p.resolve []]
    | .var x => match lookupIdx x env with
      | some i => .bvar i
      | none => .fvar x
  /-- A process; a receive binds its variable in its body. -/
  def RProc.resolve (env : List String) : RProc → Pattern
    | .nil => .apply "PZero" []
    | .par ps => .collection .hashBag (ps.resolve env) none
    | .send m p => .apply "POutput" [m.resolve env, p.resolve env]
    | .recv m x p => .apply "PInput" [m.resolve env, .lambda none (p.resolve (x :: env))]
    | .drop m => .apply "PDrop" [m.resolve env]
  def RProcs.resolve (env : List String) : RProcs → List Pattern
    | .nil => []
    | .cons p ps => p.resolve env :: ps.resolve env
end

/-! ## Free names -/

mutual
  /-- Every free name of a name has the sort `Name` in the free context. -/
  def RName.namesIn (free : FreeSortContext) (env : List String) : RName → Prop
    | .quote p => p.namesIn free []
    | .var x => lookupIdx x env = none → free x = some "Name"
  def RProc.namesIn (free : FreeSortContext) (env : List String) : RProc → Prop
    | .nil => True
    | .par ps => ps.namesIn free env
    | .send m p => m.namesIn free env ∧ p.namesIn free env
    | .recv m x p => m.namesIn free env ∧ p.namesIn free (x :: env)
    | .drop m => m.namesIn free env
  def RProcs.namesIn (free : FreeSortContext) (env : List String) : RProcs → Prop
    | .nil => True
    | .cons p ps => p.namesIn free env ∧ ps.namesIn free env
end

/-- The free context in which every name is a `Name`. -/
def allNames : FreeSortContext := fun _ => some "Name"

mutual
  theorem RName.namesIn_allNames (env : List String) : ∀ (m : RName), m.namesIn allNames env
    | .quote p => by simp only [RName.namesIn]; exact RProc.namesIn_allNames [] p
    | .var x => by simp [RName.namesIn, allNames]
  theorem RProc.namesIn_allNames (env : List String) : ∀ (p : RProc), p.namesIn allNames env
    | .nil => by simp [RProc.namesIn]
    | .par ps => by simp only [RProc.namesIn]; exact RProcs.namesIn_allNames env ps
    | .send m p => ⟨RName.namesIn_allNames env m, RProc.namesIn_allNames env p⟩
    | .recv m x p => ⟨RName.namesIn_allNames env m, RProc.namesIn_allNames (x :: env) p⟩
    | .drop m => RName.namesIn_allNames env m
  theorem RProcs.namesIn_allNames (env : List String) : ∀ (ps : RProcs), ps.namesIn allNames env
    | .nil => by simp [RProcs.namesIn]
    | .cons p ps => ⟨RProc.namesIn_allNames env p, RProcs.namesIn_allNames env ps⟩
end

/-! ## The resolved term is well sorted and quote-safe -/

/-- The sorts of the bound indices: every binder binds a name. -/
def boundSorts (env : List String) (extra : List String) : List String :=
  env.map (fun _ => "Name") ++ extra

theorem boundSorts_get (env extra : List String) (i : Nat) (hi : i < env.length) :
    (boundSorts env extra)[i]? = some "Name" := by
  unfold boundSorts
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

mutual
  theorem RName.resolve_wellSorted (free : FreeSortContext) :
      ∀ (env extra : List String) (m : RName), m.namesIn free env →
        NameWellSorted rhoReflectivePresentation free (boundSorts env extra) (m.resolve env)
    | env, extra, .quote p, h => by
      simp only [RName.resolve]
      exact NameWellSorted.quote (by
        have := RProc.resolve_wellSorted free [] (boundSorts env extra) p h
        simpa [boundSorts] using this)
    | env, extra, .var x, h => by
      simp only [RName.resolve]
      cases hx : lookupIdx x env with
      | some i =>
        exact NameWellSorted.bvar (by
          rw [boundSorts_get env extra i (lookupIdx_lt x env i hx)]; rfl)
      | none => exact NameWellSorted.fvar (by rw [h hx]; rfl)
  theorem RProc.resolve_wellSorted (free : FreeSortContext) :
      ∀ (env extra : List String) (p : RProc), p.namesIn free env →
        ProcWellSorted rhoReflectivePresentation free (boundSorts env extra) (p.resolve env)
    | env, extra, .nil, _ => by
      simp only [RProc.resolve]
      exact ProcWellSorted.unit
    | env, extra, .par ps, h => by
      simp only [RProc.resolve]
      exact ProcWellSorted.parallel (RProcs.resolve_wellSorted free env extra ps h)
    | env, extra, .send m p, h => by
      simp only [RProc.resolve]
      exact ProcWellSorted.output (RName.resolve_wellSorted free env extra m h.1)
        (RProc.resolve_wellSorted free env extra p h.2)
    | env, extra, .recv m x p, h => by
      simp only [RProc.resolve]
      have hb := RProc.resolve_wellSorted free (x :: env) extra p h.2
      exact ProcWellSorted.input (RName.resolve_wellSorted free env extra m h.1)
        (by have hn : rhoReflectivePresentation.nameSort = "Name" := rfl
            rw [hn]; simpa [boundSorts] using hb)
    | env, extra, .drop m, h => by
      simp only [RProc.resolve]
      exact ProcWellSorted.drop (RName.resolve_wellSorted free env extra m h)
  theorem RProcs.resolve_wellSorted (free : FreeSortContext) :
      ∀ (env extra : List String) (ps : RProcs), ps.namesIn free env →
        ProcListWellSorted rhoReflectivePresentation free (boundSorts env extra) (ps.resolve env)
    | env, extra, .nil, _ => by
      simp only [RProcs.resolve]
      exact ProcListWellSorted.nil
    | env, extra, .cons p ps, h => by
      simp only [RProcs.resolve]
      exact ProcListWellSorted.cons (RProc.resolve_wellSorted free env extra p h.1)
        (RProcs.resolve_wellSorted free env extra ps h.2)
end

mutual
  theorem RName.resolve_safe : ∀ (env : List String) (m : RName),
      binderSafeAt "NQuote" env.length (m.resolve env) = true
    | env, .quote p => by
      simp only [RName.resolve, binderSafeAt, beq_self_eq_true, if_true]
      exact RProc.resolve_safe [] p
    | env, .var x => by
      simp only [RName.resolve]
      cases hx : lookupIdx x env with
      | some i => simp [binderSafeAt, lookupIdx_lt x env i hx]
      | none => simp [binderSafeAt]
  theorem RProc.resolve_safe : ∀ (env : List String) (p : RProc),
      binderSafeAt "NQuote" env.length (p.resolve env) = true
    | env, .nil => by simp [RProc.resolve, binderSafeAt, binderSafeListAt]
    | env, .par ps => by
      simp only [RProc.resolve, binderSafeAt]
      exact RProcs.resolve_safe env ps
    | env, .send m p => by
      simp only [RProc.resolve, binderSafeAt, binderSafeListAt, Bool.and_eq_true]
      exact ⟨RName.resolve_safe env m, RProc.resolve_safe env p, trivial⟩
    | env, .recv m x p => by
      simp only [RProc.resolve, binderSafeAt, binderSafeListAt, Bool.and_eq_true]
      refine ⟨RName.resolve_safe env m, ?_, trivial⟩
      have := RProc.resolve_safe (x :: env) p
      simpa using this
    | env, .drop m => by
      simp only [RProc.resolve, binderSafeAt]
      have hne : ("PDrop" == "NQuote") = false := by decide
      simp only [hne, Bool.false_eq_true, if_false, binderSafeListAt, Bool.and_true]
      exact RName.resolve_safe env m
  theorem RProcs.resolve_safe : ∀ (env : List String) (ps : RProcs),
      binderSafeListAt "NQuote" env.length (ps.resolve env) = true
    | env, .nil => by simp [RProcs.resolve, binderSafeListAt]
    | env, .cons p ps => by
      simp only [RProcs.resolve, binderSafeListAt, Bool.and_eq_true]
      exact ⟨RProc.resolve_safe env p, RProcs.resolve_safe env ps⟩
end

/-- A process read from the top, with every free name a name: its term is well sorted and
quote-safe, whatever its binders are called. -/
theorem resolve_wellSorted (p : RProc) :
    ProcWellSorted rhoReflectivePresentation allNames [] (p.resolve []) ∧
      binderSafeAt "NQuote" 0 (p.resolve []) = true :=
  ⟨by simpa [boundSorts] using RProc.resolve_wellSorted allNames [] [] p (RProc.namesIn_allNames [] p),
    by simpa using RProc.resolve_safe [] p⟩

/-- A process with no free name is a term of Mettapedia's established closed process carrier, on
which its rho reduction (`rhoRewriteSystem`, `rhoProcessRewrites`) is defined. -/
theorem resolve_closed (p : RProc) (hclosed : p.namesIn FreeSortContext.empty []) :
    RhoClosedTermWellSorted rhoProc (p.resolve []) :=
  (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨by simpa [boundSorts] using RProc.resolve_wellSorted FreeSortContext.empty [] [] p hclosed,
      by simpa using RProc.resolve_safe [] p⟩

/-! ## Controls -/

private def at0 : RName := .quote .nil

/-- Renaming a binder changes nothing: `for(x <- @0){*x}` and `for(y <- @0){*y}` are one term. -/
theorem control_alpha :
    (RProc.recv at0 "x" (.drop (.var "x"))).resolve [] = (RProc.recv at0 "y" (.drop (.var "y"))).resolve [] := by
  decide +kernel

/-- Two receives of one spelling: the inner one binds (`mrho_shadow_same_spelling.mrho`). -/
theorem control_shadow :
    (RProc.recv at0 "x" (.recv at0 "x" (.drop (.var "x")))).resolve [] =
      .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
        (.apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PDrop" [.bvar 0])])] := by
  decide +kernel

/-- A quote seals: in `for(x <- @0){@{*x}!(0)}` the `x` inside the quote is free
(`mrho_quote_seals_outer_binder.mrho`); the same `*x` outside a quote is bound. -/
theorem control_seal :
    (RProc.recv at0 "x" (.send (.quote (.drop (.var "x"))) .nil)).resolve [] =
        .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
          (.apply "POutput" [.apply "NQuote" [.apply "PDrop" [.fvar "x"]], .apply "PZero" []])] ∧
      (RProc.recv at0 "x" (.send (.var "x") .nil)).resolve [] =
        .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
          (.apply "POutput" [.bvar 0, .apply "PZero" []])] := by
  decide +kernel

/-- A free name and a receive of the same spelling stay apart: in `$x!(0) | for(x <- @0){*x}` the first
`$x` is free and the second bound (`mrho_free_name_same_spelling_binder.mrho`). -/
theorem control_free_and_bound :
    (RProc.par (.cons (.send (.var "x") .nil) (.cons (.recv at0 "x" (.drop (.var "x"))) .nil))).resolve [] =
      .collection .hashBag [.apply "POutput" [.fvar "x", .apply "PZero" []],
        .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PDrop" [.bvar 0])]] none := by
  decide +kernel

/-- The reference's residual of `capture_avoidance_alpha_h7.mrho`,
`(rho:recv (rho:quote rho:nil) $x_rho1 (rho:drop $x))`: its printer renamed the binder so that the free
`$x` is not captured, and the reading keeps them apart. -/
theorem control_capture_residual :
    (RProc.recv at0 "x_rho1" (.drop (.var "x"))).resolve [] =
      .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PDrop" [.fvar "x"])] := by
  decide +kernel

/-- Negative control: a quote seals, so a variable of an outer receive is no index inside the quote;
the unsealed reading is a different term. -/
theorem control_seal_differs :
    (RProc.recv at0 "x" (.send (.quote (.drop (.var "x"))) .nil)).resolve [] ≠
      .apply "PInput" [.apply "NQuote" [.apply "PZero" []], .lambda none
        (.apply "POutput" [.apply "NQuote" [.apply "PDrop" [.bvar 0]], .apply "PZero" []])] := by
  decide +kernel

/-- The reference's first example is a closed process of Mettapedia's rho calculus. -/
theorem coreComm_closed : RhoClosedTermWellSorted rhoProc (coreComm.resolve []) :=
  resolve_closed coreComm (by simp [coreComm, RProc.namesIn, RProcs.namesIn, RName.namesIn, lookupIdx])

end Mettapedia.GSLT.Readers.Rho.Record
