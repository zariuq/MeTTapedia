import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ByValue

/-!
# By-value function variables use the common native frontier controller

The owner's scoping and arrow lemmas discharge every source-side condition
of the whole-frontier correspondence. The target is the same finite native
catalogue controller used for plain programs, now with both sequencing rules.
The scope is the owner's undeclared by-value value-text class; run marks,
mutable spaces and value-type check frames remain outside these hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.FunctionVariables Hosting

variable (N : Nodes MSig [] ()) (τ : Typing) (supply : Nat → MClosed)
  (spaces : MClosed → Multiset (Row mkeys [] ())) (π : Params)
  (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram) (noDecls : P.decls = [])
  (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
  (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
  (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))

def byValueCorrespondence :
    OperationalCorrespondence (source (D := τ.discipline) (elaborateByValue π P) supply)
      (target (D := τ.discipline) N (elaborateByValue π P)) := by
  obtain ⟨scopedQuery, distinct, arrow⟩ :=
    elabQueryH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls t names valued
  exact correspondence (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t))
    (elaborateH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls texts present)
    scopedQuery distinct arrow

include byValue noDecls texts present names valued

theorem byValue_source_run {C : Config mkeys [] () MTy}
    (runs : Runs τ.discipline (elaborateByValue π P) supply
      (Config.initial spaces (elabQueryByValue π P (.text t))) C) :
    ∃ next, (target (D := τ.discipline) N (elaborateByValue π P)).MultiStep
        (initialState (D := τ.discipline) N (elaborateByValue π P) (elabQueryByValue π P (.text t))) next ∧
      Representation (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t)) C next ∧
      C.answers (D := τ.discipline) = answers N next := by
  obtain ⟨scopedQuery, distinct, arrow⟩ :=
    elabQueryH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls t names valued
  exact source_run (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t))
    (elaborateH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls texts present)
    scopedQuery distinct arrow runs

theorem byValue_target_run {next : State MSig}
    (runs : (target (D := τ.discipline) N (elaborateByValue π P)).MultiStep
      (initialState (D := τ.discipline) N (elaborateByValue π P) (elabQueryByValue π P (.text t))) next) :
    ∃ C, Runs τ.discipline (elaborateByValue π P) supply
        (Config.initial spaces (elabQueryByValue π P (.text t))) C ∧
      Representation (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t)) C next ∧
      C.answers (D := τ.discipline) = answers N next := by
  obtain ⟨scopedQuery, distinct, arrow⟩ :=
    elabQueryH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls t names valued
  exact target_run (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t))
    (elaborateH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls texts present)
    scopedQuery distinct arrow runs

theorem byValue_prefixes_iff (post : Multiset (Set MClosed) → Prop) :
    (∃ C, Runs τ.discipline (elaborateByValue π P) supply
        (Config.initial spaces (elabQueryByValue π P (.text t))) C ∧ post (C.answers (D := τ.discipline))) ↔
      ∃ next, (target (D := τ.discipline) N (elaborateByValue π P)).MultiStep
        (initialState (D := τ.discipline) N (elaborateByValue π P) (elabQueryByValue π P (.text t))) next ∧
        post (answers N next) := by
  obtain ⟨scopedQuery, distinct, arrow⟩ :=
    elabQueryH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls t names valued
  exact prefixes_iff (D := τ.discipline) N (elaborateByValue π P) supply spaces (elabQueryByValue π P (.text t))
    (elaborateH_asked .byValue π byValue_faithful byValue_arrows byValue P noDecls texts present)
    scopedQuery distinct arrow post

omit byValue noDecls texts present names valued in
open ExampleTwice in
/-- The actual nested function-variable program reaches its complete two-successor value. -/
theorem twice_native : ∃ next,
    (target (D := D) N program).MultiStep (initialState (D := D) N program query) next ∧
      answers N next = {{ctuple [csym "S", ctuple [csym "S", csym "Z"]]}} := by
  obtain ⟨C, runs, _, answer⟩ := ExampleTwice.runs_answers
  obtain ⟨next, path, _, same⟩ := source_run (D := D) N program ExampleTwice.supply sp query
    twice_asked query_scoped query_distinct query_arrows runs
  exact ⟨next, path, same.symm.trans answer⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
