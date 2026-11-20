import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting

/-!
# A machine whose configurations are terms and whose steps are root rewrites is a positive program

A **term-rewriting machine** over rows is a finite list of rewrite schemas, pairs of a left and a right pattern
with unknowns; a configuration is one ground row, and a step rewrites the whole row: `RootStep`. Machines with a
control state, registers, stacks, a tape as two lists around a head, or an environment and a continuation are of
this kind when their transition table is finitely many such schemas.

* **The program** (`rootRules`): one rule per schema, which takes the left row and makes the right row
  (`rowRule`). When the unknowns of each right pattern occur in its left pattern, the rules are range-restricted
  and positive (`rootRules_fragment`): no read, tell, equation guard, none check, count check or query pattern.
* **One root rewrite is one rewrite of the one-row bag** (`rewrites_rootRules_iff`).
* **One root rewrite is one firing, and no other firing is admitted**, at every state that reads as the row
  (`firing_of_rootStep`, `rootStep_of_firing`).
* **As a correspondence** (`rootCorrespondence`): an `OperationalCorrespondence` from the machine
  (`rootSystem`) to the step of its program, the composite of `rootHosted` with `Machines.correspondence`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open Presentation.Schematic

universe uO

/-! ## Patterns and one-row rules -/

/-- **The unknowns of a pattern**, as a list. -/
def unknowns : Tm → List ℕ
  | .var x => [x]
  | .const _ => []
  | .app .app ts => unknowns (ts head) ++ unknowns (ts tail)
  | .app .code ts => unknowns (ts body)

theorem mem_unknowns : ∀ (t : Tm) {x : ℕ}, x ∈ Term.freeVars (σ := rowSig) t → x ∈ unknowns t
  | .var _, _, member => List.mem_singleton.mpr (mem_vars_var.mp member)
  | .const _, _, member => absurd member not_mem_vars_const
  | .app .app ts, _, member => by
      rcases mem_vars_app_cases member with inside | inside
      · exact List.mem_append_left _ (mem_unknowns (ts head) inside)
      · exact List.mem_append_right _ (mem_unknowns (ts tail) inside)
  | .app .code ts, _, member => mem_unknowns (ts body) (mem_vars_code_cases member)

theorem vars_of_mem_unknowns : ∀ (t : Tm) {x : ℕ}, x ∈ unknowns t → x ∈ Term.freeVars (σ := rowSig) t
  | .var _, _, member => mem_vars_var.mpr (List.mem_singleton.mp member)
  | .const _, _, member => absurd member List.not_mem_nil
  | .app .app ts, _, member => by
      rcases List.mem_append.mp member with inside | inside
      · exact mem_vars_head (vars_of_mem_unknowns (ts head) inside)
      · exact mem_vars_tail (vars_of_mem_unknowns (ts tail) inside)
  | .app .code ts, _, member => mem_vars_body (vars_of_mem_unknowns (ts body) member)

/-- **A rule that takes one row and makes one row.** -/
def rowRule (l r : Tm) : SRule := ⟨PUnit.unit, ⟨[l], [], [], [], [r]⟩, []⟩

/-- **A one-row rule whose made row has only unknowns of its taken row is range-restricted and positive.** -/
theorem rowRule_fragment {l r : Tm} (range : ∀ x ∈ unknowns r, x ∈ unknowns l) :
    RangeRestrictedPositive (rowRule l r) := by
  refine ⟨rfl, rfl, fun t inWritten x vars => ?_⟩
  have isMade : t = r := by simpa [written, rowRule] using inWritten
  rw [isMade] at vars
  exact ⟨l, List.mem_cons_self, vars_of_mem_unknowns l (range x (mem_unknowns r vars))⟩

/-! ## Root rewriting -/

/-- **One root rewrite of a ground row**: a schema of the list and an instantiation of its unknowns that send
the left pattern to the row and the right pattern to the result. -/
def RootStep (schemas : List (Tm × Tm)) (e e' : Expr) : Prop :=
  ∃ p ∈ schemas, ∃ θ : ℕ → Expr, inst θ p.1 = e ∧ inst θ p.2 = e'

/-- **The program of a list of schemas**: one one-row rule per schema. -/
def rootRules (schemas : List (Tm × Tm)) : List SRule := schemas.map fun p => rowRule p.1 p.2

/-- **The program of schemas whose right unknowns occur on the left is range-restricted and positive.** -/
theorem rootRules_fragment {schemas : List (Tm × Tm)}
    (closed : ∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1) :
    ∀ r ∈ rootRules schemas, RangeRestrictedPositive r := by
  intro r member
  obtain ⟨p, inside, rfl⟩ := List.mem_map.mp member
  exact rowRule_fragment (closed p inside)

/-- **One root rewrite is one rewrite of the one-row bag.** -/
theorem rewrites_rootRules_iff (schemas : List (Tm × Tm)) (e : Expr) (bag' : Multiset Expr) :
    Rewrites (rootRules schemas) {e} bag' ↔ ∃ e', RootStep schemas e e' ∧ bag' = {e'} := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, rfl⟩
    obtain ⟨p, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨matched, restEmpty⟩ := row_of_singleton split
    refine ⟨inst θ p.2, ⟨p, inside, θ, matched, rfl⟩, ?_⟩
    rw [restEmpty]
    exact add_zero _
  · rintro ⟨e', ⟨p, inside, θ, matched, made⟩, rfl⟩
    exact ⟨rowRule p.1 p.2, List.mem_map_of_mem inside, θ, 0,
      (add_zero _).trans (congrArg (fun a => ({a} : Multiset Expr)) matched),
      fun q member => absurd member List.not_mem_nil, fun a member => absurd member List.not_mem_nil,
      ((add_zero _).trans (congrArg (fun a => ({a} : Multiset Expr)) made)).symm⟩

section Step

variable {O : Type uO} [DecidableEq O] {schemas : List (Tm × Tm)}

/-- **A root rewrite is one admitted firing of the program**, at every state that reads as the row, and the
result reads as the rewritten row. -/
theorem firing_of_rootStep [Infinite O] (closed : ∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1)
    {s : SState O} {e e' : Expr} (reads : ReadsBag s {e}) (rooted : RootStep schemas e e') :
    ∃ (g : Firing O E {r | r ∈ rootRules schemas} s.frame)
      (admitted : (schematicStep O (rootRules schemas)).Admits (s := s) g),
      ReadsBag ((schematicStep O (rootRules schemas)).result g admitted) {e'} :=
  readsBag_forward (rootRules_fragment closed) reads
    ((rewrites_rootRules_iff schemas e _).mpr ⟨e', rooted, rfl⟩)

/-- **Every admitted firing of the program is a root rewrite**, at a state that reads as a row, and its
result reads as the rewritten row. -/
theorem rootStep_of_firing (closed : ∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1)
    {s : SState O} {e : Expr} (reads : ReadsBag s {e}) (g : Firing O E {r | r ∈ rootRules schemas} s.frame)
    (admitted : (schematicStep O (rootRules schemas)).Admits (s := s) g) :
    ∃ e', RootStep schemas e e' ∧
      ReadsBag ((schematicStep O (rootRules schemas)).result g admitted) {e'} := by
  obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward (rootRules_fragment closed) reads g admitted
  obtain ⟨e', rooted, rfl⟩ := (rewrites_rootRules_iff schemas e bag').mp rewrites
  exact ⟨e', rooted, reads'⟩

end Step

/-! ## The correspondence -/

/-- **A term-rewriting machine, as a system**: ground rows under root rewriting. -/
def rootSystem (schemas : List (Tm × Tm)) : GSLT := equalityGSLT Expr (RootStep schemas)

/-- A row is hosted by its one-row bag. -/
def RowBag (e : Expr) (bag : Multiset Expr) : Prop := bag = {e}

/-- **A term-rewriting machine and rewriting of one-row bags**: one root rewrite for one rewrite, both ways. -/
def rootHosted (schemas : List (Tm × Tm)) :
    OperationalCorrespondence (rootSystem schemas) (rewriting (rootRules schemas)) where
  related := RowBag
  readStep := by
    intro e bag bag' same stepped
    have isRow : bag = ({e} : Multiset Expr) := same
    subst isRow
    obtain ⟨e', rooted, sameBag⟩ := (rewrites_rootRules_iff schemas e bag').mp stepped
    exact Or.inr ⟨e', rooted, sameBag⟩
  forward := by
    intro e e' bag same stepped
    have isRow : bag = ({e} : Multiset Expr) := same
    subst isRow
    exact ⟨({e'} : Multiset Expr), (executionPath_nonempty_iff_multiStep (rewriting (rootRules schemas)) _ _).mpr
      (.step ((rewrites_rootRules_iff schemas e _).mpr ⟨e', stepped, rfl⟩) (.refl _)), rfl⟩

/-- **A term-rewriting machine and the step of its program**: one root rewrite for one firing, both ways,
related by reading a state as the one-row bag of the row. -/
def rootCorrespondence {O : Type uO} [DecidableEq O] [Infinite O] {schemas : List (Tm × Tm)}
    (closed : ∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1) :
    OperationalCorrespondence (rootSystem schemas) (stepSystem O (rootRules schemas)) :=
  (rootHosted schemas).comp (correspondence (rootRules_fragment closed))

#print axioms rowRule_fragment
#print axioms rootRules_fragment
#print axioms rewrites_rootRules_iff
#print axioms firing_of_rootStep
#print axioms rootStep_of_firing
#print axioms rootHosted
#print axioms rootCorrespondence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
