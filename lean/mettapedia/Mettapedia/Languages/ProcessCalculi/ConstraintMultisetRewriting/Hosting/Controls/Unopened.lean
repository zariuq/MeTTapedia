import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hosting

/-!
# The control for `unopened`, the one hypothesis of the first fragment's run theorems on the query

`runs_forward` and `runs_reflected` ask that the query's names be unopened: a query name at scope `[0]`
would be the first copy of an equation's own name. This control violates that hypothesis and only it.

The program `(= (f $y) (pair $y $z))` (its `$z` occurs only on the right) and the query `(f [0]$z)`,
whose one name is the copy at scope `0` of the equation's own `$z`: the program and the query are of
the first fragment, and only `unopened` fails (`opened`).

* The source copies the equation at scope `0`, so the copy's `$z` **is** the query's name: the only
  alternative a move of the start makes never reads `(pair one two)` (`source_never`).
* The step's equation schema opens its own fresh `$z`: its canonical firing at the start is admitted
  (`step_fires`), and its made row reads `(pair one two)` (`step_reads`).

So at a query that violates only `unopened`, a firing of the translated program reads what no source
move makes, and its result represents no alternative of any move of the start: the conclusion of
`reflection` fails there (`unopened_needed`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.Unopened

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting

/-- The trivial discipline, with its type language on the nose (so that case analysis on moves sees it). -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

abbrev yU : MData := foD [] [500] 0
abbrev zU : MData := foD [] [500] 1
/-- The query's name: the copy at scope `0` of the equation's `$z`. -/
abbrev z0 : MData := foD [0] [500] 1

def fy : MData := tuple [sym "f", yU]
def pairYZ : MData := tuple [sym "pair", yU, zU]
/-- `(= (f $y) (pair $y $z))`. -/
def eU : SourceLanguage.Equation mkeys [] () MTy := ⟨[500], fy, .ret pairYZ⟩
def PU : SourceLanguage.Program mkeys [] () MTy := ⟨[eU], fun t => .apply t⟩
def callU : MData := tuple [sym "f", z0]
/-- The query `(f [0]$z)`. -/
def qU : Comp mkeys [] () MTy := .apply callU

theorem plain_program : PlainProgram PU := by
  intro e member
  rw [List.mem_singleton.mp member]
  trivial

theorem plain_query : PlainComp qU := trivial

/-- **The one hypothesis the control violates.** -/
theorem opened : ¬ ∀ t ∈ qU.data, ∀ x ∈ support t, x.scopes = [] := by
  intro unopened
  have inside : fo [0] [500] 1 ∈ support callU := by decide
  exact absurd (unopened callU (List.mem_singleton_self _) _ inside) (by decide)

/-! ## The step: a fresh `$z` -/

abbrev s0 : HostState MSig := Hosting.start N PU qU

abbrev fU : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N PU) s0.frame :=
  canonicalAt s0 (schema N eU) (schema_mem N PU (List.mem_singleton_self _)) PU.equations.length

abbrev B0 : Interface.Frames.Frame MSig := ⟨Empty, noNames⟩

/-- The reading `alt(eval(ret (pair one two)), empty)`. -/
def pair12 : Term (signature MSig noNames) [] () := tupleAt [symAt "pair", symAt "one", symAt "two"]
def qObs : Observation MSig B0.arity := observe (altN N (evalN N (retN N pair12)) (emptyN N))

/-- The start's names read: every name as `one`. -/
def σS : Assignment (startArity mkeys) B0.arity
  | .inl x => closeNames [] (csym "one") x
  | .inr p => closeNames [] (csym "one") p.2

/-- The schema's unknowns: `$y` as `one`, `$z` as `two`, the stack empty. -/
def hU : Assignment (schemaArity [] () mkeys) B0.arity :=
  schemaFill (B := B0) (closeNames [(([], [500], 0), csym "one"), (([], [500], 1), csym "two")] (csym "one"))
    (emptyN N)

theorem simpleU : Simple fU PU.equations.length (freshId s0)
    (observe (altN N (evalN N (applyN N (instantiate asUnknowns eU.lhs))) schemaStack))
    (observe (altN N (evalN N (encComp N (instantiate asUnknowns) eU.rhs)) schemaStack)) :=
  canonical_simple rfl rfl rfl

theorem shapesU : fU.Shapes (Interface.Frames.contextual MSig) s0 :=
  canonical_shapes rfl rfl rfl rfl

theorem presentU : PU.equations.length ∈ s0.present := Finset.mem_insert_self _ _

theorem s0_models : (Interface.Frames.contextual MSig).Models σS s0.knowledge := by
  intro e member
  cases member

/-- **The step's made row reads `(pair one two)`.** -/
theorem step_reads :
    rowReads (fU.result (Interface.Frames.contextual MSig) s0) (freshId s0) B0 qObs :=
  (rowReads_result simpleU shapesU presentU B0 qObs).mpr
    ⟨hU, ⟨σS, ⟨s0_models, rfl⟩⟩, models_nil_tells _, rfl⟩

/-- **The canonical firing is admitted.** -/
theorem step_fires : Fires N PU s0 (fU.result (Interface.Frames.contextual MSig) s0) := by
  obtain ⟨u, solved, _⟩ := step_reads
  exact ⟨fU, ⟨shapesU, enabled_single presentU (freshId_not_mem s0), ⟨B0, u, solved⟩,
    entails_of_no_checks rfl rfl⟩, rfl⟩

/-! ## The source: the copy's `$z` is the query's name -/

abbrev XU : Branch mkeys [] () MTy :=
  ⟨[] ++ [(instantiate (copyAt mkeys 0) fy, callU)], .eval ((Comp.ret pairYZ).inst (copyAt mkeys 0)), [], []⟩

theorem XU_never : ¬ branchReads N XU B0 qObs := by
  rintro ⟨σ, solved, same⟩
  have store := solved _ (List.mem_singleton_self _)
  change tupleAt [symAt "f", instantiate σ (foD [0] [500] 0)] = tupleAt [symAt "f", instantiate σ (foD [0] [500] 1)]
    at store
  have yz := (tuple2_inj store).2
  change observe (N.node .alt ![N.node .eval ![N.node .ret ![tupleAt [symAt "pair", instantiate σ (foD [0] [500] 0),
      instantiate σ (foD [0] [500] 1)]]], N.node .empty ![]]) = observe (N.node .alt ![N.node .eval ![N.node .ret
      ![pair12]], N.node .empty ![]]) at same
  obtain ⟨onFocus, _⟩ := vec2_inj (N.args_eq (observe_injective same))
  have onRet := vec1_inj (N.args_eq onFocus)
  have onPair := vec1_inj (N.args_eq onRet)
  obtain ⟨_, onY, onZ⟩ := tuple3_inj onPair
  have bad := onY.symm.trans (yz.trans onZ)
  simp [symAt] at bad

theorem live_U : Solvable ([] ++ [(instantiate (copyAt mkeys 0) eU.lhs, callU)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "one"), fun c member => by
    simp only [List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

theorem moves_make_XU {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (move : Move D PU supply w b w' bs)
    (hb : b = ⟨[], .eval (.apply callU), [], []⟩) (zero : w.scope = 0) : ∀ b' ∈ bs, b' = XU := by
  cases move <;> cases hb
  · intro b' made
    rw [zero] at made
    change b' ∈ (([callBranch D 0 [] callU [] [] eU] : List (Branch mkeys [] () MTy)) :
      Multiset (Branch mkeys [] () MTy)) at made
    simp only [Multiset.coe_singleton, Multiset.mem_singleton] at made
    rw [made]
    rfl
  · rename_i none
    rw [zero] at none
    exact absurd live_U (none eU (List.mem_singleton_self _))

/-- **No move of the start makes an alternative that reads `(pair one two)`.** -/
theorem source_never {w' : World mkeys [] ()} {bs : Multiset (Branch mkeys [] () D.Ty)}
    (move : Move D PU supply ⟨0, 0, sp⟩ (initialBranch qU) w' bs) :
    ∀ b' ∈ bs, ¬ branchReads N b' B0 qObs := by
  intro b' member reads
  rw [moves_make_XU move rfl rfl b' member] at reads
  exact XU_never reads

/-- **The control.** At the start of a query that violates only `unopened`, the translated program has
a firing whose made row reads what no alternative of any move of the start reads; so that firing's
result represents no child of a source move (`Represents.reads` would equate the two readings). -/
theorem unopened_needed :
    (¬ ∀ t ∈ qU.data, ∀ x ∈ support t, x.scopes = []) ∧
    Fires N PU s0 (fU.result (Interface.Frames.contextual MSig) s0) ∧
    rowReads (fU.result (Interface.Frames.contextual MSig) s0) (freshId s0) B0 qObs ∧
    ∀ w' bs, Move D PU supply ⟨0, 0, sp⟩ (initialBranch qU) w' bs → ∀ b' ∈ bs, ¬ branchReads N b' B0 qObs :=
  ⟨opened, step_fires, step_reads, fun _ _ move => source_never move⟩

#print axioms opened
#print axioms step_reads
#print axioms step_fires
#print axioms source_never
#print axioms unopened_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.Unopened
