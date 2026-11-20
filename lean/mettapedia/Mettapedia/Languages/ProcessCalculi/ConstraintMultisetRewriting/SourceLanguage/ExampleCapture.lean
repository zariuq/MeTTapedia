import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Hygiene

/-!
# The control: a reading that puts its arrows at the same sites at every run captures a name

The **positional reading** reads text as code by the elaboration (by value), with its arrows at the
fixed sites `[2] ++ path` at every run (`positional`). It is not hygienic (`positional_not_hygienic`):
a name an earlier run left in the store can have the site of an arrow of a later run's code.

The well-formed query (over the empty program read this way)

```
(let (k $p $q) (run (k b $w))
  (let $u (run (k2 c d $q)) (pair $w $u)))
```

runs `(k b $w)`, whose second argument the reading's arrow at site `[2,1]` binds to a name of that site
(`S1a`). The store then entails `$q = $w` (`q_linked`). One principal solution of that store (`θlink`)
dereferences the second text to `(k2 c d $w)`; another, equally principal (`θcapture`), to
`(k2 c d S1a)`. Through the second, the reading's arrow at site `[2,1]` of the second `run` renames
`S1a`, which sits in its body, to a fresh name (`S1c`): the run ends with a finished, live alternative
that reads `(pair 1 (k2 c d 2))` (`captured_reading`), although the argument it ran was entailed equal
to `$w` (`capture`). The elaboration's reading puts its arrows at sites fresh for the text it reads,
and the same program and choice do not capture (`ExampleCaptureRepaired`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCapture

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Hygiene

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

/-- Pass every undeclared position by value. -/
def valueReading : Params := ⟨fun _ _ => .value, false, false⟩

/-- **The positional reading**: the elaboration with every variable a value and its arrows at the
fixed sites below `[2]`, whatever text it reads. -/
def positional (π : Params) (decls : List Decl) (t : MData) : Comp mkeys [] () MTy :=
  elabText π decls (fun _ => .value) [2] (view t)

/-- **The empty program**, reading text as code positionally. -/
def program : Program mkeys [] () MTy := ⟨[], positional valueReading []⟩

def supply : ℕ → MClosed := fun _ => csym "fresh"

/-! ## The query -/

def w : MData := mvar [3] 0
def p : MData := mvar [3, 1] 0
def q : MData := mvar [3, 1] 1
def u : MData := mvar [3, 2] 0

def T1 : MData := tuple [sym "k", sym "b", w]
def P1 : MData := tuple [sym "k", p, q]
def T2 : MData := tuple [sym "k2", sym "c", sym "d", q]

def K' : Comp mkeys [] () MTy := .let_ [3, 2] u (.run T2) (.ret (tuple [sym "pair", w, u]))

def query : Comp mkeys [] () MTy := .let_ [3, 1] P1 (.run T1) K'

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

theorem program_wellFormed : WellFormed program := by decide

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

/-! ## Names the run opens -/

/-- The reading's slots. -/
def S0 : MData := mvar [2, 0] 0
def S1 : MData := mvar [2, 1] 0
def S2 : MData := mvar [2, 2] 0

def S0a : MData := foD [0] [2, 0] 0
def S1a : MData := foD [1] [2, 1] 0
def p2 : MData := foD [2] [3, 1] 0
def q2 : MData := foD [2] [3, 1] 1
def S0b : MData := foD [3] [2, 0] 0
def S1b : MData := foD [4] [2, 1] 0
/-- **The captured name**: `S1a` renamed by the second `run`'s arrow at site `[2,1]`. -/
def S1c : MData := foD [4, 1] [2, 1] 0
def S2b : MData := foD [5] [2, 2] 0
def u6 : MData := foD [6] [3, 2] 0

def W (n : ℕ) : World mkeys [] () := ⟨n, 0, fun _ => 0⟩

/-! ## The computations along the run -/

def fr31 : Frame mkeys [] () MTy := .bindTo [3, 1] P1 K'
def B1 : Comp mkeys [] () MTy := .let_ [2, 1] S1 (.ret w) (.apply (tuple [sym "k", S0, S1]))
def R1 : Comp mkeys [] () MTy := .let_ [2, 0] S0 (.apply (sym "b")) B1
def B1a : Comp mkeys [] () MTy := .let_ [2, 1] S1 (.ret w) (.apply (tuple [sym "k", S0a, S1]))
def C1 : MData := tuple [sym "k", S0a, S1a]
def P1a : MData := tuple [sym "k", p2, q2]
def T2a : MData := tuple [sym "k2", sym "c", sym "d", q2]
def K'a : Comp mkeys [] () MTy := .let_ [3, 2] u (.run T2a) (.ret (tuple [sym "pair", w, u]))
def fr32 : Frame mkeys [] () MTy := .bindTo [3, 2] u (.ret (tuple [sym "pair", w, u]))
def B3 : Comp mkeys [] () MTy := .let_ [2, 2] S2 (.ret S1a) (.apply (tuple [sym "k2", S0b, S1, S2]))
def B2 : Comp mkeys [] () MTy := .let_ [2, 1] S1 (.apply (sym "d")) (.let_ [2, 2] S2 (.ret S1a)
  (.apply (tuple [sym "k2", S0, S1, S2])))
def R2 : Comp mkeys [] () MTy := .let_ [2, 0] S0 (.apply (sym "c")) B2
def B2a : Comp mkeys [] () MTy := .let_ [2, 1] S1 (.apply (sym "d")) B3
def B3a : Comp mkeys [] () MTy := .let_ [2, 2] S2 (.ret S1c) (.apply (tuple [sym "k2", S0b, S1b, S2]))
def C2 : MData := tuple [sym "k2", S0b, S1b, S2b]
def result : MData := tuple [sym "pair", w, u6]

/-! ## The stores along the run -/

def L1 : List (Constraint mkeys [] ()) := [] ++ [(S0a, sym "b")]
def L2 : List (Constraint mkeys [] ()) := L1 ++ [(S1a, w)]
def L3 : List (Constraint mkeys [] ()) := L2 ++ [(P1a, C1)]
def L4 : List (Constraint mkeys [] ()) := L3 ++ [(S0b, sym "c")]
def L5 : List (Constraint mkeys [] ()) := L4 ++ [(S1b, sym "d")]
def L6 : List (Constraint mkeys [] ()) := L5 ++ [(S2b, S1c)]
def L7 : List (Constraint mkeys [] ()) := L6 ++ [(u6, C2)]

/-- A solution of the final store in which `$w` is `1` and the captured name is `2`. -/
def σf : Assignment (fam mkeys) noNames :=
  closeNames [(([], [3], 0), cnum 1), (([1], [2, 1], 0), cnum 1), (([2], [3, 1], 1), cnum 1),
    (([0], [2, 0], 0), csym "b"), (([2], [3, 1], 0), csym "b"), (([3], [2, 0], 0), csym "c"),
    (([4], [2, 1], 0), csym "d"), (([4, 1], [2, 1], 0), cnum 2), (([5], [2, 2], 0), cnum 2),
    (([6], [3, 2], 0), ctuple [csym "k2", csym "c", csym "d", cnum 2])] (csym "a")

theorem L7_solved : Models σf L7 := by decide

theorem L7_live : Solvable L7 := ⟨Empty, noNames, σf, L7_solved⟩
theorem L6_live : Solvable L6 := solvable_of_append L7_live
theorem L5_live : Solvable L5 := solvable_of_append L6_live
theorem L4_live : Solvable L4 := solvable_of_append L5_live
theorem L3_live : Solvable L3 := solvable_of_append L4_live
theorem L2_live : Solvable L2 := solvable_of_append L3_live
theorem L1_live : Solvable L1 := solvable_of_append L2_live

/-! ## Most general solutions of the store at the second `run` -/

theorem principal_empty : Principal ([] : List (Constraint mkeys [] ())) (generator (fam mkeys)) :=
  ⟨fun _ member => (by cases member), fun _ σ _ name => instantiate_generator σ name⟩

/-- What every solution of `L3` says about its names. -/
theorem L3_entails {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target)
    (solved : Models σ L3) :
    σ (fo [0] [2, 0] 0) = instantiate σ (sym "b") ∧ σ (fo [1] [2, 1] 0) = σ (fo [] [3] 0) ∧
      σ (fo [2] [3, 1] 0) = σ (fo [0] [2, 0] 0) ∧ σ (fo [2] [3, 1] 1) = σ (fo [1] [2, 1] 0) := by
  have e1 : instantiate σ S0a = instantiate σ (sym "b") := solved (S0a, sym "b") (by simp [L3, L2, L1])
  have e2 : instantiate σ S1a = instantiate σ w := solved (S1a, w) (by simp [L3, L2, L1])
  have e3 : instantiate σ P1a = instantiate σ C1 := solved (P1a, C1) (by simp [L3, L2, L1])
  have parts : tupleAt [symAt "k", instantiate σ (foD [2] [3, 1] 0), instantiate σ (foD [2] [3, 1] 1)] =
      tupleAt [symAt "k", instantiate σ (foD [0] [2, 0] 0), instantiate σ (foD [1] [2, 1] 0)] := e3
  obtain ⟨-, hp, hq⟩ := tuple3_inj parts
  rw [instantiate_foD, instantiate_foD] at hp hq
  refine ⟨?_, ?_, hp, hq⟩
  · have e1' : instantiate σ (foD [0] [2, 0] 0) = instantiate σ (sym "b") := e1
    rw [instantiate_foD] at e1'
    exact e1'
  · have e2' : instantiate σ (foD [1] [2, 1] 0) = instantiate σ (foD [] [3] 0) := e2
    rw [instantiate_foD, instantiate_foD] at e2'
    exact e2'

/-- **`$q` is linked to `$w`** in the store at the second `run`. -/
theorem q_linked : EntailsEq L3 q2 w := by
  intro X target σ solved
  obtain ⟨-, h1, -, h3⟩ := L3_entails σ solved
  show instantiate σ (foD [2] [3, 1] 1) = instantiate σ (foD [] [3] 0)
  rw [instantiate_foD, instantiate_foD, h3, h1]

/-- The solution that keeps `$w` as the representative of its class. -/
def θlink : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [2, 0], 0), sym "b"), (([2], [3, 1], 0), sym "b"), (([1], [2, 1], 0), w),
    (([2], [3, 1], 1), w)]

/-- The solution that takes the reading's slot `S1a` as the representative. -/
def θcapture : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [2, 0], 0), sym "b"), (([2], [3, 1], 0), sym "b"), (([], [3], 0), S1a),
    (([2], [3, 1], 1), S1a)]

theorem principal_link : Principal L3 θlink := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  obtain ⟨h0, h1, h2, h3⟩ := L3_entails σ models
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact h0
  · exact h2.trans h0
  · show σ (fo [1] [2, 1] 0) = instantiate σ (foD [] [3] 0)
    rw [instantiate_foD]
    exact h1
  · show σ (fo [2] [3, 1] 1) = instantiate σ (foD [] [3] 0)
    rw [instantiate_foD]
    exact h3.trans h1

theorem principal_capture : Principal L3 θcapture := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  obtain ⟨h0, h1, h2, h3⟩ := L3_entails σ models
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact h0
  · exact h2.trans h0
  · show σ (fo [] [3] 0) = instantiate σ (foD [1] [2, 1] 0)
    rw [instantiate_foD]
    exact h1.symm
  · show σ (fo [2] [3, 1] 1) = instantiate σ (foD [1] [2, 1] 0)
    rw [instantiate_foD]
    exact h3

theorem link_text : instantiate θlink T2a = tuple [sym "k2", sym "c", sym "d", w] := rfl
theorem capture_text : instantiate θcapture T2a = tuple [sym "k2", sym "c", sym "d", S1a] := rfl

/-- **The two principal solutions give two different texts to run.** -/
theorem texts_differ : instantiate θlink T2a ≠ instantiate θcapture T2a := by
  rw [link_text, capture_text]
  decide

/-! ## The run through `θcapture` -/

theorem no_equations (K : List (Constraint mkeys [] ())) (t : MData) (n : ℕ) :
    ∀ e ∈ program.equations, ¬ Solvable (K ++ [(instantiate (copyAt mkeys n) e.lhs, t)]) := by
  intro e member
  simp [program] at member

def finalBranch : Branch mkeys [] () MTy := ⟨L7, .value result, [], []⟩

def final : Config mkeys [] () MTy := ⟨W 7, {finalBranch}⟩

theorem runs : Runs D program supply start final := by
  refine .head (b := ⟨W 0, {⟨[], .eval (.run T1), [fr31], []⟩}⟩)
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 0, {⟨[], .eval R1, [fr31], []⟩}⟩)
    (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_empty)) ?_
  refine .head (b := ⟨W 0, {⟨[], .eval (.apply (sym "b")), [.bindTo [2, 0] S0 B1, fr31], []⟩}⟩)
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 0, {⟨[], .value (sym "b"), [.bindTo [2, 0] S0 B1, fr31], []⟩}⟩)
    (step_one live_nil (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 1, {⟨L1, .eval B1a, [fr31], []⟩}⟩)
    (step_one live_nil (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 1, {⟨L1, .eval (.ret w), [.bindTo [2, 1] S1 (.apply (tuple [sym "k", S0a, S1])), fr31],
      []⟩}⟩)
    (step_one L1_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 1, {⟨L1, .value w, [.bindTo [2, 1] S1 (.apply (tuple [sym "k", S0a, S1])), fr31],
      []⟩}⟩)
    (step_one L1_live (.ret _ _ _ _ _)) ?_
  refine .head (b := ⟨W 2, {⟨L2, .eval (.apply C1), [fr31], []⟩}⟩)
    (step_one L1_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 2, {⟨L2, .value C1, [fr31], []⟩}⟩)
    (step_one L2_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval K'a, [], []⟩}⟩)
    (step_one L2_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval (.run T2a), [fr32], []⟩}⟩)
    (step_one L3_live (.letStart _ _ _ _ _ _ _ _)) ?_
  -- the second `run`, through the principal solution that takes the slot `S1a` as representative
  refine .head (b := ⟨W 3, {⟨L3, .eval R2, [fr32], []⟩}⟩)
    (step_one L3_live (.run _ _ _ _ _ θcapture principal_capture)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval (.apply (sym "c")), [.bindTo [2, 0] S0 B2, fr32], []⟩}⟩)
    (step_one L3_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .value (sym "c"), [.bindTo [2, 0] S0 B2, fr32], []⟩}⟩)
    (step_one L3_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 4, {⟨L4, .eval B2a, [fr32], []⟩}⟩)
    (step_one L3_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨L4, .eval (.apply (sym "d")), [.bindTo [2, 1] S1 B3, fr32], []⟩}⟩)
    (step_one L4_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨L4, .value (sym "d"), [.bindTo [2, 1] S1 B3, fr32], []⟩}⟩)
    (step_one L4_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  -- the arrow at site `[2,1]` opens its body, and with it the earlier slot `S1a`
  refine .head (b := ⟨W 5, {⟨L5, .eval B3a, [fr32], []⟩}⟩)
    (step_one L4_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨L5, .eval (.ret S1c),
      [.bindTo [2, 2] S2 (.apply (tuple [sym "k2", S0b, S1b, S2])), fr32], []⟩}⟩)
    (step_one L5_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨L5, .value S1c,
      [.bindTo [2, 2] S2 (.apply (tuple [sym "k2", S0b, S1b, S2])), fr32], []⟩}⟩)
    (step_one L5_live (.ret _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨L6, .eval (.apply C2), [fr32], []⟩}⟩)
    (step_one L5_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨L6, .value C2, [fr32], []⟩}⟩)
    (step_one L6_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 7, {⟨L7, .eval (.ret result), [], []⟩}⟩)
    (step_one L6_live (.letBind _ _ _ _ _ _ _ _)) ?_
  exact .single (step_one L7_live (.ret _ _ _ _ _))

/-! ## The answer has lost the link -/

/-- **A reading of the finished alternative in which `$w` is `1` and the argument run is `2`.** -/
theorem captured_reading :
    Reads L7 result (ctuple [csym "pair", cnum 1, ctuple [csym "k2", csym "c", csym "d", cnum 2]]) :=
  ⟨Empty, noNames, σf, L7_solved, rfl⟩

/-- The slot that received the argument is not linked to `$w` in the final store. -/
theorem not_linked : ¬ EntailsEq L7 S2b w := by
  intro linked
  have same := linked noNames σf L7_solved
  exact absurd same (by decide)

theorem finalBranch_finished : Branch.Finished (D := D) finalBranch := ⟨rfl, _, rfl⟩

/-- **Capture through `run`.** A well-formed program and query; at the second `run` the store entails
that the text's argument `$q` equals `$w`, and has two principal solutions giving two different texts;
the run through one of them ends with a finished, live alternative that reads `$w` as `1` and the
argument as `2`, and the argument's slot is no longer linked to `$w`. -/
theorem capture :
    WellFormed program ∧ QueryWellFormed program [3] query ∧
      Runs D program supply start final ∧ Branch.Finished (D := D) finalBranch ∧ Solvable L7 ∧
      EntailsEq L3 q2 w ∧ Principal L3 θlink ∧ Principal L3 θcapture ∧
      instantiate θlink T2a ≠ instantiate θcapture T2a ∧
      Reads L7 result (ctuple [csym "pair", cnum 1, ctuple [csym "k2", csym "c", csym "d", cnum 2]]) ∧
      ¬ EntailsEq L7 S2b w :=
  ⟨program_wellFormed, query_wellFormed, runs, finalBranch_finished, L7_live, q_linked, principal_link,
    principal_capture, texts_differ, captured_reading, not_linked⟩

/-- **The positional reading is not hygienic**: it reads `(k2 c d S1a)` with an arrow at `S1a`'s own
site. -/
theorem positional_not_hygienic : ¬ ReadingHygienic (positional valueReading []) := by
  intro hygienic
  have inText : fo [1] [2, 1] 0 ∈ support (tuple [sym "k2", sym "c", sym "d", S1a]) := by decide
  exact hygienic.apart _ _ inText (by decide)

#print axioms program_wellFormed
#print axioms query_wellFormed
#print axioms principal_link
#print axioms principal_capture
#print axioms texts_differ
#print axioms runs
#print axioms captured_reading
#print axioms capture
#print axioms positional_not_hygienic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCapture
