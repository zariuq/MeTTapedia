import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene

/-!
# The capture program under the elaboration's reading: no capture, and the two choices agree

The program and query of `ExampleCapture`, here over the empty program read by the elaboration, whose
reading puts its arrows at sites fresh for the text it reads (`program_hygienic`):

```
(let (k $p $q) (run (k b $w))
  (let $u (run (k2 c d $q)) (pair $w $u)))
```

The first `run` reads `(k b $w)` with its arrows below `[2, 0]`; its second slot `S1a` (site `[2,0,1]`)
is left in the store, linked to `$w`. At the second `run` the store has the same two principal
solutions as there (`principal_link`, `principal_capture`): one dereferences the text to
`(k2 c d $w)`, the other to `(k2 c d S1a)`. The reading of the second text puts its arrows below
`[2, 1]`, past `S1a`'s site, so no arrow renames `S1a` (`capture_store_linked`: the slot that received
the argument stays entailed equal to `$w`).

Both runs end with one finished alternative (`runs_link`, `runs_capture`), and the two answers are
equal (`choices_agree`): each is the set of readings of `(pair $w (k2 c d $w))` under the store of the
first run, because every later equation of each run defines a fresh name (`reads_drop_fresh`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCaptureRepaired

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Hygiene ElaborationHygiene

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

/-- Pass every undeclared position by value. -/
def valueReading : Params := ⟨fun _ _ => .value, false, false⟩

/-- **The empty program**, reading text as code by the elaboration. -/
def program : Program mkeys [] () MTy := elaborate valueReading ⟨[], []⟩

def supply : ℕ → MClosed := fun _ => csym "fresh"

theorem program_hygienic : ReadingHygienic program.reflect := elaborate_hygienic valueReading ⟨[], []⟩

/-! ## Readings through definitions of fresh names -/

/-- Data the store entails equal have the same readings. -/
theorem reads_of_entails {L : List (Constraint mkeys [] ())} {r r' : MData} (same : EntailsEq L r r')
    (g : MClosed) : Reads L r g ↔ Reads L r' g := by
  constructor
  · rintro ⟨X, target, σ, solved, read⟩
    exact ⟨X, target, σ, solved, (same target σ solved).symm.trans read⟩
  · rintro ⟨X, target, σ, solved, read⟩
    exact ⟨X, target, σ, solved, (same target σ solved).trans read⟩

/-- **A definition of a fresh name changes no reading**: an equation `x = t` whose first-order name `x`
occurs neither in the rest of the store, nor in `t`, nor in the datum read. -/
theorem reads_drop_fresh {L : List (Constraint mkeys [] ())} (scopes site : List ℕ) (index : ℕ)
    {t r : MData} {g : MClosed}
    (freshL : ∀ e ∈ L, fo scopes site index ∉ support e.1 ∧ fo scopes site index ∉ support e.2)
    (freshT : fo scopes site index ∉ support t) (freshR : fo scopes site index ∉ support r) :
    Reads (L ++ [(foD scopes site index, t)]) r g ↔ Reads L r g := by
  constructor
  · exact reads_of_append
  · rintro ⟨X, target, σ, solved, read⟩
    let σ' : Assignment (fam mkeys) target :=
      Function.update σ (fo scopes site index) (instantiate σ t)
    have keep : ∀ d : MData, fo scopes site index ∉ support d → instantiate σ' d = instantiate σ d :=
      fun d fresh => instantiate_congr σ' σ d fun y hy => by
        have ne : y ≠ fo scopes site index := fun same => fresh (same ▸ hy)
        exact Function.update_of_ne ne _ _
    refine ⟨X, target, σ', fun e member => ?_, (keep r freshR).trans read⟩
    rcases List.mem_append.mp member with old | new
    · rw [keep e.1 (freshL e old).1, keep e.2 (freshL e old).2]
      exact solved e old
    · rw [List.mem_singleton.mp new]
      show instantiate σ' (foD scopes site index) = instantiate σ' t
      rw [instantiate_foD, keep t freshT]
      exact Function.update_self _ _ _

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

/-! ## The first run (the reading's arrows below `[2, 0]`) -/

def S0 : MData := mvar [2, 0, 0] 0
def S1 : MData := mvar [2, 0, 1] 0
def S2 : MData := mvar [2, 0, 2] 0

def S0a : MData := foD [0] [2, 0, 0] 0
/-- The slot the first run leaves in the store, linked to `$w`. -/
def S1a : MData := foD [1] [2, 0, 1] 0
def p2 : MData := foD [2] [3, 1] 0
def q2 : MData := foD [2] [3, 1] 1
def u6 : MData := foD [6] [3, 2] 0

def W (n : ℕ) : World mkeys [] () := ⟨n, 0, fun _ => 0⟩

def fr31 : Frame mkeys [] () MTy := .bindTo [3, 1] P1 K'
def B1 : Comp mkeys [] () MTy := .let_ [2, 0, 1] S1 (.ret w) (.apply (tuple [sym "k", S0, S1]))
def R1 : Comp mkeys [] () MTy := .let_ [2, 0, 0] S0 (.apply (sym "b")) B1
def B1a : Comp mkeys [] () MTy := .let_ [2, 0, 1] S1 (.ret w) (.apply (tuple [sym "k", S0a, S1]))
def C1 : MData := tuple [sym "k", S0a, S1a]
def P1a : MData := tuple [sym "k", p2, q2]
def T2a : MData := tuple [sym "k2", sym "c", sym "d", q2]
def K'a : Comp mkeys [] () MTy := .let_ [3, 2] u (.run T2a) (.ret (tuple [sym "pair", w, u]))
def fr32 : Frame mkeys [] () MTy := .bindTo [3, 2] u (.ret (tuple [sym "pair", w, u]))

def L1 : List (Constraint mkeys [] ()) := [] ++ [(S0a, sym "b")]
def L2 : List (Constraint mkeys [] ()) := L1 ++ [(S1a, w)]
def L3 : List (Constraint mkeys [] ()) := L2 ++ [(P1a, C1)]

theorem no_equations (K : List (Constraint mkeys [] ())) (t : MData) (n : ℕ) :
    ∀ e ∈ program.equations, ¬ Solvable (K ++ [(instantiate (copyAt mkeys n) e.lhs, t)]) := by
  intro e member
  simp [program, elaborate] at member

theorem principal_empty : Principal ([] : List (Constraint mkeys [] ())) (generator (fam mkeys)) :=
  ⟨fun _ member => (by cases member), fun _ σ _ name => instantiate_generator σ name⟩

/-- What every solution of `L3` says about its names. -/
theorem L3_entails {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target)
    (solved : Models σ L3) :
    σ (fo [0] [2, 0, 0] 0) = instantiate σ (sym "b") ∧ σ (fo [1] [2, 0, 1] 0) = σ (fo [] [3] 0) ∧
      σ (fo [2] [3, 1] 0) = σ (fo [0] [2, 0, 0] 0) ∧ σ (fo [2] [3, 1] 1) = σ (fo [1] [2, 0, 1] 0) := by
  have e1 : instantiate σ S0a = instantiate σ (sym "b") := solved (S0a, sym "b") (by simp [L3, L2, L1])
  have e2 : instantiate σ S1a = instantiate σ w := solved (S1a, w) (by simp [L3, L2, L1])
  have e3 : instantiate σ P1a = instantiate σ C1 := solved (P1a, C1) (by simp [L3, L2, L1])
  have parts : tupleAt [symAt "k", instantiate σ (foD [2] [3, 1] 0), instantiate σ (foD [2] [3, 1] 1)] =
      tupleAt [symAt "k", instantiate σ (foD [0] [2, 0, 0] 0), instantiate σ (foD [1] [2, 0, 1] 0)] := e3
  obtain ⟨-, hp, hq⟩ := tuple3_inj parts
  rw [instantiate_foD, instantiate_foD] at hp hq
  refine ⟨?_, ?_, hp, hq⟩
  · have e1' : instantiate σ (foD [0] [2, 0, 0] 0) = instantiate σ (sym "b") := e1
    rw [instantiate_foD] at e1'
    exact e1'
  · have e2' : instantiate σ (foD [1] [2, 0, 1] 0) = instantiate σ (foD [] [3] 0) := e2
    rw [instantiate_foD, instantiate_foD] at e2'
    exact e2'

/-- The solution that keeps `$w` as the representative of its class. -/
def θlink : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [2, 0, 0], 0), sym "b"), (([2], [3, 1], 0), sym "b"), (([1], [2, 0, 1], 0), w),
    (([2], [3, 1], 1), w)]

/-- The solution that takes the first run's slot `S1a` as the representative. -/
def θcapture : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [2, 0, 0], 0), sym "b"), (([2], [3, 1], 0), sym "b"), (([], [3], 0), S1a),
    (([2], [3, 1], 1), S1a)]

theorem principal_link : Principal L3 θlink := by
  refine principal_bindNames (by decide) ?_
  intro entry member X target σ models
  obtain ⟨h0, h1, h2, h3⟩ := L3_entails σ models
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact h0
  · exact h2.trans h0
  · show σ (fo [1] [2, 0, 1] 0) = instantiate σ (foD [] [3] 0)
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
  · show σ (fo [] [3] 0) = instantiate σ (foD [1] [2, 0, 1] 0)
    rw [instantiate_foD]
    exact h1.symm
  · show σ (fo [2] [3, 1] 1) = instantiate σ (foD [1] [2, 0, 1] 0)
    rw [instantiate_foD]
    exact h3

/-- **The two principal solutions give two different texts to run.** -/
theorem texts_differ : instantiate θlink T2a ≠ instantiate θcapture T2a := by
  show tuple [sym "k2", sym "c", sym "d", w] ≠ tuple [sym "k2", sym "c", sym "d", S1a]
  decide

/-- The first run, and the configuration about to run the second text. -/
def mid : Config mkeys [] () MTy := ⟨W 3, {⟨L3, .eval (.run T2a), [fr32], []⟩}⟩

/-! ## The second run through `θlink` (arrows below `[2, 0]`) -/

def B2 : Comp mkeys [] () MTy := .let_ [2, 0, 1] S1 (.apply (sym "d")) (.let_ [2, 0, 2] S2 (.ret w)
  (.apply (tuple [sym "k2", S0, S1, S2])))
def R2 : Comp mkeys [] () MTy := .let_ [2, 0, 0] S0 (.apply (sym "c")) B2
def S0b : MData := foD [3] [2, 0, 0] 0
def S1b : MData := foD [4] [2, 0, 1] 0
def S2b : MData := foD [5] [2, 0, 2] 0
def B3 : Comp mkeys [] () MTy := .let_ [2, 0, 2] S2 (.ret w) (.apply (tuple [sym "k2", S0b, S1, S2]))
def B2a : Comp mkeys [] () MTy := .let_ [2, 0, 1] S1 (.apply (sym "d")) B3
def B3a : Comp mkeys [] () MTy := .let_ [2, 0, 2] S2 (.ret w) (.apply (tuple [sym "k2", S0b, S1b, S2]))
def C2 : MData := tuple [sym "k2", S0b, S1b, S2b]
def result : MData := tuple [sym "pair", w, u6]

def L4 : List (Constraint mkeys [] ()) := L3 ++ [(S0b, sym "c")]
def L5 : List (Constraint mkeys [] ()) := L4 ++ [(S1b, sym "d")]
def L6 : List (Constraint mkeys [] ()) := L5 ++ [(S2b, w)]
def L7 : List (Constraint mkeys [] ()) := L6 ++ [(u6, C2)]

def σlink : Assignment (fam mkeys) noNames :=
  closeNames [(([], [3], 0), cnum 1), (([1], [2, 0, 1], 0), cnum 1), (([2], [3, 1], 1), cnum 1),
    (([0], [2, 0, 0], 0), csym "b"), (([2], [3, 1], 0), csym "b"), (([3], [2, 0, 0], 0), csym "c"),
    (([4], [2, 0, 1], 0), csym "d"), (([5], [2, 0, 2], 0), cnum 1),
    (([6], [3, 2], 0), ctuple [csym "k2", csym "c", csym "d", cnum 1])] (csym "a")

theorem L7_solved : Models σlink L7 := by decide

theorem L7_live : Solvable L7 := ⟨Empty, noNames, σlink, L7_solved⟩
theorem L6_live : Solvable L6 := solvable_of_append L7_live
theorem L5_live : Solvable L5 := solvable_of_append L6_live
theorem L4_live : Solvable L4 := solvable_of_append L5_live
theorem L3_live : Solvable L3 := solvable_of_append L4_live
theorem L2_live : Solvable L2 := solvable_of_append L3_live
theorem L1_live : Solvable L1 := solvable_of_append L2_live

/-- **The first run**, to the second `run`. -/
theorem runs_mid : Runs D program supply start mid := by
  refine .head (b := ⟨W 0, {⟨[], .eval (.run T1), [fr31], []⟩}⟩)
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 0, {⟨[], .eval R1, [fr31], []⟩}⟩)
    (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_empty)) ?_
  refine .head (b := ⟨W 0, {⟨[], .eval (.apply (sym "b")), [.bindTo [2, 0, 0] S0 B1, fr31], []⟩}⟩)
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 0, {⟨[], .value (sym "b"), [.bindTo [2, 0, 0] S0 B1, fr31], []⟩}⟩)
    (step_one live_nil (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 1, {⟨L1, .eval B1a, [fr31], []⟩}⟩)
    (step_one live_nil (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 1, {⟨L1, .eval (.ret w),
      [.bindTo [2, 0, 1] S1 (.apply (tuple [sym "k", S0a, S1])), fr31], []⟩}⟩)
    (step_one L1_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 1, {⟨L1, .value w,
      [.bindTo [2, 0, 1] S1 (.apply (tuple [sym "k", S0a, S1])), fr31], []⟩}⟩)
    (step_one L1_live (.ret _ _ _ _ _)) ?_
  refine .head (b := ⟨W 2, {⟨L2, .eval (.apply C1), [fr31], []⟩}⟩)
    (step_one L1_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 2, {⟨L2, .value C1, [fr31], []⟩}⟩)
    (step_one L2_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval K'a, [], []⟩}⟩)
    (step_one L2_live (.letBind _ _ _ _ _ _ _ _)) ?_
  exact .single (step_one L3_live (.letStart _ _ _ _ _ _ _ _))

def finalLink : Branch mkeys [] () MTy := ⟨L7, .value result, [], []⟩

/-- **The run through `θlink`.** -/
theorem runs_link : Runs D program supply start ⟨W 7, {finalLink}⟩ := by
  refine runs_mid.trans ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval R2, [fr32], []⟩}⟩)
    (step_one L3_live (.run _ _ _ _ _ θlink principal_link)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval (.apply (sym "c")), [.bindTo [2, 0, 0] S0 B2, fr32], []⟩}⟩)
    (step_one L3_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .value (sym "c"), [.bindTo [2, 0, 0] S0 B2, fr32], []⟩}⟩)
    (step_one L3_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 4, {⟨L4, .eval B2a, [fr32], []⟩}⟩)
    (step_one L3_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨L4, .eval (.apply (sym "d")), [.bindTo [2, 0, 1] S1 B3, fr32], []⟩}⟩)
    (step_one L4_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨L4, .value (sym "d"), [.bindTo [2, 0, 1] S1 B3, fr32], []⟩}⟩)
    (step_one L4_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 5, {⟨L5, .eval B3a, [fr32], []⟩}⟩)
    (step_one L4_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨L5, .eval (.ret w),
      [.bindTo [2, 0, 2] S2 (.apply (tuple [sym "k2", S0b, S1b, S2])), fr32], []⟩}⟩)
    (step_one L5_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨L5, .value w,
      [.bindTo [2, 0, 2] S2 (.apply (tuple [sym "k2", S0b, S1b, S2])), fr32], []⟩}⟩)
    (step_one L5_live (.ret _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨L6, .eval (.apply C2), [fr32], []⟩}⟩)
    (step_one L5_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨L6, .value C2, [fr32], []⟩}⟩)
    (step_one L6_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 7, {⟨L7, .eval (.ret result), [], []⟩}⟩)
    (step_one L6_live (.letBind _ _ _ _ _ _ _ _)) ?_
  exact .single (step_one L7_live (.ret _ _ _ _ _))

/-! ## The second run through `θcapture` (arrows below `[2, 1]`, past `S1a`'s site) -/

def U0 : MData := mvar [2, 1, 0] 0
def U1 : MData := mvar [2, 1, 1] 0
def U2 : MData := mvar [2, 1, 2] 0
def U0b : MData := foD [3] [2, 1, 0] 0
def U1b : MData := foD [4] [2, 1, 1] 0
def U2b : MData := foD [5] [2, 1, 2] 0

def V2 : Comp mkeys [] () MTy := .let_ [2, 1, 1] U1 (.apply (sym "d")) (.let_ [2, 1, 2] U2 (.ret S1a)
  (.apply (tuple [sym "k2", U0, U1, U2])))
def Q2 : Comp mkeys [] () MTy := .let_ [2, 1, 0] U0 (.apply (sym "c")) V2
def V3 : Comp mkeys [] () MTy := .let_ [2, 1, 2] U2 (.ret S1a) (.apply (tuple [sym "k2", U0b, U1, U2]))
def V2a : Comp mkeys [] () MTy := .let_ [2, 1, 1] U1 (.apply (sym "d")) V3
/-- After the arrow at site `[2,1,1]` binds: `S1a` is still `S1a`. -/
def V3a : Comp mkeys [] () MTy := .let_ [2, 1, 2] U2 (.ret S1a) (.apply (tuple [sym "k2", U0b, U1b, U2]))
def C2' : MData := tuple [sym "k2", U0b, U1b, U2b]

def M4 : List (Constraint mkeys [] ()) := L3 ++ [(U0b, sym "c")]
def M5 : List (Constraint mkeys [] ()) := M4 ++ [(U1b, sym "d")]
def M6 : List (Constraint mkeys [] ()) := M5 ++ [(U2b, S1a)]
def M7 : List (Constraint mkeys [] ()) := M6 ++ [(u6, C2')]

def σcapture : Assignment (fam mkeys) noNames :=
  closeNames [(([], [3], 0), cnum 1), (([1], [2, 0, 1], 0), cnum 1), (([2], [3, 1], 1), cnum 1),
    (([0], [2, 0, 0], 0), csym "b"), (([2], [3, 1], 0), csym "b"), (([3], [2, 1, 0], 0), csym "c"),
    (([4], [2, 1, 1], 0), csym "d"), (([5], [2, 1, 2], 0), cnum 1),
    (([6], [3, 2], 0), ctuple [csym "k2", csym "c", csym "d", cnum 1])] (csym "a")

theorem M7_solved : Models σcapture M7 := by decide

theorem M7_live : Solvable M7 := ⟨Empty, noNames, σcapture, M7_solved⟩
theorem M6_live : Solvable M6 := solvable_of_append M7_live
theorem M5_live : Solvable M5 := solvable_of_append M6_live
theorem M4_live : Solvable M4 := solvable_of_append M5_live

def finalCapture : Branch mkeys [] () MTy := ⟨M7, .value result, [], []⟩

/-- **The run through `θcapture`.** -/
theorem runs_capture : Runs D program supply start ⟨W 7, {finalCapture}⟩ := by
  refine runs_mid.trans ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval Q2, [fr32], []⟩}⟩)
    (step_one L3_live (.run _ _ _ _ _ θcapture principal_capture)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .eval (.apply (sym "c")), [.bindTo [2, 1, 0] U0 V2, fr32], []⟩}⟩)
    (step_one L3_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 3, {⟨L3, .value (sym "c"), [.bindTo [2, 1, 0] U0 V2, fr32], []⟩}⟩)
    (step_one L3_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 4, {⟨M4, .eval V2a, [fr32], []⟩}⟩)
    (step_one L3_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨M4, .eval (.apply (sym "d")), [.bindTo [2, 1, 1] U1 V3, fr32], []⟩}⟩)
    (step_one M4_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 4, {⟨M4, .value (sym "d"), [.bindTo [2, 1, 1] U1 V3, fr32], []⟩}⟩)
    (step_one M4_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  -- the arrow at site `[2,1,1]` opens its body; `S1a` (site `[2,0,1]`) is not renamed
  refine .head (b := ⟨W 5, {⟨M5, .eval V3a, [fr32], []⟩}⟩)
    (step_one M4_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨M5, .eval (.ret S1a),
      [.bindTo [2, 1, 2] U2 (.apply (tuple [sym "k2", U0b, U1b, U2])), fr32], []⟩}⟩)
    (step_one M5_live (.letStart _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 5, {⟨M5, .value S1a,
      [.bindTo [2, 1, 2] U2 (.apply (tuple [sym "k2", U0b, U1b, U2])), fr32], []⟩}⟩)
    (step_one M5_live (.ret _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨M6, .eval (.apply C2'), [fr32], []⟩}⟩)
    (step_one M5_live (.letBind _ _ _ _ _ _ _ _)) ?_
  refine .head (b := ⟨W 6, {⟨M6, .value C2', [fr32], []⟩}⟩)
    (step_one M6_live (.unmatched _ _ _ _ _ (no_equations _ _ _))) ?_
  refine .head (b := ⟨W 7, {⟨M7, .eval (.ret result), [], []⟩}⟩)
    (step_one M6_live (.letBind _ _ _ _ _ _ _ _)) ?_
  exact .single (step_one M7_live (.ret _ _ _ _ _))

/-- **No capture**: the slot that received the argument stays entailed equal to `$w`. -/
theorem capture_store_linked : EntailsEq M7 U2b w := by
  intro X target σ solved
  have e2 : instantiate σ S1a = instantiate σ w := solved (S1a, w) (by simp [M7, M6, M5, M4, L3, L2, L1])
  have e6 : instantiate σ U2b = instantiate σ S1a := solved (U2b, S1a) (by simp [M7, M6])
  exact e6.trans e2

/-! ## The two answers agree -/

/-- The datum both answers read. -/
def linked : MData := tuple [sym "pair", w, tuple [sym "k2", sym "c", sym "d", w]]

theorem answer_eq_reads (K : List (Constraint mkeys [] ())) :
    Branch.answer (D := D) (⟨K, .value result, [], []⟩ : Branch mkeys [] () MTy) = {g | Reads K result g} := by
  ext g
  constructor
  · rintro ⟨t, same, reads⟩
    cases same
    exact reads
  · intro reads
    exact ⟨result, rfl, reads⟩

theorem link_reads (g : MClosed) : Reads L7 result g ↔ Reads L3 linked g := by
  have e7 : EntailsEq L7 result (tuple [sym "pair", w, C2]) := by
    intro X target σ solved
    have e : instantiate σ u6 = instantiate σ C2 := solved (u6, C2) (by simp [L7])
    show tupleAt [symAt "pair", instantiate σ w, instantiate σ u6] =
      tupleAt [symAt "pair", instantiate σ w, instantiate σ C2]
    rw [e]
  have e6 : EntailsEq L6 (tuple [sym "pair", w, C2])
      (tuple [sym "pair", w, tuple [sym "k2", S0b, S1b, w]]) := by
    intro X target σ solved
    have e : instantiate σ S2b = instantiate σ w := solved (S2b, w) (by simp [L6])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ S0b, instantiate σ S1b, instantiate σ S2b]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ S0b, instantiate σ S1b, instantiate σ w]]
    rw [e]
  have e5 : EntailsEq L5 (tuple [sym "pair", w, tuple [sym "k2", S0b, S1b, w]])
      (tuple [sym "pair", w, tuple [sym "k2", S0b, sym "d", w]]) := by
    intro X target σ solved
    have e : instantiate σ S1b = instantiate σ (sym "d") := solved (S1b, sym "d") (by simp [L5])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ S0b, instantiate σ S1b, instantiate σ w]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ S0b, instantiate σ (sym "d"), instantiate σ w]]
    rw [e]
  have e4 : EntailsEq L4 (tuple [sym "pair", w, tuple [sym "k2", S0b, sym "d", w]]) linked := by
    intro X target σ solved
    have e : instantiate σ S0b = instantiate σ (sym "c") := solved (S0b, sym "c") (by simp [L4])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ S0b, instantiate σ (sym "d"), instantiate σ w]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ (sym "c"), instantiate σ (sym "d"), instantiate σ w]]
    rw [e]
  rw [reads_of_entails e7, show L7 = L6 ++ [(foD [6] [3, 2] 0, C2)] from rfl,
    reads_drop_fresh [6] [3, 2] 0 (by decide) (by decide) (by decide),
    reads_of_entails e6, show L6 = L5 ++ [(foD [5] [2, 0, 2] 0, w)] from rfl,
    reads_drop_fresh [5] [2, 0, 2] 0 (by decide) (by decide) (by decide),
    reads_of_entails e5, show L5 = L4 ++ [(foD [4] [2, 0, 1] 0, sym "d")] from rfl,
    reads_drop_fresh [4] [2, 0, 1] 0 (by decide) (by decide) (by decide),
    reads_of_entails e4, show L4 = L3 ++ [(foD [3] [2, 0, 0] 0, sym "c")] from rfl,
    reads_drop_fresh [3] [2, 0, 0] 0 (by decide) (by decide) (by decide)]

theorem capture_reads (g : MClosed) : Reads M7 result g ↔ Reads L3 linked g := by
  have e7 : EntailsEq M7 result (tuple [sym "pair", w, C2']) := by
    intro X target σ solved
    have e : instantiate σ u6 = instantiate σ C2' := solved (u6, C2') (by simp [M7])
    show tupleAt [symAt "pair", instantiate σ w, instantiate σ u6] =
      tupleAt [symAt "pair", instantiate σ w, instantiate σ C2']
    rw [e]
  have e6 : EntailsEq M6 (tuple [sym "pair", w, C2'])
      (tuple [sym "pair", w, tuple [sym "k2", U0b, U1b, S1a]]) := by
    intro X target σ solved
    have e : instantiate σ U2b = instantiate σ S1a := solved (U2b, S1a) (by simp [M6])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ U0b, instantiate σ U1b, instantiate σ U2b]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ U0b, instantiate σ U1b, instantiate σ S1a]]
    rw [e]
  have e5 : EntailsEq M5 (tuple [sym "pair", w, tuple [sym "k2", U0b, U1b, S1a]])
      (tuple [sym "pair", w, tuple [sym "k2", U0b, sym "d", S1a]]) := by
    intro X target σ solved
    have e : instantiate σ U1b = instantiate σ (sym "d") := solved (U1b, sym "d") (by simp [M5])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ U0b, instantiate σ U1b, instantiate σ S1a]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ U0b, instantiate σ (sym "d"), instantiate σ S1a]]
    rw [e]
  have e4 : EntailsEq M4 (tuple [sym "pair", w, tuple [sym "k2", U0b, sym "d", S1a]])
      (tuple [sym "pair", w, tuple [sym "k2", sym "c", sym "d", S1a]]) := by
    intro X target σ solved
    have e : instantiate σ U0b = instantiate σ (sym "c") := solved (U0b, sym "c") (by simp [M4])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ U0b, instantiate σ (sym "d"), instantiate σ S1a]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ (sym "c"), instantiate σ (sym "d"), instantiate σ S1a]]
    rw [e]
  have e3 : EntailsEq L3 (tuple [sym "pair", w, tuple [sym "k2", sym "c", sym "d", S1a]]) linked := by
    intro X target σ solved
    have e : instantiate σ S1a = instantiate σ w := solved (S1a, w) (by simp [L3, L2])
    show tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ (sym "c"), instantiate σ (sym "d"), instantiate σ S1a]] =
      tupleAt [symAt "pair", instantiate σ w,
        tupleAt [symAt "k2", instantiate σ (sym "c"), instantiate σ (sym "d"), instantiate σ w]]
    rw [e]
  rw [reads_of_entails e7, show M7 = M6 ++ [(foD [6] [3, 2] 0, C2')] from rfl,
    reads_drop_fresh [6] [3, 2] 0 (by decide) (by decide) (by decide),
    reads_of_entails e6, show M6 = M5 ++ [(foD [5] [2, 1, 2] 0, S1a)] from rfl,
    reads_drop_fresh [5] [2, 1, 2] 0 (by decide) (by decide) (by decide),
    reads_of_entails e5, show M5 = M4 ++ [(foD [4] [2, 1, 1] 0, sym "d")] from rfl,
    reads_drop_fresh [4] [2, 1, 1] 0 (by decide) (by decide) (by decide),
    reads_of_entails e4, show M4 = L3 ++ [(foD [3] [2, 1, 0] 0, sym "c")] from rfl,
    reads_drop_fresh [3] [2, 1, 0] 0 (by decide) (by decide) (by decide), reads_of_entails e3]

theorem finalLink_finished : Branch.Finished (D := D) finalLink := ⟨rfl, _, rfl⟩
theorem finalCapture_finished : Branch.Finished (D := D) finalCapture := ⟨rfl, _, rfl⟩

/-- **The two choices agree**: a well-formed program and query, read hygienically; at the second
`run` two principal solutions give two different texts; the runs through both end, each with one
finished live alternative, and the two bags of answers are equal. -/
theorem choices_agree :
    WellFormed program ∧ QueryWellFormed program [3] query ∧ ReadingHygienic program.reflect ∧
      Principal L3 θlink ∧ Principal L3 θcapture ∧ instantiate θlink T2a ≠ instantiate θcapture T2a ∧
      Runs D program supply start ⟨W 7, {finalLink}⟩ ∧ Runs D program supply start ⟨W 7, {finalCapture}⟩ ∧
      Config.Quiescent (D := D) program supply ⟨W 7, {finalLink}⟩ ∧
      Config.Quiescent (D := D) program supply ⟨W 7, {finalCapture}⟩ ∧
      Config.answers (D := D) (⟨W 7, {finalLink}⟩ : Config mkeys [] () MTy) =
        Config.answers (D := D) (⟨W 7, {finalCapture}⟩ : Config mkeys [] () MTy) := by
  refine ⟨program_wellFormed, query_wellFormed, program_hygienic, principal_link, principal_capture,
    texts_differ, runs_link, runs_capture, Config.quiescent_single, Config.quiescent_single, ?_⟩
  rw [answers_singleton (D := D) finalLink_finished L7_live,
    answers_singleton (D := D) finalCapture_finished M7_live]
  refine congrArg (fun s : Set MClosed => ({s} : Multiset (Set MClosed))) ?_
  show Branch.answer (D := D) (⟨L7, .value result, [], []⟩ : Branch mkeys [] () MTy) =
    Branch.answer (D := D) (⟨M7, .value result, [], []⟩ : Branch mkeys [] () MTy)
  rw [answer_eq_reads, answer_eq_reads]
  ext g
  exact (link_reads g).trans (capture_reads g).symm

/-- **The second text, read under the capture choice, is left alone by its code's arrow at `[2,1,1]`**
(an instance of `Hygiene.opening_fixes_text`): opening that site at scope `4`, where the positional
reading renamed `S1a`, leaves `(k2 c d S1a)` as it is. -/
theorem capture_text_fixed :
    instantiate (openAt mkeys [2, 1, 1] 4) (tuple [sym "k2", sym "c", sym "d", S1a]) =
      tuple [sym "k2", sym "c", sym "d", S1a] :=
  opening_fixes_text program_hygienic _ (by decide) 4

/-- **The two dereferenced texts are instances of each other and entailed equal** (an instance of
`Hygiene.principal_texts`). -/
theorem texts_mutual :
    instantiate θcapture (instantiate θlink T2a) = instantiate θcapture T2a ∧
      instantiate θlink (instantiate θcapture T2a) = instantiate θlink T2a ∧
      EntailsEq L3 (instantiate θlink T2a) (instantiate θcapture T2a) :=
  principal_texts principal_link principal_capture T2a

/-- **The invariant on this run**: every alternative of the configuration the capture choice reaches
has uniform binders (an instance of `Hygiene.uniform_along_runs`). -/
theorem uniform_on_run :
    ∀ b ∈ (⟨W 7, {finalCapture}⟩ : Config mkeys [] () MTy).branches, BranchUniform b :=
  uniform_along_runs program_wellFormed query_wellFormed program_hygienic.uniform (fun _ => 0) runs_capture

#print axioms reads_drop_fresh
#print axioms capture_text_fixed
#print axioms texts_mutual
#print axioms uniform_on_run
#print axioms runs_link
#print axioms runs_capture
#print axioms capture_store_linked
#print axioms choices_agree

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleCaptureRepaired
