import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Firings

/-!
# The generated possibility of the presented program is the firing possibility of its step

For a program of the positive fragment over ground rows, presented as a language definition with one
premise-free rewrite per rule (`present`), the framework's derived possibility modality
(`TypeSynthesis.langDiamondUsing`, OSLF's diamond over the reduction span of the presented language) at the
store of a configuration holds of a property exactly when some admitted firing of the step of the program
leads to a configuration whose store has the property.

* `generated_possibility_iff`: on the step of the program as a set of ground rule instances
  (`ProgramAdequacy.program ground`), for every configuration with trivial knowledge and every
  equation-invariant property, given fresh identities for every label.
* `pulled_back_diamond_iff`: the same in OSLF's form, as derived diamonds: the generated diamond pulled back
  along the store map is the derived diamond of the step's own firing span (`StepSpan.firingSpan`) of the
  pulled-back property. Unlike the earlier presentation (`PresentationMeetsStep.diamond_meets_step`) there
  is no span of choices between them and no premise that asks the step.
* `generated_possibility_keeping`: the same for `RuleSyntax.step`, through the one-frame instance: the
  label-keeping step of the program (`OneFrame.keeping`), by `RuleInstanceSets.instanceSet_eq` and
  `FirstOrderEq.firstOrder_eq`.
* `present_premises`: no rewrite of the presentation has a premise.

## Examples and controls (`Examples`)

* Inside and outside the fragment: `demo_positive`; `spawn_outside`, `countOne_outside`,
  `withCollect_outside`; a rule with a failing ground guard has no rewrite (`refused_not_presented`).
* **Existence**: at the store holding one token `1` the generated possibility of "the store is `{2}`" holds,
  and the step fires there (`possibility_holds`); at the empty store no generated possibility holds and the
  step does not fire (`possibility_fails`).
* **The knowledge hypothesis is needed** (`inconsistent_control`): beside an equation `sym 0 = sym 1` the
  presented language still steps, and the step fires nothing.
* **Reading reads without repetition is needed** (`naive_control`): a rule reading the row `7` twice fires on
  one copy of `7`; the naive reading, one row per read, presents no step there.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis (langDiamondUsing langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate saturatePredicate)
open Mettapedia.OSLF.Framework.DerivedModalities (derivedDiamond pb)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground Occ Conf)
open LogicOverTheStep.ProgramAdequacy (program program_succ_iff Supply occSupply)
open LogicOverTheStep.StepSpan (Succ firingSpan)
open OneFrame (bodies embed keeping)

universe uO

/-! ## Stores of configurations and of states -/

section Stores

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

/-- **The store of a configuration**: the bag of the codes of its present rows. -/
noncomputable def storeOf (C : Configuration Expr O) : Pattern := storeCode (C.present.toList.map label)

/-- **The store of a state of `RuleSyntax.step`** at the one frame: the bag of the codes of its present rows,
under the state's labels. -/
noncomputable def stateStore (s : State Rows O) : Pattern := storeCode (s.present.toList.map s.label)

omit [DecidableEq O] in
theorem stateStore_embed (C : Configuration Expr O) : stateStore (embed label C) = storeOf label C := rfl

omit [DecidableEq O] in
theorem coe_rows (C : Configuration Expr O) :
    ((C.present.toList.map label : List Expr) : Multiset Expr) = bagOf label C := by
  rw [← Multiset.map_coe, Finset.coe_toList]
  rfl

end Stores

/-! ## The theorem -/

variable {O : Type uO} [DecidableEq O] (label : O → Expr) {rules : List (Rule Rows)} {relEnv : RelationEnv}

/-- **No rewrite of the presentation has a premise**: none asks the step. -/
theorem present_premises : ∀ rule ∈ (present rules).rewrites, rule.premises = [] :=
  fun rule member => (presentWith_plain rule member).1

/-- **The generated possibility is the firing possibility**: for a program of the positive fragment, at the
store of a configuration with trivial knowledge, the framework's derived possibility of an equation-invariant
property holds exactly when some admitted firing of the step of the program reaches a configuration whose
store has the property. -/
theorem generated_possibility_iff (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C : Configuration Expr O} (knowledge : Trivial C.equations)
    (φ : EquationPredicate (langGSLTUsing relEnv (present rules))) :
    (langDiamondUsing relEnv (present rules) φ).1 (storeOf label C) ↔
      ∃ C', Succ (program ground label (bodies {r | r ∈ rules})) C C' ∧ φ.1 (storeOf label C') := by
  refine (diamond_storeCode_iff φ _).trans ?_
  constructor
  · rintro ⟨r, member, holds, rest, split, satisfied⟩
    have bag : ((consumes r : List Expr) : Multiset Expr) + (rest : Multiset Expr) = bagOf label C := by
      rw [Multiset.coe_add, ← coe_rows label C]
      exact Multiset.coe_eq_coe.mpr split
    obtain ⟨C', step, after⟩ := succ_of_bag label supply member (positive r member) holds knowledge bag
    refine ⟨C', step, (φ.2 ?_).mp satisfied⟩
    refine equationEquiv_storeCode_of_perm presentWith_formers presentWith_store (Multiset.coe_eq_coe.mp ?_)
    rw [← Multiset.coe_add, coe_rows, after]
    rfl
  · rintro ⟨C', step, satisfied⟩
    obtain ⟨r, member, holds, rest, before, after, -⟩ := succ_bag label step
    have before' : ((standard.consumed r : List Expr) : Multiset Expr) + rest = bagOf label C := before
    have after' : bagOf label C' = ((standard.yielded r : List Expr) : Multiset Expr) + rest := after
    refine ⟨r, member, holds, rest.toList, ?_, (φ.2 ?_).mpr satisfied⟩
    · refine Multiset.coe_eq_coe.mp ?_
      rw [← Multiset.coe_add, Multiset.coe_toList, before', coe_rows]
    · refine equationEquiv_storeCode_of_perm presentWith_formers presentWith_store (Multiset.coe_eq_coe.mp ?_)
      rw [← Multiset.coe_add, Multiset.coe_toList, coe_rows, after']

/-- **In OSLF's form**: the generated diamond, pulled back along the store map, is the derived diamond of the
step's own firing span of the pulled-back property, at every configuration with trivial knowledge. No span of
choices stands between them. -/
theorem pulled_back_diamond_iff (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C : Configuration Expr O} (knowledge : Trivial C.equations)
    (φ : EquationPredicate (langGSLTUsing relEnv (present rules))) :
    pb (storeOf label) (langDiamondUsing relEnv (present rules) φ).1 C ↔
      derivedDiamond (firingSpan (program ground label (bodies {r | r ∈ rules}))) (pb (storeOf label) φ.1) C := by
  refine (generated_possibility_iff label supply positive knowledge φ).trans ?_
  constructor
  · rintro ⟨C', ⟨f, admitted, rfl⟩, holds⟩
    exact ⟨⟨C, f, admitted⟩, rfl, holds⟩
  · rintro ⟨⟨_, f, admitted⟩, rfl, holds⟩
    exact ⟨_, ⟨f, admitted, rfl⟩, holds⟩

/-- **The same for `RuleSyntax.step`**, through the one-frame instance: at the embedded state of a configuration
with trivial knowledge, the generated possibility holds exactly when some admitted label-keeping firing of the
step of the program reaches a state whose store has the property. -/
theorem generated_possibility_keeping (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C : Configuration Expr O} (knowledge : Trivial C.equations)
    (φ : EquationPredicate (langGSLTUsing relEnv (present rules))) :
    (langDiamondUsing relEnv (present rules) φ).1 (stateStore (embed label C)) ↔
      ∃ s', Succ (keeping ground {r | r ∈ rules}) (embed label C) s' ∧ φ.1 (stateStore s') := by
  refine (generated_possibility_iff label supply positive knowledge φ).trans ?_
  have groundRules : ∀ r ∈ ({r | r ∈ rules} : Set (Rule Rows)), OneFrame.Ground ground r :=
    fun _ _ _ _ _ => rfl
  have noCollect : ∀ r ∈ ({r | r ∈ rules} : Set (Rule Rows)), r.collect = [] :=
    fun r member => (positive r member).1
  constructor
  · rintro ⟨C', step, holds⟩
    exact ⟨embed label C',
      (OneFrame.firstOrder_eq C C').mp ((OneFrame.instanceSet_eq groundRules noCollect C C').mp step), holds⟩
  · rintro ⟨s', step, holds⟩
    obtain ⟨C', rfl⟩ := OneFrame.keeping_closed C step
    exact ⟨C', (OneFrame.instanceSet_eq groundRules noCollect C C').mpr ((OneFrame.firstOrder_eq C C').mpr step),
      holds⟩

/-- A configuration from which the step fires has trivial knowledge. -/
theorem trivial_of_succ {C C' : Configuration Expr O}
    (step : Succ (program ground label (bodies {r | r ∈ rules})) C C') : Trivial C.equations := by
  obtain ⟨rule, sel, -, valid, -⟩ := (program_succ_iff ground label _ C C').mp step
  obtain ⟨σ, solved⟩ := valid.consistent
  exact (Selection.models_problem ground valid solved).1

#print axioms present_premises
#print axioms generated_possibility_iff
#print axioms pulled_back_diamond_iff
#print axioms generated_possibility_keeping
#print axioms trivial_of_succ

/-! ## Examples and controls -/

namespace Examples

/-- A rule over rows without collect patterns. -/
def rule (take read : List Expr) (tell : EquationStore Expr) (checks : List (Check Expr))
    (produce : List Expr) : Rule Rows :=
  ⟨PUnit.unit, ⟨take, read, tell, checks, produce⟩, []⟩

/-- Take the token `1`, make a `2`. -/
def consume : Rule Rows := rule [.sym 1] [] [] [] [.sym 2]

/-- Read a `2`, make a `3`. -/
def observe : Rule Rows := rule [] [.sym 2] [] [] [.sym 3]

/-- Take a `3` under the guard `4 = 4`, make a `5`. -/
def guarded : Rule Rows := rule [.sym 3] [] [] [.equal (.sym 4) (.sym 4)] [.sym 5]

/-- Take a `3` under the guard `4 = 5`, which fails. -/
def refused : Rule Rows := rule [.sym 3] [] [] [.equal (.sym 4) (.sym 5)] [.sym 6]

/-- Read the row `7` twice, make an `8`. -/
def readTwice : Rule Rows := rule [] [.sym 7, .sym 7] [] [] [.sym 8]

/-- **A program of the fragment.** -/
def demo : List (Rule Rows) := [consume, observe, guarded, refused, readTwice]

/-- Make a `12` where `11` is absent: an absence check. -/
def spawn : Rule Rows := rule [] [] [] [.predicate .none (.sym 11)] [.sym 12]

/-- Make a `12` where exactly one `11` is present: a count check. -/
def countOne : Rule Rows := rule [] [] [] [.count (.sym 11) 1] [.sym 12]

/-- A rule with a collect pattern. -/
def withCollect : Rule Rows := ⟨PUnit.unit, ⟨[], [], [], [], []⟩, [.sym 11]⟩

theorem demo_positive : ∀ r ∈ demo, Positive r := by decide

theorem spawn_outside : ¬ Positive spawn := by decide

theorem countOne_outside : ¬ Positive countOne := by decide

theorem withCollect_outside : ¬ Positive withCollect := by decide

/-- **One rewrite per rule whose guards hold**: four of the five rules. -/
theorem demo_rewrites : (present demo).rewrites.length = 4 := by decide

theorem refused_not_presented : guardsHold refused = false := by decide

/-- One token `1`. -/
def oneToken : Conf := ⟨[], {(.sym 1, 0)}⟩

/-- The empty store. -/
def emptyConf : Conf := ⟨[], ∅⟩

/-- The token `1` beside the unsolvable knowledge `sym 0 = sym 1`. -/
def inconsistent : Conf := ⟨[(.sym 0, .sym 1)], {(.sym 1, 0)}⟩

/-- One copy of the row `7`. -/
def oneSeven : Conf := ⟨[], {(.sym 7, 0)}⟩

/-- "The store is `{2}`", closed under the equations. -/
def isTwo (relEnv : RelationEnv) (rules : List (Rule Rows)) :
    EquationPredicate (langGSLTUsing relEnv (present rules)) :=
  saturatePredicate _ fun p => p = storeCode [.sym 2]

/-- Every term. -/
def everything (relEnv : RelationEnv) (L : LanguageDef) : EquationPredicate (langGSLTUsing relEnv L) :=
  ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩

theorem storeOf_oneToken : storeOf Prod.fst oneToken = storeCode [.sym 1] := by
  simp [storeOf, oneToken, Finset.toList_singleton]

theorem storeOf_emptyConf : storeOf Prod.fst emptyConf = storeCode [] := by
  simp [storeOf, emptyConf, Finset.toList_empty]

theorem storeOf_inconsistent : storeOf Prod.fst inconsistent = storeCode [.sym 1] := by
  simp [storeOf, inconsistent, Finset.toList_singleton]

theorem storeOf_oneSeven : storeOf Prod.fst oneSeven = storeCode [.sym 7] := by
  simp [storeOf, oneSeven, Finset.toList_singleton]

theorem consume_member : consume ∈ demo := List.mem_cons_self

/-- **Existence, positive**: at one token `1`, the generated possibility of "the store is `{2}`" holds, and so
the step of the program fires there. -/
theorem possibility_holds :
    (langDiamondUsing relEnv (present demo) (isTwo relEnv demo)).1 (storeOf Prod.fst oneToken) ∧
      ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ demo})) oneToken C' := by
  have holds : (langDiamondUsing relEnv (present demo) (isTwo relEnv demo)).1 (storeOf Prod.fst oneToken) := by
    rw [storeOf_oneToken]
    exact (diamond_storeCode_iff _ _).mpr ⟨consume, consume_member, by decide, [], by decide,
      ⟨_, Relation.EqvGen.refl _, rfl⟩⟩
  obtain ⟨C', step, -⟩ := (generated_possibility_iff Prod.fst occSupply demo_positive
    (C := oneToken) (fun _ member => absurd member List.not_mem_nil) (isTwo relEnv demo)).mp holds
  exact ⟨holds, C', step⟩

/-- **Existence, negative**: at the empty store no generated possibility holds, and the step does not fire. -/
theorem possibility_fails :
    ¬ (langDiamondUsing relEnv (present demo) (everything relEnv (present demo))).1 (storeOf Prod.fst emptyConf) ∧
      ¬ ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ demo})) emptyConf C' := by
  have none : ¬ (langDiamondUsing relEnv (present demo) (everything relEnv (present demo))).1
      (storeOf Prod.fst emptyConf) := by
    rw [storeOf_emptyConf]
    intro possible
    obtain ⟨r, member, -, rest, split, -⟩ := (diamond_storeCode_iff _ _).mp possible
    have consumedEmpty := (List.append_eq_nil_iff.mp split.eq_nil).1
    simp only [demo, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact absurd consumedEmpty (by decide)
  refine ⟨none, ?_⟩
  rintro ⟨C', step⟩
  exact none ((generated_possibility_iff Prod.fst occSupply demo_positive (C := emptyConf)
    (fun _ member => absurd member List.not_mem_nil) (everything relEnv (present demo))).mpr ⟨C', step, trivial⟩)

/-- **Control: the knowledge hypothesis is needed.** Beside the unsolvable `sym 0 = sym 1`, the presented
language still steps from the store of the token `1`, and the step of the program fires nothing. -/
theorem inconsistent_control :
    (langDiamondUsing relEnv (present demo) (everything relEnv (present demo))).1 (storeOf Prod.fst inconsistent) ∧
      ¬ ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ demo})) inconsistent C' := by
  refine ⟨?_, ?_⟩
  · rw [storeOf_inconsistent]
    exact (diamond_storeCode_iff _ _).mpr ⟨consume, consume_member, by decide, [], by decide, trivial⟩
  · rintro ⟨C', step⟩
    have knowledge := trivial_of_succ Prod.fst step
    exact absurd (knowledge (.sym 0, .sym 1) List.mem_cons_self) (by decide)

theorem consumes_readTwice : consumes readTwice = [.sym 7] := by decide

/-- **Control: reads are read without repetition.** The rule reading `7` twice fires on one copy of `7`, and so
the presented language steps there; under the naive reading, one row per read, it does not. -/
theorem naive_control :
    (∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ [readTwice]})) oneSeven C') ∧
      (langDiamondUsing relEnv (present [readTwice]) (everything relEnv (present [readTwice]))).1
        (storeOf Prod.fst oneSeven) ∧
      ¬ (langDiamondUsing relEnv (presentWith naive [readTwice])
          (everything relEnv (presentWith naive [readTwice]))).1 (storeOf Prod.fst oneSeven) := by
  refine ⟨?_, ?_, ?_⟩
  · have split : ((consumes readTwice : List Expr) : Multiset Expr) + 0 = bagOf Prod.fst oneSeven := by
      rw [add_zero, consumes_readTwice]
      rfl
    obtain ⟨C', step, -⟩ := succ_of_bag Prod.fst occSupply (rules := [readTwice]) List.mem_cons_self (by decide)
      (by decide) (C := oneSeven) (fun _ member => absurd member List.not_mem_nil) split
    exact ⟨C', step⟩
  · rw [storeOf_oneSeven]
    exact (diamond_storeCode_iff _ _).mpr ⟨readTwice, List.mem_cons_self, by decide, [], by decide, trivial⟩
  · rw [storeOf_oneSeven]
    intro possible
    obtain ⟨r, member, -, rest, split, -⟩ := (diamond_storeCode_iff _ _).mp possible
    rw [List.mem_singleton] at member
    subst member
    have lengths := split.length_eq
    simp only [naive, readTwice, rule, List.nil_append, List.length_append, List.length_cons, List.length_nil]
      at lengths
    omega

#print axioms demo_positive
#print axioms demo_rewrites
#print axioms possibility_holds
#print axioms possibility_fails
#print axioms inconsistent_control
#print axioms naive_control

end Examples

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
