import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawExtension

/-!
# Adding an equation: held as data changes nothing, held as code changes the bag

The new equation is `(= (h $x) done)`. The program has no other equation.

* **Held as data**: the query returns the text `(h 1)`. The law's condition holds (the program calls
  nothing and runs no text), so the law applies (`data_condition`), and the bag is `{(h 1)}` with or
  without the equation (`data_without`, `data_with`).
* **Held as code** (the control): the query runs the text `(h 1)`. Without the equation the call is
  unmatched and the bag is `{(h 1)}` (`code_without`); with it the bag is `{done}` (`code_with`).
* **The syntactic condition for MeTTa text** (`separated_of_heads`): a call whose head symbol differs
  from the head of the new equation's left-hand side is separated from it. With it the law applies to
  the call `(g (h 1))`, which holds `h` as data (`call_condition`), and the bag is `{(g (h 1))}` with or
  without the equation (`call_without`, `call_with`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit Extension

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def P : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def e : Equation mkeys [] () MTy := ⟨[100], tuple [sym "h", foD [] [100] 0], .ret (sym "done")⟩

def text : MData := tuple [sym "h", num 1]
def supply : ℕ → MClosed := fun _ => csym "space"

def hOne : MClosed := ctuple [csym "h", cnum 1]

theorem text_determines : Determines ([] : List (Constraint mkeys [] ())) text hOne :=
  ⟨live_nil, fun _ _ _ => rfl⟩

/-! ## Held as data -/

def dataQuery : Comp mkeys [] () MTy := .ret text

theorem data_condition : ProgramApart (D := D) P e ∧
    Related (D := D) e (Config.initial (fun _ => 0) dataQuery) (Config.initial (fun _ => 0) dataQuery) := by
  refine ⟨fun e' member => (by cases member), rfl, ⟨0, (add_zero _).symm, by simp⟩, ?_⟩
  intro b member
  rw [Multiset.mem_singleton.mp member]
  exact ⟨fun c same => (by simp only [Focus.eval.injEq] at same; subst same; trivial),
    fun _ _ _ member' => (by cases member'), fun _ member' => (by cases member')⟩

def dataFinal : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value text, [], []⟩}⟩

theorem data_answers : Config.answers (D := D) dataFinal = {{hOne}} := by
  have bag := answers_singleton (D := D) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value text, [], []⟩)
    ⟨rfl, _, rfl⟩ live_nil
  rw [answer_of_determines rfl text_determines] at bag
  exact bag

theorem data_without : Runs D P supply (Config.initial (fun _ => 0) dataQuery) dataFinal ∧
    Config.Quiescent (D := D) P supply dataFinal ∧ Config.answers (D := D) dataFinal = {{hOne}} :=
  ⟨Relation.ReflTransGen.single (step_one live_nil (.ret _ _ _ _ _)), Config.quiescent_single, data_answers⟩

theorem data_with : Runs D (extend P e) supply (Config.initial (fun _ => 0) dataQuery) dataFinal ∧
    Config.Quiescent (D := D) (extend P e) supply dataFinal ∧ Config.answers (D := D) dataFinal = {{hOne}} :=
  ⟨Relation.ReflTransGen.single (step_one live_nil (.ret _ _ _ _ _)), Config.quiescent_single, data_answers⟩

/-! ## Held as code: the control -/

def codeQuery : Comp mkeys [] () MTy := .run text

theorem principal_nil : Principal ([] : List (Constraint mkeys [] ())) (generator (fam mkeys)) :=
  ⟨fun _ member => (by cases member), fun _ σ _ name => instantiate_generator σ name⟩

def codeFinalWithout : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value text, [], []⟩}⟩

theorem code_without : Runs D P supply (Config.initial (fun _ => 0) codeQuery) codeFinalWithout ∧
    Config.Quiescent (D := D) P supply codeFinalWithout ∧ Config.answers (D := D) codeFinalWithout = {{hOne}} := by
  refine ⟨?_, Config.quiescent_single, data_answers⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.apply text), [], []⟩}⟩) ?_
    (step_one live_nil (.unmatched _ _ _ _ _ (fun e' member => (by cases member))))
  exact Relation.ReflTransGen.single (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_nil))

def doneStore : List (Constraint mkeys [] ()) := [] ++ [(instantiate (copyAt mkeys 0) e.lhs, text)]

def closeDone : Assignment (fam mkeys) noNames := closeNames [(([0], [100], 0), cnum 1)] (csym "a")

theorem doneStore_live : Solvable doneStore := ⟨Empty, noNames, closeDone, by decide⟩

def codeFinalWith : Config mkeys [] () MTy :=
  ⟨⟨1, 0, fun _ => 0⟩, {⟨doneStore, .value (instantiate (copyAt mkeys 0) (sym "done")), [], []⟩}⟩

theorem code_with : Runs D (extend P e) supply (Config.initial (fun _ => 0) codeQuery) codeFinalWith ∧
    Config.Quiescent (D := D) (extend P e) supply codeFinalWith ∧
    Config.answers (D := D) codeFinalWith = {{csym "done"}} := by
  refine ⟨?_, Config.quiescent_single, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
        {⟨doneStore, .eval (.ret (instantiate (copyAt mkeys 0) (sym "done"))), [], []⟩}⟩) ?_
      (step_one doneStore_live (.ret _ _ _ _ _))
    refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.apply text), [], []⟩}⟩) ?_
      (Step.of_eq (D := D) (P := extend P e) (supply := supply) (rest := 0) rfl rfl live_nil
        (.apply ⟨0, 0, fun _ => 0⟩ [] text [] [] ⟨e, List.mem_singleton_self _, doneStore_live⟩))
    exact Relation.ReflTransGen.single (step_one live_nil (.run _ _ _ _ _ (generator (fam mkeys)) principal_nil))
  · have bag := answers_singleton (D := D) (w := ⟨1, 0, fun _ => 0⟩)
      (b := ⟨doneStore, .value (instantiate (copyAt mkeys 0) (sym "done")), [], []⟩) ⟨rfl, _, rfl⟩ doneStore_live
    rw [answer_of_determines (g := csym "done") rfl ⟨doneStore_live, fun _ _ _ => rfl⟩] at bag
    exact bag

/-! ## The syntactic condition for MeTTa text -/

/-- The symbol at the head of a tuple's elements, if any. -/
def firstSym {X : Type} {target : X → MetaArity MSig} :
    {as : List (List Unit × Unit)} → Args (signature MSig target) as [] → Option String
  | _, .nil => none
  | _, .cons (.op (.inl (.sym f)) _) _ => some f
  | _, .cons _ _ => none

/-- The head symbol of a tuple, if any. -/
def headSym {X : Type} {target : X → MetaArity MSig} : Term (signature MSig target) [] () → Option String
  | .op (.inl (.tup _)) args => firstSym args
  | _ => none

/-- **The syntactic condition**: a call whose head is a symbol other than the head of `e`'s
left-hand side is separated from `e`, whatever the rest of either holds. -/
theorem separated_of_heads {D' : Discipline MSig [] ()} (e' : Equation mkeys [] () D'.Ty) {f g : String}
    {args args' : List MData} (lhs : e'.lhs = tuple (sym g :: args')) (different : f ≠ g) :
    Separated e' (tuple (sym f :: args)) := by
  intro n X target σ σ' same
  rw [lhs] at same
  have heads := congrArg headSym same
  have one : headSym (instantiate σ (tuple (sym f :: args))) = some f := rfl
  have two : headSym (instantiate σ' (instantiate (copyAt mkeys n) (tuple (sym g :: args')))) = some g := rfl
  rw [one, two] at heads
  exact different (Option.some.inj heads)

/-! ## A call beside held data: the condition holds by the heads -/

/-- The query `(g (h 1))`: a call whose head is `g`, holding the new equation's head `h` as data. -/
def gText : MData := tuple [sym "g", text]
def callQuery : Comp mkeys [] () MTy := .apply gText
def gClosed : MClosed := ctuple [csym "g", hOne]

theorem call_condition : ProgramApart (D := D) P e ∧
    BranchApart (D := D) e (⟨[], .eval callQuery, [], []⟩ : Branch mkeys [] () MTy) := by
  refine ⟨fun e' member => (by cases member), fun c same => ?_, fun _ _ _ member => (by cases member),
    fun _ member => (by cases member)⟩
  simp only [Focus.eval.injEq] at same
  subst same
  exact separated_of_heads (D' := D) e (f := "g") (g := "h") (args := [text]) (args' := [foD [] [100] 0])
    rfl (by decide)

def callFinal : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value gText, [], []⟩}⟩

theorem call_answers : Config.answers (D := D) callFinal = {{gClosed}} := by
  have bag := answers_singleton (D := D) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value gText, [], []⟩)
    ⟨rfl, _, rfl⟩ live_nil
  rw [answer_of_determines (g := gClosed) rfl ⟨live_nil, fun _ _ _ => rfl⟩] at bag
  exact bag

/-- Without the equation, `(g (h 1))` is unmatched: the bag is `{(g (h 1))}`. -/
theorem call_without : Runs D P supply (Config.initial (fun _ => 0) callQuery) callFinal ∧
    Config.Quiescent (D := D) P supply callFinal ∧ Config.answers (D := D) callFinal = {{gClosed}} :=
  ⟨Relation.ReflTransGen.single (step_one live_nil (.unmatched _ _ _ _ _ (fun e' member => by cases member))),
    Config.quiescent_single, call_answers⟩

/-- With the equation, the same bag: the new equation's alternative is dead. -/
theorem call_with : Runs D (extend P e) supply (Config.initial (fun _ => 0) callQuery) callFinal ∧
    Config.Quiescent (D := D) (extend P e) supply callFinal ∧ Config.answers (D := D) callFinal = {{gClosed}} := by
  refine ⟨Relation.ReflTransGen.single (step_one live_nil (.unmatched _ _ _ _ _ fun e' member => ?_)),
    Config.quiescent_single, call_answers⟩
  simp only [Extension.extend, P, List.nil_append, List.mem_singleton] at member
  subst member
  exact dead_new (separated_of_heads (D' := D) e (f := "g") (g := "h") (args := [text])
    (args' := [foD [] [100] 0]) rfl (by decide)) 0 []

/-- **The control**: the two bags differ. -/
theorem code_bags_differ : ({{hOne}} : Multiset (Set MClosed)) ≠ {{csym "done"}} := by
  intro same
  have := congrArg (fun m : Multiset (Set MClosed) => hOne ∈ (m.toList.headD ∅)) same
  have member : hOne ∈ ({hOne} : Set MClosed) := rfl
  have notMember : hOne ∉ ({csym "done"} : Set MClosed) := by
    intro h
    have := Set.mem_singleton_iff.mp h
    cases this
  have injective := Multiset.singleton_inj.mp same
  exact notMember (injective ▸ member)

#print axioms data_condition
#print axioms code_without
#print axioms code_with
#print axioms code_bags_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleExtension
