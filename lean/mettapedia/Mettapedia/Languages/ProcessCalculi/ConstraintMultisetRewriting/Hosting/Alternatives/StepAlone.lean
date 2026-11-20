import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls

/-!
# What the bag is a function of, and which equations count as distinct

* `bag_from_step`: `bag_of_rule_classes` with its right side written with the translated program, the
  start state and the identity of the query's row only (`CompleteWord`, `FinishedWord`, `wordAnswer`
  mention no source program). `counted_once_unique`: the multiset that counts each complete word once
  is unique, so the right side is a function of those three.
* The hypotheses stay hypotheses on a source program: the translation is not injective
  (`same_translation_two_bags`: one translated program, two source programs, bags `{one, one}` and
  `{one}`).
* `same_word_same_answer` does not ask for a plain program: the two rules of `let` are rules of every
  translation (`let_rules_translated`), and two histories with one word of rules show the same answer
  whether or not that word has them (`let_words_same_answer`).
* `two_sites_distinct`: the equation `(= (f x) x)` written at two sites, each with its variable named
  at its own site, has two different schemas; the hypothesis of distinct schemas holds of that
  program of two equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.StepAlone

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

section StepAlone

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)

/-- No firing of the program at the state. -/
def Stuck (Prog : CProgram S) (s : HostState S) : Prop :=
  ∀ f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame,
    ¬ f.Admits (Interface.Frames.contextual S) s

/-- A word of rules that some history from the start follows to a state with no firing. -/
def CompleteWord (Prog : CProgram S) (s₀ : HostState S) (a₀ : ℕ) (word : List (CRule S)) : Prop :=
  ∃ s a, Chain (FiresAt Prog) s₀ a₀ word s a ∧ Stuck Prog s

/-- A word of rules that some history follows to a finished state. -/
def FinishedWord (Prog : CProgram S) (s₀ : HostState S) (a₀ : ℕ) (word : List (CRule S)) : Prop :=
  ∃ s a, Chain (FiresAt Prog) s₀ a₀ word s a ∧ StateFinished N s a

/-- What the last states of the histories of a word show. -/
def wordAnswer (Prog : CProgram S) (s₀ : HostState S) (a₀ : ℕ) (word : List (CRule S)) :
    Set (Term S Γ star) :=
  {g | ∃ s a, Chain (FiresAt Prog) s₀ a₀ word s a ∧ g ∈ stateAnswer N s a}

omit N in
/-- **The multiset that counts each complete word once is unique.** -/
theorem counted_once_unique (Prog : CProgram S) (s₀ : HostState S) (a₀ : ℕ)
    {M M' : Multiset (List (CRule S))}
    (h : ∀ w, M.count w = if CompleteWord Prog s₀ a₀ w then 1 else 0)
    (h' : ∀ w, M'.count w = if CompleteWord Prog s₀ a₀ w then 1 else 0) : M = M' :=
  Multiset.ext.mpr fun w => (h w).trans (h' w).symm

variable {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

theorem terminal_iff_stuck (s : HostState S) : Terminal N P s ↔ Stuck (translate N P) s :=
  ⟨fun terminal f admitted => terminal _ ⟨f, admitted, rfl⟩,
    fun stuck _ ⟨f, admitted, _⟩ => stuck f admitted⟩

/-- **`bag_of_rule_classes` with its right side a function of the translated program, the start state
and the identity of the query's row.** The hypotheses are those of `bag_of_rule_classes`: they speak
of the source program and of a source run that ends. -/
theorem bag_from_step (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (distinct : (P.equations.map (schema N)).Nodup) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List (CRule S)),
      (∀ word, M.count word =
        if CompleteWord (translate N P) (start N P q) P.equations.length word then 1 else 0) ∧
        C.answers (D := D) =
          (M.filter (FinishedWord N (translate N P) (start N P q) P.equations.length)).map
            (wordAnswer N (translate N P) (start N P q) P.equations.length) := by
  obtain ⟨M, count, answers⟩ := bag_of_rule_classes N spaces q plainP plainQ unopened distinct runs quiet
  refine ⟨M, fun word => ?_, answers⟩
  rw [count word]
  have same : CompleteRuleClass N P q word ↔
      CompleteWord (translate N P) (start N P q) P.equations.length word :=
    ⟨fun ⟨s, a, reached, terminal⟩ => ⟨s, a, reached, (terminal_iff_stuck N s).mp terminal⟩,
      fun ⟨s, a, reached, stuck⟩ => ⟨s, a, reached, (terminal_iff_stuck N s).mpr stuck⟩⟩
  by_cases complete : CompleteRuleClass N P q word
  · rw [if_pos complete, if_pos (same.mp complete)]
  · rw [if_neg complete, if_neg fun c => complete (same.mpr c)]

/-- **The two rules of `let` are rules of every translation.** -/
theorem let_rules_translated {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) :
    bindStartRule N ∈ translate N P ∧ bindValueRule N ∈ translate N P :=
  ⟨(mem_translate N).mpr (Or.inl ((mem_controlRules N).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    (mem_translate N).mpr (Or.inl ((mem_controlRules N).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))⟩

/-- **A word of rules determines the answer for every program of the source**, with `let` or without:
no hypothesis on the program or on the word. -/
theorem let_words_same_answer (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)
    {word : List (CRule S)} {s₁ s₂ : HostState S} {a₁ a₂ : ℕ}
    (chain₁ : Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s₁ a₁)
    (chain₂ : Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s₂ a₂) :
    stateAnswer N s₁ a₁ = stateAnswer N s₂ a₂ ∧ (StateFinished N s₁ a₁ ↔ StateFinished N s₂ a₂) :=
  same_word_same_answer N q chain₁ chain₂

/-- **The bag found so far, at every configuration a source run reaches**, whether or not the run
ends: distinct words of names, each with a history, whose finished ones give the configuration's bag
of answers. No hypothesis that the configuration is quiescent. -/
theorem partial_bag (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L : Multiset (List RuleName), L.Nodup ∧ (∀ w ∈ L, ∃ s a, NamedFrom N P q w s a) ∧
      C.answers (D := D) = (L.filter (FinishedClass N P q)).map (classAnswer N P q) := by
  obtain ⟨L, G, tracing⟩ := tracing_runs N spaces q plainP plainQ unopened runs
  have liveOf : ∀ x ∈ L, Solvable x.1.store := fun x member => by
    have inBranches : x.1 ∈ C.branches.filter (fun b => Solvable b.store) := by
      rw [← tracing.branches]; exact Multiset.mem_map_of_mem _ member
    exact (Multiset.mem_filter.mp inBranches).2
  have finishedIff : ∀ x ∈ L, FinishedClass N P q x.2 ↔ x.1.Finished (D := D) := by
    intro x member
    constructor
    · rintro ⟨s, a, reached, finished⟩
      exact ((finished_iff N (tracing.uniform x member s a reached)).mpr finished).1
    · intro finished
      obtain ⟨s, a, reached⟩ := tracing.reached x member
      exact ⟨s, a, reached,
        (finished_iff N (tracing.uniform x member s a reached)).mp ⟨finished, liveOf x member⟩⟩
  have answerAt : ∀ x ∈ L, x.1.Finished (D := D) → classAnswer N P q x.2 = x.1.answer (D := D) := by
    intro x member finished
    ext g
    constructor
    · rintro ⟨s, a, reached, shown⟩
      rw [answer_eq N (tracing.uniform x member s a reached) finished] at shown
      exact shown
    · intro answered
      obtain ⟨s, a, reached⟩ := tracing.reached x member
      refine ⟨s, a, reached, ?_⟩
      rw [answer_eq N (tracing.uniform x member s a reached) finished]
      exact answered
  refine ⟨L.map Prod.snd, (Multiset.nodup_add.mp tracing.nodup).1, fun w member => ?_, ?_⟩
  · obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp member
    exact tracing.reached x xMember
  · have split : C.branches.filter (fun b => b.Finished (D := D) ∧ Solvable b.store) =
        (C.branches.filter (fun b => Solvable b.store)).filter (fun b => b.Finished (D := D)) := by
      rw [Multiset.filter_filter]
    unfold Config.answers
    rw [split, ← tracing.branches, Multiset.filter_map, Multiset.map_map, Multiset.filter_map,
      Multiset.map_map]
    have sameFilter : L.filter ((fun b : Branch κ Γ star D.Ty => b.Finished (D := D)) ∘ Prod.fst) =
        L.filter (FinishedClass N P q ∘ Prod.snd) :=
      Multiset.filter_congr fun x member => (finishedIff x member).symm
    rw [sameFilter]
    apply Multiset.map_congr rfl
    intro x member
    obtain ⟨inL, finishedClass⟩ := Multiset.mem_filter.mp member
    exact (answerAt x inL ((finishedIff x inL).mp finishedClass)).symm

/-! ### Every history of every translated program is a chain -/

section Shape

variable {Ty : Type} (P' : SourceLanguage.Program κ Γ star Ty)

/-- **The shape of a state of a history**: the equation rows, and one more row. No alternative of the
source is mentioned. -/
structure Shaped (s : HostState S) (a : ℕ) : Prop where
  notRow : P'.equations.length ≤ a
  present : s.present = insert a (Finset.range P'.equations.length)
  rows : ∀ (B : Interface.Frames.Frame S) (σ : Assignment s.frame.arity B.arity),
    (Interface.Frames.contextual S).Models σ s.knowledge → ∀ (i : ℕ) (hi : i < P'.equations.length),
      ∃ θ : Assignment (fam κ) B.arity,
        instantiateObservation σ (s.label i) = eqnRow N (P'.equations.get ⟨i, hi⟩) θ

variable {P'}

/-- **A firing at a shaped state takes the one more row and makes one, and the result is shaped.**
For every rule of every translation: the two rules of `let` and the schemas of all equations
included. -/
theorem shaped_fires {s : HostState S} {a : ℕ} (shaped : Shaped N P' s a)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P') s.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) s) :
    ∃ a', f.selection.taken = [a] ∧ f.selection.made = [a'] ∧
      Shaped N P' (f.result (Interface.Frames.contextual S) s) a' := by
  obtain ⟨pat, out, simpleRule, altHead⟩ := translate_simple N f.member
  obtain ⟨shapes, enabled, solvable, _⟩ := admitted
  have shapes' := shapes
  obtain ⟨_, _, _, takeLen, readLen, prodLen, _⟩ := shapes
  rw [simpleRule.take] at takeLen
  rw [simpleRule.noRead] at readLen
  rw [simpleRule.produce] at prodLen
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp prodLen.symm
  have read : f.selection.read = [] := List.eq_nil_of_length_eq_zero readLen.symm
  have simple : Simple f o o' pat out :=
    ⟨taken, read, made, simpleRule.take, simpleRule.noRead, simpleRule.produce⟩
  have oPresent : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit, taken])
  have o'Fresh : o' ∉ s.present := by
    intro inside
    exact Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit, made]) inside
  obtain ⟨B, u, solved⟩ := solvable
  obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
  have isAlt : o = a := by
    by_contra other
    have small : o < P'.equations.length := by
      have := oPresent
      rw [shaped.present, Finset.mem_insert, Finset.mem_range] at this
      exact this.resolve_left other
    obtain ⟨θ, row⟩ := shaped.rows B _ known o small
    obtain ⟨x, y, headed⟩ := altHead (Assignment.compose u f.opening)
    have same := matched.trans row
    rw [headed] at same
    have tags := N.tag_eq (observe_injective same)
    exact absurd tags (by decide)
  subst isAlt
  have o'Large : P'.equations.length ≤ o' := by
    by_contra small
    exact o'Fresh (by
      rw [shaped.present]
      exact Finset.mem_insert_of_mem (Finset.mem_range.mpr (not_le.mp small)))
  have oNotRow : o ∉ Finset.range P'.equations.length := fun inside =>
    absurd (Finset.mem_range.mp inside) (not_lt.mpr shaped.notRow)
  refine ⟨o', taken, made, o'Large, ?_, ?_⟩
  · rw [simple_present simple, shaped.present, Finset.erase_insert oNotRow]
  · intro B' σ' solved' i hi
    obtain ⟨known', _, _⟩ := simple_restrict simple σ' solved'
    obtain ⟨θ, row⟩ := shaped.rows B' _ known' i hi
    refine ⟨θ, ?_⟩
    have other : i ≠ o' := fun same => absurd hi (not_lt.mpr (same ▸ o'Large))
    rw [simple_label_other simple other]
    show instantiateObservation σ' (instantiateObservation
      ((RuleSyntax.Contextual.declarations S).weaken f.ext) (s.label i)) = _
    rw [instantiateObservation_comp]
    exact row

/-- **Every history of every translated program from the start of a query is a chain.** No
hypothesis that the program or the query is in the first fragment: `let` and every other construct
that is translated are included. -/
theorem every_history_a_chain {D' : Discipline S Γ star} {Q : SourceLanguage.Program κ Γ star D'.Ty}
    (q : Comp κ Γ star D'.Ty) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {s : HostState S} (run : Relation.ReflTransGen (Fires N Q) (start N Q q) s) :
    ∃ (word : List (CRule S)) (a : ℕ),
      Chain (FiresAt (translate N Q)) (start N Q q) Q.equations.length word s a ∧ Shaped N Q s a := by
  induction run with
  | refl =>
      have rep := start_represents N Q q unopened
      exact ⟨[], _, .nil _ _, rep.notRow, rep.present, rep.rows⟩
  | tail _ fired ih =>
      obtain ⟨word, a, chain, shaped⟩ := ih
      obtain ⟨f, admitted, result⟩ := fired
      obtain ⟨a', taken, made, shaped'⟩ := shaped_fires N shaped admitted
      exact ⟨word ++ [f.rule], a', .snoc chain ⟨f, rfl, admitted, taken, made, result⟩,
        result ▸ shaped'⟩

end Shape

end StepAlone

/-! ## One translated program, two source programs, two bags -/

section SameTranslation

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Alternatives.Controls (N D supply one f eqAt dupP q3 W0 matchedStore matchedStore_live
  called calledDone calledDone_finished calledDone_answer q3_source)

/-- The program with the equation once. -/
def onceP : SourceLanguage.Program mkeys [] () MTy := ⟨[eqAt [1]], fun t => .apply t⟩

theorem matchedOnce :
    ∃ e ∈ onceP.equations, Solvable ([] ++ [(instantiate (copyAt mkeys W0.scope) e.lhs, f)]) :=
  ⟨eqAt [1], List.mem_singleton_self _, matchedStore_live⟩

theorem onceP_source :
    ∃ C : Config mkeys [] () MTy, Runs D onceP supply (Config.initial (fun _ => 0) q3) C ∧
      C.Quiescent (D := D) onceP supply ∧ C.answers (D := D) = {{csym "one"}} := by
  refine ⟨⟨W0.fresh, {calledDone}⟩, ?_, ?_, ?_⟩
  · have s1 : SourceLanguage.Step D onceP supply (Config.initial (fun _ => 0) q3)
        ⟨W0.fresh, {called [1]}⟩ :=
      Step.single live_nil (.apply W0 [] f [] [] matchedOnce)
    have s2 : SourceLanguage.Step D onceP supply ⟨W0.fresh, {called [1]}⟩ ⟨W0.fresh, {calledDone}⟩ :=
      Step.of_eq (rest := 0) rfl rfl matchedStore_live (.ret W0.fresh matchedStore _ [] [])
    exact (Relation.ReflTransGen.single s1).tail s2
  · refine Config.quiescent_of_finished fun b member _ => ?_
    rw [Multiset.mem_singleton.mp member]
    exact calledDone_finished
  · show Config.answers (D := D) ⟨W0.fresh, {calledDone}⟩ = _
    rw [answers_singleton calledDone_finished matchedStore_live, calledDone_answer]

/-- **One translated program, two source programs, two bags.** -/
theorem same_translation_two_bags :
    translate N dupP = translate N onceP ∧
      (∃ C : Config mkeys [] () MTy, Runs D dupP supply (Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) dupP supply ∧ C.answers (D := D) = {{csym "one"}, {csym "one"}}) ∧
      (∃ C : Config mkeys [] () MTy, Runs D onceP supply (Config.initial (fun _ => 0) q3) C ∧
        C.Quiescent (D := D) onceP supply ∧ C.answers (D := D) = {{csym "one"}}) :=
  ⟨translate_duplicate N onceP (List.mem_singleton_self _) [2], q3_source, onceP_source⟩

end SameTranslation

/-! ## The same equation at two sites, with a variable -/

section TwoSites

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Alternatives.Controls (N)

/-- The equation `(= (f x) x)` at a site, its variable named at that site. -/
def varAt (site : List ℕ) : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨site, tuple [sym "f", foD [] site 0], .ret (foD [] site 0)⟩

/-- **The equation at two sites has two schemas.** -/
theorem varAt_schema_ne : schema N (varAt [1]) ≠ schema N (varAt [2]) := by
  intro same
  unfold schema varAt at same
  injection same with _ body _
  injection body with _ _ _ _ produce
  injection produce with made
  have outer := vec2_inj (N.args_eq (observe_injective made))
  have inner := vec1_inj (N.args_eq outer.1)
  have returned : instantiate (asUnknowns (Γ := []) (star := ())) (foD [] [1] 0) =
      instantiate asUnknowns (foD [] [2] 0) := vec1_inj (N.args_eq inner)
  rw [instantiate_foD, instantiate_foD] at returned
  unfold asUnknowns generator at returned
  injection returned with _ _ operator _
  injection operator with made'
  injection made' with name
  have unknown : (Sum.inl (fo [] [1] 0) : Name mkeys ⊕ Unit) = Sum.inl (fo [] [2] 0) := name
  have key : fo [] [1] 0 = fo [] [2] 0 := Sum.inl.inj unknown
  have site : ([1] : List ℕ) = [2] := congrArg (fun x : Name mkeys => x.key.site) key
  exact absurd site (by decide)

/-- The program of the two equations. -/
def twoSites : SourceLanguage.Program mkeys [] () MTy := ⟨[varAt [1], varAt [2]], fun t => .apply t⟩

/-- **The hypothesis of distinct schemas holds of a program of two equations that are one equation at
two sites**, and the program is in the fragment. -/
theorem two_sites_distinct :
    (twoSites.equations.map (schema N)).Nodup ∧ PlainProgram twoSites := by
  refine ⟨List.nodup_cons.mpr ⟨fun inside => varAt_schema_ne (List.mem_singleton.mp inside),
    List.nodup_singleton _⟩, fun e member => ?_⟩
  simp only [twoSites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

end TwoSites

#print axioms counted_once_unique
#print axioms bag_from_step
#print axioms partial_bag
#print axioms shaped_fires
#print axioms every_history_a_chain
#print axioms let_rules_translated
#print axioms let_words_same_answer
#print axioms onceP_source
#print axioms same_translation_two_bags
#print axioms varAt_schema_ne
#print axioms two_sites_distinct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.StepAlone
