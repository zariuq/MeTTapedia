import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Classes

/-!
# Classes by words of rules: the step of a program alone, when its equations have distinct schemas

The step does not know names: a history of the step is labelled by the rules its firings used. A
**class by rules** (`RuleFrom`) is a word of rules; it is complete when one of its histories ends in a
state with no firing (`CompleteRuleClass`).

* **The rules of the first fragment are distinct**: a rule's checks and the tag under `eval` in its
  take pattern (`HeadTag`, `headTag_unique`) tell them apart, and the two halves of a choice differ in
  the branch they run (`left_ne_right`).
* `ruleNamed_injective`: when the program's equations have pairwise distinct schemas, a rule has at
  most one name.
* `lift_rule_chain`: every history of the step from the start of a query of the fragment is a named
  history with the same rules (no `let` rule fires there: `no_bind_firing`).
* `bag_by_rule_words`: **how duplicate equations are counted**, for every program of the fragment: the
  bag of answers is read off words of rules, each counted once per complete named class over it.
* **`bag_of_rule_classes`**: for programs whose equations have pairwise distinct schemas, the complete
  classes by rules, each counted once, form a multiset, and the bag of answers is the answers of its
  finished classes: **the bag is determined by the step of the translated program alone**. With two
  equations of one schema it is not (`Controls.duplicate_two_classes_one_rule_word`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## The rules of the fragment are distinct -/

section Distinct

/-- **The tag under `eval`** in every instance of a rule's take patterns. -/
def HeadTag (r : CRule S) (k : Tag) : Prop :=
  ∀ pat ∈ r.body.take, ∀ (B : Interface.Frames.Frame S) (h : Assignment r.locals.arity B.arity),
    ∃ (args : Fin k.arity → Term (signature S B.arity) Γ star) (y : Term (signature S B.arity) Γ star),
      instantiateObservation h pat = observe (altN N (evalN N (N.node k args)) y)

theorem headTag_unique {r : CRule S} {k k' : Tag} (nonempty : r.body.take ≠ []) (one : HeadTag N r k)
    (two : HeadTag N r k') : k = k' := by
  obtain ⟨pat, rest, eq⟩ := List.exists_cons_of_ne_nil nonempty
  have member : pat ∈ r.body.take := by rw [eq]; exact List.mem_cons_self
  obtain ⟨a₁, y₁, e₁⟩ := one pat member r.locals (generator r.locals.arity)
  obtain ⟨a₂, y₂, e₂⟩ := two pat member r.locals (generator r.locals.arity)
  have same := observe_injective (e₁.symm.trans e₂)
  have outer := vec2_inj (N.args_eq same)
  exact N.tag_eq (vec1_inj (N.args_eq outer.1))

theorem retRule_headTag : HeadTag N (retRule N) .ret := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (unk .datum)], instantiate h (unk .stack), ?_⟩
  change observe (instantiate h _) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_retN]

theorem choiceLeftRule_headTag : HeadTag N (choiceLeftRule N) .choice := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (unk .first), instantiate h (unk .second)], instantiate h (unk .stack), ?_⟩
  change observe (instantiate h _) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_choiceN]

theorem choiceRightRule_headTag : HeadTag N (choiceRightRule N) .choice := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (unk .first), instantiate h (unk .second)], instantiate h (unk .stack), ?_⟩
  change observe (instantiate h _) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_choiceN]

theorem schema_headTag {Ty : Type} (e : SourceLanguage.Equation κ Γ star Ty) : HeadTag N (schema N e) .apply := by
  intro pat member B h
  rw [List.mem_singleton.mp member]
  refine ⟨![instantiate h (instantiate asUnknowns e.lhs)], instantiate h schemaStack, ?_⟩
  change observe (instantiate h _) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN]

theorem ne_of_headTag {r r' : CRule S} {k k' : Tag} (nonempty : r.body.take ≠ []) (one : HeadTag N r k)
    (two : HeadTag N r' k') (different : k ≠ k') : r ≠ r' := by
  intro same
  subst same
  exact different (headTag_unique N nonempty one two)

omit N in
theorem checks_ne {r r' : CRule S} (different : r.body.checks.length ≠ r'.body.checks.length) : r ≠ r' := by
  intro same
  subst same
  exact different rfl

omit N in
theorem unk_injective {x y : Unknown} (same : unk (S := S) (Γ := Γ) (star := star) x = unk y) : x = y := by
  unfold unk generator at same
  injection same with _ _ operator _
  injection operator with made
  injection made

/-- The two halves of a choice run different branches. -/
theorem left_ne_right : choiceLeftRule N ≠ choiceRightRule N := by
  intro same
  unfold choiceLeftRule choiceRightRule at same
  injection same with _ body _
  injection body with _ _ _ _ produce
  injection produce with made
  have outer := vec2_inj (N.args_eq (observe_injective made))
  have inner := vec1_inj (N.args_eq outer.1)
  exact absurd (unk_injective inner) (by decide)

end Distinct

/-! ## Names are determined by rules when schemas are distinct -/

section Injective

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **A rule has at most one name** when the program's equations have pairwise distinct schemas. -/
theorem ruleNamed_injective (distinct : (P.equations.map (schema N)).Nodup) {n₁ n₂ : RuleName} {r : CRule S}
    (h₁ : ruleNamed N P n₁ = some r) (h₂ : ruleNamed N P n₂ = some r) : n₁ = n₂ := by
  have retTake : (retRule N).body.take ≠ [] := List.cons_ne_nil _ _
  have leftTake : (choiceLeftRule N).body.take ≠ [] := List.cons_ne_nil _ _
  have rightTake : (choiceRightRule N).body.take ≠ [] := List.cons_ne_nil _ _
  have retLeft := ne_of_headTag N retTake (retRule_headTag N) (choiceLeftRule_headTag N) (by decide)
  have retRight := ne_of_headTag N retTake (retRule_headTag N) (choiceRightRule_headTag N) (by decide)
  have retSchema : ∀ e : SourceLanguage.Equation κ Γ star Ty, retRule N ≠ schema N e := fun e =>
    ne_of_headTag N retTake (retRule_headTag N) (schema_headTag N e) (by decide)
  have leftSchema : ∀ e : SourceLanguage.Equation κ Γ star Ty, choiceLeftRule N ≠ schema N e := fun e =>
    ne_of_headTag N leftTake (choiceLeftRule_headTag N) (schema_headTag N e) (by decide)
  have rightSchema : ∀ e : SourceLanguage.Equation κ Γ star Ty, choiceRightRule N ≠ schema N e := fun e =>
    ne_of_headTag N rightTake (choiceRightRule_headTag N) (schema_headTag N e) (by decide)
  have unmatchedRet : unmatchedRule N ≠ retRule N := checks_ne (by show (1 : ℕ) ≠ 0; omega)
  have unmatchedLeft : unmatchedRule N ≠ choiceLeftRule N := checks_ne (by show (1 : ℕ) ≠ 0; omega)
  have unmatchedRight : unmatchedRule N ≠ choiceRightRule N := checks_ne (by show (1 : ℕ) ≠ 0; omega)
  have unmatchedSchema : ∀ e : SourceLanguage.Equation κ Γ star Ty, unmatchedRule N ≠ schema N e := fun e =>
    checks_ne (by show (1 : ℕ) ≠ 0; omega)
  have leftRight := left_ne_right N
  cases n₁ with
  | ret =>
      simp only [ruleNamed, Option.some.injEq] at h₁
      subst h₁
      cases n₂ with
      | ret => rfl
      | unmatched => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ unmatchedRet
      | left => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm retLeft
      | right => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm retRight
      | eqn j =>
          obtain ⟨e, _, same⟩ := Option.map_eq_some_iff.mp h₂
          exact absurd same.symm (retSchema e)
  | unmatched =>
      simp only [ruleNamed, Option.some.injEq] at h₁
      subst h₁
      cases n₂ with
      | ret => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm unmatchedRet
      | unmatched => rfl
      | left => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm unmatchedLeft
      | right => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm unmatchedRight
      | eqn j =>
          obtain ⟨e, _, same⟩ := Option.map_eq_some_iff.mp h₂
          exact absurd same.symm (unmatchedSchema e)
  | left =>
      simp only [ruleNamed, Option.some.injEq] at h₁
      subst h₁
      cases n₂ with
      | ret => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ retLeft
      | unmatched => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ unmatchedLeft
      | left => rfl
      | right => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂.symm leftRight
      | eqn j =>
          obtain ⟨e, _, same⟩ := Option.map_eq_some_iff.mp h₂
          exact absurd same.symm (leftSchema e)
  | right =>
      simp only [ruleNamed, Option.some.injEq] at h₁
      subst h₁
      cases n₂ with
      | ret => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ retRight
      | unmatched => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ unmatchedRight
      | left => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ leftRight
      | right => rfl
      | eqn j =>
          obtain ⟨e, _, same⟩ := Option.map_eq_some_iff.mp h₂
          exact absurd same.symm (rightSchema e)
  | eqn i =>
      obtain ⟨e₁, g₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      cases n₂ with
      | ret => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ (retSchema e₁)
      | unmatched => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ (unmatchedSchema e₁)
      | left => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ (leftSchema e₁)
      | right => simp only [ruleNamed, Option.some.injEq] at h₂; exact absurd h₂ (rightSchema e₁)
      | eqn j =>
          obtain ⟨e₂, g₂, same⟩ := Option.map_eq_some_iff.mp h₂
          obtain ⟨hi, ei⟩ := List.getElem?_eq_some_iff.mp g₁
          obtain ⟨hj, ej⟩ := List.getElem?_eq_some_iff.mp g₂
          have mapped : (P.equations.map (schema N))[i]'(by simpa using hi) =
              (P.equations.map (schema N))[j]'(by simpa using hj) := by
            simp only [List.getElem_map, ei, ej, same]
          rw [(distinct.getElem_inj_iff).mp mapped]

/-- The names of a named history all denote rules. -/
theorem chain_valid {s s' : HostState S} {o o' : ℕ} {word : List RuleName}
    (chain : Chain (FiresNamed N P) s o word s' o') : ∀ n ∈ word, ∃ r, ruleNamed N P n = some r := by
  induction chain with
  | nil => intro n member; cases member
  | snoc _ last ih =>
      intro n member
      rcases List.mem_append.mp member with old | new
      · exact ih n old
      · rw [List.mem_singleton.mp new]
        obtain ⟨r, named, _⟩ := last
        exact ⟨r, named⟩

/-- **Forgetting names is injective on words of names that denote rules**, when schemas are distinct. -/
theorem forget_injective (distinct : (P.equations.map (schema N)).Nodup) :
    ∀ (ν₁ ν₂ : List RuleName), (∀ n ∈ ν₁, ∃ r, ruleNamed N P n = some r) →
      (∀ n ∈ ν₂, ∃ r, ruleNamed N P n = some r) →
      ν₁.filterMap (ruleNamed N P) = ν₂.filterMap (ruleNamed N P) → ν₁ = ν₂
  | [], [], _, _, _ => rfl
  | [], n :: _, _, valid, same => by
      obtain ⟨r, named⟩ := valid n List.mem_cons_self
      rw [List.filterMap_nil, List.filterMap_cons_some named] at same
      cases same
  | n :: _, [], valid, _, same => by
      obtain ⟨r, named⟩ := valid n List.mem_cons_self
      rw [List.filterMap_nil, List.filterMap_cons_some named] at same
      cases same
  | n₁ :: rest₁, n₂ :: rest₂, valid₁, valid₂, same => by
      obtain ⟨r₁, named₁⟩ := valid₁ n₁ List.mem_cons_self
      obtain ⟨r₂, named₂⟩ := valid₂ n₂ List.mem_cons_self
      rw [List.filterMap_cons_some named₁, List.filterMap_cons_some named₂, List.cons.injEq] at same
      obtain ⟨sameRule, sameRest⟩ := same
      subst sameRule
      rw [ruleNamed_injective N distinct named₁ named₂,
        forget_injective distinct rest₁ rest₂ (fun n member => valid₁ n (List.mem_cons_of_mem _ member))
          (fun n member => valid₂ n (List.mem_cons_of_mem _ member)) sameRest]

end Injective

/-! ## Histories by rules are named histories -/

section Lift

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-- A named move is a move of the source. -/
theorem NamedMove.toMove {w w' : World κ Γ star} {b b' : Branch κ Γ star D.Ty} {n : RuleName}
    (move : NamedMove P w b n w' b') : ∃ bs, Move D P supply w b w' bs ∧ b' ∈ bs := by
  cases move with
  | ret K t fs ps => exact ⟨_, .ret w K t fs ps, Multiset.mem_singleton_self _⟩
  | unmatched K t fs ps none => exact ⟨_, .unmatched w K t fs ps none, Multiset.mem_singleton_self _⟩
  | left K c d fs ps => exact ⟨_, .choice w K c d fs ps, Multiset.mem_cons_self _ _⟩
  | right K c d fs ps =>
      exact ⟨_, .choice w K c d fs ps, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)⟩
  | eqn K t fs ps i e get matched =>
      exact ⟨_, .apply w K t fs ps matched,
        Multiset.mem_coe.mpr (List.mem_map.mpr ⟨e, List.mem_of_getElem? get, rfl⟩)⟩

/-- **No `let` rule fires from an alternative of the first fragment.** -/
theorem no_bind_firing {n : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (plain : PlainBranch b)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) s) :
    f.rule ≠ bindStartRule N ∧ f.rule ≠ bindValueRule N := by
  obtain ⟨noFrames, shape⟩ := plain
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  constructor
  · intro isStart
    simp only at isStart
    subst isStart
    obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
      (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
    obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
    rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
    · rw [focus] at same
      cases same
      exact pc
    · rw [focus] at same
      cases same
  · intro isValue
    simp only at isValue
    subst isValue
    obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
      (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
    obtain ⟨_, _, _, _, frames⟩ := shape_bindValue N reads
    rw [noFrames] at frames
    cases frames

/-- **Every history of the step from the start of a query of the fragment is a named history** with
the same rules, and its last state represents an alternative of a configuration a source run reaches. -/
theorem lift_rule_chain (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {word : List (CRule S)} {s : HostState S} {a : ℕ}
    (chain : Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s a) :
    ∃ names : List RuleName, names.filterMap (ruleNamed N P) = word ∧ NamedFrom N P q names s a ∧
      ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty), Runs D P supply (Config.initial spaces q) C ∧
        b ∈ C.branches ∧ Represents N P C.world.scope b s a ∧ PlainBranch b := by
  induction chain with
  | nil =>
      exact ⟨[], rfl, .nil _ _, _, initialBranch q, .refl, Multiset.mem_singleton_self _,
        start_represents N P q unopened, rfl, .inl ⟨q, rfl, plainQ⟩⟩
  | snoc _ last ih =>
      obtain ⟨names, forget, namedChain, C, b, runs, member, rep, plain⟩ := ih
      obtain ⟨f, rfl, admitted, taken, made, result⟩ := last
      obtain ⟨notStart, notValue⟩ := no_bind_firing N rep plain admitted
      have named : ∃ n, ruleNamed N P n = some f.rule := by
        rcases (mem_translate N).mp f.member with control | ⟨e, eMember, eq⟩
        · rcases (mem_controlRules N).mp control with h | h | h | h | h | h
          · exact ⟨.ret, by rw [h]; rfl⟩
          · exact ⟨.unmatched, by rw [h]; rfl⟩
          · exact ⟨.left, by rw [h]; rfl⟩
          · exact ⟨.right, by rw [h]; rfl⟩
          · exact absurd h notStart
          · exact absurd h notValue
        · obtain ⟨i, small, rfl⟩ := List.getElem_of_mem eMember
          exact ⟨.eqn i, by simp [ruleNamed, List.getElem?_eq_getElem small, eq]⟩
      obtain ⟨n, hn⟩ := named
      have fired : FiresNamed N P n _ _ _ _ := ⟨f.rule, hn, f, rfl, admitted, taken, made, result⟩
      obtain ⟨w', b', move, rep', plain'⟩ := reflection_named N plainP rep plain fired
      obtain ⟨bs, sourceMove, child⟩ := move.toMove (supply := supply)
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      refine ⟨names ++ [n], ?_, .snoc namedChain fired, ⟨w', bs + rest⟩, b', runs.tail ?_,
        Multiset.mem_add.mpr (.inl child), rep', plain'⟩
      · rw [List.filterMap_append, forget, List.filterMap_cons_some hn, List.filterMap_nil]
      · obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world w' b rest bs (live_of_fires N rep (firesNamed_fires N fired)) sourceMove

end Lift

/-! ## The bag of answers from classes by rules -/

section RuleBag

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

variable (P) (q : Comp κ Γ star D.Ty)

/-- A history of the step from the start of the query, labelled by its rules. -/
abbrev RuleFrom (word : List (CRule S)) (s : HostState S) (a : ℕ) : Prop :=
  Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s a

/-- **A complete class by rules.** -/
def CompleteRuleClass (word : List (CRule S)) : Prop := ∃ s a, RuleFrom N P q word s a ∧ Terminal N P s

/-- **A finished class by rules.** -/
def FinishedRuleClass (word : List (CRule S)) : Prop := ∃ s a, RuleFrom N P q word s a ∧ StateFinished N s a

/-- **The answer of a class by rules.** -/
def ruleClassAnswer (word : List (CRule S)) : Set (Term S Γ star) :=
  {g | ∃ s a, RuleFrom N P q word s a ∧ g ∈ stateAnswer N s a}

variable {P q}

/-- **How duplicate equations are counted, in general**: the bag of answers is read off words of
rules, each word counted once for every complete named class whose names denote it. With pairwise
distinct schemas every word has at most one such class (`bag_of_rule_classes`); two equations of one
schema give one word two classes (`Controls.duplicate_two_classes_one_rule_word`). -/
theorem bag_by_rule_words (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ word, M.count word = if CompleteClass N P q word then 1 else 0) ∧
        C.answers (D := D) = ((M.map fun ν => ν.filterMap (ruleNamed N P)).filter
          (FinishedRuleClass N P q)).map (ruleClassAnswer N P q) := by
  obtain ⟨M, count, answers⟩ := bag_of_classes N spaces q plainP plainQ unopened runs quiet
  have reachedOf : ∀ ν ∈ M, ∃ s a, NamedFrom N P q ν s a := by
    intro ν member
    have one := count ν
    by_cases complete : CompleteClass N P q ν
    · obtain ⟨s, a, reached, _⟩ := complete
      exact ⟨s, a, reached⟩
    · rw [if_neg complete] at one
      exact absurd member (Multiset.count_eq_zero.mp one)
  refine ⟨M, count, ?_⟩
  have finishedIff : ∀ ν ∈ M, FinishedRuleClass N P q (ν.filterMap (ruleNamed N P)) ↔ FinishedClass N P q ν := by
    intro ν member
    obtain ⟨s₀, a₀, reached₀⟩ := reachedOf ν member
    constructor
    · rintro ⟨s, a, reached, finished⟩
      exact ⟨s₀, a₀, reached₀, ((same_word_same_answer N q reached (chain_forget N reached₀)).2).mp finished⟩
    · rintro ⟨s, a, reached, finished⟩
      exact ⟨s, a, chain_forget N reached, finished⟩
  have answerEq : ∀ ν ∈ M, ruleClassAnswer N P q (ν.filterMap (ruleNamed N P)) = classAnswer N P q ν := by
    intro ν member
    obtain ⟨s₀, a₀, reached₀⟩ := reachedOf ν member
    ext g
    constructor
    · rintro ⟨s, a, reached, shown⟩
      rw [(same_word_same_answer N q reached (chain_forget N reached₀)).1] at shown
      exact ⟨s₀, a₀, reached₀, shown⟩
    · rintro ⟨s, a, reached, shown⟩
      exact ⟨s, a, chain_forget N reached, shown⟩
  rw [answers, Multiset.filter_map, Multiset.map_map]
  have sameFilter : M.filter (FinishedRuleClass N P q ∘ fun ν => ν.filterMap (ruleNamed N P)) =
      M.filter (FinishedClass N P q) :=
    Multiset.filter_congr fun ν member => finishedIff ν member
  rw [sameFilter]
  apply Multiset.map_congr rfl
  intro ν member
  exact (answerEq ν (Multiset.mem_of_mem_filter member)).symm

/-- **The bag of answers from the step alone**: for a program of the first fragment whose equations
have pairwise distinct schemas, and every source run that ends, the complete classes of the
translated program's histories by rules, each counted once, form a multiset `M`, and the bag of
answers is the answers of its finished classes. -/
theorem bag_of_rule_classes (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (distinct : (P.equations.map (schema N)).Nodup) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List (CRule S)),
      (∀ word, M.count word = if CompleteRuleClass N P q word then 1 else 0) ∧
        C.answers (D := D) = (M.filter (FinishedRuleClass N P q)).map (ruleClassAnswer N P q) := by
  obtain ⟨M, count, answers⟩ := bag_of_classes N spaces q plainP plainQ unopened runs quiet
  have complete : ∀ ν ∈ M, CompleteClass N P q ν := by
    intro ν member
    have one := count ν
    by_contra notComplete
    rw [if_neg notComplete] at one
    exact Multiset.count_eq_zero.mp one member
  have reachedOf : ∀ ν ∈ M, ∃ s a, NamedFrom N P q ν s a := fun ν member =>
    let ⟨s, a, reached, _⟩ := complete ν member
    ⟨s, a, reached⟩
  have validOf : ∀ ν ∈ M, ∀ n ∈ ν, ∃ r, ruleNamed N P n = some r := fun ν member =>
    let ⟨_, _, reached⟩ := reachedOf ν member
    chain_valid N reached
  have nodupM : M.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro ν
    rw [count ν]
    split <;> omega
  let forget : List RuleName → List (CRule S) := fun ν => ν.filterMap (ruleNamed N P)
  have nodupImage : (M.map forget).Nodup :=
    Multiset.Nodup.map_on (fun ν₁ m₁ ν₂ m₂ same =>
      forget_injective N distinct ν₁ ν₂ (validOf ν₁ m₁) (validOf ν₂ m₂) same) nodupM
  have inImage : ∀ word, word ∈ M.map forget ↔ CompleteRuleClass N P q word := by
    intro word
    constructor
    · intro member
      obtain ⟨ν, νMember, rfl⟩ := Multiset.mem_map.mp member
      obtain ⟨s, a, reached, terminal⟩ := complete ν νMember
      exact ⟨s, a, chain_forget N reached, terminal⟩
    · rintro ⟨s, a, reached, terminal⟩
      obtain ⟨names, forgotten, namedChain, _⟩ :=
        lift_rule_chain N (supply := supply) spaces q plainP plainQ unopened reached
      have inM : names ∈ M := by
        have one := count names
        rw [if_pos ⟨s, a, namedChain, terminal⟩] at one
        exact Multiset.count_pos.mp (by omega)
      exact Multiset.mem_map.mpr ⟨names, inM, forgotten⟩
  refine ⟨M.map forget, ?_, ?_⟩
  · intro word
    by_cases inside : word ∈ M.map forget
    · rw [if_pos ((inImage word).mp inside)]
      exact Multiset.count_eq_one_of_mem nodupImage inside
    · rw [if_neg (fun c => inside ((inImage word).mpr c))]
      exact Multiset.count_eq_zero.mpr inside
  · have finishedIff : ∀ ν ∈ M, FinishedRuleClass N P q (forget ν) ↔ FinishedClass N P q ν := by
      intro ν member
      obtain ⟨s₀, a₀, reached₀⟩ := reachedOf ν member
      constructor
      · rintro ⟨s, a, reached, finished⟩
        have same := (same_word_same_answer N q reached (chain_forget N reached₀)).2
        exact ⟨s₀, a₀, reached₀, same.mp finished⟩
      · rintro ⟨s, a, reached, finished⟩
        exact ⟨s, a, chain_forget N reached, finished⟩
    have answerEq : ∀ ν ∈ M, ruleClassAnswer N P q (forget ν) = classAnswer N P q ν := by
      intro ν member
      obtain ⟨s₀, a₀, reached₀⟩ := reachedOf ν member
      ext g
      constructor
      · rintro ⟨s, a, reached, shown⟩
        rw [(same_word_same_answer N q reached (chain_forget N reached₀)).1] at shown
        exact ⟨s₀, a₀, reached₀, shown⟩
      · rintro ⟨s, a, reached, shown⟩
        exact ⟨s, a, chain_forget N reached, shown⟩
    rw [answers, Multiset.filter_map, Multiset.map_map]
    have sameFilter : M.filter (FinishedRuleClass N P q ∘ forget) = M.filter (FinishedClass N P q) :=
      Multiset.filter_congr fun ν member => finishedIff ν member
    rw [sameFilter]
    apply Multiset.map_congr rfl
    intro ν member
    exact (answerEq ν (Multiset.mem_of_mem_filter member)).symm

end RuleBag

#print axioms headTag_unique
#print axioms left_ne_right
#print axioms ruleNamed_injective
#print axioms forget_injective
#print axioms no_bind_firing
#print axioms lift_rule_chain
#print axioms bag_by_rule_words
#print axioms bag_of_rule_classes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives
