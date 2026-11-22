import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedAdequacy

/-!
# The manuscript's COMM as one firing of the one-match step

`MeTTaCalculus` is the calculus of the F1R3FLY manuscript. Its COMM rule is
`for(t <- x)P | for(u <- x)Q → P·σ̇ | Q·σ̇`, with `σ` a unifier of `t` and `u` and the dot quoting each
bound value. The tree states it literally (`ReflectionClosure.Step`) and under the variable convention
(`Corrected.Step`).

The step used here is the one-match step of a program, `RuleSyntax.step`, at the one frame of structural
substitution on patterns (`OneFrame.frames patternAction`, with identity extensions). Its five choices:

* the store is a bag of occurrences: a finite set of identities, each with a label;
* a firing is one match: one rule, one opening, one selection;
* a firing's guards are asked at every solution of its information, which includes its own tells (the
  comm rule has no guard, so this choice is not exercised here);
* the program is a fixed set of rules beside the store: here the one-rule program `commProgram`, whose
  rule `commSchema` has the body `MeTTaOperationsComm.commRule` of one redex shape (take both inputs, tell
  `t = u`, make both dotted continuations);
* there is one store of knowledge.

## What is shown

* `comm_one_firing`: one COMM of the manuscript is one admitted firing of the one-rule program, at every
  fresh opening, under exactly the side conditions of `MeTTaOperationsComm.comm_adequacy`: a ground
  principal unifier, first-order continuations, continuations whose variables the two patterns bind
  (closed processes), two distinct made identities that are not present, and the patterns' variables
  apart from the knowledge. Every solution of the result's knowledge reads the two made rows as the
  manuscript's dotted continuations. The made identities need no label beforehand: the step labels them.
* `exists_fresh_opening`: every such firing has a fresh opening, by renaming apart (`fresh_of_renaming`,
  `exists_apart_renaming`); `comm_one_transition` packages the transition with its result, and its
  knowledge is solvable, so the read-off is about a nonempty set of solutions.
* `comm_one_firing_corrected`: the same for the corrected step through `comm_adequacy_corrected`: any
  principal unifier and the variable convention; every solution reads the uniform dot.
* `comm_admitted`: admission asks nothing of the continuations: a principal unifier, the redex's rows,
  the made identities, the patterns' variables apart from a consistent knowledge, and a fresh opening.
* `comm_one_firing_open`: closedness of the continuations is needed only for reading a fixed pattern.
  Without it, every solution `σ` reads each made row as the manuscript's dotted continuation read
  through `σ`.
* `comm_one_firing_structural`: outside the first-order fragment, every solution reads each made row as
  the structural dot (`structuralDot`), which keeps explicit substitution nodes and collection rests as
  syntax; on first-order continuations it is the manuscript's dot (`applyDot_eq_structuralDot`).
* `comm_one_firing_reading`: the same as `comm_one_firing` when the taken rows read as the two inputs at
  every solution of the knowledge, as the rows made by an earlier COMM do; runs are built on it in
  `CommRuns`.
* `comm_firstOrderOn`: through `OneFrame.firstOrder_eq`, where the made identities already carry the
  opened made rows, the transition is one of the first-order step restricted to the fresh openings of the
  program: the base layer's firing of the opened rule.

## How `comm_adequacy` is lifted

`comm_adequacy` is a statement about the base layer: one rule instance whose take patterns are the labels
of the taken rows, so it shares their variables. The step of a program opens its rule apart from
everything the state mentions, and equates the opened take patterns with the rows' labels. Two facts
connect the two problems at one configuration:

* `opened_refines_reading` (any opening): every solution of the opened problem solves the unopened
  problem and reads each opened made row as the unopened one (`opened_refines` when the rows are labelled
  by the inputs). It rests on `agree_of_psubst_eq`: structural substitution determines a substitution on
  a pattern's variables.
* `information_amalgamates_matched` (any frame action, a fresh opening): a solution of the knowledge and
  one of the rule's tells that agree on the selected rows extend together to a solution of the
  information. With no takes and no reads it is `information_amalgamates`. It gives admission
  (`comm_admits_reading`) from one solution of the knowledge that unifies the two patterns.

`comm_adequacy` is then used unchanged, at the labels `unopenedLabels` that put the unopened made rows on
the made identities: its validity gives that solution (`solution_of_valid`), its second conjunct the
manuscript's step, its third the read-off (`reads_of_unopened`).

**Label keeping.** `firstOrder_eq` relates the step of a program only to firings whose made identities
already carry the opened made rows. At a fresh opening the opened made row of a continuation with a
variable is never the unopened one (`opened_row_moves`, `opened_row_moves₂`), so the labels of
`comm_adequacy` are never label-keeping there; the step itself needs no such labels.

## What is not shown here

Only a root COMM between two present rows is a firing; PAR, EQUIV and REFL are not. Runs of COMM steps
are in `CommRuns`, a computed example and the controls of each side condition in `CommControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none psubst_congr psubst_of_pvars_nil pvars
  patternAction PSubst quoteOn dotted commRule commSelection GroundPrincipal storePVars comm_adequacy
  comm_problem lookup_eq_none_of_keys applyDot_eq psubst_nQuote dotted_resolves)
open MeTTaCalculus.Corrected (psubst_getD_congr_on pvars_pFor nameOf nameOf_injOn nameOf_mem freshNames
  freshNames_length freshNames_nodup freshNames_fresh)
open OneFrame (Terms frames ext embed keeping firstOrderOn)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

/-! ## Structural substitution is determined on a pattern's variables -/

/-- **Two substitutions that act alike on a pattern agree on its variables**, each variable read as the
pattern put in its place. The converse is `Corrected.psubst_getD_congr_on`. -/
theorem agree_of_psubst_eq {σ τ : PSubst} {p : Pattern} (same : psubst σ p = psubst τ p) :
    ∀ x ∈ pvars p, (σ x).getD (.fvar x) = (τ x).getD (.fvar x) := by
  revert same
  induction p using Pattern.rec
      (motive_2 := fun ps => MeTTaOperationsComm.psubst.psubstList σ ps =
          MeTTaOperationsComm.psubst.psubstList τ ps →
        ∀ x ∈ MeTTaOperationsComm.pvars.pvarsList ps, (σ x).getD (.fvar x) = (τ x).getD (.fvar x)) with
  | bvar n => intro _ x member; simp [pvars] at member
  | fvar y =>
    intro same x member
    simp only [pvars, List.mem_singleton] at member
    subst member
    exact same
  | apply c args ih =>
    intro same x member
    simp only [psubst, Pattern.apply.injEq, true_and] at same
    exact ih same x member
  | lambda nm body ih =>
    intro same x member
    simp only [psubst, Pattern.lambda.injEq, true_and] at same
    exact ih same x member
  | multiLambda n nms body ih =>
    intro same x member
    simp only [psubst, Pattern.multiLambda.injEq, true_and] at same
    exact ih same x member
  | subst body repl ihb ihr =>
    intro same x member
    simp only [psubst, Pattern.subst.injEq] at same
    simp only [pvars, List.mem_append] at member
    rcases member with inBody | inRepl
    · exact ihb same.1 x inBody
    · exact ihr same.2 x inRepl
  | collection ct elems rest ih =>
    intro same x member
    simp only [psubst, Pattern.collection.injEq, true_and, and_true] at same
    exact ih same x member
  | nil => rename_i member; simp [MeTTaOperationsComm.pvars.pvarsList] at member
  | cons p ps head tail =>
    rename_i same x member
    simp only [MeTTaOperationsComm.psubst.psubstList, List.cons.injEq] at same
    simp only [MeTTaOperationsComm.pvars.pvarsList, List.mem_append] at member
    rcases member with inHead | inTail
    · exact head same.1 x inHead
    · exact tail same.2 x inTail

/-- Structural substitution acts alike on a pattern exactly when the substitutions agree on its
variables. -/
theorem psubst_eq_iff {σ τ : PSubst} {p : Pattern} :
    psubst σ p = psubst τ p ↔ ∀ x ∈ pvars p, (σ x).getD (.fvar x) = (τ x).getD (.fvar x) :=
  ⟨agree_of_psubst_eq, psubst_getD_congr_on⟩

/-- Substitutions that agree on a continuation's variables act alike on its dotted form. -/
theorem psubst_dotted_congr {σ τ : PSubst} (vs : List String) (P : Pattern)
    (agree : ∀ x ∈ pvars P, (σ x).getD (.fvar x) = (τ x).getD (.fvar x)) :
    psubst σ (dotted vs P) = psubst τ (dotted vs P) := by
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_getD_congr_on
  intro x member
  by_cases inside : x ∈ vs
  · simp only [pcomp, quoteOn, if_pos inside, Option.getD_some, psubst_nQuote]
    exact congrArg nQuote (agree x member)
  · simp only [pcomp, quoteOn, if_neg inside]
    exact agree x member

/-! ## The one frame of patterns, and the comm rule as a program -/

/-- Patterns at the one frame. -/
abbrev Tm : PUnit.{1} → Type := Terms Pattern

/-- The one-frame action of structural substitution on patterns. -/
abbrev X : Frames Tm (fun _ _ : PUnit.{1} => PSubst) := frames patternAction

/-- Firings move along the identity. -/
abbrev E : Extensions.{0, 0, 0} (fun _ _ : PUnit.{1} => PSubst) := ext patternAction

/-- **The comm rule of one redex shape**, at the one frame: its body is `MeTTaOperationsComm.commRule`,
and it has no collect pattern. -/
def commSchema (t u channel P Q : Pattern) : Rule Tm := ⟨PUnit.unit, commRule t u channel P Q, []⟩

/-- **The one-rule program** whose rule is the comm rule of one redex shape. -/
def commProgram (t u channel P Q : Pattern) : Program Tm := {commSchema t u channel P Q}

/-- **The COMM firing**: the comm rule opened by `ρ`, taking `first` and `second`, making `made₁` and
`made₂`. -/
def commFiring {O : Type*} (t u channel P Q : Pattern) (ρ : PSubst) (first second made₁ made₂ : O) :
    Firing O E (commProgram t u channel P Q) PUnit.unit :=
  ⟨commSchema t u channel P Q, Set.mem_singleton _, PUnit.unit, ρ, commSelection first second made₁ made₂, []⟩

/-- The variables of a rule's terms. -/
def ruleVars (r : Rule Tm) : List String := r.terms.flatMap pvars

/-! ## Fresh openings by renaming apart -/

/-- The opening that renames every variable by `g`. -/
def renameBy (g : String → String) : PSubst := fun x => some (.fvar (g x))

/-- A solution that puts the rule's instance on the renamed variables and the state's instance
elsewhere. -/
def apartSolution (vars : List String) (g : String → String) (onState onRule : PSubst) : PSubst := fun y =>
  match vars.find? (fun x => g x == y) with
  | some x => some ((onRule x).getD (.fvar x))
  | none => onState y

theorem apartSolution_renamed {vars : List String} {g : String → String}
    (injective : ∀ x ∈ vars, ∀ y ∈ vars, g x = g y → x = y) {x : String} (member : x ∈ vars)
    (onState onRule : PSubst) :
    apartSolution vars g onState onRule (g x) = some ((onRule x).getD (.fvar x)) := by
  unfold apartSolution
  split
  · rename_i x' found
    have same : g x' = g x := by simpa using List.find?_some found
    rw [injective x' (List.mem_of_find?_eq_some found) x member same]
  · rename_i found
    exact absurd (List.find?_eq_none.mp found x member) (by simp)

theorem apartSolution_outside {vars : List String} {g : String → String} {y : String}
    (outside : ∀ x ∈ vars, g x ≠ y) (onState onRule : PSubst) :
    apartSolution vars g onState onRule y = onState y := by
  unfold apartSolution
  split
  · rename_i x found
    exact absurd (by simpa using List.find?_some found) (outside x (List.mem_of_find?_eq_some found))
  · rfl

variable {O : Type*}

/-- **A renaming apart is a fresh opening.** At the one frame, an opening that renames the rule's
variables injectively onto names that no term the state mentions contains is fresh. -/
theorem fresh_of_renaming {Prog : Program Tm} (s : State Tm O) (f : Firing O E Prog s.frame)
    (g : String → String) (opening : f.opening = renameBy g)
    (injective : ∀ x ∈ ruleVars f.rule, ∀ y ∈ ruleVars f.rule, g x = g y → x = y)
    (avoids : ∀ x ∈ ruleVars f.rule, ∀ m, s.Mentions m → g x ∉ pvars m) : f.Fresh X s := by
  intro b onState onRule
  refine ⟨apartSolution (ruleVars f.rule) g onState onRule, fun m mentions => ?_, fun r member => ?_⟩
  · show psubst _ (psubst (fun _ => none) m) = psubst onState m
    rw [psubst_none]
    apply psubst_congr
    intro y occurs
    have outside : ∀ x ∈ ruleVars f.rule, g x ≠ y := fun x inVars same =>
      avoids x inVars m mentions (same ▸ occurs)
    exact apartSolution_outside outside onState onRule
  · show psubst _ (psubst f.opening r) = psubst onRule r
    rw [opening, psubst_comp]
    apply psubst_getD_congr_on
    intro x occurs
    have inVars : x ∈ ruleVars f.rule := List.mem_flatMap.mpr ⟨r, member, occurs⟩
    show (apartSolution (ruleVars f.rule) g onState onRule (g x)).getD (.fvar (g x)) = _
    rw [apartSolution_renamed injective inVars onState onRule, Option.getD_some]

/-- **Names apart exist**: for every state and every list of variables there is a renaming, injective
on the list, whose names no term the state mentions contains. -/
theorem exists_apart_renaming (s : State Tm O) (vars : List String) :
    ∃ g : String → String, (∀ x ∈ vars, ∀ y ∈ vars, g x = g y → x = y) ∧
      ∀ x ∈ vars, ∀ m, s.Mentions m → g x ∉ pvars m := by
  let avoid : List String :=
    storePVars s.knowledge ++ s.present.toList.flatMap fun o => pvars (s.label o)
  have long : vars.length ≤ (freshNames avoid 0 vars.length).length :=
    (freshNames_length avoid 0 vars.length).ge
  refine ⟨nameOf (freshNames avoid 0 vars.length) vars,
    nameOf_injOn (freshNames_nodup avoid 0 vars.length) long, ?_⟩
  intro x member m mentions occurs
  apply freshNames_fresh (nameOf_mem long member)
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, inside, List.mem_append_left _ occurs⟩)
  · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp known
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, inside, List.mem_append_right _ occurs⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, Finset.mem_toList.mpr present, occurs⟩)

/-- **Every COMM firing has a fresh opening.** -/
theorem exists_fresh_opening (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel P Q : Pattern) (first second made₁ made₂ : O) :
    ∃ ρ : PSubst, (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C) := by
  obtain ⟨g, injective, avoids⟩ :=
    exists_apart_renaming (embed label C) (ruleVars (commSchema t u channel P Q))
  exact ⟨renameBy g, fresh_of_renaming (embed label C) _ g rfl injective avoids⟩

/-! ## Amalgamation with takes and reads, at every frame action -/

section Amalgamation

universe uObj uTm uHom uExt uOcc

variable {Obj : Type uObj} {Tm' : Obj → Type uTm} {Hom : Obj → Obj → Type uHom} {Y : Frames Tm' Hom}
  {O' : Type uOcc} {E' : Extensions.{uObj, uHom, uExt} Hom} {Prog : Program Tm'}

/-- An equation of the information between an opened pattern and its selected row. -/
theorem mem_matching_opened {s : State Tm' O'} (f : Firing O' E' Prog s.frame)
    {patterns : List (Tm' f.rule.locals)} {selected : List O'} {e : Equation (Tm' (E'.target f.ext))}
    (member : e ∈ f.matching Y s (patterns.map (Y.act f.opening)) selected) :
    ∃ q ∈ patterns.zip selected, e = (Y.act f.opening q.1, f.row Y s q.2) := by
  unfold Firing.matching at member
  rw [← List.map_uncurry_zip_eq_zipWith, List.zip_map_left, List.map_map] at member
  obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp member
  exact ⟨(p, o), inside, rfl⟩

/-- **Amalgamation with takes and reads.** A firing with a fresh opening has, for every solution `g` of
the knowledge and every solution `h` of the rule's own tells that agree on each selected row (its pattern
read by `h`, its label read by `g`), a solution of its information that agrees with `g` on every term the
state mentions and with `h` on the rule's terms. With no takes and no reads this is
`information_amalgamates`. -/
theorem information_amalgamates_matched {s : State Tm' O'} (f : Firing O' E' Prog s.frame)
    (fresh : f.Fresh Y s) {b : Obj} (g : Hom s.frame b) (h : Hom f.rule.locals b)
    (known : Y.Models g s.knowledge) (told : Y.Models h f.rule.body.tell)
    (takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.present)
    (readPresent : ∀ o ∈ f.selection.read, o ∈ s.present)
    (takeAgree : ∀ q ∈ f.rule.body.take.zip f.selection.taken,
      Y.E (Y.act h q.1) (Y.act g (s.label q.2)))
    (readAgree : ∀ q ∈ f.rule.body.read.zip f.selection.read,
      Y.E (Y.act h q.1) (Y.act g (s.label q.2))) :
    ∃ u : Hom (E'.target f.ext) b, Y.Models u (f.information Y s) ∧
      (∀ t, s.Mentions t → Y.E (Y.act u (Y.act (E'.weaken f.ext) t)) (Y.act g t)) ∧
      ∀ t ∈ f.rule.terms, Y.E (Y.act u (Y.act f.opening t)) (Y.act h t) := by
  obtain ⟨u, state, rule⟩ := fresh b g h
  refine ⟨u, ?_, state, rule⟩
  have symm := fun {x y : Tm' b} (same : Y.E x y) => (Y.equivalence b).symm same
  have trans := fun {x y z : Tm' b} (one : Y.E x y) (two : Y.E y z) => (Y.equivalence b).trans one two
  have matched : ∀ (patterns : List (Tm' f.rule.locals)) (selected : List O'),
      (∀ p ∈ patterns, p ∈ f.rule.terms) → (∀ o ∈ selected, o ∈ s.present) →
      (∀ q ∈ patterns.zip selected, Y.E (Y.act h q.1) (Y.act g (s.label q.2))) →
      Y.Models u (f.matching Y s (patterns.map (Y.act f.opening)) selected) := by
    intro patterns selected terms present agree e member
    obtain ⟨⟨p, o⟩, inside, rfl⟩ := mem_matching_opened f member
    have pattern := rule p (terms p (List.of_mem_zip inside).1)
    have row := state (s.label o) (Or.inr (Or.inr ⟨o, present o (List.of_mem_zip inside).2, rfl⟩))
    exact trans pattern (trans (agree (p, o) inside) (symm row))
  intro e member
  unfold Firing.information at member
  rcases List.mem_append.mp member with front | tells
  · rcases List.mem_append.mp front with front | reads
    · rcases List.mem_append.mp front with old | takes
      · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
        have left := state original.1 (Or.inl (List.mem_map_of_mem inside))
        have right := state original.2 (Or.inr (Or.inl (List.mem_map_of_mem inside)))
        exact trans left (trans (known original inside) (symm right))
      · exact matched f.rule.body.take f.selection.taken
          (fun p inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ inside))))))
          takenPresent takeAgree e takes
    · exact matched f.rule.body.read f.selection.read
        (fun p inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ inside))))))
        readPresent readAgree e reads
  · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp tells
    have firstTerm : original.1 ∈ f.rule.terms :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem inside)))))
    have secondTerm : original.2 ∈ f.rule.terms :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem inside))))
    exact trans (rule original.1 firstTerm)
      (trans (told original inside) (symm (rule original.2 secondTerm)))

end Amalgamation

/-! ## The opened problem refines the unopened one -/

/-- The base-layer problem of the comm rule opened by `ρ`. -/
theorem opened_problem (label : O → Pattern) (t u channel P Q : Pattern) (ρ : PSubst)
    (C : Configuration Pattern O) (first second made₁ made₂ : O) :
    (commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C =
      C.equations ++ [(psubst ρ (pFor t channel P), label first),
        (psubst ρ (pFor u channel Q), label second), (psubst ρ t, psubst ρ u)] := by
  simp [Selection.problem, Selection.equations, commSelection, commRule, RuleInstance.map]

/-- **The opened COMM problem refines the unopened one.** At a configuration whose taken rows read as the
unopened take patterns at every solution of the knowledge, every solution of the base-layer problem of the
comm rule opened by any `ρ` solves the problem of the unopened rule, at any labels that agree on the taken
rows, and reads each opened made row as the unopened made row. -/
theorem opened_refines_reading (label label' : O → Pattern) (t u channel P Q : Pattern) (ρ : PSubst)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel P))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel Q))
    (sameFirst : label' first = label first) (sameSecond : label' second = label second) {σ : PSubst}
    (solved : patternAction.Models σ
      ((commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C)) :
    patternAction.Models σ
        ((commSelection first second made₁ made₂).problem label' (commRule t u channel P Q) C) ∧
      psubst σ (psubst ρ (dotted (pvars t ++ pvars u) P)) = psubst σ (dotted (pvars t ++ pvars u) P) ∧
      psubst σ (psubst ρ (dotted (pvars t ++ pvars u) Q)) = psubst σ (dotted (pvars t ++ pvars u) Q) := by
  rw [opened_problem] at solved
  have known : patternAction.Models σ C.equations := fun e member =>
    solved e (List.mem_append_left _ member)
  have take₁ : psubst σ (psubst ρ (pFor t channel P)) = psubst σ (pFor t channel P) :=
    (show psubst σ (psubst ρ (pFor t channel P)) = psubst σ (label first) from
      solved (psubst ρ (pFor t channel P), label first) (by simp)).trans (readsFirst σ known)
  have take₂ : psubst σ (psubst ρ (pFor u channel Q)) = psubst σ (pFor u channel Q) :=
    (show psubst σ (psubst ρ (pFor u channel Q)) = psubst σ (label second) from
      solved (psubst ρ (pFor u channel Q), label second) (by simp)).trans (readsSecond σ known)
  have told : psubst σ (psubst ρ t) = psubst σ (psubst ρ u) := solved (psubst ρ t, psubst ρ u) (by simp)
  have agree₁ := agree_of_psubst_eq ((psubst_comp σ ρ _).symm.trans take₁)
  have agree₂ := agree_of_psubst_eq ((psubst_comp σ ρ _).symm.trans take₂)
  have onT : psubst σ (psubst ρ t) = psubst σ t := by
    rw [psubst_comp]
    exact psubst_getD_congr_on fun x occurs => agree₁ x (by
      rw [pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ occurs))
  have onU : psubst σ (psubst ρ u) = psubst σ u := by
    rw [psubst_comp]
    exact psubst_getD_congr_on fun x occurs => agree₂ x (by
      rw [pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ occurs))
  refine ⟨?_, ?_, ?_⟩
  · rw [comm_problem]
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with old | rfl | rfl | rfl
    · exact known e old
    · show psubst σ (pFor t channel P) = psubst σ (label' first)
      rw [sameFirst, readsFirst σ known]
    · show psubst σ (pFor u channel Q) = psubst σ (label' second)
      rw [sameSecond, readsSecond σ known]
    · show psubst σ t = psubst σ u
      rw [← onT, ← onU]
      exact told
  · rw [psubst_comp]
    exact psubst_dotted_congr _ P fun x occurs => agree₁ x (by
      rw [pvars_pFor]; exact List.mem_append_right _ occurs)
  · rw [psubst_comp]
    exact psubst_dotted_congr _ Q fun x occurs => agree₂ x (by
      rw [pvars_pFor]; exact List.mem_append_right _ occurs)

/-- **The opened COMM problem refines the unopened one**, at a configuration whose taken rows are labelled
by the unopened take patterns. -/
theorem opened_refines (label label' : O → Pattern) (t u channel P Q : Pattern) (ρ : PSubst)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (sameFirst : label' first = label first) (sameSecond : label' second = label second) {σ : PSubst}
    (solved : patternAction.Models σ
      ((commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C)) :
    patternAction.Models σ
        ((commSelection first second made₁ made₂).problem label' (commRule t u channel P Q) C) ∧
      psubst σ (psubst ρ (dotted (pvars t ++ pvars u) P)) = psubst σ (dotted (pvars t ++ pvars u) P) ∧
      psubst σ (psubst ρ (dotted (pvars t ++ pvars u) Q)) = psubst σ (dotted (pvars t ++ pvars u) Q) :=
  opened_refines_reading label label' t u channel P Q ρ C first second made₁ made₂
    (fun σ _ => congrArg (psubst σ) labelFirst) (fun σ _ => congrArg (psubst σ) labelSecond) sameFirst
    sameSecond solved

/-- **A unifier glues with every solution of a knowledge apart from the patterns**: some solution of the
knowledge unifies the two patterns. -/
theorem glued_solution {t u : Pattern} {bs : Bindings} (solves : psubst bs.lookup t = psubst bs.lookup u)
    {K : EquationStore Pattern} (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars K)
    (base : patternAction.Consistent K) :
    ∃ σ₀ : PSubst, patternAction.Models σ₀ K ∧ psubst σ₀ t = psubst σ₀ u := by
  obtain ⟨σ, solved⟩ := base
  let glued : PSubst := fun x => if x ∈ pvars t ++ pvars u then bs.lookup x else σ x
  have outside : ∀ term, (∀ x ∈ pvars term, x ∈ storePVars K) → psubst glued term = psubst σ term := by
    intro term inside
    apply psubst_congr
    intro x occurs
    have notPattern : x ∉ pvars t ++ pvars u := fun inPattern => apart x inPattern (inside x occurs)
    show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ x) = σ x
    rw [if_neg notPattern]
  have onPatterns : ∀ term, (∀ x ∈ pvars term, x ∈ pvars t ++ pvars u) →
      psubst glued term = psubst bs.lookup term := by
    intro term inside
    apply psubst_congr
    intro x occurs
    show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ x) = bs.lookup x
    rw [if_pos (inside x occurs)]
  refine ⟨glued, fun e member => ?_, ?_⟩
  · show psubst glued e.1 = psubst glued e.2
    rw [outside e.1 (fun x occurs => List.mem_flatMap.mpr ⟨e, member, List.mem_append_left _ occurs⟩),
      outside e.2 (fun x occurs => List.mem_flatMap.mpr ⟨e, member, List.mem_append_right _ occurs⟩)]
    exact solved e member
  · rw [onPatterns t (fun x occurs => List.mem_append_left _ occurs),
      onPatterns u (fun x occurs => List.mem_append_right _ occurs)]
    exact solves

/-! ## The COMM firing of the step -/

/-- A present identity is not an absent one. -/
theorem ne_of_present {o made : O} {present : Finset O} (inside : o ∈ present) (absent : made ∉ present) :
    o ≠ made := fun same => absent (same ▸ inside)

section Step

variable [DecidableEq O]

/-- **The base layer's labels at which `comm_adequacy` is read**: the made identities carry the unopened
made rows, and every other identity keeps its label. The step of a program reads no label of an absent
identity. -/
def unopenedLabels (label : O → Pattern) (t u P Q : Pattern) (made₁ made₂ : O) : O → Pattern :=
  fun o => if o = made₂ then dotted (pvars t ++ pvars u) Q
    else if o = made₁ then dotted (pvars t ++ pvars u) P else label o

theorem unopenedLabels_made₁ (label : O → Pattern) (t u P Q : Pattern) {made₁ made₂ : O}
    (madeDistinct : made₁ ≠ made₂) :
    unopenedLabels label t u P Q made₁ made₂ made₁ = dotted (pvars t ++ pvars u) P := by
  show (if made₁ = made₂ then _ else if made₁ = made₁ then _ else _) = _
  rw [if_neg madeDistinct, if_pos rfl]

theorem unopenedLabels_made₂ (label : O → Pattern) (t u P Q : Pattern) (made₁ made₂ : O) :
    unopenedLabels label t u P Q made₁ made₂ made₂ = dotted (pvars t ++ pvars u) Q := by
  show (if made₂ = made₂ then _ else _) = _
  rw [if_pos rfl]

theorem unopenedLabels_other (label : O → Pattern) (t u P Q : Pattern) {made₁ made₂ o : O}
    (other₁ : o ≠ made₁) (other₂ : o ≠ made₂) : unopenedLabels label t u P Q made₁ made₂ o = label o := by
  show (if o = made₂ then _ else if o = made₁ then _ else _) = _
  rw [if_neg other₂, if_neg other₁]

theorem commFiring_label₁ (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (ρ : PSubst) (first second made₁ made₂ : O) :
    ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label made₁ =
      psubst ρ (dotted (pvars t ++ pvars u) P) := by
  show (if made₁ = made₁ then psubst ρ (dotted (pvars t ++ pvars u) P) else _) = _
  rw [if_pos rfl]

theorem commFiring_label₂ (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (ρ : PSubst) (first second : O) {made₁ made₂ : O} (madeDistinct : made₁ ≠ made₂) :
    ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label made₂ =
      psubst ρ (dotted (pvars t ++ pvars u) Q) := by
  show (if made₂ = made₁ then _ else if made₂ = made₂ then psubst ρ (dotted (pvars t ++ pvars u) Q)
    else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

/-- **A valid base-layer COMM firing has a solution of the knowledge that unifies the two patterns.** -/
theorem solution_of_valid {label' : O → Pattern} {t u channel P Q : Pattern} {C : Configuration Pattern O}
    {first second made₁ made₂ : O}
    (valid : (commSelection first second made₁ made₂).Valid patternAction label'
      (commRule t u channel P Q) C) :
    ∃ σ₀ : PSubst, patternAction.Models σ₀ C.equations ∧ psubst σ₀ t = psubst σ₀ u := by
  obtain ⟨σ₀, solved₀⟩ := valid.consistent
  rw [comm_problem] at solved₀
  exact ⟨σ₀, fun e member => solved₀ e (List.mem_append_left _ member), solved₀ (t, u) (by simp)⟩

/-- **Admission at a fresh opening.** The COMM firing of the one-rule program is admitted at every fresh
opening when its taken rows are distinct, present, and read as the two inputs at every solution of the
knowledge, its made identities are distinct and not present, and some solution of the knowledge unifies
the two patterns. -/
theorem comm_admits_reading (label : O → Pattern) (t u channel P Q : Pattern) (C : Configuration Pattern O)
    (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel P))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel Q))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : patternAction.Models σ₀ C.equations) (unifies : psubst σ₀ t = psubst σ₀ u)
    {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
      (commFiring t u channel P Q ρ first second made₁ made₂) := by
  obtain ⟨w, solved, -, -⟩ := information_amalgamates_matched (Y := X) (s := embed label C)
    (commFiring t u channel P Q ρ first second made₁ made₂) opensFreshly (b := PUnit.unit) σ₀ σ₀ known
    (fun e member => by
      obtain rfl := List.mem_singleton.mp member
      exact unifies)
    (fun o member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact present₁
      · obtain rfl := List.mem_singleton.mp member
        exact present₂)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact (readsFirst σ₀ known).symm
      · obtain rfl := List.mem_singleton.mp member
        exact (readsSecond σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [commFiring, commSelection, distinct], by simp [commFiring, commSelection, madeDistinct],
      rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [commFiring, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  · intro o member
    simp [commFiring, commSelection, Selection.commit] at member
  · simp [commFiring, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commFiring, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Every reading of the base layer's unopened firing is a reading of the step's firing.** Every
solution of the knowledge after the COMM firing of the step solves the knowledge after the unopened
base-layer firing at `unopenedLabels`, and reads the step's made rows as that firing's made rows. -/
theorem reads_of_unopened (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (ρ : PSubst) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (madeDistinct : made₁ ≠ made₂) (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present) {σ : PSubst}
    (solved : patternAction.Models σ
      ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge) :
    patternAction.Models σ ((commSelection first second made₁ made₂).result
        (unopenedLabels label t u P Q made₁ made₂) (commRule t u channel P Q) C).equations ∧
      psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label
          made₁) = psubst σ (unopenedLabels label t u P Q made₁ made₂ made₁) ∧
      psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label
          made₂) = psubst σ (unopenedLabels label t u P Q made₁ made₂ made₂) := by
  have key : (commFiring t u channel P Q ρ first second made₁ made₂).information X (embed label C) =
      (commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C :=
    OneFrame.information_eq C _
  have opened : patternAction.Models σ
      ((commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C) := by
    rw [← key]
    exact solved
  have first' : unopenedLabels label t u P Q made₁ made₂ first = label first :=
    unopenedLabels_other label t u P Q (ne_of_present present₁ fresh₁)
      (ne_of_present present₁ fresh₂)
  have second' : unopenedLabels label t u P Q made₁ made₂ second = label second :=
    unopenedLabels_other label t u P Q (ne_of_present present₂ fresh₁)
      (ne_of_present present₂ fresh₂)
  obtain ⟨unopened, row₁, row₂⟩ := opened_refines label (unopenedLabels label t u P Q made₁ made₂)
    t u channel P Q ρ C first second made₁ made₂ labelFirst labelSecond first' second' opened
  refine ⟨unopened, ?_, ?_⟩
  · rw [commFiring_label₁, unopenedLabels_made₁ label t u P Q madeDistinct]
    exact row₁
  · rw [commFiring_label₂ label C t u channel P Q ρ first second madeDistinct, unopenedLabels_made₂]
    exact row₂

/-- **COMM as one firing of the one-match step.** Under the side conditions of `comm_adequacy`, each
named: a ground principal unifier (`gp`), first-order continuations (`foP`, `foQ`), continuations whose
variables the patterns bind (`closedP`, `closedQ`), distinct made identities that are not present
(`madeDistinct`, `fresh₁`, `fresh₂`), and the patterns' variables apart from the knowledge (`apart`),
together with the redex's two present rows and a consistent knowledge: at every fresh opening the COMM
firing of the one-rule program is admitted, the manuscript's COMM relates the redex to the dotted
continuations, and every solution of the result's knowledge reads the two made rows as them. -/
theorem comm_one_firing (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
    (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
        (commFiring t u channel P Q ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₁) = applyDot bs P ∧
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₂) = applyDot bs Q := by
  have first' : unopenedLabels label t u P Q made₁ made₂ first = pFor t channel P :=
    (unopenedLabels_other label t u P Q (ne_of_present present₁ fresh₁)
      (ne_of_present present₁ fresh₂)).trans labelFirst
  have second' : unopenedLabels label t u P Q made₁ made₂ second = pFor u channel Q :=
    (unopenedLabels_other label t u P Q (ne_of_present present₂ fresh₁)
      (ne_of_present present₂ fresh₂)).trans labelSecond
  obtain ⟨valid, manuscript, reads⟩ := comm_adequacy (unopenedLabels label t u P Q made₁ made₂)
    t u channel P Q bs gp foP foQ closedP closedQ C first second made₁ made₂ first' second' distinct
    madeDistinct present₁ present₂ fresh₁ fresh₂ (unopenedLabels_made₁ label t u P Q madeDistinct)
    (unopenedLabels_made₂ label t u P Q made₁ made₂) apart base
  obtain ⟨σ₀, known, unifies⟩ := solution_of_valid valid
  refine ⟨comm_admits_reading label t u channel P Q C first second made₁ made₂
    (fun σ _ => congrArg (psubst σ) labelFirst) (fun σ _ => congrArg (psubst σ) labelSecond) distinct
    madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly, manuscript, fun σ solved => ?_⟩
  obtain ⟨unopened, row₁, row₂⟩ := reads_of_unopened label C t u channel P Q ρ first second made₁ made₂
    labelFirst labelSecond madeDistinct present₁ present₂ fresh₁ fresh₂ solved
  obtain ⟨read₁, read₂⟩ := reads σ unopened
  exact ⟨row₁.trans read₁, row₂.trans read₂⟩

/-- **The COMM transition of the step, with its result.** Under the side conditions of
`comm_one_firing` (no opening is assumed: a fresh one exists), the manuscript's COMM relates the redex to
the dotted continuations, and the step of the one-rule program moves the embedded configuration to a
state whose present rows are the old ones with the two inputs replaced by the two made identities, whose
other labels are unchanged, whose knowledge has a solution, and every solution of whose knowledge reads
the made rows as the dotted continuations. -/
theorem comm_one_transition (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
    (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) :
    MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      ∃ s' : State Tm O, Succ (RuleSyntax.step X O E (commProgram t u channel P Q)).toStep
          (embed label C) s' ∧
        s'.present = (C.present \ {first, second}) ∪ {made₁, made₂} ∧
        (∀ o, o ≠ made₁ → o ≠ made₂ → s'.label o = label o) ∧
        (∃ σ : PSubst, patternAction.Models σ s'.knowledge) ∧
        ∀ σ : PSubst, patternAction.Models σ s'.knowledge →
          psubst σ (s'.label made₁) = applyDot bs P ∧ psubst σ (s'.label made₂) = applyDot bs Q := by
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening label C t u channel P Q first second made₁ made₂
  obtain ⟨admitted, manuscript, reads⟩ := comm_one_firing label t u channel P Q bs gp foP foQ closedP
    closedQ C first second made₁ made₂ labelFirst labelSecond distinct madeDistinct present₁ present₂
    fresh₁ fresh₂ apart base opensFreshly
  obtain ⟨_, σ, solvedσ⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  refine ⟨manuscript, (commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C),
    ⟨_, admitted, rfl⟩, ?_, fun o other₁ other₂ => ?_, ⟨σ, solvedσ⟩, reads⟩
  · show fire C.present ((commSelection first second made₁ made₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  · have absent : o ∉ (commFiring t u channel P Q ρ first second made₁ made₂).selection.made := by
      simp [commFiring, commSelection, other₁, other₂]
    exact (Firing.result_label_other (X := X) (s := embed label C) _ absent).trans (psubst_none (label o))

/-! ## Through `firstOrder_eq` -/

/-- **Through `firstOrder_eq`.** Where the made identities already carry the opened made rows (label
keeping), the COMM transition of the step is a transition of the label-keeping step of the one-rule
program, and so of the first-order step restricted to the fresh openings of that program: the base
layer's firing of the opened rule. -/
theorem comm_firstOrderOn (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
    (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C))
    (keeps₁ : label made₁ = psubst ρ (dotted (pvars t ++ pvars u) P))
    (keeps₂ : label made₂ = psubst ρ (dotted (pvars t ++ pvars u) Q)) :
    Succ (keeping patternAction (commProgram t u channel P Q)) (embed label C)
        (embed label ((commSelection first second made₁ made₂).result label
          ((commRule t u channel P Q).map (psubst ρ)) C)) ∧
      Succ (firstOrderOn patternAction label (commProgram t u channel P Q)) C
        ((commSelection first second made₁ made₂).result label ((commRule t u channel P Q).map (psubst ρ)) C) := by
  have admitted := (comm_one_firing label t u channel P Q bs gp foP foQ closedP closedQ C first second
    made₁ made₂ labelFirst labelSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ apart base
    opensFreshly).1
  have keeps : (commFiring t u channel P Q ρ first second made₁ made₂).selection.made.map
      (embed label C).label = ((commFiring t u channel P Q ρ first second made₁ made₂).opened X).produce := by
    show [label made₁, label made₂] = [psubst ρ (dotted (pvars t ++ pvars u) P),
      psubst ρ (dotted (pvars t ++ pvars u) Q)]
    rw [keeps₁, keeps₂]
  have kept : Succ (keeping patternAction (commProgram t u channel P Q)) (embed label C)
      (embed label ((commSelection first second made₁ made₂).result label
        ((commRule t u channel P Q).map (psubst ρ)) C)) :=
    ⟨_, ⟨admitted, keeps⟩, OneFrame.result_toFirstOrder C _ keeps⟩
  exact ⟨kept, (OneFrame.firstOrder_eq C _).mpr kept⟩

end Step

/-- **A fresh opening fixes no rule term with a variable that the state mentions.** -/
theorem fresh_moves {Prog : Program Tm} (s : State Tm O) (f : Firing O E Prog s.frame)
    (opensFreshly : f.Fresh X s) {m : Pattern} (term : m ∈ f.rule.terms) (mentioned : s.Mentions m)
    {x : String} (occurs : x ∈ pvars m) : psubst f.opening m ≠ m := by
  intro same
  obtain ⟨w, state, rule⟩ := opensFreshly PUnit.unit (fun _ => none) (fun _ => some pZero)
  have onState := state m mentioned
  change psubst w (psubst (fun _ => none) m) = psubst (fun _ => none) m at onState
  rw [psubst_none] at onState
  have onRule := rule m term
  change psubst w (psubst f.opening m) = psubst (fun _ => some pZero) m at onRule
  rw [same] at onRule
  have agree := agree_of_psubst_eq ((psubst_none m).trans (onState.symm.trans onRule)) x occurs
  exact Pattern.noConfusion agree

/-- **Where `firstOrder_eq` does not reach `comm_adequacy`.** The base-layer firing of `comm_adequacy`,
whose rule instance is the unopened comm rule, is the image of no fresh opening of the comm program as soon
as the first input pattern has a variable. So it is no firing of the first-order step restricted to the
program (`firstOrderOn`), and `firstOrder_eq` does not relate it to the step. -/
theorem unopened_not_opensProgram [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (t u channel P Q : Pattern) (first second made₁ made₂ : O) (labelFirst : label first = pFor t channel P)
    (present₁ : first ∈ C.present) {x : String} (occurs : x ∈ pvars t) :
    ¬ OneFrame.OpensProgram patternAction label (commProgram t u channel P Q) C
      ⟨commRule t u channel P Q, [], commSelection first second made₁ made₂⟩ := by
  rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, fresh, -, image⟩
  have same : rule = commSchema t u channel P Q := member
  subst same
  have takes := congrArg RuleInstance.take (congrArg AnnotatedRuns.Firing.rule image)
  change [psubst opening (pFor t channel P), psubst opening (pFor u channel Q)] =
    [pFor t channel P, pFor u channel Q] at takes
  exact fresh_moves (embed label C) _ fresh (m := pFor t channel P)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))))))
    (Or.inr (Or.inr ⟨first, present₁, labelFirst⟩))
    (by rw [pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ occurs))
    (List.cons.inj takes).1

/-- **A fresh opening moves every dotted rule term with a variable that the state mentions.** If a term the
state mentions contains the variables of `K`, and the dotted form of `K` is a term of the rule, a fresh
opening does not fix that dotted form, as soon as `K` has a variable. -/
theorem fresh_moves_dotted {Prog : Program Tm} (s : State Tm O) (f : Firing O E Prog s.frame)
    (opensFreshly : f.Fresh X s) (vs : List String) (K m : Pattern) (mentioned : s.Mentions m)
    (inside : ∀ y ∈ pvars K, y ∈ pvars m) (term : dotted vs K ∈ f.rule.terms) {x : String}
    (occurs : x ∈ pvars K) : psubst f.opening (dotted vs K) ≠ dotted vs K := by
  intro same
  obtain ⟨w, state, rule⟩ := opensFreshly PUnit.unit (fun _ => none) (fun _ => some pZero)
  have onMentioned : psubst w m = psubst (fun _ => none) m := by
    have seen := state m mentioned
    change psubst w (psubst (fun _ => none) m) = psubst (fun _ => none) m at seen
    rw [psubst_none] at seen
    exact seen.trans (psubst_none _).symm
  have onK : ∀ y ∈ pvars K, (w y).getD (.fvar y) = ((fun _ => none : PSubst) y).getD (.fvar y) :=
    fun y inK => agree_of_psubst_eq onMentioned y (inside y inK)
  have made := rule (dotted vs K) term
  change psubst w (psubst f.opening (dotted vs K)) = psubst (fun _ => some pZero) (dotted vs K) at made
  rw [same, psubst_dotted_congr vs K onK, psubst_none] at made
  unfold dotted at made
  rw [psubst_comp] at made
  have agree := agree_of_psubst_eq made x occurs
  by_cases quoted : x ∈ vs
  · have quote : quoteOn vs x = some (nQuote (.fvar x)) := if_pos quoted
    simp only [pcomp, quote, Option.getD_some] at agree
    have zero : nQuote (.fvar x) = nQuote pZero := agree
    simp [nQuote, pZero] at zero
  · have plain : quoteOn vs x = none := if_neg quoted
    simp only [pcomp, plain, Option.getD_none, Option.getD_some] at agree
    simp [pZero] at agree

/-- **Where label keeping fails.** At a fresh opening, the opened made row of a continuation that has a
variable is never its unopened made row. So the labels of `comm_adequacy`, which put the unopened rows on
the made identities, are never label-keeping when a continuation has a variable, and `firstOrder_eq` does
not see the COMM firing at those labels; the step itself needs no labels on made identities. -/
theorem opened_row_moves (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (ρ : PSubst) (first second made₁ made₂ : O) (labelFirst : label first = pFor t channel P)
    (present₁ : first ∈ C.present)
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C))
    {x : String} (occurs : x ∈ pvars P) :
    psubst ρ (dotted (pvars t ++ pvars u) P) ≠ dotted (pvars t ++ pvars u) P :=
  fresh_moves_dotted (embed label C) _ opensFreshly _ P (pFor t channel P)
    (Or.inr (Or.inr ⟨first, present₁, labelFirst⟩))
    (fun y inP => by rw [pvars_pFor]; exact List.mem_append_right _ inP)
    (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)) occurs

/-- The same for the second continuation. -/
theorem opened_row_moves₂ (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (ρ : PSubst) (first second made₁ made₂ : O) (labelSecond : label second = pFor u channel Q)
    (present₂ : second ∈ C.present)
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C))
    {x : String} (occurs : x ∈ pvars Q) :
    psubst ρ (dotted (pvars t ++ pvars u) Q) ≠ dotted (pvars t ++ pvars u) Q :=
  fresh_moves_dotted (embed label C) _ opensFreshly _ Q (pFor u channel Q)
    (Or.inr (Or.inr ⟨second, present₂, labelSecond⟩))
    (fun y inQ => by rw [pvars_pFor]; exact List.mem_append_right _ inQ)
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))) occurs

/-! ## Ground principal unifiers and principal unifiers -/

/-- **A ground principal unifier is principal** in the sense of the corrected semantics. -/
theorem principal_of_groundPrincipal {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) :
    MeTTaCalculus.Corrected.Principal t u bs where
  solves := gp.solves
  keys := gp.keys
  general := by
    intro τ solved p
    rw [psubst_comp]
    apply psubst_getD_congr_on
    intro x _
    by_cases inside : x ∈ pvars t ++ pvars u
    · obtain ⟨v, found, closed⟩ := gp.covers x inside
      simp only [pcomp, found, Option.getD_some, psubst_of_pvars_nil τ v closed]
      exact (gp.principal τ solved x inside v found).symm
    · simp only [pcomp, lookup_eq_none_of_keys gp.keys inside]

/-- **A principal unifier that binds every pattern variable to a closed pattern is a ground principal
unifier.** -/
theorem groundPrincipal_of_principal {t u : Pattern} {bs : Bindings}
    (principal : MeTTaCalculus.Corrected.Principal t u bs)
    (covers : ∀ x ∈ pvars t ++ pvars u, ∃ v, bs.lookup x = some v ∧ pvars v = []) :
    GroundPrincipal t u bs where
  keys := principal.keys
  covers := covers
  solves := principal.solves
  principal := by
    intro σ solved x inside v found
    obtain ⟨v', found', closed⟩ := covers x inside
    have same : v' = v := Option.some.inj (found'.symm.trans found)
    have general := principal.general σ solved (.fvar x)
    change psubst σ ((bs.lookup x).getD (.fvar x)) = psubst σ (.fvar x) at general
    rw [found, Option.getD_some, psubst_of_pvars_nil σ v (same ▸ closed)] at general
    exact general.symm

/-- **The structural dot**: each variable the unifier binds is replaced, structurally, by the quotation
of its value; explicit substitution nodes and collection rests stay as syntax. On first-order patterns it
is the manuscript's dot (`applyDot_eq_structuralDot`); outside them it differs
(`Controls.subst_misreads`). -/
def structuralDot (bs : Bindings) (P : Pattern) : Pattern := psubst (fun x => (bs.lookup x).map nQuote) P

theorem applyDot_eq_structuralDot (bs : Bindings) (P : Pattern)
    (fo : MeTTaOperationsComm.firstOrder P = true) : applyDot bs P = structuralDot bs P :=
  applyDot_eq bs P fo

/-- **Every unifier reads a dotted continuation as the structural dot, read through it**, whatever the
continuation. -/
theorem dotted_reads_structural {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) {σ : PSubst}
    (solved : psubst σ t = psubst σ u) (P : Pattern) :
    psubst σ (dotted (pvars t ++ pvars u) P) = psubst σ (structuralDot bs P) := by
  rw [structuralDot, dotted, psubst_comp, psubst_comp]
  apply psubst_getD_congr_on
  intro x _
  by_cases inside : x ∈ pvars t ++ pvars u
  · obtain ⟨v, found, closed⟩ := gp.covers x inside
    simp only [pcomp, quoteOn, if_pos inside, found, Option.map_some, Option.getD_some, psubst_nQuote,
      psubst_of_pvars_nil σ v closed]
    rw [gp.principal σ solved x inside v found]
  · simp only [pcomp, quoteOn, if_neg inside, lookup_eq_none_of_keys gp.keys inside, Option.map_none]

/-- **Every unifier reads a dotted continuation as the manuscript's dot, read through it.** No
closedness of the continuation is needed. -/
theorem dotted_reads {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) {σ : PSubst}
    (solved : psubst σ t = psubst σ u) (P : Pattern) (fo : MeTTaOperationsComm.firstOrder P = true) :
    psubst σ (dotted (pvars t ++ pvars u) P) = psubst σ (applyDot bs P) := by
  rw [applyDot_eq_structuralDot bs P fo]
  exact dotted_reads_structural gp solved P

section Variants

variable [DecidableEq O]

/-- **Admission asks nothing of the continuations.** A principal unifier (not necessarily ground), the
redex's two present rows, distinct made identities that are not present, the patterns' variables apart
from a consistent knowledge, and a fresh opening: the COMM firing of the step is admitted, whatever the
continuations are. -/
theorem comm_admitted (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (principal : MeTTaCalculus.Corrected.Principal t u bs)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
      (commFiring t u channel P Q ρ first second made₁ made₂) := by
  obtain ⟨σ₀, known, unifies⟩ := glued_solution principal.solves apart base
  exact comm_admits_reading label t u channel P Q C first second made₁ made₂
    (fun σ _ => congrArg (psubst σ) labelFirst) (fun σ _ => congrArg (psubst σ) labelSecond) distinct
    madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly

/-- **Rows that read as the redex.** Under the side conditions of `comm_one_firing`, with the taken rows
reading as the two inputs at every solution of the knowledge instead of being labelled by them, the COMM
firing of the step is admitted at every fresh opening, the manuscript's COMM relates the redex to the
dotted continuations, and every solution of the result's knowledge reads the made rows as them. Rows made
by an earlier COMM read as their continuations in this way. -/
theorem comm_one_firing_reading (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
    (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel P))
    (readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel Q))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
        (commFiring t u channel P Q ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₁) = applyDot bs P ∧
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₂) = applyDot bs Q := by
  obtain ⟨σ₀, known, unifies⟩ := glued_solution gp.solves apart base
  refine ⟨comm_admits_reading label t u channel P Q C first second made₁ made₂ readsFirst readsSecond
    distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly,
    .comm t u channel P Q bs gp, fun σ solved => ?_⟩
  have key : (commFiring t u channel P Q ρ first second made₁ made₂).information X (embed label C) =
      (commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C :=
    OneFrame.information_eq C _
  have opened : patternAction.Models σ
      ((commSelection first second made₁ made₂).problem label ((commRule t u channel P Q).map (psubst ρ)) C) := by
    rw [← key]
    exact solved
  obtain ⟨unopened, row₁, row₂⟩ := opened_refines_reading label label t u channel P Q ρ C first second
    made₁ made₂ readsFirst readsSecond rfl rfl opened
  rw [comm_problem] at unopened
  have unify : psubst σ t = psubst σ u := unopened (t, u) (by simp)
  rw [commFiring_label₁, commFiring_label₂ label C t u channel P Q ρ first second madeDistinct]
  exact ⟨row₁.trans (dotted_resolves gp unify P foP closedP),
    row₂.trans (dotted_resolves gp unify Q foQ closedQ)⟩

/-- **Closedness is needed only to read a fixed pattern.** Without closed continuations, under the other
side conditions of `comm_one_firing`, the COMM firing of the step is admitted at every fresh opening, and
every solution `σ` of the result's knowledge reads each made row as the manuscript's dotted continuation
read through `σ`. -/
theorem comm_one_firing_open (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
    (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
        (commFiring t u channel P Q ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₁) = psubst σ (applyDot bs P) ∧
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₂) = psubst σ (applyDot bs Q) := by
  refine ⟨comm_admitted label t u channel P Q bs (principal_of_groundPrincipal gp) C first second made₁
    made₂ labelFirst labelSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ apart base
    opensFreshly, .comm t u channel P Q bs gp, fun σ solved => ?_⟩
  obtain ⟨unopened, row₁, row₂⟩ := reads_of_unopened label C t u channel P Q ρ first second made₁ made₂
    labelFirst labelSecond madeDistinct present₁ present₂ fresh₁ fresh₂ solved
  have unifies : psubst σ t = psubst σ u := unopened (t, u) (by simp [Selection.result, comm_problem])
  rw [unopenedLabels_made₁ label t u P Q madeDistinct] at row₁
  rw [unopenedLabels_made₂] at row₂
  exact ⟨row₁.trans (dotted_reads gp unifies P foP), row₂.trans (dotted_reads gp unifies Q foQ)⟩

/-- **Outside the first-order fragment.** Under the side conditions of `comm_one_firing` without
first-order or closed continuations, the COMM firing of the step is admitted at every fresh opening, and
every solution `σ` of the result's knowledge reads each made row as the structural dot read through `σ`.
On first-order continuations the structural dot is the manuscript's dot; outside them the two differ. -/
theorem comm_one_firing_structural (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
        (commFiring t u channel P Q ρ first second made₁ made₂) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₁) = psubst σ (structuralDot bs P) ∧
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₂) = psubst σ (structuralDot bs Q) := by
  refine ⟨comm_admitted label t u channel P Q bs (principal_of_groundPrincipal gp) C first second made₁
    made₂ labelFirst labelSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ apart base
    opensFreshly, fun σ solved => ?_⟩
  obtain ⟨unopened, row₁, row₂⟩ := reads_of_unopened label C t u channel P Q ρ first second made₁ made₂
    labelFirst labelSecond madeDistinct present₁ present₂ fresh₁ fresh₂ solved
  have unifies : psubst σ t = psubst σ u := unopened (t, u) (by simp [Selection.result, comm_problem])
  rw [unopenedLabels_made₁ label t u P Q madeDistinct] at row₁
  rw [unopenedLabels_made₂] at row₂
  exact ⟨row₁.trans (dotted_reads_structural gp unifies P), row₂.trans (dotted_reads_structural gp unifies Q)⟩

/-- **COMM of the corrected step as one firing of the one-match step.** Under the side conditions of
`comm_adequacy_corrected`, each named: a principal unifier (`principal`), the variable convention
(`convention`), first-order continuations (`foP`, `foQ`), distinct made identities that are not present,
and the patterns' variables apart from the knowledge: at every fresh opening the COMM firing of the
one-rule program is admitted, the corrected step relates the redex to the dotted continuations, every
solution of the result's knowledge reads the made rows as the uniform dot, and as the manuscript's dot
wherever the unifier binds every pattern variable a continuation reads. -/
theorem comm_one_firing_corrected (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (principal : MeTTaCalculus.Corrected.Principal t u bs)
    (convention : MeTTaCalculus.Corrected.Apart t P u Q)
    (foP : MeTTaOperationsComm.firstOrder P = true) (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations)
    (base : patternAction.Consistent C.equations) {ρ : PSubst}
    (opensFreshly : (commFiring t u channel P Q ρ first second made₁ made₂).Fresh X (embed label C)) :
    (RuleSyntax.step X O E (commProgram t u channel P Q)).Admits (s := embed label C)
        (commFiring t u channel P Q ρ first second made₁ made₂) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor t channel P) (pFor u channel Q)) (par (applyDot bs P) (applyDot bs Q)) ∧
      (∀ σ : PSubst, patternAction.Models σ
          ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₁) =
            psubst σ (MeTTaCalculus.Corrected.uniformDot (pvars t ++ pvars u) bs P) ∧
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
            (embed label C)).label made₂) =
            psubst σ (MeTTaCalculus.Corrected.uniformDot (pvars t ++ pvars u) bs Q)) ∧
      ((∀ v ∈ pvars P ++ pvars Q, v ∈ pvars t ++ pvars u → ∃ w, bs.lookup v = some w) →
        ∀ σ : PSubst, patternAction.Models σ
            ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
          psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
              (embed label C)).label made₁) = psubst σ (applyDot bs P) ∧
            psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X
              (embed label C)).label made₂) = psubst σ (applyDot bs Q)) := by
  have first' : unopenedLabels label t u P Q made₁ made₂ first = pFor t channel P :=
    (unopenedLabels_other label t u P Q (ne_of_present present₁ fresh₁)
      (ne_of_present present₁ fresh₂)).trans labelFirst
  have second' : unopenedLabels label t u P Q made₁ made₂ second = pFor u channel Q :=
    (unopenedLabels_other label t u P Q (ne_of_present present₂ fresh₁)
      (ne_of_present present₂ fresh₂)).trans labelSecond
  obtain ⟨valid, manuscript, uniform, bound⟩ := MeTTaCalculus.Corrected.comm_adequacy_corrected
    (unopenedLabels label t u P Q made₁ made₂) t u channel P Q bs principal convention foP foQ C first
    second made₁ made₂ first' second' distinct madeDistinct present₁ present₂ fresh₁ fresh₂
    (unopenedLabels_made₁ label t u P Q madeDistinct) (unopenedLabels_made₂ label t u P Q made₁ made₂)
    apart base
  have lift : ∀ σ : PSubst, patternAction.Models σ
      ((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).knowledge →
      patternAction.Models σ ((commSelection first second made₁ made₂).result
          (unopenedLabels label t u P Q made₁ made₂) (commRule t u channel P Q) C).equations ∧
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label
            made₁) = psubst σ (unopenedLabels label t u P Q made₁ made₂ made₁) ∧
        psubst σ (((commFiring t u channel P Q ρ first second made₁ made₂).result X (embed label C)).label
            made₂) = psubst σ (unopenedLabels label t u P Q made₁ made₂ made₂) :=
    fun σ solved => reads_of_unopened label C t u channel P Q ρ first second made₁ made₂ labelFirst
      labelSecond madeDistinct present₁ present₂ fresh₁ fresh₂ solved
  obtain ⟨σ₀, known, unifies⟩ := solution_of_valid valid
  refine ⟨comm_admits_reading label t u channel P Q C first second made₁ made₂
    (fun σ _ => congrArg (psubst σ) labelFirst) (fun σ _ => congrArg (psubst σ) labelSecond) distinct
    madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly, manuscript,
    fun σ solved => ?_, fun binds σ solved => ?_⟩
  · obtain ⟨unopened, row₁, row₂⟩ := lift σ solved
    obtain ⟨read₁, read₂⟩ := uniform σ unopened
    exact ⟨row₁.trans read₁, row₂.trans read₂⟩
  · obtain ⟨unopened, row₁, row₂⟩ := lift σ solved
    obtain ⟨read₁, read₂⟩ := bound binds σ unopened
    exact ⟨row₁.trans read₁, row₂.trans read₂⟩

end Variants

#print axioms agree_of_psubst_eq
#print axioms psubst_dotted_congr
#print axioms fresh_of_renaming
#print axioms exists_apart_renaming
#print axioms exists_fresh_opening
#print axioms information_amalgamates_matched
#print axioms opened_refines_reading
#print axioms opened_refines
#print axioms glued_solution
#print axioms solution_of_valid
#print axioms comm_admits_reading
#print axioms reads_of_unopened
#print axioms comm_one_firing
#print axioms comm_one_transition
#print axioms comm_firstOrderOn
#print axioms fresh_moves
#print axioms unopened_not_opensProgram
#print axioms fresh_moves_dotted
#print axioms opened_row_moves
#print axioms opened_row_moves₂
#print axioms comm_admitted
#print axioms comm_one_firing_reading
#print axioms principal_of_groundPrincipal
#print axioms groundPrincipal_of_principal
#print axioms dotted_reads_structural
#print axioms dotted_reads
#print axioms comm_one_firing_open
#print axioms comm_one_firing_structural
#print axioms comm_one_firing_corrected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm
