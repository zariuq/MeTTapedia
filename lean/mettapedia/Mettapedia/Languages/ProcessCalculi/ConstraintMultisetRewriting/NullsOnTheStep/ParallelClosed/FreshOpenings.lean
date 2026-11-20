import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.StartPrivacy

/-!
# The line on the step with fresh openings: success is switched off only through a shared unknown

On the step of a program (`RuleSyntax.step`) at one frame over first-order terms with infinitely many
unknowns, a firing opens its rule's unknowns freshly, apart from what the state mentions, so a
neighbour cannot capture them (on the step of rule instances it can: `SharedUnknown.captor_switches`).

**Switching, in this vocabulary** (`SwitchesOff P barb D C`): the neighbour `D` and the system `C` are
composable, that is their rows are disjoint and their knowledges are solvable together; `C` alone
reaches success by a run whose made identities are new to `D` (`StepAvoiding`); and the composition
`beside D C` reaches no success.

**The line** (`switchesOff_shares`): for a program of positive rules (equation checks only, no
none queries, no count, no collect query) and a barb invariant under renaming, a neighbour switches reachable
success off only through an unknown that the system's start mentions and that the neighbour mentions,
in its knowledge or in the labels of its rows. It is the contrapositive of
`Scope.success_persists_from_start` (privacy at the start suffices: the run's own fresh unknowns are
renamed away from the neighbour's), which this module applies and does not reprove; the one-step form
is `Scope.admits_beside_iff`. The theorem speaks of what the neighbour mentions, rows included; a form
that counts only the neighbour's knowledge is not proved here.

Controls:
* **the line is not vacuous** (`shared_switches`, `shared_switches_through_x`): the neighbour whose
  knowledge `x = 6` contradicts the tell on the request's unknown switches success off, through `x`;
* **capture cannot happen** (`captor_analog_keeps`): the neighbour whose knowledge `x₁ = 7` constrains
  the unknown the request's run first opens, which the request does not mention, switches nothing
  off; on the step of rule instances the neighbour constraining the instance's own variable does
  (`SharedUnknown.captor_switches`);
* **the line is necessary, not sufficient** (`friend_keeps`): the neighbour `x = 5` shares and
  constrains the request's unknown, agrees with the tell, and success persists, so for a fixed
  program a shared, constrained unknown need not switch it off; and not even for some positive
  program: a neighbour with no rows whose equations are equations of the system's knowledge switches
  no positive program off (`repeated_knowledge_runs`), while it shares and constrains the system's
  unknown (`shared_constrained_never_switches`); a positive program that succeeds there alone succeeds
  beside it (`knowsSix_succeeds_beside`);
* **positivity is needed**: a none check is refused beside a ground row that shares nothing
  (`Scope.CompositionControls.none_refused_beside_ground`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.FreshOpenings

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open RuleSyntax
open RuleSyntax.OneFrame (Terms frames ext)
open RuleSyntax.Scope

section General

variable {sig : LPSignature} [DecidableEq sig.vars] {O : Type*} [DecidableEq O]

local notation "FO" => FirstOrder.action sig

/-- **A step of the program whose made identities avoid `I`.** -/
def StepAvoiding (P : Program (Terms (Term sig))) (I : Finset O) (C C' : State (Terms (Term sig)) O) :
    Prop :=
  ∃ f : Firing O (ext FO) P PUnit.unit, (step (frames FO) O (ext FO) P).Admits (s := C) f ∧
    (∀ o ∈ f.selection.made, o ∉ I) ∧ f.result (frames FO) C = C'

/-- **A neighbour switches the system's reachable success off**: their rows are disjoint and their
knowledges solvable together, the system alone reaches success by a run whose made identities are new
to the neighbour, and the composition reaches no success. -/
structure SwitchesOff (P : Program (Terms (Term sig))) (barb : Term sig → Prop)
    (D C : State (Terms (Term sig)) O) : Prop where
  apart : Disjoint D.present C.present
  joint : (FO).Consistent (D.knowledge ++ C.knowledge)
  alone : ∃ C', Relation.ReflTransGen (StepAvoiding P D.present) C C' ∧ Succeeds barb C'
  blocked : ¬ ∃ t, Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) (beside D C) t ∧
    Succeeds barb t

/-- **The line on the step with fresh openings**: for a program of positive rules and a barb invariant
under renaming, a neighbour that switches reachable success off shares an unknown with the system's
start: an unknown the neighbour mentions (in its knowledge or its rows) and the system's start
mentions. -/
theorem switchesOff_shares [Infinite sig.vars] {P : Program (Terms (Term sig))} {barb : Term sig → Prop}
    (positive : ∀ r ∈ P, Positive r)
    (invariant : ∀ e : sig.vars ≃ sig.vars, ∀ t, barb (Subst.applyTerm (permSubst e) t) ↔ barb t)
    {D C : State (Terms (Term sig)) O} (switches : SwitchesOff P barb D C) :
    ∃ v, UnknownsOf D.Mentions v ∧ UnknownsOf C.Mentions v := by
  by_contra shared
  have privateStart : ∀ v, UnknownsOf D.Mentions v → ¬ UnknownsOf C.Mentions v :=
    fun v inD inC => shared ⟨v, inD, inC⟩
  obtain ⟨C', run, succeeds⟩ := switches.alone
  have positiveRun : Relation.ReflTransGen (PositiveStep P D.present) C C' :=
    reflTransGen_imp (fun _ _ ⟨f, admitted, avoid, result⟩ =>
      ⟨f, admitted, positive f.rule f.member, avoid, result⟩) run
  have solvableD : (FO).Consistent D.knowledge := by
    obtain ⟨σ, solved⟩ := switches.joint
    exact ⟨σ, fun e member => solved e (List.mem_append_left _ member)⟩
  exact switches.blocked
    (success_persists_from_start invariant positiveRun succeeds switches.apart solvableD privateStart)

/-! ## The converse fails over every positive program: a neighbour that repeats the system -/

omit [DecidableEq sig.vars] [DecidableEq O] in
/-- Freshness passes to a state that mentions no more. -/
theorem fresh_mono {P : Program (Terms (Term sig))} {s s' : State (Terms (Term sig)) O}
    {f : Firing O (ext FO) P PUnit.unit} (fewer : ∀ t, s'.Mentions t → s.Mentions t)
    (fresh : f.Fresh (frames FO) s) : f.Fresh (frames FO) s' := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  exact ⟨u, fun t mentioned => onState t (fewer t mentioned), onRule⟩

omit [DecidableEq sig.vars] [DecidableEq O] in
/-- The knowledge a firing fires at is part of its information, at the one frame. -/
theorem knowledge_mem_information {P : Program (Terms (Term sig))} {C : State (Terms (Term sig)) O}
    (f : Firing O (ext FO) P PUnit.unit) {e : Equation (Term sig)} (inside : e ∈ C.knowledge) :
    e ∈ f.information (frames FO) C := by
  unfold Firing.information
  have known : (frames FO).applyStore ((ext FO).weaken f.ext) C.knowledge = C.knowledge :=
    Interface.Frames.applyStore_id (X := frames FO) C.knowledge
  rw [known]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ inside))

omit [DecidableEq sig.vars] in
/-- **One step beside a neighbour that repeats the system's knowledge.** -/
theorem repeated_step {P : Program (Terms (Term sig))} (positive : ∀ r ∈ P, Positive r)
    {D C C' : State (Terms (Term sig)) O} (noRows : D.present = ∅)
    (repeats : ∀ e ∈ D.knowledge, e ∈ C.knowledge)
    (moved : Succ (step (frames FO) O (ext FO) P).toStep C C') :
    Succ (step (frames FO) O (ext FO) P).toStep (beside D C) (beside D C') ∧
      ∀ e ∈ D.knowledge, e ∈ C'.knowledge := by
  obtain ⟨f, admitted, rfl⟩ := moved
  have apart : Disjoint D.present C.present := by
    rw [noRows]
    exact Finset.disjoint_empty_left _
  have madeNew : ∀ o ∈ f.selection.made, o ∉ D.present := by
    intro o _
    rw [noRows]
    exact Finset.notMem_empty o
  obtain ⟨fresh, -, enabled, ⟨_, σ, solved⟩, -, -⟩ := (admits_iff (s := C) f).mp admitted
  have fewer : ∀ t, (beside D C).Mentions t → C.Mentions t := by
    intro t mentioned
    rcases (mentions_beside apart t).mp mentioned with inD | inC
    · rcases inD with first | second | ⟨o, present, -⟩
      · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
        exact Or.inl (List.mem_map.mpr ⟨e, repeats e member, rfl⟩)
      · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
        exact Or.inr (Or.inl (List.mem_map.mpr ⟨e, repeats e member, rfl⟩))
      · rw [noRows] at present
        exact absurd present (Finset.notMem_empty o)
    · exact inC
  have joint : ∃ ρ, (FO).Models ρ (f.information (frames FO) C) ∧ (FO).Models ρ D.knowledge :=
    ⟨σ, solved, fun e inside => solved e (knowledge_mem_information f (repeats e inside))⟩
  refine ⟨⟨f, (admits_beside_iff FO (positive f.rule f.member) admitted apart madeNew
    (fresh_mono fewer fresh)).mpr joint, result_beside FO f apart enabled madeNew⟩,
    fun e inside => knowledge_mem_information f (repeats e inside)⟩

omit [DecidableEq sig.vars] in
/-- **A neighbour that repeats the system's knowledge switches no positive program off**: a neighbour
with no rows, each of whose equations is an equation of the system's knowledge; every run of a
positive program from the system is, beside it, a run from the composition. Its unknowns are all the
system's, and its knowledge may constrain them. -/
theorem repeated_knowledge_runs {P : Program (Terms (Term sig))} (positive : ∀ r ∈ P, Positive r)
    {D C C' : State (Terms (Term sig)) O} (noRows : D.present = ∅)
    (repeats : ∀ e ∈ D.knowledge, e ∈ C.knowledge)
    (run : Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) C C') :
    Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) (beside D C) (beside D C') ∧
      ∀ e ∈ D.knowledge, e ∈ C'.knowledge := by
  induction run with
  | refl => exact ⟨Relation.ReflTransGen.refl, repeats⟩
  | tail _ last ih =>
      obtain ⟨lifted, repeats'⟩ := ih
      obtain ⟨moved, repeats''⟩ := repeated_step positive noRows repeats' last
      exact ⟨lifted.tail moved, repeats''⟩

end General

/-! ## Controls -/

section Controls

open RuleSyntax.Examples (Tm X E x c everywhere)
open RuleSyntax.Scope.CompositionControls
open RuleSyntax.Scope.StartPrivacyControls (nine_invariant)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

theorem tellProgram_positive : ∀ r ∈ tellProgram, Positive r := by
  intro r member
  have isTell : r = tellRule := member
  rw [isTell]
  exact tellRule_positive

/-- **The line is not vacuous**: the neighbour whose knowledge `x = 6` contradicts the tell switches
the request's success off. -/
theorem shared_switches : SwitchesOff tellProgram (· = c 9) neighbour request :=
  ⟨neighbour_apart, shared_composable.2,
    ⟨_, .single ⟨tellAt, tellAt_admitted, by simp [neighbour], rfl⟩, result_succeeds⟩,
    shared_success_unreachable⟩

/-- **It does so through the request's unknown `x`.** -/
theorem shared_switches_through_x : UnknownsOf neighbour.Mentions 0 ∧ UnknownsOf request.Mentions 0 :=
  ⟨⟨x, Or.inl (by simp [neighbour]), by simp [x, Term.freeVars]⟩,
    ⟨x, Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩), by simp [x, Term.freeVars]⟩⟩

/-- A neighbour constraining the unknown `x₁` that the request's run first opens: no rows, and the
knowledge `x₁ = 7`. -/
def captorAnalog : State Tm ℕ := ⟨PUnit.unit, [(.var 1, c 7)], ∅, fun _ => c 0⟩

theorem captorAnalog_unknowns {v : ℕ} (inside : UnknownsOf captorAnalog.Mentions v) : v = 1 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [captorAnalog, List.map_cons, List.map_nil, List.mem_singleton] at first
    subst first
    exact freeVars_var 1 member
  · simp only [captorAnalog, List.map_cons, List.map_nil, List.mem_singleton] at second
    subst second
    exact (freeVars_const 7 member).elim
  · simp [captorAnalog] at present

/-- **Capture cannot happen with fresh openings**: the neighbour constraining the unknown the
request's run first opens does not switch success off, by the line, since it shares no unknown with
the request; the run opens its rule's unknown elsewhere. -/
theorem captor_analog_keeps : ¬ SwitchesOff tellProgram (· = c 9) captorAnalog request := by
  intro switches
  obtain ⟨v, inD, inC⟩ :=
    switchesOff_shares (barb := (· = c 9)) tellProgram_positive nine_invariant switches
  have one := captorAnalog_unknowns inD
  obtain ⟨t, mentioned, member⟩ := inC
  rw [request_mentions mentioned] at member
  have zero := freeVars_var 0 member
  omega

/-- **A neighbour that shares and constrains the request's unknown and agrees with the tell**: no rows,
and the knowledge `x = 5`. -/
def friendState : State Tm ℕ := ⟨PUnit.unit, [(x, c 5)], ∅, fun _ => c 0⟩

theorem friend_mentions {t : Term atoms} (mentioned : friendState.Mentions t) : t = x ∨ t = c 5 := by
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [friendState, List.map_cons, List.map_nil, List.mem_singleton] at first
    exact Or.inl first
  · simp only [friendState, List.map_cons, List.map_nil, List.mem_singleton] at second
    exact Or.inr second
  · simp [friendState] at present

theorem tellAt_fresh_beside_friend : tellAt.Fresh X (beside friendState request) := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · intro t mentioned
    rcases (mentions_beside (Finset.disjoint_empty_left _) t).mp mentioned with inD | inC
    · rcases friend_mentions inD with rfl | rfl <;> rfl
    · rw [request_mentions inC]
      rfl
  · intro t member
    rcases tellRule_terms member with rfl | rfl | rfl <;> rfl

theorem tellAt_beside_friend :
    (step X ℕ E tellProgram).Admits (s := beside friendState request) tellAt :=
  (admits_beside_iff action tellRule_positive tellAt_admitted (Finset.disjoint_empty_left _)
    (by simp [friendState]) tellAt_fresh_beside_friend).mpr
    ⟨everywhere 5, fun e member => by
        rw [tellAt_information] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl,
      fun e member => by
        simp only [friendState, List.mem_singleton] at member
        subst member
        rfl⟩

/-- **The line is necessary, not sufficient**: the friend shares the request's unknown `x` and
constrains it, the two are composable, and beside it the request still reaches success. -/
theorem friend_keeps :
    UnknownsOf friendState.Mentions 0 ∧ UnknownsOf request.Mentions 0 ∧
      Disjoint friendState.present request.present ∧
      action.Consistent (friendState.knowledge ++ request.knowledge) ∧
      ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) (beside friendState request) t ∧
        Succeeds (· = c 9) t := by
  refine ⟨⟨x, Or.inl (by simp [friendState]), by simp [x, Term.freeVars]⟩,
    ⟨x, Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩), by simp [x, Term.freeVars]⟩,
    Finset.disjoint_empty_left _,
    ⟨everywhere 5, fun e member => by
      simp only [friendState, request, List.append_nil, List.mem_singleton] at member
      subst member
      rfl⟩, ?_⟩
  refine ⟨_, .single ⟨tellAt, tellAt_beside_friend, rfl⟩, ?_⟩
  show Succeeds (· = c 9) (tellAt.result X (beside friendState request))
  rw [result_beside action tellAt (Finset.disjoint_empty_left _) tellAt_admitted.2.1
    (by simp [friendState])]
  exact succeeds_beside (Finset.disjoint_empty_left _) result_succeeds

/-- The system that knows `x = 6`, with a row `x`. -/
def knowsSix : State Tm ℕ := ⟨PUnit.unit, [(x, c 6)], {0}, fun _ => x⟩

/-- **The converse of the line fails over every positive program**: the neighbour `x = 6` shares the
unknown `x` with the system that already knows `x = 6`, and constrains it (no solution of its knowledge
sends `x` to `7`), yet it switches no positive program off, whatever the barb
(`repeated_knowledge_runs`). -/
theorem shared_constrained_never_switches :
    UnknownsOf neighbour.Mentions 0 ∧ UnknownsOf knowsSix.Mentions 0 ∧
      (¬ ∃ σ : Subst atoms, action.Models σ neighbour.knowledge ∧ σ 0 = c 7) ∧
      ∀ (P : Program Tm) (barb : Term atoms → Prop), (∀ r ∈ P, Positive r) →
        ¬ SwitchesOff P barb neighbour knowsSix := by
  refine ⟨⟨x, Or.inl (by simp [neighbour]), by simp [x, Term.freeVars]⟩,
    ⟨x, Or.inl (by simp [knowsSix]), by simp [x, Term.freeVars]⟩, ?_, ?_⟩
  · rintro ⟨σ, solved, seven⟩
    have six : σ 0 = c 6 := solved (x, c 6) List.mem_cons_self
    have same : (c 6 : Term atoms) = c 7 := six.symm.trans seven
    exact absurd (Term.const.inj same) (by decide)
  · intro P barb positive switches
    obtain ⟨C', run, succeeds⟩ := switches.alone
    have plain : Relation.ReflTransGen (Succ (step X ℕ E P).toStep) knowsSix C' :=
      reflTransGen_imp (fun _ _ ⟨f, admitted, _, result⟩ => ⟨f, admitted, result⟩) run
    obtain ⟨lifted, -⟩ := repeated_knowledge_runs positive (D := neighbour) (C := knowsSix) rfl
      (fun _ inside => inside) plain
    exact switches.blocked ⟨_, lifted,
      succeeds_beside (show Disjoint neighbour.present C'.present from Finset.disjoint_empty_left _)
        succeeds⟩

/-- **Read any row, make `9`**: a positive rule with no tell and no check. -/
def readMake : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [], [c 9]⟩, []⟩

theorem readMake_positive : ∀ r ∈ ({readMake} : Program Tm), Positive r := by
  intro r member
  have isRead : r = readMake := member
  rw [isRead]
  exact ⟨fun _ member => absurd member List.not_mem_nil, rfl⟩

/-- Read row `0` of the system with the rule's unknown opened as `x₁`, make identity `1`. -/
def readAt : Firing ℕ E ({readMake} : Program Tm) PUnit.unit :=
  ⟨readMake, rfl, PUnit.unit, RuleSyntax.Examples.shift, ⟨[], [0], [1]⟩, []⟩

theorem readAt_information : readAt.information X knowsSix = [(x, c 6), (.var 1, x)] := rfl

theorem readAt_admitted : (step X ℕ E ({readMake} : Program Tm)).Admits (s := knowsSix) readAt := by
  refine (admits_iff readAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
    · intro t mentioned
      rcases mentioned with first | second | ⟨o, -, rfl⟩
      · simp only [knowsSix, List.map_cons, List.map_nil, List.mem_singleton] at first
        subst first
        rfl
      · simp only [knowsSix, List.map_cons, List.map_nil, List.mem_singleton] at second
        subst second
        rfl
      · rfl
    · intro t member
      simp only [readAt, readMake, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
        List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [readAt, knowsSix, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 6, fun e member => ?_⟩
    rw [readAt_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [readAt, readMake, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [readAt, readMake, Firing.collectOpened] at member

/-- **Existence for the converse**: the system succeeds alone by the positive program that reads a row
and makes `9`, and so, by `repeated_knowledge_runs`, beside the neighbour that repeats its knowledge. -/
theorem knowsSix_succeeds_beside :
    (∃ t, Relation.ReflTransGen (Succ (step X ℕ E ({readMake} : Program Tm)).toStep) knowsSix t ∧
        Succeeds (· = c 9) t) ∧
      ∃ t, Relation.ReflTransGen (Succ (step X ℕ E ({readMake} : Program Tm)).toStep)
        (beside neighbour knowsSix) t ∧ Succeeds (· = c 9) t := by
  have alone : Succeeds (· = c 9) (readAt.result X knowsSix) :=
    ⟨1, by simp [Firing.result, readAt, knowsSix, fire, Selection.commit], rfl⟩
  have run : Relation.ReflTransGen (Succ (step X ℕ E ({readMake} : Program Tm)).toStep) knowsSix
      (readAt.result X knowsSix) := .single ⟨readAt, readAt_admitted, rfl⟩
  refine ⟨⟨_, run, alone⟩, ?_⟩
  obtain ⟨lifted, -⟩ := repeated_knowledge_runs readMake_positive (D := neighbour) (C := knowsSix) rfl
    (fun _ inside => inside) run
  exact ⟨_, lifted, succeeds_beside
    (show Disjoint neighbour.present (readAt.result X knowsSix).present from
      Finset.disjoint_empty_left _) alone⟩

end Controls

#print axioms knowsSix_succeeds_beside
#print axioms repeated_knowledge_runs
#print axioms shared_constrained_never_switches
#print axioms switchesOff_shares
#print axioms shared_switches
#print axioms shared_switches_through_x
#print axioms captor_analog_keeps
#print axioms friend_keeps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.FreshOpenings
