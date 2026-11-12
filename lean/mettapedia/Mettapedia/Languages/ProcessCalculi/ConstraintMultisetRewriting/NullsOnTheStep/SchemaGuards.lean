import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.CodeOnlyLoading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluation

/-!
# Guards with three outcomes, and absence over stored schemas

## Three outcomes on any step

A guard has a meaning, a predicate on the solutions of a firing's information, as in
`Interface.Step.guarded`. Its evaluation (`ThreeValued`) answers `holds`, `fails` or `noVerdict`,
and must be sound: `holds` only where the meaning is entailed, `fails` only where it is not. The step
of the evaluation admits a prepared candidate exactly when the evaluation holds (`ThreeValued.step`).

The three answers are the outcomes of the step's existing evaluation interface
(`Interface.Step.Evaluation.Attempt`) on the guarded step: `holds` is an admission with its
evidence, `fails` (or no preparation) is a refusal with its refutation, and `noVerdict` is
unresolved work, which makes no negative claim (`ThreeValued.attempt`).

* `noVerdict_unresolved`: **no verdict is never an admission and never a refusal**: its attempt is
  unresolved.
* `admitted_sound`, `toGuarded`: every admission of the evaluation is an admission of the meaning,
  and every run is a run of the guarded step; refusals carry their refutation by their type.
* `refines_keeps_attempt`: an evaluation that keeps every verdict of another changes only
  unresolved attempts.
* `evaluate_halts_unresolved`, `evaluate_sound`: driven by the existing budgeted evaluator, a
  candidate without a verdict halts the run as unresolved work, in the state it was proposed at.

## Absence over stored schemas

A stored schema (`storedSchema`) is a pattern whose holes are private: the occurrence stands for
every instance (`Stands`). Absence of a term over a store (`SchemaAbsent`) means that no present
label stands for it. The evaluation available today (`evalRef`) compares ground labels and answers no
verdict as soon as a stored schema is present; `evalHead` also refutes a match by the shape of the
pattern, and keeps every verdict of `evalRef` (`head_refines_reference`).

* `noVerdict_both_ways`: with the schema `A(_)` stored, the reference evaluation gives no verdict for
  `A(7)`, which is not absent, and for `B(7)`, which is. Turning no verdict into a refusal would
  refuse the second; turning it into an admission would accept the first.
* `unresolved_then_admitted`: a firing guarded by the absence of `B(7)` is unresolved under the
  reference evaluation and admitted under the evaluation by shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep

/-- The three outcomes of evaluating a guard. -/
inductive Verdict where
  | holds
  | fails
  | noVerdict
  deriving DecidableEq

universe uO uT uH uOcc uS uF

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

/-- **A guard evaluated in three outcomes**, sound for its meaning. -/
structure ThreeValued (E : Interface.EffectCore X O State Firing)
    (meaning : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop) where
  eval : ∀ {s : State} (f : Firing s), E.Prepares f → Verdict
  holds_sound : ∀ {s : State} (f : Firing s) (p : E.Prepares f), eval f p = .holds →
    X.Entails (E.information f) (meaning f)
  fails_sound : ∀ {s : State} (f : Firing s) (p : E.Prepares f), eval f p = .fails →
    ¬ X.Entails (E.information f) (meaning f)

namespace ThreeValued

variable {E : Interface.EffectCore X O State Firing}
  {meaning : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop}
  (G : ThreeValued E meaning)

/-- The step of the evaluation: admitted exactly when prepared and the evaluation holds. -/
def step : Interface.Step X O State Firing := Interface.Step.ofEffect E fun f p => G.eval f p = .holds

open Interface.Step.Evaluation (Attempt evaluate)

/-- **The attempt of a candidate** on the guarded step: holds is an admission with its evidence,
fails or no preparation is a refusal with its refutation, and no verdict is unresolved work. -/
noncomputable def attempt {s : State} (f : Firing s) : Attempt (Interface.Step.guarded E meaning) s := by
  classical
  exact if p : E.Prepares f then
    match verdict : G.eval f p with
    | .holds => .admitted f ⟨p, G.holds_sound f p verdict⟩
    | .fails => .refused f (fun ⟨_, entailed⟩ => G.fails_sound f p verdict entailed)
    | .noVerdict => .unresolved (some f)
  else .refused f (fun ⟨prepared, _⟩ => p prepared)

theorem attempt_of_noVerdict {s : State} {f : Firing s} (p : E.Prepares f)
    (none : G.eval f p = .noVerdict) : G.attempt f = .unresolved (some f) := by
  unfold attempt
  rw [dif_pos p]
  split
  · rename_i verdict
    rw [none] at verdict
    cases verdict
  · rename_i verdict
    rw [none] at verdict
    cases verdict
  · rfl

theorem attempt_of_holds {s : State} {f : Firing s} (p : E.Prepares f)
    (holds : G.eval f p = .holds) : ∃ permission, G.attempt f = .admitted f permission := by
  unfold attempt
  rw [dif_pos p]
  split
  · exact ⟨⟨p, G.holds_sound f p holds⟩, rfl⟩
  · rename_i verdict
    rw [holds] at verdict
    cases verdict
  · rename_i verdict
    rw [holds] at verdict
    cases verdict

theorem attempt_of_fails {s : State} {f : Firing s} (p : E.Prepares f)
    (fails : G.eval f p = .fails) : ∃ refutation, G.attempt f = .refused f refutation := by
  unfold attempt
  rw [dif_pos p]
  split
  · rename_i verdict
    rw [fails] at verdict
    cases verdict
  · exact ⟨fun ⟨_, entailed⟩ => G.fails_sound f p fails entailed, rfl⟩
  · rename_i verdict
    rw [fails] at verdict
    cases verdict

theorem attempt_of_unprepared {s : State} {f : Firing s} (p : ¬ E.Prepares f) :
    ∃ refutation, G.attempt f = .refused f refutation := by
  unfold attempt
  rw [dif_neg p]
  exact ⟨fun ⟨prepared, _⟩ => p prepared, rfl⟩

/-- **Admission of the evaluation is an admitted attempt.** -/
theorem admits_iff_attempt {s : State} (f : Firing s) :
    G.step.Admits f ↔ ∃ permission, G.attempt f = .admitted f permission := by
  constructor
  · rintro ⟨p, holds⟩
    exact G.attempt_of_holds p holds
  · rintro ⟨_, same⟩
    by_cases p : E.Prepares f
    · refine ⟨p, ?_⟩
      cases verdict : G.eval f p with
      | holds => exact verdict
      | fails =>
          obtain ⟨_, other⟩ := G.attempt_of_fails p verdict
          rw [other] at same
          cases same
      | noVerdict =>
          rw [G.attempt_of_noVerdict p verdict] at same
          cases same
    · obtain ⟨_, other⟩ := G.attempt_of_unprepared p
      rw [other] at same
      cases same

/-- **No verdict is never an admission and never a refusal**: its attempt is unresolved. -/
theorem noVerdict_unresolved {s : State} {f : Firing s} (p : E.Prepares f)
    (none : G.eval f p = .noVerdict) :
    G.attempt f = .unresolved (some f) ∧ ¬ G.step.Admits f ∧
      ∀ (g : Firing s) (refutation : ¬ (Interface.Step.guarded E meaning).Admits g),
        G.attempt f ≠ .refused g refutation := by
  have unresolved := G.attempt_of_noVerdict p none
  refine ⟨unresolved, ?_, fun g refutation same => ?_⟩
  · rintro ⟨_, holds⟩
    have holdsHere : G.eval f p = .holds := holds
    rw [none] at holdsHere
    cases holdsHere
  · rw [unresolved] at same
    cases same

/-- **Every admission of the evaluation is an admission of the meaning.** -/
theorem admitted_sound {s : State} {f : Firing s} (admitted : G.step.Admits f) :
    (Interface.Step.guarded E meaning).Admits f := by
  obtain ⟨p, holds⟩ := admitted
  exact ⟨p, G.holds_sound f p holds⟩

/-- Every run of the evaluation is a run of the guarded step. -/
def toGuarded : ∀ {s : State}, G.step.Run s → (Interface.Step.guarded E meaning).Run s
  | _, .nil s => .nil s
  | _, .cons f admitted rest => .cons f (G.admitted_sound admitted) (toGuarded rest)

/-- An evaluation that keeps every verdict of another. -/
def Refines (G' : ThreeValued E meaning) : Prop :=
  ∀ {s : State} (f : Firing s) (p : E.Prepares f), G.eval f p ≠ .noVerdict → G'.eval f p = G.eval f p

/-- **A refinement changes only unresolved attempts.** -/
theorem refines_keeps_attempt {G' : ThreeValued E meaning} (refines : G.Refines G') {s : State}
    {f : Firing s} (decided : ∀ candidate, G.attempt f ≠ .unresolved candidate) :
    G'.attempt f = G.attempt f := by
  by_cases p : E.Prepares f
  · cases verdict : G.eval f p with
    | holds =>
        obtain ⟨_, mine⟩ := G.attempt_of_holds p verdict
        obtain ⟨_, theirs⟩ :=
          G'.attempt_of_holds p ((refines f p (by rw [verdict]; decide)).trans verdict)
        rw [mine, theirs]
    | fails =>
        obtain ⟨_, mine⟩ := G.attempt_of_fails p verdict
        obtain ⟨_, theirs⟩ :=
          G'.attempt_of_fails p ((refines f p (by rw [verdict]; decide)).trans verdict)
        rw [mine, theirs]
    | noVerdict => exact absurd (G.attempt_of_noVerdict p verdict) (decided _)
  · obtain ⟨_, mine⟩ := G.attempt_of_unprepared p
    obtain ⟨_, theirs⟩ := G'.attempt_of_unprepared p
    rw [mine, theirs]

/-- A strategy proposing one candidate at each state, decided by the evaluation. -/
noncomputable def strategy (choose : (s : State) → Firing s) (s : State) :
    Attempt (Interface.Step.guarded E meaning) s :=
  G.attempt (choose s)

/-- **A candidate without a verdict halts the existing evaluator as unresolved work**, at the state
it was proposed at. -/
theorem evaluate_halts_unresolved (choose : (s : State) → Firing s) (fuel : ℕ) {s : State}
    (p : E.Prepares (choose s)) (none : G.eval (choose s) p = .noVerdict) :
    evaluate (Interface.Step.guarded E meaning) (G.strategy choose) (fuel + 1) s =
      ⟨.nil s, .unresolved (some (choose s))⟩ := by
  have selected : G.strategy choose s = .unresolved (some (choose s)) := G.attempt_of_noVerdict p none
  simp [evaluate, selected]
  rfl

end ThreeValued

end Generic

/-! ## Absence over stored schemas -/

namespace StoredSchemas

open NamesOnTheStep NamesOnTheStep.IssuingControls NamesOnTheStep.CodeOnlyLoading

/-- Read a stored pattern back. -/
def decodePat : Expr → Option Pat
  | .app (.sym 201) (.code e) => some (.lit e)
  | .app (.sym 202) (.sym i) => some (.hole i)
  | .app (.app (.sym 203) f) a => do
      let f' ← decodePat f
      let a' ← decodePat a
      pure (.app f' a')
  | _ => none

theorem decodePat_encode : ∀ p : Pat, decodePat p.encode = some p
  | .lit _ => rfl
  | .hole _ => rfl
  | .app f a => by simp [Pat.encode, decodePat, decodePat_encode f, decodePat_encode a]

/-- A stored schema: a pattern whose holes are private to it. -/
def storedSchema (p : Pat) : Expr := .app (.sym 210) p.encode

def schemaOf : Expr → Option Pat
  | .app (.sym 210) e => decodePat e
  | _ => none

theorem schemaOf_stored (p : Pat) : schemaOf (storedSchema p) = some p := by
  simp [storedSchema, schemaOf, decodePat_encode]

/-- **What a present label stands for**: every instance of a stored schema; itself otherwise. -/
def Stands (label e : Expr) : Prop :=
  match schemaOf label with
  | some p => ∃ σ : ℕ → Expr, p.inst σ = e
  | none => label = e

/-- **Absence over stored schemas**: no present label stands for the term. -/
def SchemaAbsent (q : Expr) (C : Conf) : Prop := ∀ o ∈ C.present, ¬ Stands o.1 q

/-- The evaluation available today: ground labels are compared, and any stored schema leaves no
verdict. -/
def evalRef (q : Expr) (C : Conf) : Verdict :=
  if ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q then .fails
  else if ∃ o ∈ C.present, schemaOf o.1 ≠ none then .noVerdict
  else .holds

/-- Whether a pattern could have the term as an instance, by shape. -/
def couldMatch : Pat → Expr → Bool
  | .hole _, _ => true
  | .lit e, e' => decide (e = e')
  | .app f a, .app f' a' => couldMatch f f' && couldMatch a a'
  | .app _ _, _ => false

/-- An instance is never refuted by shape. -/
theorem couldMatch_inst (σ : ℕ → Expr) : ∀ p : Pat, couldMatch p (p.inst σ) = true
  | .hole _ => rfl
  | .lit _ => by simp [couldMatch, Pat.inst]
  | .app f a => by simp [couldMatch, Pat.inst, couldMatch_inst σ f, couldMatch_inst σ a]

/-- The evaluation by shape: as `evalRef`, and a stored schema that cannot match leaves a verdict. -/
def evalHead (q : Expr) (C : Conf) : Verdict :=
  if ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q then .fails
  else if ∃ o ∈ C.present, (schemaOf o.1).any (fun p => couldMatch p q) = true then .noVerdict
  else .holds

theorem stands_of_ground {label e : Expr} (ground : schemaOf label = none) :
    Stands label e ↔ label = e := by
  unfold Stands
  split
  · rename_i p stored
    rw [ground] at stored
    cases stored
  · exact Iff.rfl

theorem evalRef_holds {q : Expr} {C : Conf} (holds : evalRef q C = .holds) : SchemaAbsent q C := by
  unfold evalRef at holds
  by_cases witness : ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q
  · rw [if_pos witness] at holds
    cases holds
  · rw [if_neg witness] at holds
    by_cases schema : ∃ o ∈ C.present, schemaOf o.1 ≠ none
    · rw [if_pos schema] at holds
      cases holds
    · intro o present stands
      have ground : schemaOf o.1 = none := by
        by_contra notGround
        exact schema ⟨o, present, notGround⟩
      exact witness ⟨o, present, ground, (stands_of_ground ground).mp stands⟩

theorem evalRef_fails {q : Expr} {C : Conf} (fails : evalRef q C = .fails) : ¬ SchemaAbsent q C := by
  unfold evalRef at fails
  by_cases witness : ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q
  · obtain ⟨o, present, ground, same⟩ := witness
    exact fun absent => absent o present ((stands_of_ground ground).mpr same)
  · rw [if_neg witness] at fails
    by_cases schema : ∃ o ∈ C.present, schemaOf o.1 ≠ none
    · rw [if_pos schema] at fails
      cases fails
    · rw [if_neg schema] at fails
      cases fails

theorem evalHead_holds {q : Expr} {C : Conf} (holds : evalHead q C = .holds) :
    SchemaAbsent q C := by
  unfold evalHead at holds
  by_cases witness : ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q
  · rw [if_pos witness] at holds
    cases holds
  · rw [if_neg witness] at holds
    by_cases schema : ∃ o ∈ C.present, (schemaOf o.1).any (fun p => couldMatch p q) = true
    · rw [if_pos schema] at holds
      cases holds
    · intro o present stands
      cases stored : schemaOf o.1 with
      | none => exact witness ⟨o, present, stored, (stands_of_ground stored).mp stands⟩
      | some p =>
          simp only [Stands, stored] at stands
          obtain ⟨σ, rfl⟩ := stands
          exact schema ⟨o, present, by rw [stored]; simp [couldMatch_inst]⟩

theorem evalHead_fails {q : Expr} {C : Conf} (fails : evalHead q C = .fails) :
    ¬ SchemaAbsent q C := by
  unfold evalHead at fails
  by_cases witness : ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q
  · obtain ⟨o, present, ground, same⟩ := witness
    exact fun absent => absent o present ((stands_of_ground ground).mpr same)
  · rw [if_neg witness] at fails
    by_cases schema : ∃ o ∈ C.present, (schemaOf o.1).any (fun p => couldMatch p q) = true
    · rw [if_pos schema] at fails
      cases fails
    · rw [if_neg schema] at fails
      cases fails

/-! ### On the first-order step -/

/-- The absence patterns a rule asks. -/
def absences (r : RuleInstance Expr) : List Expr :=
  r.checks.filterMap fun
    | .absent q => some q
    | _ => none

/-- Combine the verdicts of several guards. -/
def combine (verdicts : List Verdict) : Verdict :=
  if .fails ∈ verdicts then .fails else if .noVerdict ∈ verdicts then .noVerdict else .holds

/-- The meaning: every asked absence holds over stored schemas. -/
abbrev meaning : ∀ {_C : Conf} (_f : Fir) (_b : PUnit.{1}), Unit → Prop :=
  fun {C} f _ _ => ∀ q ∈ absences f.rule, SchemaAbsent q C

theorem combine_holds {verdicts : List Verdict} (holds : combine verdicts = .holds) :
    ∀ v ∈ verdicts, v = .holds := by
  unfold combine at holds
  by_cases failed : Verdict.fails ∈ verdicts
  · rw [if_pos failed] at holds
    cases holds
  · rw [if_neg failed] at holds
    by_cases none : Verdict.noVerdict ∈ verdicts
    · rw [if_pos none] at holds
      cases holds
    · intro v member
      cases v with
      | holds => rfl
      | fails => exact absurd member failed
      | noVerdict => exact absurd member none

theorem combine_fails {verdicts : List Verdict} (fails : combine verdicts = .fails) :
    Verdict.fails ∈ verdicts := by
  unfold combine at fails
  by_cases failed : Verdict.fails ∈ verdicts
  · exact failed
  · rw [if_neg failed] at fails
    by_cases none : Verdict.noVerdict ∈ verdicts
    · rw [if_pos none] at fails
      cases fails
    · rw [if_neg none] at fails
      cases fails

/-- A three-valued evaluation of stored-schema absence on the first-order step, from any sound
evaluation of single absences. -/
def onStep (eval : Expr → Conf → Verdict)
    (holds : ∀ {q C}, eval q C = .holds → SchemaAbsent q C)
    (fails : ∀ {q C}, eval q C = .fails → ¬ SchemaAbsent q C) :
    ThreeValued base.toEffectCore @meaning where
  eval := fun {C} f _ => combine ((absences f.rule).map fun q => eval q C)
  holds_sound := by
    intro C f _ combined b u _ q member
    exact holds (combine_holds combined _ (List.mem_map_of_mem member))
  fails_sound := by
    intro C f p combined entailed
    obtain ⟨q, member, verdict⟩ := List.mem_map.mp (combine_fails combined)
    obtain ⟨b, u, solved⟩ := p.2.2
    exact fails verdict (entailed b u solved q member)

/-- The reference evaluation on the step. -/
def reference : ThreeValued base.toEffectCore @meaning := onStep evalRef evalRef_holds evalRef_fails

/-- The evaluation by shape on the step. -/
def byShape : ThreeValued base.toEffectCore @meaning := onStep evalHead evalHead_holds evalHead_fails

/-- **The evaluation by shape keeps every verdict of the reference.** -/
theorem head_refines_reference : reference.Refines byShape := by
  intro C f _ decided
  show combine ((absences f.rule).map fun q => evalHead q C) =
    combine ((absences f.rule).map fun q => evalRef q C)
  have same : ∀ q, evalRef q C ≠ .noVerdict → evalHead q C = evalRef q C := by
    intro q notNone
    unfold evalRef at notNone ⊢
    unfold evalHead
    by_cases witness : ∃ o ∈ C.present, schemaOf o.1 = none ∧ o.1 = q
    · rw [if_pos witness, if_pos witness]
    · rw [if_neg witness] at notNone ⊢
      rw [if_neg witness]
      by_cases schema : ∃ o ∈ C.present, schemaOf o.1 ≠ none
      · rw [if_pos schema] at notNone
        exact absurd rfl notNone
      · rw [if_neg schema]
        have noMatch : ¬ ∃ o ∈ C.present, (schemaOf o.1).any (fun p => couldMatch p q) = true := by
          rintro ⟨o, present, matching⟩
          apply schema
          refine ⟨o, present, fun ground => ?_⟩
          rw [ground] at matching
          simp at matching
        rw [if_neg noMatch]
  change combine ((absences f.rule).map fun q => evalRef q C) ≠ .noVerdict at decided
  unfold combine at decided ⊢
  by_cases failed : Verdict.fails ∈ (absences f.rule).map fun q => evalRef q C
  · obtain ⟨q, member, verdict⟩ := List.mem_map.mp failed
    have verdictRef : evalRef q C = .fails := verdict
    have headFails : Verdict.fails ∈ (absences f.rule).map fun q => evalHead q C :=
      List.mem_map.mpr ⟨q, member, (same q (by rw [verdictRef]; decide)).trans verdictRef⟩
    rw [if_pos failed, if_pos headFails]
  · rw [if_neg failed] at decided ⊢
    by_cases none : Verdict.noVerdict ∈ (absences f.rule).map fun q => evalRef q C
    · rw [if_pos none] at decided
      exact absurd rfl decided
    · rw [if_neg none]
      have allHold : ∀ q ∈ absences f.rule, evalRef q C = .holds := by
        intro q member
        cases verdict : evalRef q C with
        | holds => rfl
        | fails => exact absurd (List.mem_map.mpr ⟨q, member, verdict⟩) failed
        | noVerdict => exact absurd (List.mem_map.mpr ⟨q, member, verdict⟩) none
      have headHold : ∀ q ∈ absences f.rule, evalHead q C = .holds := fun q member =>
        (same q (by rw [allHold q member]; decide)).trans (allHold q member)
      have noFail : Verdict.fails ∉ (absences f.rule).map fun q => evalHead q C := by
        intro member
        obtain ⟨q, inAbsences, verdict⟩ := List.mem_map.mp member
        rw [headHold q inAbsences] at verdict
        cases verdict
      have noNone : Verdict.noVerdict ∉ (absences f.rule).map fun q => evalHead q C := by
        intro member
        obtain ⟨q, inAbsences, verdict⟩ := List.mem_map.mp member
        rw [headHold q inAbsences] at verdict
        cases verdict
      rw [if_neg noFail, if_neg noNone]

/-! ### Controls -/

/-- The schema `A(_)`. -/
def schemaA : Expr := storedSchema (.app (.lit (.sym 13)) (.hole 0))

/-- The store holding the schema `A(_)`. -/
def schemaStore : Conf := ⟨[], {(schemaA, 0)}⟩

/-- **No verdict, both ways.** The reference evaluation gives no verdict for `A(7)`, which is not
absent, and for `B(7)`, which is. -/
theorem noVerdict_both_ways :
    evalRef (factA (.sym 7)) schemaStore = .noVerdict ∧ ¬ SchemaAbsent (factA (.sym 7)) schemaStore ∧
      evalRef (factB (.sym 7)) schemaStore = .noVerdict ∧ SchemaAbsent (factB (.sym 7)) schemaStore := by
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro absent
    apply absent (schemaA, 0) (by simp [schemaStore])
    simp only [Stands, schemaA, schemaOf_stored]
    exact ⟨fun _ => .sym 7, rfl⟩
  · intro o present stands
    simp only [schemaStore, Finset.mem_singleton] at present
    subst present
    simp only [Stands, schemaA, schemaOf_stored] at stands
    obtain ⟨σ, same⟩ := stands
    simp [Pat.inst, factB] at same

/-- A firing guarded by the absence of `B(7)`, making `V(7)`. -/
def guardedB : Fir := ⟨rule [] [] [factV (.sym 7)] [.absent (factB (.sym 7))], [],
  ⟨[], [], [(factV (.sym 7), 0)]⟩⟩

theorem guardedB_prepared : base.toEffectCore.Prepares (s := schemaStore) guardedB := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, by decide, PUnit.unit, (), ?_⟩
  intro e member
  exact absurd (show e ∈ ([] : List (Equation Expr)) from member) List.not_mem_nil

/-- **Unresolved, then admitted**: under the reference evaluation the guarded firing's attempt is
unresolved work, neither admitted nor refused; under the evaluation by shape it is admitted. -/
theorem unresolved_then_admitted :
    reference.attempt (s := schemaStore) guardedB = .unresolved (some guardedB) ∧
      ¬ reference.step.Admits (s := schemaStore) guardedB ∧
      byShape.step.Admits (s := schemaStore) guardedB := by
  have none : reference.eval (s := schemaStore) guardedB guardedB_prepared = .noVerdict := by decide
  obtain ⟨unresolved, notAdmitted, _⟩ := reference.noVerdict_unresolved guardedB_prepared none
  exact ⟨unresolved, notAdmitted, guardedB_prepared, by decide⟩

end StoredSchemas

#print axioms ThreeValued.noVerdict_unresolved
#print axioms ThreeValued.admits_iff_attempt
#print axioms ThreeValued.admitted_sound
#print axioms ThreeValued.refines_keeps_attempt
#print axioms ThreeValued.evaluate_halts_unresolved
#print axioms StoredSchemas.evalRef_holds
#print axioms StoredSchemas.evalHead_holds
#print axioms StoredSchemas.head_refines_reference
#print axioms StoredSchemas.noVerdict_both_ways
#print axioms StoredSchemas.unresolved_then_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep
