import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore

/-! # Effects, independently admitted steps, and certified profiles

A step combines a semantic effect core with permission that implies preparation.
Guard semantics, literal store transport and semantic exactness are optional
certificates. `Step.Standard` is the explicit guarded, literally exact builder;
its certificates are inferred for consumers that require them. No evaluator,
coverage law or recording obligation is imposed by the general step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open MeTTaCalculus.OccurrenceCommits (Enabled fire)
universe uO uT uH

universe uOcc uS uF

/-- An effect core with an independently supplied permission predicate. -/
structure Step {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (State : Type uS) (Firing : State → Type uF) extends EffectCore X O State Firing where
  Admits : {s : State} → Firing s → Prop
  admitted_prepares : ∀ {s : State} (f : Firing s), Admits f → toEffectCore.Prepares f

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

/-- **Preparation**: everything admission asks except the guards and predicate queries. It and the
derived `result` and `settle` are reducible, as the fields they replace were: tactics see through
them to the prepared effect. -/
abbrev Prepares {s : State} (f : Firing s) : Prop :=
  P.Shapes f ∧ Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
    X.Solvable (P.information f)

/-- Optional guard semantics. This data is not determined by the admitted set alone. -/
class Guarded where
  holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (P.target f) b → Prop
  admission : ∀ {s : State} (f : Firing s),
    P.Admits f ↔ P.Prepares f ∧ X.Entails (P.information f) (holds f)

class LiteralInformation : Prop where
  contains : ∀ {s : State} (f : Firing s) (e : Equation (Tm (P.frame s))), e ∈ P.knowledge s →
    (X.act (P.extension f) e.1, X.act (P.extension f) e.2) ∈ P.information f

class LiteralKnowledge : Prop where
  knowledge : ∀ {s : State} (f : Firing s) (p : P.Prepares f),
    P.knowledge (P.preparedResult f p) = X.applyStore (P.preparedSettle f p) (P.information f)

abbrev ExactKnowledge : Prop := P.toEffectCore.ExactKnowledge

class Exact : Prop where
  exactness : P.ExactKnowledge

abbrev Holds [P.Guarded] {s : State} (f : Firing s) := Guarded.holds (P := P) f

abbrev transported [P.LiteralInformation] {s : State} (f : Firing s) :=
  LiteralInformation.contains (P := P) f

abbrev knowledge_preparedResult [P.LiteralKnowledge] {s : State}
    (f : Firing s) (p : P.Prepares f) := LiteralKnowledge.knowledge (P := P) f p

instance literal_exact [P.LiteralKnowledge] : P.Exact where
  exactness f p := by
    intro b σ solved
    rw [P.knowledge_preparedResult f p]
    exact (Frames.models_applyStore _ _ _).mpr solved

/-- An admitted firing is prepared, independently of any guard profile. -/
theorem prepares {s : State} {f : Firing s} (admitted : P.Admits f) : P.Prepares f :=
  P.admitted_prepares f admitted

theorem admits_iff_prepares [P.Guarded] {s : State} (f : Firing s) :
    P.Admits f ↔ P.Prepares f ∧ X.Entails (P.information f) (P.Holds f) :=
  Guarded.admission f

theorem admits_iff [P.Guarded] {s : State} (f : Firing s) : P.Admits f ↔ P.Shapes f ∧
    Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
    X.Solvable (P.information f) ∧ X.Entails (P.information f) (P.Holds f) :=
  (P.admits_iff_prepares f).trans
    ⟨fun ⟨⟨a,b,c⟩,d⟩ => ⟨a,b,c,d⟩, fun ⟨a,b,c,d⟩ => ⟨⟨a,b,c⟩,d⟩⟩

/-- **The result of an admitted firing**: its prepared result. -/
abbrev result {s : State} (f : Firing s) (admitted : P.Admits f) : State :=
  P.preparedResult f (P.prepares admitted)

theorem present_result {s : State} (f : Firing s) (admitted : P.Admits f) :
    P.present (P.result f admitted) = fire (P.present s) ((P.selection f).commit (T := Unit)) :=
  P.present_preparedResult f _

/-- **The settlement of an admitted firing**: its prepared settlement. The result keeps the
information along it. -/
abbrev settle {s : State} (f : Firing s) (admitted : P.Admits f) :
    Hom (P.target f) (P.frame (P.result f admitted)) :=
  P.preparedSettle f _

theorem knowledge_result [P.LiteralKnowledge] {s : State} (f : Firing s) (admitted : P.Admits f) :
    P.knowledge (P.result f admitted) = X.applyStore (P.settle f admitted) (P.information f) :=
  P.knowledge_preparedResult f _

/-- The morphism of frames a firing moves along: its extension, then its settlement. -/
def along {s : State} (f : Firing s) (admitted : P.Admits f) :
    Hom (P.frame s) (P.frame (P.result f admitted)) :=
  X.comp (P.settle f admitted) (P.extension f)

/-- An admitted firing has solvable information. -/
theorem solvable_information {s : State} {f : Firing s} (admitted : P.Admits f) :
    X.Solvable (P.information f) :=
  (P.prepares admitted).2.2

/-- The information of a firing refines the knowledge it starts from. -/
theorem models_knowledge {s : State} (f : Firing s) {b : Obj} (σ : Hom (P.target f) b)
    (solved : X.Models σ (P.information f)) :
    X.Models (X.comp σ (P.extension f)) (P.knowledge s) :=
  P.information_refines f σ solved

/-- An admitted firing starts from solvable knowledge. -/
theorem solvable_knowledge {s : State} {f : Firing s} (admitted : P.Admits f) :
    X.Solvable (P.knowledge s) := by
  obtain ⟨b, σ, solved⟩ := P.solvable_information admitted
  exact ⟨b, X.comp σ (P.extension f), P.models_knowledge f σ solved⟩

/-- **A firing only refines knowledge**: a solution after it pulls back along it. -/
theorem models_along {s : State} {f : Firing s} (admitted : P.Admits f) {b : Obj}
    (σ : Hom (P.frame (P.result f admitted)) b)
    (solved : X.Models σ (P.knowledge (P.result f admitted))) :
    X.Models (X.comp σ (P.along f admitted)) (P.knowledge s) :=
  P.toEffectCore.models_along f (P.prepares admitted) σ solved

/-- A run: a dependent word of admitted firings. -/
inductive Run : State → Type (max uS uF)
  | nil (s : State) : Run s
  | cons {s : State} (f : Firing s) (admitted : P.Admits f) (rest : Run (P.result f admitted)) : Run s

namespace Run

variable {P}

/-- The state a run ends in. -/
def last : {s : State} → P.Run s → State
  | _, .nil s => s
  | _, .cons _ _ rest => rest.last

/-- The morphism of frames a run moves along. -/
def toLast : {s : State} → (r : P.Run s) → Hom (P.frame s) (P.frame r.last)
  | _, .nil s => X.id (P.frame s)
  | _, .cons f admitted rest => X.comp rest.toLast (P.along f admitted)

/-- Its firings, each with the state it fires at. -/
def word : {s : State} → P.Run s → List ((t : State) × Firing t)
  | _, .nil _ => []
  | _, .cons f _ rest => ⟨_, f⟩ :: rest.word

/-- **Knowledge only refines along a run**: every solution of the last knowledge pulls back
to a solution of the first. -/
theorem models_start : ∀ {s : State} (r : P.Run s) {b : Obj} (σ : Hom (P.frame r.last) b),
    X.Models σ (P.knowledge r.last) → X.Models (X.comp σ r.toLast) (P.knowledge s)
  | _, .nil s, _, σ, solved =>
      (Frames.models_congr (fun t => Frames.act_comp_id σ t) (P.knowledge s)).mp solved
  | _, .cons f admitted rest, _, σ, solved => by
      have later := P.models_along admitted _ (models_start rest σ solved)
      exact (Frames.models_congr (fun t => Frames.act_comp_assoc (P.along f admitted) rest.toLast σ t)
        (P.knowledge _)).mp later

theorem solvable_start {s : State} (r : P.Run s) (solvable : X.Solvable (P.knowledge r.last)) :
    X.Solvable (P.knowledge s) := by
  obtain ⟨b, σ, solved⟩ := solvable
  exact ⟨b, X.comp σ r.toLast, r.models_start σ solved⟩

/-- Concatenation of runs: the composition of the free category of runs. -/
def append : {s : State} → (r : P.Run s) → P.Run r.last → P.Run s
  | _, .nil _, later => later
  | _, .cons f admitted rest, later => .cons f admitted (rest.append later)

theorem last_append : ∀ {s : State} (r : P.Run s) (later : P.Run r.last),
    (r.append later).last = later.last
  | _, .nil _, _ => rfl
  | _, .cons _ _ rest, later => last_append rest later

theorem word_append : ∀ {s : State} (r : P.Run s) (later : P.Run r.last),
    (r.append later).word = r.word ++ later.word
  | _, .nil _, _ => rfl
  | _, .cons _ _ rest, later => congrArg (List.cons _) (word_append rest later)

/-- **A site account**: the product of the grades of a run's firings, in order. -/
def account {M : Type*} [Monoid M] (grade : (t : State) → Firing t → M) :
    {s : State} → P.Run s → M
  | _, .nil _ => 1
  | _, .cons f _ rest => grade _ f * rest.account grade

/-- **Accounts are functors out of the free category of runs.** -/
theorem account_append {M : Type*} [Monoid M] (grade : (t : State) → Firing t → M) :
    ∀ {s : State} (r : P.Run s) (later : P.Run r.last),
      (r.append later).account grade = r.account grade * later.account grade
  | _, .nil _, _ => (one_mul _).symm
  | _, .cons f _ rest, later =>
      (congrArg (fun m => grade _ f * m) (account_append grade rest later)).trans (mul_assoc _ _ _).symm

end Run

/-- The profile's underlying shared effect. -/
abbrev effectCore : EffectCore X O State Firing := P.toEffectCore

theorem effectCore_exact [P.Exact] : P.effectCore.ExactKnowledge := Exact.exactness

def eventAdmission : P.effectCore.Admission := fun f _ => P.Admits f

theorem eventAdmission_iff {s : State} (f : Firing s) (p : P.Prepares f) :
    P.eventAdmission f p ↔ P.Admits f := Iff.rfl

def event {s : State} (f : Firing s) (a : P.Admits f) :
    P.effectCore.Event P.eventAdmission s (P.result f a) :=
  ⟨f, P.prepares a, (P.eventAdmission_iff f _).mpr a, rfl⟩

structure Standard {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (State : Type uS) (Firing : State → Type uF) extends Step X O State Firing where
  transported : ∀ {s : State} (f : Firing s) (e : Equation (Tm (frame s))), e ∈ knowledge s →
    (X.act (extension f) e.1, X.act (extension f) e.2) ∈ information f
  Holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (target f) b → Prop
  admits_iff : ∀ {s : State} (f : Firing s), Admits f ↔ Shapes f ∧
    Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧
    X.Solvable (information f) ∧ X.Entails (information f) (Holds f)
  knowledge_preparedResult : ∀ {s : State} (f : Firing s) (p : Shapes f ∧
      Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧ X.Solvable (information f)),
    knowledge (preparedResult f p) = X.applyStore (preparedSettle f p) (information f)
  information_refines := fun {s} f {_b} σ solved =>
    Frames.models_of_transport X (knowledge s) (information f) (extension f) (transported f) σ solved
  result_refines := fun {_s} f p {_b} σ solved =>
    (Frames.models_applyStore _ _ _).mp
      ((congrArg (X.Models σ) (knowledge_preparedResult f p)).mp solved)
  admitted_prepares := fun f a =>
    ⟨((admits_iff f).mp a).1, ((admits_iff f).mp a).2.1, ((admits_iff f).mp a).2.2.1⟩

instance : CoeOut (Standard X O State Firing) (Step X O State Firing) := ⟨Standard.toStep⟩

instance standard_guarded (Q : Standard X O State Firing) : Q.toStep.Guarded where
  holds := Q.Holds
  admission f := (Q.admits_iff f).trans
    ⟨fun ⟨a,b,c,d⟩ => ⟨⟨a,b,c⟩,d⟩, fun ⟨⟨a,b,c⟩,d⟩ => ⟨a,b,c,d⟩⟩

instance standard_literalKnowledge (Q : Standard X O State Firing) : Q.toStep.LiteralKnowledge :=
  ⟨Q.knowledge_preparedResult⟩

instance standard_literalInformation (Q : Standard X O State Firing) : Q.toStep.LiteralInformation :=
  ⟨Q.transported⟩

instance standard_exact (Q : Standard X O State Firing) : Q.toStep.Exact where
  exactness f p := by
    intro b σ solved
    rw [Q.knowledge_preparedResult f p]
    exact (Frames.models_applyStore _ _ _).mpr solved

/-- Recover the explicit builder from a step carrying the three stronger certificates. -/
def Standard.ofCertified (Q : Step X O State Firing)
    [Q.Guarded] [Q.LiteralInformation] [Q.LiteralKnowledge] : Standard X O State Firing where
  toStep := Q
  Holds := Q.Holds
  admits_iff := Q.admits_iff
  transported := Q.transported
  knowledge_preparedResult := Q.knowledge_preparedResult

/-- An explicit permission policy over any effect core; no exactness is required. -/
def ofEffect (E : EffectCore X O State Firing) (allow : E.Admission) : Step X O State Firing where
  toEffectCore := E
  Admits f := ∃ p : E.Prepares f, allow f p
  admitted_prepares _ admitted := by rcases admitted with ⟨prepared, _⟩; exact prepared

def guarded (E : EffectCore X O State Firing)
    (holds : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop) : Step X O State Firing :=
  ofEffect E (E.guardAdmission holds)

instance guarded_profile (E : EffectCore X O State Firing)
    (holds : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop) :
    (guarded E holds).Guarded where
  holds := holds
  admission f := by
    change (∃ p : E.Prepares f, X.Entails (E.information f) (holds f)) ↔
      E.Prepares f ∧ X.Entails (E.information f) (holds f)
    exact ⟨fun ⟨p,h⟩ => ⟨p,h⟩, fun ⟨p,h⟩ => ⟨p,h⟩⟩

end Step

#print axioms Frames.models_applyStore
#print axioms Frames.solvable_of_applyStore
#print axioms Frames.Principal.models_iff
#print axioms Frames.solvable_iff_into
#print axioms Frames.solvable_iff_endo_consistent
#print axioms Frames.Principal.endo
#print axioms Frames.Entails.endo
#print axioms Frames.ofSubstitution_solvable_iff
#print axioms Frames.ofSubstitution_entails_iff
#print axioms Frames.ofSubstitution_principal_iff
#print axioms Frames.firstOrderFrame_weaklyTerminal
#print axioms Frames.contextual_solvable_iff
#print axioms Frames.contextual_solvable_iff_firstOrder
#print axioms Frames.contextual_endo
#print axioms Frames.contextual_solvable_iff_consistent
#print axioms Step.models_knowledge
#print axioms Step.solvable_knowledge
#print axioms Step.models_along
#print axioms Step.Run.models_start
#print axioms Step.Run.solvable_start
#print axioms Step.Run.last_append
#print axioms Step.Run.word_append
#print axioms Step.Run.account_append
#print axioms Step.prepares
#print axioms Step.admits_iff_prepares

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
