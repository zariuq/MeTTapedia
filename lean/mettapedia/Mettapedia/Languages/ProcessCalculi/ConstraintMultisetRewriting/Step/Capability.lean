import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoreControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationEnumerationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AdmissionObservationCoverControls

/-!
# Semantic meaning and executable capability

A problem of the step means what its frames say: solvability of a store and asks of guards at every
solution (`Interface.Frames.Solvable`, `Entails`). An executable capability is extra structure on a
named domain, with authored syntax, its interpretation as an ambient problem, a recognizer or a
certificate, and a soundness theorem against the meaning. A problem outside every recognized domain
keeps its meaning.

## Outcomes (`Outcome`, `Outcome.Sound`)

An attempt on a problem reports one of five outcomes: **refuted**, a **witness**, an equivalent
**residual**, a **universal certificate** of the guard, or an **exhausted** budget. Each is sound
exactly when it means what it says; an exhausted budget claims nothing.

* **The ambient residual keeps its meaning without any capability** (`ambient_residual_sound`,
  `residual_meaning`): reporting the problem itself as residual is always sound, and a sound residual
  has the problem's solvability and asks.
* **A budget is never a refutation** (`exhausted_not_refutation`): on a solvable problem, exhaustion
  is sound and refutation is not.
* **The outcomes stay distinct**: a universal certificate is no witness (`certified_without_witness`)
  and a witness is no certificate (`witness_without_certificate`).

## The four capabilities

* **A decidable solver** (`DecisionProfile`): its procedure decides solvability on the recognized
  syntax (`sound`); its outcomes are sound and never exhausted (`attempt_sound`,
  `attempt_ne_exhausted`); a problem is handed to it only through a **checked recognition**, and
  otherwise kept as residual (`Recognition`, `dispatch`, `dispatch_sound`). Instance: unifiability of
  rational trees from finite presentations (`rationalDecision`), which accepts `X = f(X)` and refutes
  `f(X) = g(Y)` (`rational_loop_decided`, `rational_clash_decided`).
* **Complete positive search** (`SearchProfile`): a budgeted enumeration of unifiers with the
  **eventual-coverage obligation** (`UnificationEnumerationProgress.EventuallyCovers`): reported
  answers solve (`reported_sound`), every solvable recognized problem eventually reports a witness
  (`witness_eventually`), and a cut-off report never refutes (`cutOff_not_refuted`). Instance: the
  finite enumeration of the substitutions of two-bit worlds (`worldSearch`).
* **Finite observation decision** (`ObservationProfile`): an exact finite cover of a guard's
  observations is the certificate; checking a local guard at the covered values decides the ask
  (`check_iff`). Instance: the correlated two-bit store (`worldObservation`, `world_check_refuses`).
* **A productive interaction protocol** (`ProtocolProfile`): an answer for output depth `n` computed
  from the input to its demanded depth, sound against the meaning; output agreement follows from
  input agreement at the demanded depth (`productive`). Instance: the stream tail, which demands one
  more level (`shiftProtocol`) and has no same-depth protocol (`shift_no_same_depth_protocol`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Capability

open Interface (Frames)

universe uO uT uH

/-! ## Ambient problems and outcomes -/

section Ambient

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

variable (Tm) in
/-- **An ambient problem**: a store at a frame. -/
structure Problem where
  frame : Obj
  store : EquationStore (Tm frame)

/-- **The outcomes of an attempt** on a problem, for a guard asked at its solutions. -/
inductive Outcome (p : Problem Tm) (guard : (b : Obj) → Hom p.frame b → Prop) : Type (max uO uT uH) where
  /-- the problem has no solution -/
  | refuted
  /-- a solution -/
  | witness (b : Obj) (σ : Hom p.frame b)
  /-- an equivalent residual problem -/
  | residual (q : EquationStore (Tm p.frame))
  /-- the guard holds at every solution -/
  | certified
  /-- the budget is spent -/
  | exhausted

/-- **Soundness of an outcome** at the frames `X`: each claiming outcome means what it says; an
exhausted budget claims nothing. -/
inductive Outcome.Sound {p : Problem Tm} {guard : (b : Obj) → Hom p.frame b → Prop} :
    Outcome p guard → Prop
  | refuted : ¬ X.Solvable p.store → Sound .refuted
  | witness {b : Obj} {σ : Hom p.frame b} : X.Models σ p.store → Sound (.witness b σ)
  | residual {q : EquationStore (Tm p.frame)} : X.Equivalent q p.store → Sound (.residual q)
  | certified : X.Entails p.store guard → Sound .certified
  | exhausted : Sound .exhausted

variable {X} {p : Problem Tm} {guard : (b : Obj) → Hom p.frame b → Prop}

theorem refuted_sound_iff : (Outcome.refuted : Outcome p guard).Sound X ↔ ¬ X.Solvable p.store :=
  ⟨fun | .refuted h => h, .refuted⟩

theorem certified_sound_iff : (Outcome.certified : Outcome p guard).Sound X ↔ X.Entails p.store guard :=
  ⟨fun | .certified h => h, .certified⟩

theorem witness_sound_iff {b : Obj} (σ : Hom p.frame b) :
    (Outcome.witness b σ : Outcome p guard).Sound X ↔ X.Models σ p.store :=
  ⟨fun | .witness h => h, .witness⟩

/-- **The ambient residual keeps its meaning without any capability.** -/
theorem ambient_residual_sound : (Outcome.residual p.store : Outcome p guard).Sound X :=
  .residual fun _ _ => Iff.rfl

/-- **A sound residual has the problem's solvability and asks.** -/
theorem residual_meaning {q : EquationStore (Tm p.frame)}
    (sound : (Outcome.residual q : Outcome p guard).Sound X) :
    (X.Solvable q ↔ X.Solvable p.store) ∧
      ∀ observation : (b : Obj) → Hom p.frame b → Prop, X.Entails q observation ↔ X.Entails p.store observation := by
  cases sound with
  | residual same => exact ⟨same.solvable_iff, fun observation => same.entails_iff observation⟩

/-- **A budget is never a refutation**: on a solvable problem, exhaustion is sound and refutation is
not. -/
theorem exhausted_not_refutation (solvable : X.Solvable p.store) :
    (Outcome.exhausted : Outcome p guard).Sound X ∧ ¬ (Outcome.refuted : Outcome p guard).Sound X :=
  ⟨.exhausted, fun refuted => refuted_sound_iff.mp refuted solvable⟩

end Ambient

/-! ## The outcomes stay distinct, at two-bit worlds -/

section Distinct

open AdmissionObservationCover.Controls (World frame correlated impossible observe impossible_not_solvable)

/-- Outcomes of problems at the frame of two-bit worlds. -/
abbrev WorldOutcome (store : EquationStore (World → Bool)) (guard : Unit → (World → World) → Prop) :=
  @Outcome Unit (fun _ => World → Bool) (fun _ _ => World → World) ⟨(), store⟩ guard

/-- **A universal certificate is no witness**: the impossible store certifies every guard and has
no solution. -/
theorem certified_without_witness (guard : Unit → (World → World) → Prop) :
    (Outcome.certified : WorldOutcome impossible guard).Sound frame ∧
      ∀ (b : Unit) (σ : World → World), ¬ (Outcome.witness b σ : WorldOutcome impossible guard).Sound frame := by
  refine ⟨.certified fun b σ solved => absurd ⟨b, σ, solved⟩ impossible_not_solvable, ?_⟩
  intro b σ sound
  cases sound with
  | witness solved => exact impossible_not_solvable ⟨b, σ, solved⟩

/-- **A witness is no certificate**: the correlated store has the all-true solution, and the guard
"the first bit observes `true`" fails at the all-false one. -/
theorem witness_without_certificate :
    (Outcome.witness () (fun _ _ => true) : WorldOutcome correlated (fun b σ => observe 0 b σ = true)).Sound frame ∧
      ¬ (Outcome.certified : WorldOutcome correlated (fun b σ => observe 0 b σ = true)).Sound frame := by
  refine ⟨.witness ?_, fun sound => ?_⟩
  · intro e member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · have asked := certified_sound_iff.mp sound () (fun _ _ => false) (by
      intro e member
      obtain rfl := List.mem_singleton.mp member
      rfl)
    cases asked

end Distinct

/-! ## A decidable solver -/

section Decision

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **A decidable solver profile**: authored problem syntax, its interpretation as an ambient
problem, the recognizer of the profile's domain, and a procedure deciding solvability there. -/
structure DecisionProfile where
  Syntax : Type
  interpret : Syntax → Problem Tm
  recognize : Syntax → Bool
  decide : Syntax → Bool
  /-- **Soundness on the domain**: the procedure decides semantic solvability. -/
  sound : ∀ e, recognize e = true → (decide e = true ↔ X.Solvable (interpret e).store)

variable {X} (D : DecisionProfile X)

/-- **The attempt of a decision profile**: refuted or residual on its domain; residual outside it. -/
def DecisionProfile.attempt (e : D.Syntax) (guard : (b : Obj) → Hom (D.interpret e).frame b → Prop) :
    Outcome (D.interpret e) guard :=
  if D.recognize e = true then (if D.decide e = true then .residual (D.interpret e).store else .refuted)
  else .residual (D.interpret e).store

theorem DecisionProfile.attempt_sound (e : D.Syntax) (guard : (b : Obj) → Hom (D.interpret e).frame b → Prop) :
    (D.attempt e guard).Sound X := by
  unfold DecisionProfile.attempt
  by_cases recognized : D.recognize e = true
  · by_cases decided : D.decide e = true
    · simp only [recognized, decided, if_true]
      exact ambient_residual_sound
    · simp only [recognized, decided, if_true]
      exact .refuted fun solvable => decided ((D.sound e recognized).mpr solvable)
  · simp only [recognized]
    exact ambient_residual_sound

/-- **A decision profile never exhausts.** -/
theorem DecisionProfile.attempt_ne_exhausted (e : D.Syntax)
    (guard : (b : Obj) → Hom (D.interpret e).frame b → Prop) : D.attempt e guard ≠ Outcome.exhausted := by
  unfold DecisionProfile.attempt
  split
  · split <;> intro same <;> cases same
  · intro same
    cases same

/-- **A checked recognition** of an ambient problem: authored syntax in the profile's domain that
interprets as the problem. -/
structure Recognition (p : Problem Tm) where
  presented : D.Syntax
  recognized : D.recognize presented = true
  interprets : D.interpret presented = p

/-- **Dispatch after recognition**: a recognized problem is decided; an unrecognized one is kept. -/
def DecisionProfile.dispatch {p : Problem Tm} (guard : (b : Obj) → Hom p.frame b → Prop) :
    Option (Recognition D p) → Outcome p guard
  | none => .residual p.store
  | some r => if D.decide r.presented = true then .residual p.store else .refuted

/-- **Dispatch is sound**, recognized or not. -/
theorem DecisionProfile.dispatch_sound {p : Problem Tm} (guard : (b : Obj) → Hom p.frame b → Prop)
    (recognition : Option (Recognition D p)) : (D.dispatch guard recognition).Sound X := by
  cases recognition with
  | none => exact ambient_residual_sound
  | some r =>
      unfold DecisionProfile.dispatch
      by_cases decided : D.decide r.presented = true
      · simp only [decided, if_true]
        exact ambient_residual_sound
      · simp only [decided]
        have decides := D.sound r.presented r.recognized
        rw [r.interprets] at decides
        exact .refuted fun solvable => decided (decides.mpr solvable)

end Decision

section Rational

open Rational

/-- **Rational unifiability as a decidable solver**: finite graph presentations with equations
between nodes, interpreted as stores of rational trees, decided by the computed closure. -/
def rationalDecision (σ : Mettapedia.Logic.LP.LPSignature) (N : Type) [Fintype N] [DecidableEq N]
    [DecidableEq (Head σ)] : DecisionProfile (rationalFrames σ) where
  Syntax := Raw.Graph σ N × List (N × N)
  interpret e := ⟨PUnit.unit, e.1.rstore e.2⟩
  recognize _ := true
  decide e := e.1.unifiable e.2
  sound _ _ := Raw.Graph.consistent_rstore_iff_unifiable.symm.trans
    (Frames.ofSubstitution_solvable_iff _ _).symm

theorem rationalDecision_decide (σ : Mettapedia.Logic.LP.LPSignature) {N : Type} [Fintype N] [DecidableEq N]
    [DecidableEq (Head σ)] (G : Raw.Graph σ N) (E : List (N × N)) :
    (rationalDecision σ N).decide (G, E) = G.unifiable E :=
  rfl

/-- **It accepts `X = f(X)`.** -/
theorem rational_loop_decided :
    (rationalDecision Controls.ctlSig (Fin 2)).decide (Controls.loopPresented, [(0, 1)]) = true :=
  ((rationalDecision Controls.ctlSig (Fin 2)).sound _ rfl).mpr
    ((Frames.ofSubstitution_solvable_iff _ _).mpr Controls.loopPresented_consistent)

/-- **It refutes `f(X) = g(Y)`.** -/
theorem rational_clash_decided :
    (rationalDecision Controls.ctlSig (Fin 4)).decide (Controls.clashPresented, [(2, 3)]) = false :=
  Bool.eq_false_iff.mpr fun accepted => Controls.clashPresented_inconsistent
    ((Frames.ofSubstitution_solvable_iff _ _).mp (((rationalDecision Controls.ctlSig (Fin 4)).sound _ rfl).mp accepted))

end Rational

/-! ## Complete positive search -/

section Search

variable {T S : Type} (A : SubstitutionAction T S)

/-- **A complete positive search profile**: authored problem syntax, its interpretation as a store,
the recognizer of the domain, a budgeted enumeration of unifiers, and the eventual-coverage
obligation on the domain. -/
structure SearchProfile where
  Syntax : Type
  interpret : Syntax → EquationStore T
  recognize : Syntax → Bool
  enumerate : (e : Syntax) → Superposition.UnifierEnumeration A (interpret e)
  covers : ∀ e, recognize e = true →
    UnificationEnumerationProgress.EventuallyCovers A (interpret e) (enumerate e)

variable {A} (P : SearchProfile A)

/-- **Reported answers solve.** -/
theorem SearchProfile.reported_sound (e : P.Syntax) (n : ℕ) {u : S}
    (member : u ∈ ((P.enumerate e).report n).answers) : A.Models u (P.interpret e) :=
  (P.enumerate e).sound n u member

/-- **Every solvable recognized problem eventually reports a witness.** -/
theorem SearchProfile.witness_eventually (e : P.Syntax) (recognized : P.recognize e = true)
    (solvable : A.Consistent (P.interpret e)) :
    ∃ (n : ℕ) (u : S), u ∈ ((P.enumerate e).report n).answers ∧ A.Models u (P.interpret e) := by
  obtain ⟨σ, solved⟩ := solvable
  obtain ⟨n, u, member, -⟩ := P.covers e recognized σ solved
  exact ⟨n, u, member, P.reported_sound e n member⟩

/-- **A cut-off report never refutes.** -/
theorem SearchProfile.cutOff_not_refuted (e : P.Syntax) {n : ℕ}
    (cut : ((P.enumerate e).report n).status = .cutOff) :
    ((P.enumerate e).report n).verdict ≠ .refuted :=
  (P.enumerate e).not_refuted_of_cutOff cut

end Search

section WorldSearch

open AdmissionObservationCover.Controls (World)

/-- The substitutions of two-bit worlds acting on Boolean observations. -/
def worldAction : SubstitutionAction (World → Bool) (World → World) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply σ t := fun w => t (σ w)
  identity := id
  compose later earlier := fun w => earlier (later w)
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves := by intro σ s t same; subst same; rfl

instance worldModels (σ : World → World) (K : EquationStore (World → Bool)) :
    Decidable (worldAction.Models σ K) :=
  show Decidable (∀ e ∈ K, (fun w => e.1 (σ w)) = (fun w => e.2 (σ w))) from inferInstance

/-- **The finite enumeration**: all solutions among the finitely many substitutions, finished. -/
def worldEnumeration (K : EquationStore (World → Bool)) : Superposition.UnifierEnumeration worldAction K where
  report _ := ⟨(Finset.univ.filter fun σ => worldAction.Models σ K).val, .finished⟩
  sound _ _ member := (Finset.mem_filter.mp (Finset.mem_val.mp member)).2
  complete _ _ σ solved :=
    ⟨σ, Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, solved⟩), ⟨id, fun _ => rfl⟩⟩

/-- **Complete positive search at two-bit worlds.** -/
def worldSearch : SearchProfile worldAction where
  Syntax := EquationStore (World → Bool)
  interpret K := K
  recognize _ := true
  enumerate := worldEnumeration
  covers _ _ σ solved :=
    ⟨0, σ, Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, solved⟩), ⟨id, fun _ => rfl⟩⟩

end WorldSearch

/-! ## Finite observation decision -/

section Observation

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)
  {a : Obj} (K : EquationStore (Tm a)) {I : Type} [Fintype I] {Value : I → Type}
  (observe : (index : I) → (b : Obj) → Hom a b → Value index)

/-- **A finite observation profile**: an exact finite cover of the observations, the certificate. -/
structure ObservationProfile where
  cover : AdmissionObservationCover.Cover X K observe
  exact : cover.Exact

variable {X K observe} (P : ObservationProfile X K observe)

/-- **Check a local guard at the covered values.** -/
def ObservationProfile.check (guard : (index : I) → Value index → Bool) : Bool :=
  decide (∀ index, ∀ value ∈ P.cover.values index, guard index value = true)

/-- **The check decides the ask.** -/
theorem ObservationProfile.check_iff (guard : (index : I) → Value index → Bool) :
    P.check guard = true ↔ X.Entails K (fun b σ => ∀ index, guard index (observe index b σ) = true) := by
  unfold ObservationProfile.check
  rw [decide_eq_true_iff]
  exact (P.cover.entails_iff P.exact (fun index value => guard index value = true)).symm

end Observation

section WorldObservation

open AdmissionObservationCover.Controls (frame correlated observe cover cover_exact)

/-- **The correlated two-bit store**, with the exact cover of each coordinate. -/
def worldObservation : ObservationProfile frame (a := ()) correlated observe := ⟨cover, cover_exact⟩

/-- **The check refuses "every coordinate observes `true`"**, and so does the ask. -/
theorem world_check_refuses :
    worldObservation.check (fun _ value => value) = false ∧
      ¬ frame.Entails (a := ()) correlated (fun b σ => ∀ index, observe index b σ = true) := by
  have computed : worldObservation.check (fun _ value => value) = false := by decide
  refine ⟨computed, fun asked => ?_⟩
  have checked := (worldObservation.check_iff (fun _ value => value)).mpr asked
  rw [computed] at checked
  cases checked

end WorldObservation

/-! ## A productive interaction protocol -/

open CoreControls (Below shift shift_not_same_depth)

/-- **A productive interaction protocol**: a semantic stream transformer, the input depth each
output depth demands, and the answer for an output depth computed from the demanded input prefix,
sound against the meaning. -/
structure ProtocolProfile where
  meaning : (ℕ → Bool) → (ℕ → Bool)
  demand : ℕ → ℕ
  answer : (n : ℕ) → (Fin (demand n) → Bool) → Fin n → Bool
  sound : ∀ (n : ℕ) (s : ℕ → Bool) (i : Fin n), answer n (fun j => s j) i = meaning s i

/-- **Productivity**: agreement at the demanded input depth gives agreement at the output depth. -/
theorem ProtocolProfile.productive (P : ProtocolProfile) (n : ℕ) (s t : ℕ → Bool)
    (agree : Below (P.demand n) s t) : Below n (P.meaning s) (P.meaning t) := by
  intro i short
  have prefixes : (fun j : Fin (P.demand n) => s j) = fun j : Fin (P.demand n) => t j :=
    funext fun j => agree j j.2
  rw [← P.sound n s ⟨i, short⟩, ← P.sound n t ⟨i, short⟩, prefixes]

/-- **The stream tail as a protocol**: output depth `n` demands input depth `n + 1`. -/
def shiftProtocol : ProtocolProfile where
  meaning := shift
  demand n := n + 1
  answer _ input i := input ⟨i + 1, Nat.succ_lt_succ i.2⟩
  sound _ _ _ := rfl

/-- **The tail has no same-depth protocol.** -/
theorem shift_no_same_depth_protocol :
    ¬ ∃ P : ProtocolProfile, P.meaning = shift ∧ ∀ n, P.demand n = n := by
  rintro ⟨P, meaning, same⟩
  obtain ⟨s, t, agree, differ⟩ := shift_not_same_depth
  apply differ
  have productive := P.productive 1 s t (by rw [same 1]; exact agree)
  rwa [meaning] at productive

#print axioms ambient_residual_sound
#print axioms residual_meaning
#print axioms exhausted_not_refutation
#print axioms certified_without_witness
#print axioms witness_without_certificate
#print axioms DecisionProfile.attempt_sound
#print axioms DecisionProfile.attempt_ne_exhausted
#print axioms DecisionProfile.dispatch_sound
#print axioms rational_loop_decided
#print axioms rational_clash_decided
#print axioms SearchProfile.witness_eventually
#print axioms SearchProfile.cutOff_not_refuted
#print axioms worldSearch
#print axioms ObservationProfile.check_iff
#print axioms world_check_refuses
#print axioms ProtocolProfile.productive
#print axioms shift_no_same_depth_protocol

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Capability
