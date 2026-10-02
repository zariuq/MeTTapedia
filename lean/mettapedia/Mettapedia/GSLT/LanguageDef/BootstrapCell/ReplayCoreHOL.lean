import Mettapedia.Logic.HOL.ReplayCore
import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay

/-!
# The replay core in higher-order logic: the standard model

`Logic.HOL.ReplayCore` presents certificate replay as a theory of
higher-order logic in the deep embedding (seven axioms) and derives
`∀ c g. acc g c → der g` in the object logic.  This module gives that theory
its standard model: NIK's raw certificates with acceptance by replay.

**The standard model** (`model σ meaning`), for a replay signature `σ` and a
meaning of goals:
* goals are `σ.Goal`, labels are rule instances, certificates are `RawProof`
  and lists are lists;
* `rule l ps g` is `σ.step l = some (ps, g)`;
* `acc` and `accs` are `σ.replay` and `σ.replayAll`;
* `der` is the supplied meaning and `ders` its pointwise extension.

All predicate domains are full, so the induction axiom has its full strength.

**Each axiom is a clause of the replay core.**
* `accNode`: `ReplaySignature.replay_node` (`replay_node_iff`);
* `accsNil` and `accsCons`: the four `replayAll` equations
  (`replayAll_nil_iff`, `replayAll_cons_iff`);
* `derRule`: closure of the meaning under the local rule map, the hypothesis
  of `ReplaySignature.replay_sound`; `dersNil` and `dersCons` hold by the
  definition of the pointwise extension;
* `certInduction`: the recursor of `RawProof` at propositional motives.

**The target is W6's soundness theorem.**  `models_soundness_iff` states
that the interpretation of the target is
`∀ goal certificate, σ.replay goal certificate = true → meaning goal`, which
is the conclusion of `ReplaySignature.replay_sound`.  The object derivation
proves it in every standard model with a closed meaning
(`replay_sound_of_derivation`), independently of `replay_sound`, which
proves it in the metalogic (`models_soundness_of_replay_sound`).  At the
meaning "has a derivation" this is `replay_derivable_of_derivation`, and
through `checkRaw_eq_replay` and `derivationEquiv` the generic inference
checker's soundness `checkRaw_derivable_of_derivation`.

**Controls.**  `standard_and_junk_controls` puts the standard model, which
validates all seven axioms and the target, beside the junk model of
`Logic.HOL.ReplayCore`, which validates the six clauses with a cyclic
certificate and refutes induction and the target.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.ReplayCore
  (BaseSort Symbol theory clauses soundness accNode accsNil accsCons derRule dersNil
    dersCons certInduction)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

variable (σ : ReplaySignature.{u})

/-! ## The replay clauses as biconditionals -/

/-- The node clause of replay: acceptance at a node is acceptance of the
children against the premises of a rule application concluding the goal. -/
theorem replay_node_iff (goal : σ.Goal) (label : RuleInstance) (children : List RawProof) :
    σ.replay goal (.node label children) = true ↔
      ∃ premises, σ.step label = some (premises, goal) ∧
        σ.replayAll premises children = true := by
  rw [ReplaySignature.replay_node]
  cases hstep : σ.step label with
  | none => simp
  | some result =>
      rcases result with ⟨premises, conclusion⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, accepted⟩
        exact ⟨premises, rfl, accepted⟩
      · rintro ⟨premises', applied, accepted⟩
        cases applied
        exact ⟨rfl, accepted⟩

/-- The empty-children clauses of replay. -/
theorem replayAll_nil_iff (premises : List σ.Goal) :
    σ.replayAll premises [] = true ↔ premises = [] := by
  cases premises with
  | nil => exact ⟨fun _ => rfl, fun _ => ReplaySignature.replayAll_nil_nil σ⟩
  | cons premise premises =>
      rw [ReplaySignature.replayAll_cons_nil]
      exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩

/-- The nonempty-children clauses of replay. -/
theorem replayAll_cons_iff (premises : List σ.Goal) (child : RawProof)
    (children : List RawProof) :
    σ.replayAll premises (child :: children) = true ↔
      ∃ goal goals, premises = goal :: goals ∧ σ.replay goal child = true ∧
        σ.replayAll goals children = true := by
  cases premises with
  | nil =>
      rw [ReplaySignature.replayAll_nil_cons]
      constructor
      · intro h
        exact Bool.noConfusion h
      · rintro ⟨_, _, h, -⟩
        exact nomatch h
  | cons premise premises =>
      rw [ReplaySignature.replayAll_cons_cons, Bool.and_eq_true]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨premise, premises, rfl, head, tail⟩
      · rintro ⟨goal, goals, split, head, tail⟩
        cases split
        exact ⟨head, tail⟩

/-! ## The standard model -/

/-- Carriers: goals, rule instances, raw certificates, and their lists. -/
def carrier : BaseSort → Type (max 1 u)
  | .goal => ULift.{max 1 u} σ.Goal
  | .label => ULift.{max 1 u} RuleInstance
  | .cert => ULift.{max 1 u} RawProof
  | .certs => ULift.{max 1 u} (List RawProof)
  | .goals => ULift.{max 1 u} (List σ.Goal)

/-- Constants: certificate and list constructors, the graph of the local rule
map, replay, and the supplied meaning with its pointwise extension. -/
def constant (meaning : σ.Goal → Prop) :
    {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, u} (carrier σ) τ
  | _, .node => fun label children => ⟨.node label.down children.down⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun label premises conclusion =>
      ⟨σ.step label.down = some (premises.down, conclusion.down)⟩
  | _, .acc => fun goal certificate => ⟨σ.replay goal.down certificate.down = true⟩
  | _, .accs => fun premises children =>
      ⟨σ.replayAll premises.down children.down = true⟩
  | _, .der => fun goal => ⟨meaning goal.down⟩
  | _, .ders => fun premises => ⟨∀ premise ∈ premises.down, meaning premise⟩

/-- The standard model: full predicate domains over NIK's raw certificates,
with acceptance by replay. -/
def model (meaning : σ.Goal → Prop) : HenkinModel.{0, 0, u} BaseSort Symbol :=
  HenkinModel.standard (carrier σ) (constant σ meaning)

/-- A meaning closed under every local rule application: the hypothesis of
`ReplaySignature.replay_sound`. -/
def Closed (meaning : σ.Goal → Prop) : Prop :=
  ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
    (∀ premise ∈ premises, meaning premise) → meaning conclusion

variable (meaning : σ.Goal → Prop)

theorem accNode_valid : (model σ meaning).models accNode := by
  intro label _ children _ goal _
  change σ.replay goal.down (.node label.down children.down) = true ↔
    ∃ premises : ULift.{max 1 u} (List σ.Goal), True ∧
      (σ.step label.down = some (premises.down, goal.down) ∧
        σ.replayAll premises.down children.down = true)
  rw [replay_node_iff]
  constructor
  · rintro ⟨premises, applied, accepted⟩
    exact ⟨⟨premises⟩, trivial, applied, accepted⟩
  · rintro ⟨⟨premises⟩, -, applied, accepted⟩
    exact ⟨premises, applied, accepted⟩

theorem accsNil_valid : (model σ meaning).models accsNil := by
  rintro ⟨premises⟩ _
  change σ.replayAll premises [] = true ↔
    (⟨premises⟩ : ULift.{max 1 u} (List σ.Goal)) = ⟨[]⟩
  rw [replayAll_nil_iff]
  constructor
  · rintro rfl
    rfl
  · intro h
    cases h
    rfl

theorem accsCons_valid : (model σ meaning).models accsCons := by
  rintro child _ children _ ⟨premises⟩ _
  change σ.replayAll premises (child.down :: children.down) = true ↔
    ∃ goal : ULift.{max 1 u} σ.Goal, True ∧ ∃ goals : ULift.{max 1 u} (List σ.Goal), True ∧
      ((⟨premises⟩ : ULift.{max 1 u} (List σ.Goal)) = ⟨goal.down :: goals.down⟩ ∧
        σ.replay goal.down child.down = true ∧ σ.replayAll goals.down children.down = true)
  rw [replayAll_cons_iff]
  constructor
  · rintro ⟨goal, goals, rfl, head, tail⟩
    exact ⟨⟨goal⟩, trivial, ⟨goals⟩, trivial, rfl, head, tail⟩
  · rintro ⟨⟨goal⟩, -, ⟨goals⟩, -, split, head, tail⟩
    cases split
    exact ⟨goal, goals, rfl, head, tail⟩

theorem derRule_valid (closed : Closed σ meaning) : (model σ meaning).models derRule := by
  intro label _ premises _ conclusion _ applied premisesHold
  exact closed label.down premises.down conclusion.down applied premisesHold

theorem dersNil_valid : (model σ meaning).models dersNil := by
  intro premise member
  exact nomatch member

theorem dersCons_valid : (model σ meaning).models dersCons := by
  intro goal _ goals _ head tail premise member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail premise member

/-- Induction on certificates holds by the recursor of `RawProof`. -/
theorem certInduction_valid : (model σ meaning).models certInduction := by
  intro P _ Q _ nodeCase nilCase consCase certificate _
  have everyCertificate : ∀ proof : RawProof, (P ⟨proof⟩).down :=
    fun proof => RawProof.rec
      (motive_1 := fun proof => (P ⟨proof⟩).down)
      (motive_2 := fun proofs => (Q ⟨proofs⟩).down)
      (fun label children childrenHold =>
        nodeCase ⟨label⟩ trivial ⟨children⟩ trivial childrenHold)
      nilCase
      (fun child children childHolds childrenHold =>
        consCase ⟨child⟩ trivial ⟨children⟩ trivial childHolds childrenHold)
      proof
  exact everyCertificate certificate.down

/-- The standard model validates the seven axioms whenever the meaning is
closed under the local rule map. -/
theorem theory_valid (closed : Closed σ meaning) :
    ∀ φ ∈ theory (Γ := []), (model σ meaning).models φ := by
  intro φ membership
  simp only [theory, clauses, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certInduction_valid σ meaning
  · exact accNode_valid σ meaning
  · exact accsNil_valid σ meaning
  · exact accsCons_valid σ meaning
  · exact derRule_valid σ meaning closed
  · exact dersNil_valid σ meaning
  · exact dersCons_valid σ meaning

/-- **The interpretation of the target.**  In the standard model, the
soundness sentence says that every certificate replay accepts proves its
goal true in the meaning: the conclusion of `ReplaySignature.replay_sound`. -/
theorem models_soundness_iff :
    (model σ meaning).models soundness ↔
      ∀ goal certificate, σ.replay goal certificate = true → meaning goal := by
  constructor
  · intro holds goal certificate accepted
    exact holds ⟨certificate⟩ trivial ⟨goal⟩ trivial accepted
  · intro holds certificate _ goal _ accepted
    exact holds goal.down certificate.down accepted

/-- The metalogic route: `ReplaySignature.replay_sound` validates the target
in every standard model with a closed meaning. -/
theorem models_soundness_of_replay_sound (closed : Closed σ meaning) :
    (model σ meaning).models soundness :=
  (models_soundness_iff σ meaning).mpr fun _ _ accepted =>
    ReplaySignature.replay_sound meaning closed accepted

/-- **Replay soundness from the object derivation.**  Interpreting
`ReplayCore.soundness_derivation` in the standard model proves the statement
of `ReplaySignature.replay_sound` without using it. -/
theorem replay_sound_of_derivation (closed : Closed σ meaning) {goal : σ.Goal}
    {certificate : RawProof} (accepted : σ.replay goal certificate = true) :
    meaning goal :=
  (models_soundness_iff σ meaning).mp
    (ReplayCore.models_soundness_of_models_theory (model σ meaning)
      (HenkinModel.fullDomains_standard (carrier σ) (constant σ meaning))
      (theory_valid σ meaning closed))
    goal certificate accepted

/-- The standard models validate the target exactly when replay is sound for
every closed meaning, the statement of `ReplaySignature.replay_sound`. -/
theorem models_soundness_iff_replay_sound_statement :
    (∀ meaning, Closed σ meaning → (model σ meaning).models soundness) ↔
      ∀ (meaning : σ.Goal → Prop), Closed σ meaning →
        ∀ {goal : σ.Goal} {certificate : RawProof},
          σ.replay goal certificate = true → meaning goal := by
  constructor
  · intro holds meaning closed goal certificate accepted
    exact (models_soundness_iff σ meaning).mp (holds meaning closed) goal certificate accepted
  · intro holds meaning closed
    exact (models_soundness_iff σ meaning).mpr fun _ _ accepted =>
      holds meaning closed accepted

/-! ## Derivability as the meaning -/

/-- Pointwise derivable premises have a derivation list. -/
theorem nonempty_derivList :
    ∀ premises : List σ.Goal, (∀ premise ∈ premises, Nonempty (σ.Deriv premise)) →
      Nonempty (σ.DerivList premises)
  | [], _ => ⟨.nil⟩
  | premise :: premises, derivable => by
      obtain ⟨head⟩ := derivable premise List.mem_cons_self
      obtain ⟨tail⟩ := nonempty_derivList premises fun other member =>
        derivable other (List.mem_cons_of_mem _ member)
      exact ⟨.cons head tail⟩

/-- Derivability is closed under the local rule map. -/
theorem derivable_closed : Closed σ fun goal => Nonempty (σ.Deriv goal) := by
  intro label premises conclusion applied premisesDerivable
  obtain ⟨children⟩ := nonempty_derivList σ premises premisesDerivable
  exact ⟨.byStep label applied children⟩

/-- Every certificate replay accepts has a derivation of its goal, read off
the object derivation in the standard model at the meaning "derivable". -/
theorem replay_derivable_of_derivation {goal : σ.Goal} {certificate : RawProof}
    (accepted : σ.replay goal certificate = true) : Nonempty (σ.Deriv goal) :=
  replay_sound_of_derivation σ (fun goal => Nonempty (σ.Deriv goal)) (derivable_closed σ)
    accepted

/-! ## The generic inference checker -/

/-- In the standard model of a validated calculus, acceptance is the generic
inference checker. -/
theorem acc_iff_checkRaw (definition : ValidatedCalculusLanguageDef)
    (meaning : Pattern → Prop) (goal : Pattern) (certificate : RawProof) :
    ((model (nikSignature definition) meaning).constDen Symbol.acc ⟨goal⟩ ⟨certificate⟩).down ↔
      checkRaw definition goal certificate = true := by
  change (nikSignature definition).replay goal certificate = true ↔ _
  rw [checkRaw_eq_replay]

/-- Every certificate the generic inference checker accepts has a derivation
of its goal, read off the object derivation. -/
theorem checkRaw_derivable_of_derivation (definition : ValidatedCalculusLanguageDef)
    {goal : Pattern} {certificate : RawProof}
    (accepted : checkRaw definition goal certificate = true) :
    Nonempty (Derivation definition goal) := by
  rw [checkRaw_eq_replay] at accepted
  obtain ⟨derivation⟩ := replay_derivable_of_derivation (nikSignature definition) accepted
  exact ⟨(derivationEquiv definition goal).symm derivation⟩

/-! ## Controls -/

/-- The standard model validates the seven axioms and the target; the junk
model validates the six clauses and refutes induction and the target. -/
theorem standard_and_junk_controls (closed : Closed σ meaning) :
    (∀ φ ∈ theory (Γ := []), (model σ meaning).models φ) ∧
    (model σ meaning).models soundness ∧
    (∀ φ ∈ clauses (Γ := []), ReplayCore.JunkModel.model.models φ) ∧
    ¬ ReplayCore.JunkModel.model.models certInduction ∧
    ¬ ReplayCore.JunkModel.model.models soundness :=
  ⟨theory_valid σ meaning closed, models_soundness_of_replay_sound σ meaning closed,
    ReplayCore.JunkModel.clauses_valid, ReplayCore.JunkModel.certInduction_invalid,
    ReplayCore.JunkModel.soundness_invalid⟩

end Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreHOL
