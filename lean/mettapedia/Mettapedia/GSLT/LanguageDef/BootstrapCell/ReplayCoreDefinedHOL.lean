import Mettapedia.Logic.HOL.ReplayCoreDefined
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreHOL

/-!
# Defined acceptance and derivability: the standard model

`Logic.HOL.ReplayCoreDefined` defines acceptance and derivability as least
predicates over the certificate constructors and the rule relation.  This
module gives that theory its standard model on NIK's raw certificates and
reads the object derivations off in it.

**The standard model** (`model σ`), for a replay signature `σ`: the carriers
of `ReplayCoreHOL`, the constructors of `RawProof` and of lists, and the graph
of the local rule map.  It validates the theory (`theory_valid`): induction is
the recursor of `RawProof`, and freeness is injectivity and disjointness of
its constructors.

**The definitions denote the intended relations.**
* `leastDer_iff`: the least derivability predicate is derivability by the
  derivation trees of `BootstrapCell.Replay`, `Nonempty (σ.Deriv g)`.
* `leastAcc_iff`: the least acceptance is replay, `σ.replay g c = true`; one
  direction by closure of replay, the other by the recursor of `RawProof`.
* `leastCert_all`: every raw certificate is genuine.

**Replay is sound and complete, read off the object derivations**, which use
no axiom:
* `replay_derivable_of_derivation`, `replay_complete_of_derivation`, and
  `derivable_iff_accepted_of_derivations`, independent of
  `exists_deriv_of_replay` and `Deriv.replay_erase`;
* `models_completeness_of_replay_erase`: the metalogic route, through
  `Deriv.replay_erase`;
* `replay_sound_of_derivation`: soundness for every meaning closed under the
  local rule map, through the leastness of derivability;
* `solution_sound`: every checker on raw certificates that satisfies the
  replay equations is sound, read off the derivation on genuine certificates;
  `replay_sound_as_solution` instantiates it at replay;
* `checkRaw_derivable_of_derivation`, `checkRaw_complete_of_derivation`: the
  generic inference checker of every validated calculus.

**Controls.**  `standard_and_junk_controls` puts the standard model beside
the free junk model and the old theory's model without least derivability.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreDefinedHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.ReplayCore (BaseSort)
open Mettapedia.Logic.HOL.ReplayCoreDefined
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

variable (σ : ReplaySignature.{u})

/-! ## The standard model -/

/-- Constants: NIK's certificate constructors, list constructors, and the
graph of the local rule map. -/
def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) τ
  | _, .node => fun label children => ⟨.node label.down children.down⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun label premises conclusion =>
      ⟨σ.step label.down = some (premises.down, conclusion.down)⟩

/-- The standard model: full predicate domains over NIK's raw certificates. -/
def model : HenkinModel.{0, 0, u} BaseSort Symbol :=
  HenkinModel.standard (ReplayCoreHOL.carrier σ) (constant σ)

theorem certInduction_valid : (model σ).models certInduction := by
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

theorem nodeInjective_valid : (model σ).models nodeInjective := by
  intro label _ children _ label' _ children' _ h
  change (⟨.node label.down children.down⟩ : ULift.{max 1 u} RawProof) =
    ⟨.node label'.down children'.down⟩ at h
  have parts := RawProof.node.inj (congrArg ULift.down h)
  exact ⟨congrArg ULift.up parts.1, congrArg ULift.up parts.2⟩

theorem consInjective_valid : (model σ).models consInjective := by
  intro child _ children _ child' _ children' _ h
  change (⟨child.down :: children.down⟩ : ULift.{max 1 u} (List RawProof)) =
    ⟨child'.down :: children'.down⟩ at h
  have parts := List.cons.inj (congrArg ULift.down h)
  exact ⟨congrArg ULift.up parts.1, congrArg ULift.up parts.2⟩

theorem consNotNil_valid : (model σ).models consNotNil := by
  intro child _ children _ h
  change (⟨child.down :: children.down⟩ : ULift.{max 1 u} (List RawProof)) = ⟨[]⟩ at h
  exact nomatch congrArg ULift.down h

/-- **The standard model validates the theory**: induction is the recursor of
`RawProof`, freeness is injectivity and disjointness of its constructors. -/
theorem theory_valid : ∀ φ ∈ theory (Γ := []), (model σ).models φ := by
  intro φ membership
  simp only [theory, freeness, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  · exact certInduction_valid σ
  · exact nodeInjective_valid σ
  · exact consInjective_valid σ
  · exact consNotNil_valid σ

/-! ## Derivability is interpreted as derivability -/

section Derivations

variable {σ}

mutual

/-- Every predicate pair closed under the rule clauses holds of every
derivation's goal. -/
theorem deriv_closed (D : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) goalPredicate)
    (E : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) goalsPredicate)
    (closed : StandardSemantics.DerClosed (constant σ) D E) :
    {goal : σ.Goal} → σ.Deriv goal → (D ⟨goal⟩).down
  | _, .byStep label step children =>
      closed.1 ⟨label⟩ ⟨_⟩ ⟨_⟩ step (derivList_closed D E closed children)

/-- The same for ordered derivation lists. -/
theorem derivList_closed (D : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) goalPredicate)
    (E : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) goalsPredicate)
    (closed : StandardSemantics.DerClosed (constant σ) D E) :
    {goals : List σ.Goal} → σ.DerivList goals → (E ⟨goals⟩).down
  | _, .nil => closed.2.1
  | _, .cons head tail =>
      closed.2.2 ⟨_⟩ ⟨_⟩ (deriv_closed D E closed head) (derivList_closed D E closed tail)

end

end Derivations

/-- **The least derivability predicate of the standard model is derivability
by the derivation trees of `BootstrapCell.Replay`.** -/
theorem leastDer_iff (goal : σ.Goal) :
    StandardSemantics.LeastDer (constant σ) ⟨goal⟩ ↔ Nonempty (σ.Deriv goal) := by
  constructor
  · intro least
    exact least (fun goal => ⟨Nonempty (σ.Deriv goal.down)⟩)
      (fun goals => ⟨Nonempty (σ.DerivList goals.down)⟩)
      ⟨fun label _ _ step ⟨children⟩ => ⟨.byStep label.down step children⟩, ⟨.nil⟩,
        fun _ _ ⟨head⟩ ⟨tail⟩ => ⟨.cons head tail⟩⟩
  · rintro ⟨derivation⟩ D E closed
    exact deriv_closed D E closed derivation

/-- Leastness against every meaning closed under the local rule map: a goal
derivable in the model holds in every such meaning. -/
theorem meaning_of_leastDer (meaning : σ.Goal → Prop) (closed : ReplayCoreHOL.Closed σ meaning)
    {goal : σ.Goal} (least : StandardSemantics.LeastDer (constant σ) ⟨goal⟩) : meaning goal :=
  least (fun goal => ⟨meaning goal.down⟩)
    (fun premises => ⟨∀ premise ∈ premises.down, meaning premise⟩)
    ⟨fun label premises conclusion step premisesHold =>
        closed label.down premises.down conclusion.down step premisesHold,
      fun _ member => absurd member List.not_mem_nil,
      fun _ _ head tail premise member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact tail premise member⟩

/-! ## Acceptance is interpreted as replay -/

/-- Replay is closed under the clauses of acceptance. -/
theorem replay_accClosed :
    StandardSemantics.AccClosed (constant σ)
      (fun goal certificate => ⟨σ.replay goal.down certificate.down = true⟩)
      (fun premises children => ⟨σ.replayAll premises.down children.down = true⟩) :=
  ⟨fun label premises goal children step accepted =>
      (ReplayCoreHOL.replay_node_iff σ goal.down label.down children.down).mpr
        ⟨premises.down, step, accepted⟩,
    ReplaySignature.replayAll_nil_nil σ,
    fun goal child goals children head tail => by
      change σ.replayAll (goal.down :: goals.down) (child.down :: children.down) = true
      rw [ReplaySignature.replayAll_cons_cons, head, tail]
      rfl⟩

/-- Every pair closed under the clauses of acceptance contains replay; by the
recursor of `RawProof`. -/
theorem replay_least (A : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) acceptance)
    (B : Ty.denote.{0, u} (ReplayCoreHOL.carrier σ) listAcceptance)
    (closed : StandardSemantics.AccClosed (constant σ) A B) (certificate : RawProof) :
    ∀ goal : σ.Goal, σ.replay goal certificate = true → (A ⟨goal⟩ ⟨certificate⟩).down :=
  RawProof.rec
    (motive_1 := fun certificate =>
      ∀ goal : σ.Goal, σ.replay goal certificate = true → (A ⟨goal⟩ ⟨certificate⟩).down)
    (motive_2 := fun children =>
      ∀ goals : List σ.Goal, σ.replayAll goals children = true → (B ⟨goals⟩ ⟨children⟩).down)
    (fun label children childrenHold goal accepted => by
      obtain ⟨premises, step, childrenAccepted⟩ :=
        (ReplayCoreHOL.replay_node_iff σ goal label children).mp accepted
      exact closed.1 ⟨label⟩ ⟨premises⟩ ⟨goal⟩ ⟨children⟩ step
        (childrenHold premises childrenAccepted))
    (fun goals accepted => by
      cases goals with
      | nil => exact closed.2.1
      | cons _ _ =>
          rw [ReplaySignature.replayAll_cons_nil] at accepted
          exact absurd accepted Bool.false_ne_true)
    (fun child children childHolds childrenHold goals accepted => by
      cases goals with
      | nil =>
          rw [ReplaySignature.replayAll_nil_cons] at accepted
          exact absurd accepted Bool.false_ne_true
      | cons goal goals =>
          rw [ReplaySignature.replayAll_cons_cons, Bool.and_eq_true] at accepted
          exact closed.2.2 ⟨goal⟩ ⟨child⟩ ⟨goals⟩ ⟨children⟩ (childHolds goal accepted.1)
            (childrenHold goals accepted.2))
    certificate

/-- **The least acceptance of the standard model is replay.** -/
theorem leastAcc_iff (goal : σ.Goal) (certificate : RawProof) :
    StandardSemantics.LeastAcc (constant σ) ⟨goal⟩ ⟨certificate⟩ ↔
      σ.replay goal certificate = true :=
  ⟨fun least => least _ _ (replay_accClosed σ),
    fun accepted A B closed => replay_least σ A B closed certificate goal accepted⟩

/-- Every raw certificate is genuine. -/
theorem leastCert_all (certificate : RawProof) :
    StandardSemantics.LeastCert (constant σ) ⟨certificate⟩ := fun P Q closed =>
  RawProof.rec
    (motive_1 := fun certificate => (P ⟨certificate⟩).down)
    (motive_2 := fun children => (Q ⟨children⟩).down)
    (fun label children childrenHold => closed.1 ⟨label⟩ ⟨children⟩ childrenHold)
    closed.2.1
    (fun child children childHolds childrenHold =>
      closed.2.2 ⟨child⟩ ⟨children⟩ childHolds childrenHold)
    certificate

/-! ## Soundness and completeness, read off the object derivations -/

theorem extensional : (model σ).FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _
    (HenkinModel.fullDomains_standard (ReplayCoreHOL.carrier σ) (constant σ))

/-- The interpretation of the soundness sentence. -/
theorem models_soundness_iff :
    (model σ).models soundness ↔
      ∀ goal certificate, σ.replay goal certificate = true → Nonempty (σ.Deriv goal) := by
  constructor
  · intro holds goal certificate accepted
    exact (leastDer_iff σ goal).mp ((StandardSemantics.denote_derDef (constant σ) _ ⟨goal⟩).mp
      (holds ⟨certificate⟩ trivial ⟨goal⟩ trivial
        ((StandardSemantics.denote_accDef (constant σ) _ ⟨goal⟩ ⟨certificate⟩).mpr
          ((leastAcc_iff σ goal certificate).mpr accepted))))
  · intro holds certificate _ goal _ accepted
    exact (StandardSemantics.denote_derDef (constant σ) _ goal).mpr
      ((leastDer_iff σ goal.down).mpr (holds goal.down certificate.down
        ((leastAcc_iff σ goal.down certificate.down).mp
          ((StandardSemantics.denote_accDef (constant σ) _ goal certificate).mp accepted))))

/-- The interpretation of the completeness sentence. -/
theorem models_completeness_iff :
    (model σ).models completeness ↔
      ∀ goal, Nonempty (σ.Deriv goal) → ∃ certificate, σ.replay goal certificate = true := by
  constructor
  · intro holds goal derivable
    obtain ⟨certificate, -, accepted⟩ := holds ⟨goal⟩ trivial
      ((StandardSemantics.denote_derDef (constant σ) _ ⟨goal⟩).mpr
        ((leastDer_iff σ goal).mpr derivable))
    exact ⟨certificate.down, (leastAcc_iff σ goal certificate.down).mp
      ((StandardSemantics.denote_accDef (constant σ) _ ⟨goal⟩ certificate).mp accepted)⟩
  · intro holds goal _ derivable
    obtain ⟨certificate, accepted⟩ := holds goal.down ((leastDer_iff σ goal.down).mp
      ((StandardSemantics.denote_derDef (constant σ) _ goal).mp derivable))
    exact ⟨⟨certificate⟩, trivial, (StandardSemantics.denote_accDef (constant σ) _ goal
      ⟨certificate⟩).mpr ((leastAcc_iff σ goal.down certificate).mpr accepted)⟩

/-- **Replay soundness from the object derivation, which uses no axiom.**
Independent of `ReplaySignature.exists_deriv_of_replay`. -/
theorem replay_derivable_of_derivation {goal : σ.Goal} {certificate : RawProof}
    (accepted : σ.replay goal certificate = true) : Nonempty (σ.Deriv goal) :=
  (models_soundness_iff σ).mp
    (models_of_derivation (model σ) (extensional σ) (soundness_derivation (Δ := []))
      (fun _ member => absurd member List.not_mem_nil))
    goal certificate accepted

/-- **Replay completeness from the object derivation, which uses no axiom.**
Independent of `ReplaySignature.Deriv.replay_erase`. -/
theorem replay_complete_of_derivation {goal : σ.Goal} (derivable : Nonempty (σ.Deriv goal)) :
    ∃ certificate, σ.replay goal certificate = true :=
  (models_completeness_iff σ).mp
    (models_of_derivation (model σ) (extensional σ) (completeness_derivation (Δ := []))
      (fun _ member => absurd member List.not_mem_nil))
    goal derivable

/-- The metalogic route to completeness: the erasure of a derivation is
accepted. -/
theorem models_completeness_of_replay_erase : (model σ).models completeness :=
  (models_completeness_iff σ).mpr fun _ ⟨derivation⟩ =>
    ⟨derivation.erase, derivation.replay_erase⟩

/-- Derivability and acceptance coincide, both directions read off the
object derivations. -/
theorem derivable_iff_accepted_of_derivations (goal : σ.Goal) :
    Nonempty (σ.Deriv goal) ↔ ∃ certificate, σ.replay goal certificate = true :=
  ⟨replay_complete_of_derivation σ, fun ⟨_, accepted⟩ => replay_derivable_of_derivation σ accepted⟩

/-- `ReplaySignature.replay_sound` for every closed meaning, from the object
derivation and the leastness of derivability; no derivation tree is built. -/
theorem replay_sound_of_derivation (meaning : σ.Goal → Prop)
    (closed : ReplayCoreHOL.Closed σ meaning) {goal : σ.Goal} {certificate : RawProof}
    (accepted : σ.replay goal certificate = true) : meaning goal :=
  meaning_of_leastDer σ meaning closed
    ((StandardSemantics.denote_derDef (constant σ) _ ⟨goal⟩).mp
      (models_of_derivation (model σ) (extensional σ) (soundness_derivation (Δ := []))
        (fun _ member => absurd member List.not_mem_nil) ⟨certificate⟩ trivial ⟨goal⟩ trivial
        ((StandardSemantics.denote_accDef (constant σ) _ ⟨goal⟩ ⟨certificate⟩).mpr
          ((leastAcc_iff σ goal certificate).mpr accepted))))

/-! ## Any checker given by the replay equations is replay -/

/-- A semantic solution of the replay equations in the standard model. -/
structure Solution where
  accepts : σ.Goal → RawProof → Prop
  acceptsAll : List σ.Goal → List RawProof → Prop
  node : ∀ label children goal, accepts goal (.node label children) ↔
    ∃ premises, σ.step label = some (premises, goal) ∧ acceptsAll premises children
  nil : ∀ premises, acceptsAll premises [] ↔ premises = []
  cons : ∀ child children premises, acceptsAll premises (child :: children) ↔
    ∃ goal goals, premises = goal :: goals ∧ accepts goal child ∧ acceptsAll goals children

/-- Replay is a solution. -/
def replaySolution : Solution σ where
  accepts goal certificate := σ.replay goal certificate = true
  acceptsAll premises children := σ.replayAll premises children = true
  node label children goal := ReplayCoreHOL.replay_node_iff σ goal label children
  nil premises := ReplayCoreHOL.replayAll_nil_iff σ premises
  cons child children premises := ReplayCoreHOL.replayAll_cons_iff σ premises child children

/-- **Every checker given by the replay equations is sound**, read off the
object derivation on genuine certificates (no axiom), since every raw
certificate is genuine. -/
theorem solution_sound (solution : Solution σ) {goal : σ.Goal} {certificate : RawProof}
    (accepted : solution.accepts goal certificate) : Nonempty (σ.Deriv goal) := by
  have holds := models_of_derivation (model σ) (extensional σ)
    (genuineSolutionSoundness_derivation (Δ := []))
    (fun _ member => absurd member List.not_mem_nil)
  have derivable := holds
    (fun goal certificate => ⟨solution.accepts goal.down certificate.down⟩) trivial
    (fun premises children => ⟨solution.acceptsAll premises.down children.down⟩) trivial
    (by
      intro label _ children _ goal _
      change solution.accepts goal.down (.node label.down children.down) ↔
        ∃ premises : ULift.{max 1 u} (List σ.Goal), True ∧
          (σ.step label.down = some (premises.down, goal.down) ∧
            solution.acceptsAll premises.down children.down)
      rw [solution.node]
      exact ⟨fun ⟨premises, step, accepted⟩ => ⟨⟨premises⟩, trivial, step, accepted⟩,
        fun ⟨premises, _, step, accepted⟩ => ⟨premises.down, step, accepted⟩⟩)
    (by
      intro premises _
      change solution.acceptsAll premises.down [] ↔ premises = ⟨[]⟩
      rw [solution.nil]
      exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩)
    (by
      intro child _ children _ premises _
      change solution.acceptsAll premises.down (child.down :: children.down) ↔
        ∃ goal : ULift.{max 1 u} σ.Goal, True ∧ ∃ goals : ULift.{max 1 u} (List σ.Goal), True ∧
          (premises = ⟨goal.down :: goals.down⟩ ∧ solution.accepts goal.down child.down ∧
            solution.acceptsAll goals.down children.down)
      rw [solution.cons]
      constructor
      · rintro ⟨goal, goals, split, head, tail⟩
        exact ⟨⟨goal⟩, trivial, ⟨goals⟩, trivial, congrArg ULift.up split, head, tail⟩
      · rintro ⟨goal, -, goals, -, split, head, tail⟩
        exact ⟨goal.down, goals.down, congrArg ULift.down split, head, tail⟩)
    ⟨certificate⟩ trivial
    ((StandardSemantics.denote_certDef (constant σ) _ ⟨certificate⟩).mpr
      (leastCert_all σ certificate))
    ⟨goal⟩ trivial accepted
  exact (leastDer_iff σ goal).mp
    ((StandardSemantics.denote_derDef (constant σ) _ ⟨goal⟩).mp derivable)

/-- Replay itself, a third time: as a solution of its own equations. -/
theorem replay_sound_as_solution {goal : σ.Goal} {certificate : RawProof}
    (accepted : σ.replay goal certificate = true) : Nonempty (σ.Deriv goal) :=
  solution_sound σ (replaySolution σ) accepted

/-! ## The generic inference checker -/

/-- In the standard model of a validated calculus, the least acceptance is the
generic inference checker. -/
theorem leastAcc_iff_checkRaw (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (certificate : RawProof) :
    StandardSemantics.LeastAcc (constant (nikSignature definition)) ⟨goal⟩ ⟨certificate⟩ ↔
      checkRaw definition goal certificate = true := by
  rw [leastAcc_iff, checkRaw_eq_replay]

/-- Soundness of the generic inference checker, read off the object derivation. -/
theorem checkRaw_derivable_of_derivation (definition : ValidatedCalculusLanguageDef)
    {goal : Pattern} {certificate : RawProof}
    (accepted : checkRaw definition goal certificate = true) :
    Nonempty (Derivation definition goal) := by
  rw [checkRaw_eq_replay] at accepted
  obtain ⟨derivation⟩ := replay_derivable_of_derivation (nikSignature definition) accepted
  exact ⟨(derivationEquiv definition goal).symm derivation⟩

/-- Completeness of the generic inference checker, read off the object
derivation. -/
theorem checkRaw_complete_of_derivation (definition : ValidatedCalculusLanguageDef)
    {goal : Pattern} (derivable : Nonempty (Derivation definition goal)) :
    ∃ certificate, checkRaw definition goal certificate = true := by
  obtain ⟨derivation⟩ := derivable
  obtain ⟨certificate, accepted⟩ := replay_complete_of_derivation (nikSignature definition)
    ⟨derivationEquiv definition goal derivation⟩
  exact ⟨certificate, by rw [checkRaw_eq_replay]; exact accepted⟩

/-! ## Controls -/

/-- The standard model validates the theory and both target sentences; the
free junk model validates freeness and refutes induction and the soundness of
a solution of the replay equations; the old theory has a model refuting
completeness. -/
theorem standard_and_junk_controls :
    (∀ φ ∈ theory (Γ := []), (model σ).models φ) ∧
    (model σ).models soundness ∧ (model σ).models completeness ∧
    (∀ φ ∈ freeness (Γ := []), FreeJunkModel.model.models φ) ∧
    ¬ FreeJunkModel.model.models certInduction ∧
    ¬ FreeJunkModel.model.models solutionSoundness ∧
    ¬ OldTopModel.model.models oldCompleteness :=
  ⟨theory_valid σ,
    models_of_derivation (model σ) (extensional σ) (soundness_derivation (Δ := []))
      (fun _ member => absurd member List.not_mem_nil),
    models_of_derivation (model σ) (extensional σ) (completeness_derivation (Δ := []))
      (fun _ member => absurd member List.not_mem_nil),
    FreeJunkModel.freeness_valid, FreeJunkModel.certInduction_invalid,
    FreeJunkModel.solutionSoundness_invalid, OldTopModel.oldCompleteness_invalid⟩

end Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreDefinedHOL
