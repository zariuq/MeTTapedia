import Mathlib.Computability.Halting
import Mettapedia.Ethics.Core

/-!
# Rice's theorem for program-action classifiers

Actions are modeled as programs (partial recursive codes); the *consequence
profile* of an action is the partial function it computes over situations.
A *moral code* is a set of permissible program codes—an `Ethics.Theory` over
this deliberately restricted action model. Three properties may be imposed:

* `Consequentialist` — the verdict depends only on the consequence profile
  (the extensional readout of the action);
* `Nontrivial` — something is permissible and something is not;
* `DecidableMorality` — a computable judge settles permissibility.

`rice_trilemma_for_program_action_classifiers` says that no such classifier
has all three. This is a precise computability result for program-modeled
actions, not a theorem that distinguishes or ranks entire ethical paradigms.
Any two properties are jointly satisfiable:

* computable + consequentialist: the trivial code (`Set.univ`);
* computable + nontrivial: a singleton syntax classifier, which distinguishes
  two codes with identical computed profiles
  (`singletonSyntaxCode_not_consequence_invariant`);
* consequentialist + nontrivial: the responsiveness code (permissible iff
  the action delivers an outcome), undecidable by the halting problem
  (`responsivenessCode_undecidable`) — the duty to determine whether an
  action responds cannot be computably audited.

The justified conclusion is narrower: a nontrivial computable classifier of
programs cannot depend only on the partial function computed by each code.
The distinguishing information might be syntax, provenance, resource bounds,
proofs, or operational history; Rice's theorem alone does not choose among
those interpretations. This supplies one exact component of the
computational-complexity analysis of normative ethics in
J. Stenseke, *On the computational complexity of ethics* (AI Review, 2024),
and to the discussion of paradigm trade-offs in
<https://gardenofminds.art/esowiki/main/ethical-conjectures/moral-paradigm-equivalence/>.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.MoralUndecidability

open Nat.Partrec (Code)

/-! ## Actions, consequences, moral codes -/

/-- Actions as programs: an action is a partial recursive code. -/
abbrev ActionCode : Type := Code

/-- The consequence profile of an action: the outcome (if any) it yields in
each situation. -/
abbrev consequences (c : ActionCode) : ℕ →. ℕ := c.eval

/-- A moral code: the set of permissible actions — an `Ethics.Theory` over
action codes. -/
abbrev MoralCode : Type := Theory ActionCode

/-- Consequentialist: the verdict depends only on the consequence profile. -/
def Consequentialist (C : MoralCode) : Prop :=
  ∀ c₁ c₂ : ActionCode, consequences c₁ = consequences c₂ → (c₁ ∈ C ↔ c₂ ∈ C)

/-- Nontrivial: something is permissible and something is not. -/
def MorallyNontrivial (C : MoralCode) : Prop :=
  (∃ c, c ∈ C) ∧ (∃ c, c ∉ C)

/-- Computably judgeable: a computable judge settles permissibility. -/
def DecidableMorality (C : MoralCode) : Prop :=
  ComputablePred fun c => c ∈ C

/-! ## The Rice trilemma for the program-action model -/

/-- No program-action classifier is simultaneously computably judgeable,
consequence-invariant, and nontrivial. -/
theorem rice_trilemma_for_program_action_classifiers
    (C : MoralCode) (hcons : Consequentialist C)
    (hdec : DecidableMorality C) : ¬ MorallyNontrivial C := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases (ComputablePred.rice₂ C hcons).mp hdec with rfl | rfl
  · exact ha
  · exact hb (Set.mem_univ b)

/-- A nontrivial consequence-invariant classifier of program actions is not
computably decidable. -/
theorem nontrivial_consequence_invariant_classifier_undecidable (C : MoralCode)
    (hcons : Consequentialist C) (hnt : MorallyNontrivial C) :
    ¬ DecidableMorality C :=
  fun hdec => rice_trilemma_for_program_action_classifiers C hcons hdec hnt

/-- A computable nontrivial program-action classifier cannot be invariant
under equality of computed consequence profiles. -/
theorem decidable_nontrivial_classifier_not_consequence_invariant (C : MoralCode)
    (hdec : DecidableMorality C) (hnt : MorallyNontrivial C) :
    ¬ Consequentialist C :=
  fun hcons => rice_trilemma_for_program_action_classifiers C hcons hdec hnt

/-! ## Pairwise witnesses: each pair of properties is satisfiable -/

/-- The trivial permissive code: everything is allowed. -/
def trivialCode : MoralCode := Set.univ

theorem trivialCode_consequentialist : Consequentialist trivialCode :=
  fun _ _ _ => Iff.rfl

theorem trivialCode_decidable : DecidableMorality trivialCode := by
  refine ⟨fun _ => Decidable.isTrue (Set.mem_univ _), ?_⟩
  exact (Computable.const true).of_eq fun _ => rfl

theorem trivialCode_not_nontrivial : ¬ MorallyNontrivial trivialCode :=
  fun ⟨_, ⟨b, hb⟩⟩ => hb (Set.mem_univ b)

/-- A syntax classifier that accepts exactly one program code. -/
def singletonSyntaxCode : MoralCode := {Code.zero}

theorem singletonSyntaxCode_nontrivial :
    MorallyNontrivial singletonSyntaxCode := by
  refine ⟨⟨Code.zero, rfl⟩, ⟨Code.zero.comp Code.zero, ?_⟩⟩
  intro h
  exact Code.noConfusion h

theorem singletonSyntaxCode_decidable :
    DecidableMorality singletonSyntaxCode := by
  have henc : ComputablePred fun c : Code =>
      Encodable.encode c = Encodable.encode Code.zero := by
    obtain ⟨inst, hprim⟩ := Primrec.eq.comp
      (Primrec.encode : Primrec fun c : Code => Encodable.encode c)
      (Primrec.const (Encodable.encode Code.zero))
    exact ⟨inst, hprim.to_comp⟩
  refine henc.of_eq fun c => ?_
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (Encodable.encode_injective h)
  · intro h
    rw [Set.mem_singleton_iff.mp h]

/-- Two syntactically distinct program codes with identical computed
profiles: the constant-zero program and its self-composition. -/
theorem eval_comp_zero_zero :
    consequences (Code.zero.comp Code.zero) = consequences Code.zero := by
  funext n
  simp only [consequences, Code.eval]
  exact Part.bind_some 0 (pure 0 : ℕ →. ℕ)

/-- The singleton syntax classifier distinguishes two codes with the same
computed consequence profile. -/
theorem singletonSyntaxCode_not_consequence_invariant :
    ¬ Consequentialist singletonSyntaxCode := by
  intro hcons
  have h := (hcons Code.zero (Code.zero.comp Code.zero)
    eval_comp_zero_zero.symm).mp rfl
  exact Code.noConfusion h

/-- The responsiveness code: an action is permissible iff it delivers an
outcome in the base situation — a duty to respond. -/
def responsivenessCode : MoralCode := {c : ActionCode | (c.eval 0).Dom}

theorem responsivenessCode_consequentialist :
    Consequentialist responsivenessCode := by
  intro c₁ c₂ h
  simp only [responsivenessCode, Set.mem_setOf_eq]
  rw [show c₁.eval = c₂.eval from h]

theorem responsivenessCode_nontrivial : MorallyNontrivial responsivenessCode := by
  constructor
  · refine ⟨Code.zero, ?_⟩
    simp only [responsivenessCode, Set.mem_setOf_eq, Code.eval]
    exact trivial
  · obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp Nat.Partrec.none
    refine ⟨c, ?_⟩
    simp [responsivenessCode, hc]

/-- The moral halting theorem: the duty to respond cannot be computably
audited — permissibility under the responsiveness code is exactly the
halting problem. -/
theorem responsivenessCode_undecidable : ¬ DecidableMorality responsivenessCode :=
  ComputablePred.halting_problem 0

/-! ## Verdict invariance under an act-retaining observation

Any verdict becomes invariant when its observation is injective and therefore
still identifies the act.  This is a useful representation boundary, not by
itself a translation into an independently specified consequential theory.
Over the pure consequence profile the trilemma stands; over an act-retaining
profile, invariance is vacuous. -/

/-- Verdict-invariance over an arbitrary observation of actions. -/
def ConsequentialistOver {α : Type*} (obs : ActionCode → α) (C : MoralCode) : Prop :=
  ∀ c₁ c₂ : ActionCode, obs c₁ = obs c₂ → (c₁ ∈ C ↔ c₂ ∈ C)

/-- `Consequentialist` is invariance over the pure consequence profile. -/
theorem consequentialist_iff_over_consequences (C : MoralCode) :
    Consequentialist C ↔ ConsequentialistOver consequences C :=
  Iff.rfl

/-- Over any injective observation, every verdict is observation-invariant.
The hypothesis states exactly where all act information is retained. -/
theorem injective_observation_makes_every_verdict_invariant
    {α : Type*} (obs : ActionCode → α)
    (hobs : Function.Injective obs) (C : MoralCode) :
    ConsequentialistOver obs C := by
  intro c₁ c₂ h
  rw [hobs h]

/-! ## Undecidability transfers along faithful computable translations -/

/-- A computable judge pulls back along a computable faithful translation:
if `B` is faithfully translated into `A` by a computable `τ`, deciding `A`
decides `B`. -/
theorem decidability_pullback (τ : ActionCode → ActionCode)
    (hτ : Computable τ) (A B : MoralCode) (h : ∀ c, c ∈ B ↔ τ c ∈ A)
    (hA : DecidableMorality A) : DecidableMorality B := by
  obtain ⟨inst, hcomp⟩ := hA
  refine ⟨fun c => decidable_of_iff _ (h c).symm, ?_⟩
  refine (hcomp.comp hτ).of_eq fun c => ?_
  exact decide_eq_decide.mpr (h c).symm

/-- Hence every moral code that faithfully computably hosts the
responsiveness code inherits its undecidability: the trilemma spreads along
the paradigm-equivalence translations themselves. -/
theorem hosts_responsiveness_undecidable (A : MoralCode)
    (τ : ActionCode → ActionCode) (hτ : Computable τ)
    (h : ∀ c, c ∈ responsivenessCode ↔ τ c ∈ A) :
    ¬ DecidableMorality A :=
  fun hA => responsivenessCode_undecidable
    (decidability_pullback τ hτ A responsivenessCode h hA)

/-! ## Finite duty and conditional-target theories

An arbitrary verdict set embeds exactly into a one-duty deontic theory and
into a one-target target-centered theory.  These positive embeddings establish
universal expressibility for their shared act-classification fragment.  They
do not claim that every such embedding is computationally cheap, concise,
learnable, or natural in the target paradigm; those are separate properties.

The computability theorems below locate one such separation.  If every duty or
conditional target in a finite theory is computably judgeable, then the
resulting classifier is computably judgeable.  Hence an exact embedding of the
responsiveness code must retain its undecidable content somewhere in the
translated theory.  This qualifies an embedding without denying that it is an
embedding. -/

/-- A finite duty theory: finitely many predicates on actions.  This is the
act-classification fragment of a deontic theory. -/
structure FiniteDutyTheory : Type 1 where
  ruleCount : ℕ
  duty : Fin ruleCount → ActionCode → Prop

/-- Compliance: an action is permissible iff it satisfies every duty. -/
def FiniteDutyTheory.compliance (R : FiniteDutyTheory) : MoralCode :=
  {c | ∀ i, R.duty i c}

/-- A finite conditional-target theory.  Fields select where a target applies.
It formalizes the act-classification fragment of target-centered virtue ethics;
disposition and learning structure are added separately. -/
structure FiniteTargetTheory : Type 1 where
  virtueCount : ℕ
  virtueField : Fin virtueCount → Set ActionCode
  target : Fin virtueCount → ActionCode → Prop

/-- Target compliance: every applicable target is hit. -/
def FiniteTargetTheory.targetCompliance
    (V : FiniteTargetTheory) : MoralCode :=
  {c | ∀ i, c ∈ V.virtueField i → V.target i c}

/-- The one-duty embedding of an arbitrary moral code. -/
def membershipDutyTheory (C : MoralCode) : FiniteDutyTheory :=
  ⟨1, fun _ => (· ∈ C)⟩

/-- The one-duty embedding classifies exactly the original moral code. -/
theorem membershipDutyTheory_classifies (C : MoralCode) :
    (membershipDutyTheory C).compliance = C := by
  ext c
  simp [membershipDutyTheory, FiniteDutyTheory.compliance]

/-- The one-target embedding of an arbitrary moral code, using the universal
field and membership in the source code as its target. -/
def membershipTargetTheory (C : MoralCode) : FiniteTargetTheory :=
  ⟨1, fun _ => Set.univ, fun _ => (· ∈ C)⟩

/-- The one-target embedding classifies exactly the original moral code. -/
theorem membershipTargetTheory_classifies (C : MoralCode) :
    (membershipTargetTheory C).targetCompliance = C := by
  ext c
  simp [membershipTargetTheory, FiniteTargetTheory.targetCompliance]

/-- Every finite duty theory embeds as conditional targets with universal
fields. -/
def FiniteDutyTheory.toUniversalFieldTargets
    (R : FiniteDutyTheory) : FiniteTargetTheory :=
  ⟨R.ruleCount, fun _ => Set.univ, R.duty⟩

theorem FiniteDutyTheory.toUniversalFieldTargets_targetCompliance
    (R : FiniteDutyTheory) :
    R.toUniversalFieldTargets.targetCompliance = R.compliance := by
  ext c
  simp [toUniversalFieldTargets, FiniteTargetTheory.targetCompliance,
    compliance]

/-- Every finite conditional-target theory has a corresponding finite duty
theory: satisfy a target whenever its field applies. -/
def FiniteTargetTheory.toConditionalDuties
    (V : FiniteTargetTheory) : FiniteDutyTheory :=
  ⟨V.virtueCount, fun i c => c ∈ V.virtueField i → V.target i c⟩

theorem FiniteTargetTheory.toConditionalDuties_compliance
    (V : FiniteTargetTheory) :
    V.toConditionalDuties.compliance = V.targetCompliance :=
  rfl

/-- A finite conjunction of computably judgeable predicates is computably
judgeable. -/
theorem computablePred_forall_fin :
    ∀ {n : ℕ} (p : Fin n → ActionCode → Prop),
      (∀ i, ComputablePred (p i)) →
      ComputablePred fun c => ∀ i, p i c := by
  intro n
  induction n with
  | zero =>
    intro p _
    rw [ComputablePred.computable_iff]
    refine ⟨fun _ => true, Computable.const true, funext fun c => propext ?_⟩
    exact ⟨fun _ => rfl, fun _ i => i.elim0⟩
  | succ n ih =>
    intro p h
    obtain ⟨fA, hfA, hpA⟩ :=
      ComputablePred.computable_iff.mp (ih (fun i => p i.succ) fun i => h i.succ)
    obtain ⟨f0, hf0, hp0⟩ := ComputablePred.computable_iff.mp (h 0)
    rw [ComputablePred.computable_iff]
    refine ⟨fun c => f0 c && fA c, ?_, funext fun c => propext ?_⟩
    · refine (Computable.cond hf0 hfA (Computable.const false)).of_eq fun c => ?_
      cases f0 c <;> simp
    · calc (∀ i : Fin (n + 1), p i c)
          ↔ p 0 c ∧ ∀ i : Fin n, p i.succ c := Fin.forall_fin_succ
        _ ↔ (f0 c = true) ∧ (fA c = true) :=
            and_congr (iff_of_eq (congrFun hp0 c)) (iff_of_eq (congrFun hpA c))
        _ ↔ (f0 c && fA c) = true := (iff_of_eq (Bool.and_eq_true _ _)).symm

/-- A finite duty theory of computably judgeable duties yields a computable
judge, so it cannot classify a nontrivial consequentialist code. -/
theorem finiteDutyTheory_computability_boundary (R : FiniteDutyTheory)
    (h : ∀ i, ComputablePred (R.duty i))
    (hcons : Consequentialist R.compliance) :
    ¬ MorallyNontrivial R.compliance :=
  rice_trilemma_for_program_action_classifiers _ hcons
    (computablePred_forall_fin R.duty h)

/-- The same bound for finite conditional-target theories. -/
theorem finiteTargetTheory_computability_boundary (V : FiniteTargetTheory)
    (h : ∀ i, ComputablePred fun c => c ∈ V.virtueField i → V.target i c)
    (hcons : Consequentialist V.targetCompliance) :
    ¬ MorallyNontrivial V.targetCompliance :=
  finiteDutyTheory_computability_boundary V.toConditionalDuties h hcons

/-- No finite theory of computably judgeable duties classifies the
responsiveness code.  Its exact one-duty embedding necessarily retains an
undecidable predicate. -/
theorem no_computable_finiteDutyTheory_for_responsiveness
    (R : FiniteDutyTheory)
    (h : ∀ i, ComputablePred (R.duty i)) :
    R.compliance ≠ responsivenessCode := by
  intro heq
  refine finiteDutyTheory_computability_boundary R h ?_ ?_
  · rw [heq]; exact responsivenessCode_consequentialist
  · rw [heq]; exact responsivenessCode_nontrivial

/-! ## Axiom audit -/

#print axioms rice_trilemma_for_program_action_classifiers
#print axioms decidable_nontrivial_classifier_not_consequence_invariant
#print axioms singletonSyntaxCode_decidable
#print axioms singletonSyntaxCode_not_consequence_invariant
#print axioms responsivenessCode_nontrivial
#print axioms responsivenessCode_undecidable
#print axioms injective_observation_makes_every_verdict_invariant
#print axioms decidability_pullback
#print axioms hosts_responsiveness_undecidable
#print axioms membershipDutyTheory_classifies
#print axioms membershipTargetTheory_classifies
#print axioms finiteDutyTheory_computability_boundary
#print axioms finiteTargetTheory_computability_boundary
#print axioms no_computable_finiteDutyTheory_for_responsiveness

end Mettapedia.Ethics.MoralUndecidability
