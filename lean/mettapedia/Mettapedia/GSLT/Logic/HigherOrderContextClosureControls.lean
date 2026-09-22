import Mettapedia.GSLT.Logic.HigherOrderContextClosure

/-!
# Checked prefix methods for a process-bearing transition system

The existing send system supplies the operational semantics. Reflexivity and
prefixing are finite constructor rules; their local replay property is proved
from actual transitions. A retained three-node certificate proves a nested
payload equivalence. Changing a channel, supplying the wrong child, or omitting
the required child is rejected by the same rule checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HigherOrderBisimulation.ContextClosureControls

open Mettapedia.Logic PayloadControls

abbrev J := Judgment States

def pair (left right : Process) : J := ⟨(), left, right⟩

inductive Rules : List J → J → Prop
  | reflexive (state : Process) : Rules [] (pair state state)
  | send (channel : Bool) (left right : Process) :
      Rules [pair left right] (pair (.send channel left) (.send channel right))

/-- Only terminal identities are initially related; no send theorem is assumed. -/
def seeds (judgment : J) : Prop :=
  match judgment.2 with
  | (.halt _, .halt _) => True
  | _ => False

instance (judgment : J) : Decidable (seeds judgment) := by
  unfold seeds
  split <;> infer_instance

private theorem reflexive_progress (candidate : J → Prop)
    (closed : FinitaryClosure.Closed Rules candidate) (state : Process) :
    system.progressOnJudgments candidate (pair state state) := by
  have reflexive : ∀ interface state, unpack candidate interface state state := by
    intro interface state
    cases interface
    exact closed [] (pair state state) (.reflexive state) (by simp)
  refine ⟨?_, ?_, fun _ => Iff.rfl⟩
  · intro nextInterface label next step
    exact ⟨label, next, step, Label.relates_refl reflexive label, reflexive _ _⟩
  · intro nextInterface label next step
    exact ⟨label, next, step, Label.relates_refl reflexive label, reflexive _ _⟩

private theorem prefix_forward (candidate : J → Prop)
    (closed : FinitaryClosure.Closed Rules candidate)
    (channel : Bool) (left right : Process) (child : candidate (pair left right))
    {nextInterface : Unit} (label : Label controlVocabulary States () nextInterface)
    (next : Process) (step : system.act label (.send channel left) next) :
    ∃ matchedLabel matched, system.act matchedLabel (.send channel right) matched ∧
      Label.Relates (unpack candidate) label matchedLabel ∧
        unpack candidate nextInterface next matched := by
  cases nextInterface
  obtain ⟨source, rfl⟩ := step
  obtain ⟨sameChannel, samePayload⟩ := Process.send.inj source
  refine ⟨sendLabel channel right, .halt false, ⟨rfl, rfl⟩, ?_, ?_⟩
  · subst channel
    exact .mk label.skeleton label.payload (fun _ => right) (fun slot => by
      cases slot
      change candidate (pair (label.payload ()) right)
      rw [← samePayload]
      exact child)
  · exact closed [] (pair (.halt false) (.halt false)) (.reflexive _) (by simp)

/-- The local replay obligation holds because sends expose the related child
as their label payload and return the same terminal successor. -/
theorem locally_respectful :
    FinitaryClosure.LocallyRespectful Rules system.progressOnJudgments := by
  intro candidate closed premises conclusion rule children _advances
  cases rule with
  | reflexive state => exact reflexive_progress candidate closed state
  | send channel left right =>
      have child := children (pair left right) (by simp)
      refine ⟨?_, ?_, ?_⟩
      · intro nextInterface label next step
        exact prefix_forward candidate closed channel left right child label next step
      · intro nextInterface label next step
        cases nextInterface
        obtain ⟨source, rfl⟩ := step
        obtain ⟨sameChannel, samePayload⟩ := Process.send.inj source
        refine ⟨sendLabel channel left, .halt false, ⟨rfl, rfl⟩, ?_, ?_⟩
        · change Label.Relates (unpack candidate) (sendLabel channel left) label
          rw [sameChannel]
          exact Label.Relates.mk (relation := unpack candidate)
            label.skeleton (fun _ => left) label.payload (fun slot => by
            cases slot
            change candidate (pair left (label.payload ()))
            rw [← samePayload]
            exact child)
        · exact closed [] (pair (.halt false) (.halt false)) (.reflexive _) (by simp)
      · intro atom
        change Process.send channel left = .alarm ↔ Process.send channel right = .alarm
        simp

/-- Inert terminal seeds genuinely progress without presupposing bisimilarity. -/
theorem seeds_advance :
    seeds ≤ system.progressOnJudgments (FinitaryClosure.close Rules seeds) := by
  rintro ⟨interface, left, right⟩ related
  cases interface
  cases left <;> cases right <;> simp only [seeds] at related
  · refine ⟨?_, ?_, ?_⟩
    · intro nextInterface label next step
      exact False.elim (Process.noConfusion step.1)
    · intro nextInterface label next step
      exact False.elim (Process.noConfusion step.1)
    · intro atom
      change Process.halt _ = .alarm ↔ Process.halt _ = .alarm
      simp

inductive Witness where
  | seed
  | reflexive
  | send (channel : Bool)

def check : Witness → List J → J → Bool
  | .seed, premises, conclusion => decide (premises = [] ∧ seeds conclusion)
  | .reflexive, premises, conclusion => decide (premises = [] ∧ conclusion.2.1 = conclusion.2.2)
  | .send channel, [child], conclusion =>
      decide (conclusion = pair (.send channel child.2.1) (.send channel child.2.2))
  | .send _, _, _ => false

/-- Witnesses are exactly the seed, reflexivity and prefix rule instances. -/
def witnesses : RuleWitness (FinitaryClosure.seededRules Rules seeds) where
  W := Witness
  isInstance := check
  sound := by
    intro witness premises conclusion accepted
    cases witness with
    | seed => exact Or.inl (of_decide_eq_true accepted)
    | reflexive =>
        obtain ⟨rfl, equal⟩ := of_decide_eq_true accepted
        rcases conclusion with ⟨interface, left, right⟩
        cases interface
        change left = right at equal
        subst right
        exact Or.inr (.reflexive left)
    | send channel =>
        cases premises with
        | nil => simp [check] at accepted
        | cons child rest =>
            cases rest with
            | cons _ _ => simp [check] at accepted
            | nil =>
                have equal := of_decide_eq_true accepted
                subst conclusion
                rcases child with ⟨interface, left, right⟩
                cases interface
                exact Or.inr (.send channel left right)
  complete := by
    intro premises conclusion rule
    rcases rule with seed | rule
    · exact ⟨.seed, by simpa only [check, decide_eq_true_eq] using seed⟩
    · cases rule with
      | reflexive state => exact ⟨.reflexive, by simp [check, pair]⟩
      | send channel left right => exact ⟨.send channel, by simp [check, pair]⟩

def terminalCertificate : Derivation J Witness :=
  .node (pair (.halt false) (.halt true)) .seed 0 Fin.elim0

def prefixCertificate (channel : Bool) (child : Derivation J Witness) : Derivation J Witness :=
  .node (pair (.send channel child.concl.2.1) (.send channel child.concl.2.2))
    (.send channel) 1 (fun _ => child)

def nestedCertificate : Derivation J Witness :=
  prefixCertificate false (prefixCertificate true terminalCertificate)

theorem nested_accepted : nestedCertificate.valid witnesses = true := by decide +kernel

/-- This consumes the actual checked tree through the generic up-to theorem. -/
theorem nested_certificate_bisimilar :
    system.Bisimilar () (.send false (.send true (.halt false)))
      (.send false (.send true (.halt true))) :=
  system.certificate_bisimilar Rules locally_respectful seeds_advance witnesses
    nestedCertificate nested_accepted

def wrongChannelCertificate : Derivation J Witness :=
  .node (pair (.send false (.halt false)) (.send true (.halt true)))
    (.send false) 1 (fun _ => terminalCertificate)

def missingChildCertificate : Derivation J Witness :=
  .node (pair (.send false (.halt false)) (.send false (.halt true)))
    (.send false) 0 Fin.elim0

def wrongChildCertificate : Derivation J Witness :=
  .node (pair (.send false (.halt false)) (.send false (.halt false)))
    (.send false) 1 (fun _ => terminalCertificate)

theorem wrong_channel_rejected : wrongChannelCertificate.valid witnesses = false := by decide +kernel
theorem missing_child_rejected : missingChildCertificate.valid witnesses = false := by decide +kernel
theorem wrong_child_rejected : wrongChildCertificate.valid witnesses = false := by decide +kernel

/-- A nullary rule asserting equivalence across different channels cannot
satisfy local replay, even though its finite rule closure exists. -/
def unsafeRules (premises : List J) (conclusion : J) : Prop :=
  premises = [] ∧ conclusion = pair (.send false (.halt false)) (.send true (.halt false))

theorem unchecked_constructor_is_not_respectful :
    ¬ FinitaryClosure.LocallyRespectful unsafeRules system.progressOnJudgments := by
  intro localRules
  have derivation : FinitaryClosure.close unsafeRules (pack system.Bisimilar)
      (pair (.send false (.halt false)) (.send true (.halt false))) :=
    Derives.node [] _ (Or.inr ⟨rfl, rfl⟩) (by simp)
  exact different_channels_are_distinguished
    (system.finite_closure_bisimilar unsafeRules localRules derivation)

#print axioms locally_respectful
#print axioms seeds_advance
#print axioms nested_certificate_bisimilar
#print axioms wrong_channel_rejected
#print axioms missing_child_rejected
#print axioms wrong_child_rejected
#print axioms unchecked_constructor_is_not_respectful

end Mettapedia.GSLT.HigherOrderBisimulation.ContextClosureControls
