import Mettapedia.GSLT.Logic.IPOSystem
import Mathlib.Order.FixedPoints

/-!
# Interface-indexed bisimulation with process-bearing labels

A label retains its constructor skeleton and a family of process payloads,
each at its declared interface. Skeletons agree literally; payloads are related
by the same relation that compares successors. The resulting operator is
monotone, and its greatest fixed point is an equivalence relation.

Empty payload families recover literal label comparison, including the existing
IPO construction. This does not prove contextual congruence for process-bearing
labels, construct least labels for an authored LanguageDef, or establish an
equational or executable correspondence for a reflective calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HigherOrderBisimulation

universe uInterface uState uSkeleton uAtom

/-- Label shapes and the interfaces of their payload positions. -/
structure Vocabulary (Interface : Type uInterface) where
  Skeleton : Interface → Interface → Type uSkeleton
  Slot : {source target : Interface} → Skeleton source target → Type uSkeleton
  interface : {source target : Interface} →
    (shape : Skeleton source target) → Slot shape → Interface

variable {Interface : Type uInterface} {State : Interface → Type uState}
  {vocabulary : Vocabulary.{uInterface, uSkeleton} Interface}

/-- A label whose payloads inhabit their declared interfaces. -/
structure Label (vocabulary : Vocabulary.{uInterface, uSkeleton} Interface)
    (State : Interface → Type uState) (source target : Interface) where
  skeleton : vocabulary.Skeleton source target
  payload : (slot : vocabulary.Slot skeleton) → State (vocabulary.interface skeleton slot)

abbrev RelationFamily (State : Interface → Type uState) :=
  (interface : Interface) → State interface → State interface → Prop

namespace Label

/-- Positional comparison shares a skeleton and compares its payloads. -/
inductive Relates (relation : RelationFamily State) :
    {source target : Interface} →
      Label vocabulary State source target → Label vocabulary State source target → Prop
  | mk {source target : Interface} (shape : vocabulary.Skeleton source target)
      (left right : (slot : vocabulary.Slot shape) → State (vocabulary.interface shape slot))
      (related : ∀ slot, relation (vocabulary.interface shape slot) (left slot) (right slot)) :
      Relates relation ⟨shape, left⟩ ⟨shape, right⟩

theorem relates_mono {first second : RelationFamily State} (included : first ≤ second)
    {source target : Interface} {left right : Label vocabulary State source target}
    (related : Relates first left right) : Relates second left right := by
  cases related with
  | mk shape left right pairs => exact .mk shape left right (fun slot => included _ _ _ (pairs slot))

theorem relates_refl {relation : RelationFamily State}
    (reflexive : ∀ interface state, relation interface state state)
    {source target : Interface} (label : Label vocabulary State source target) :
    Relates relation label label :=
  .mk label.skeleton label.payload label.payload (fun _ => reflexive _ _)

theorem relates_converse {relation : RelationFamily State}
    {source target : Interface} {left right : Label vocabulary State source target}
    (related : Relates relation left right) :
    Relates (fun interface first second => relation interface second first) right left := by
  cases related with
  | mk shape left right pairs => exact .mk shape right left pairs

theorem relates_comp {first second : RelationFamily State}
    {source target : Interface} {left middle right : Label vocabulary State source target}
    (leftMiddle : Relates first left middle) (middleRight : Relates second middle right) :
    Relates (fun interface start finish =>
      ∃ bridge, first interface start bridge ∧ second interface bridge finish) left right := by
  cases leftMiddle with
  | mk shape left middle firstPairs =>
    cases middleRight with
    | mk _ _ right secondPairs =>
      exact .mk shape left right (fun slot => ⟨middle slot, firstPairs slot, secondPairs slot⟩)

theorem skeleton_eq {relation : RelationFamily State}
    {source target : Interface} {left right : Label vocabulary State source target}
    (related : Relates relation left right) : left.skeleton = right.skeleton := by
  cases related
  rfl

end Label

/-- Transitions and observations on interface-indexed states. -/
structure System (vocabulary : Vocabulary.{uInterface, uSkeleton} Interface)
    (State : Interface → Type uState) where
  act : {source target : Interface} →
    Label vocabulary State source target → State source → State target → Prop
  Atom : Interface → Type uAtom
  observes : {interface : Interface} → Atom interface → State interface → Prop

namespace System

variable (system : System vocabulary State)

/-- One layer of mutual successor and label-payload comparison. -/
def progress (relation : RelationFamily State) : RelationFamily State :=
  fun interface left right =>
    (∀ {nextInterface : Interface} (label : Label vocabulary State interface nextInterface) next,
      system.act label left next →
        ∃ matchedLabel matched, system.act matchedLabel right matched ∧
          Label.Relates relation label matchedLabel ∧ relation nextInterface next matched) ∧
    (∀ {nextInterface : Interface} (label : Label vocabulary State interface nextInterface) next,
      system.act label right next →
        ∃ matchedLabel matched, system.act matchedLabel left matched ∧
          Label.Relates relation matchedLabel label ∧ relation nextInterface matched next) ∧
    (∀ atom, system.observes atom left ↔ system.observes atom right)

theorem progress_mono : Monotone system.progress := by
  intro first second included interface left right related
  obtain ⟨forward, backward, atoms⟩ := related
  refine ⟨?_, ?_, atoms⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := forward label next step
    exact ⟨matchedLabel, matched, matchedStep, Label.relates_mono included labels,
      included _ _ _ successors⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := backward label next step
    exact ⟨matchedLabel, matched, matchedStep, Label.relates_mono included labels,
      included _ _ _ successors⟩

/-- The actual monotone operator, not a requested law or a chosen relation. -/
def progressHom : RelationFamily State →o RelationFamily State :=
  ⟨system.progress, system.progress_mono⟩

/-- The greatest fixed point compares payloads and successors simultaneously. -/
def Bisimilar : RelationFamily State := system.progressHom.gfp

theorem bisimilar_unfold {interface : Interface} {left right : State interface} :
    system.Bisimilar interface left right ↔ system.progress system.Bisimilar interface left right := by
  change system.progressHom.gfp interface left right ↔
    system.progressHom system.progressHom.gfp interface left right
  rw [system.progressHom.map_gfp]

/-- Any post-fixed relation supplies checked coinductive evidence. -/
theorem coinduction {relation : RelationFamily State}
    (closed : relation ≤ system.progress relation) : relation ≤ system.Bisimilar :=
  system.progressHom.le_gfp closed

theorem bisimilar_refl (interface : Interface) (state : State interface) :
    system.Bisimilar interface state state := by
  apply system.coinduction (relation := fun _ => Eq) ?_ interface state state rfl
  rintro interface left right rfl
  refine ⟨?_, ?_, fun _ => Iff.rfl⟩
  · intro nextInterface label next step
    exact ⟨label, next, step, Label.relates_refl (fun _ => Eq.refl) label, rfl⟩
  · intro nextInterface label next step
    exact ⟨label, next, step, Label.relates_refl (fun _ => Eq.refl) label, rfl⟩

theorem bisimilar_symm {interface : Interface} {left right : State interface}
    (related : system.Bisimilar interface left right) : system.Bisimilar interface right left := by
  apply system.coinduction
    (relation := fun interface first second => system.Bisimilar interface second first)
    ?_ interface right left related
  intro interface first second pair
  obtain ⟨forward, backward, atoms⟩ := system.bisimilar_unfold.mp pair
  refine ⟨?_, ?_, fun atom => (atoms atom).symm⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := backward label next step
    exact ⟨matchedLabel, matched, matchedStep, Label.relates_converse labels, successors⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := forward label next step
    exact ⟨matchedLabel, matched, matchedStep, Label.relates_converse labels, successors⟩

theorem bisimilar_trans {interface : Interface} {left middle right : State interface}
    (first : system.Bisimilar interface left middle)
    (second : system.Bisimilar interface middle right) : system.Bisimilar interface left right := by
  apply system.coinduction (relation := fun interface start finish =>
    ∃ bridge, system.Bisimilar interface start bridge ∧ system.Bisimilar interface bridge finish)
    ?_ interface left right ⟨middle, first, second⟩
  rintro interface start finish ⟨bridge, startBridge, bridgeFinish⟩
  obtain ⟨firstForward, firstBackward, firstAtoms⟩ := system.bisimilar_unfold.mp startBridge
  obtain ⟨secondForward, secondBackward, secondAtoms⟩ := system.bisimilar_unfold.mp bridgeFinish
  refine ⟨?_, ?_, fun atom => (firstAtoms atom).trans (secondAtoms atom)⟩
  · intro nextInterface label next step
    obtain ⟨bridgeLabel, bridgeNext, bridgeStep, firstLabels, firstNext⟩ :=
      firstForward label next step
    obtain ⟨finishLabel, finishNext, finishStep, secondLabels, secondNext⟩ :=
      secondForward bridgeLabel bridgeNext bridgeStep
    exact ⟨finishLabel, finishNext, finishStep, Label.relates_comp firstLabels secondLabels,
      bridgeNext, firstNext, secondNext⟩
  · intro nextInterface label next step
    obtain ⟨bridgeLabel, bridgeNext, bridgeStep, secondLabels, secondNext⟩ :=
      secondBackward label next step
    obtain ⟨startLabel, startNext, startStep, firstLabels, firstNext⟩ :=
      firstBackward bridgeLabel bridgeNext bridgeStep
    exact ⟨startLabel, startNext, startStep, Label.relates_comp firstLabels secondLabels,
      bridgeNext, firstNext, secondNext⟩

/-- Behavioral classes retain their interface. -/
def bisimSetoid (interface : Interface) : Setoid (State interface) where
  r := system.Bisimilar interface
  iseqv := ⟨system.bisimilar_refl interface, fun pair => system.bisimilar_symm pair,
    fun first second => system.bisimilar_trans first second⟩

def Class (interface : Interface) := Quotient (system.bisimSetoid interface)

def toClass {interface : Interface} (state : State interface) : system.Class interface :=
  Quotient.mk (system.bisimSetoid interface) state

theorem class_eq_iff {interface : Interface} (left right : State interface) :
    system.toClass left = system.toClass right ↔ system.Bisimilar interface left right :=
  Quotient.eq

/-- Every declared observation is invariant under the constructed relation. -/
theorem observes_iff {interface : Interface} {left right : State interface}
    (related : system.Bisimilar interface left right) (atom : system.Atom interface) :
    system.observes atom left ↔ system.observes atom right :=
  (system.bisimilar_unfold.mp related).2.2 atom

/-- Label classes use this same fixed point, not an independent payload semantics. -/
def labelSetoid (source target : Interface) : Setoid (Label vocabulary State source target) where
  r := Label.Relates system.Bisimilar
  iseqv := by
    refine ⟨Label.relates_refl system.bisimilar_refl, ?_, ?_⟩
    · intro left right related
      exact Label.relates_mono (fun _ _ _ pair => system.bisimilar_symm pair)
        (Label.relates_converse related)
    · intro left middle right first second
      exact Label.relates_mono (by
        rintro _ _ _ ⟨bridge, leftBridge, bridgeRight⟩
        exact system.bisimilar_trans leftBridge bridgeRight) (Label.relates_comp first second)

def LabelClass (source target : Interface) := Quotient (system.labelSetoid source target)

def toLabelClass {source target : Interface} (label : Label vocabulary State source target) :
    system.LabelClass source target :=
  Quotient.mk (system.labelSetoid source target) label

theorem labelClass_eq_iff {source target : Interface}
    (left right : Label vocabulary State source target) :
    system.toLabelClass left = system.toLabelClass right ↔
      Label.Relates system.Bisimilar left right :=
  Quotient.eq

/-- A quotient edge retains actual stepping representatives of all three classes. -/
def quotientStep {source target : Interface} (labelClass : system.LabelClass source target)
    (sourceClass : system.Class source) (targetClass : system.Class target) : Prop :=
  ∃ label agent next, system.toLabelClass label = labelClass ∧
    system.toClass agent = sourceClass ∧ system.act label agent next ∧
      system.toClass next = targetClass

theorem quotientStep_mk {source target : Interface}
    {label : Label vocabulary State source target} {agent : State source} {next : State target}
    (step : system.act label agent next) :
    system.quotientStep (system.toLabelClass label) (system.toClass agent) (system.toClass next) :=
  ⟨label, agent, next, rfl, rfl, step, rfl⟩

/-- A class step lifts from any source representative. Its label and successor
are recovered in their prescribed classes, not as prescribed raw values. -/
theorem quotientStep_from_class_iff {source target : Interface}
    (agent : State source) (labelClass : system.LabelClass source target)
    (targetClass : system.Class target) :
    system.quotientStep labelClass (system.toClass agent) targetClass ↔
      ∃ label next, system.toLabelClass label = labelClass ∧ system.act label agent next ∧
        system.toClass next = targetClass := by
  constructor
  · rintro ⟨label, representative, next, labels, sources, step, targets⟩
    have related := (system.class_eq_iff representative agent).mp sources
    obtain ⟨matchedLabel, matched, matchedStep, matchedLabels, matchedNext⟩ :=
      (system.bisimilar_unfold.mp related).1 label next step
    exact ⟨matchedLabel, matched,
      ((system.labelClass_eq_iff label matchedLabel).mpr matchedLabels).symm.trans labels,
      matchedStep, ((system.class_eq_iff next matched).mpr matchedNext).symm.trans targets⟩
  · rintro ⟨label, next, labels, step, targets⟩
    exact ⟨label, agent, next, labels, rfl, step, targets⟩

end System

/-- Payload-free vocabularies compare the whole label literally. -/
def literalVocabulary (Skeleton : Interface → Interface → Type uSkeleton) :
    Vocabulary.{uInterface, uSkeleton} Interface where
  Skeleton := Skeleton
  Slot := fun _ => PEmpty
  interface := fun {_ _} _ slot => nomatch slot

def literalLabel {Skeleton : Interface → Interface → Type uSkeleton}
    {source target : Interface} (skeleton : Skeleton source target) :
    Label (literalVocabulary Skeleton) State source target :=
  ⟨skeleton, fun slot => nomatch slot⟩

theorem relates_literal_iff {Skeleton : Interface → Interface → Type uSkeleton}
    (relation : RelationFamily State) {source target : Interface}
    (left right : Label (literalVocabulary Skeleton) State source target) :
    Label.Relates relation left right ↔ left.skeleton = right.skeleton := by
  constructor
  · exact Label.skeleton_eq
  · cases left with
    | mk leftShape leftBody =>
      cases right with
      | mk rightShape rightBody =>
        intro same
        cases same
        exact .mk leftShape leftBody rightBody (fun slot => nomatch slot)

namespace System

variable (system : System vocabulary State)

/-- The same transitions and observations, with each complete label treated
literally. This is an explicit comparison instance, not the higher-order definition. -/
def literalSystem :
    System (literalVocabulary (Label vocabulary State)) State where
  act label := system.act label.skeleton
  Atom := system.Atom
  observes := system.observes

/-- The same state transitions with behavioral label classes. Classification
uses the already constructed greatest fixed point; it is not a class-computation algorithm. -/
def classLabelSystem :
    System (literalVocabulary system.LabelClass) State where
  act label agent next := ∃ representative,
    system.toLabelClass representative = label.skeleton ∧ system.act representative agent next
  Atom := system.Atom
  observes := system.observes

/-- Class-label bisimulation reconstructs higher-order matching. Its coinductive
candidate includes the original relation, so payload evidence from label equality
is used honestly, rather than assumed to belong to the class-label candidate. -/
theorem bisimilar_of_classLabel {interface : Interface} {left right : State interface}
    (related : system.classLabelSystem.Bisimilar interface left right) :
    system.Bisimilar interface left right := by
  let combined : RelationFamily State := fun interface first second =>
    system.classLabelSystem.Bisimilar interface first second ∨ system.Bisimilar interface first second
  apply system.coinduction (relation := combined) ?_ interface left right (Or.inl related)
  intro current first second pair
  rcases pair with classRelated | originalRelated
  · obtain ⟨forward, backward, atoms⟩ := system.classLabelSystem.bisimilar_unfold.mp classRelated
    refine ⟨?_, ?_, atoms⟩
    · intro nextInterface label next step
      have classStep : system.classLabelSystem.act (literalLabel (system.toLabelClass label))
          first next := ⟨label, rfl, step⟩
      obtain ⟨matchedClass, matched, matchedClassStep, classes, successors⟩ :=
        forward _ next classStep
      obtain ⟨matchedLabel, matchedLabelClass, matchedStep⟩ := matchedClassStep
      have sameClass := Label.skeleton_eq classes
      change system.toLabelClass label = matchedClass.skeleton at sameClass
      have payloads := (system.labelClass_eq_iff label matchedLabel).mp
        (sameClass.trans matchedLabelClass.symm)
      exact ⟨matchedLabel, matched, matchedStep,
        Label.relates_mono (fun _ _ _ pair => Or.inr pair) payloads, Or.inl successors⟩
    · intro nextInterface label next step
      have classStep : system.classLabelSystem.act (literalLabel (system.toLabelClass label))
          second next := ⟨label, rfl, step⟩
      obtain ⟨matchedClass, matched, matchedClassStep, classes, successors⟩ :=
        backward _ next classStep
      obtain ⟨matchedLabel, matchedLabelClass, matchedStep⟩ := matchedClassStep
      have sameClass := Label.skeleton_eq classes
      change matchedClass.skeleton = system.toLabelClass label at sameClass
      have payloads := (system.labelClass_eq_iff matchedLabel label).mp
        (matchedLabelClass.trans sameClass)
      exact ⟨matchedLabel, matched, matchedStep,
        Label.relates_mono (fun _ _ _ pair => Or.inr pair) payloads, Or.inl successors⟩
  · obtain ⟨forward, backward, atoms⟩ := system.bisimilar_unfold.mp originalRelated
    refine ⟨?_, ?_, atoms⟩
    · intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := forward label next step
      exact ⟨matchedLabel, matched, matchedStep,
        Label.relates_mono (fun _ _ _ pair => Or.inr pair) labels, Or.inr successors⟩
    · intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := backward label next step
      exact ⟨matchedLabel, matched, matchedStep,
        Label.relates_mono (fun _ _ _ pair => Or.inr pair) labels, Or.inr successors⟩

/-- Higher-order matching is exactly literal matching on the constructed label
classes. This semantic theorem supplies no runtime quotienting procedure. -/
theorem bisimilar_classLabel_iff {interface : Interface} (left right : State interface) :
    system.classLabelSystem.Bisimilar interface left right ↔ system.Bisimilar interface left right := by
  refine ⟨system.bisimilar_of_classLabel, ?_⟩
  intro related
  apply system.classLabelSystem.coinduction (relation := system.Bisimilar) ?_
    interface left right related
  intro current first second pair
  obtain ⟨forward, backward, atoms⟩ := system.bisimilar_unfold.mp pair
  refine ⟨?_, ?_, atoms⟩
  · intro nextInterface classLabel next step
    obtain ⟨label, labelClass, actualStep⟩ := step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := forward label next actualStep
    have sameClass := (system.labelClass_eq_iff label matchedLabel).mpr labels
    exact ⟨classLabel, matched, ⟨matchedLabel, sameClass.symm.trans labelClass, matchedStep⟩,
      (relates_literal_iff system.Bisimilar classLabel classLabel).mpr rfl, successors⟩
  · intro nextInterface classLabel next step
    obtain ⟨label, labelClass, actualStep⟩ := step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ := backward label next actualStep
    have sameClass := (system.labelClass_eq_iff matchedLabel label).mpr labels
    exact ⟨classLabel, matched, ⟨matchedLabel, sameClass.trans labelClass, matchedStep⟩,
      (relates_literal_iff system.Bisimilar classLabel classLabel).mpr rfl, successors⟩

/-- Literal matching is at least as discriminating as positional matching. -/
theorem bisimilar_of_literal {interface : Interface} {left right : State interface}
    (related : system.literalSystem.Bisimilar interface left right) :
    system.Bisimilar interface left right := by
  apply system.coinduction (relation := system.literalSystem.Bisimilar) ?_
    interface left right related
  intro interface first second pair
  obtain ⟨forward, backward, atoms⟩ := system.literalSystem.bisimilar_unfold.mp pair
  refine ⟨?_, ?_, atoms⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
      forward (literalLabel label) next step
    have equal := Label.skeleton_eq labels
    change label = matchedLabel.skeleton at equal
    change system.act matchedLabel.skeleton second matched at matchedStep
    rw [← equal] at matchedStep
    exact ⟨label, matched, matchedStep,
      Label.relates_refl system.literalSystem.bisimilar_refl label, successors⟩
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
      backward (literalLabel label) next step
    have equal := Label.skeleton_eq labels
    change matchedLabel.skeleton = label at equal
    change system.act matchedLabel.skeleton first matched at matchedStep
    rw [equal] at matchedStep
    exact ⟨label, matched, matchedStep,
      Label.relates_refl system.literalSystem.bisimilar_refl label, successors⟩

end System

section IPO

open CategoryTheory Mettapedia.GSLT.RedexRelativeCongruence

universe v u

variable {C : Type u} [Category.{v} C] {origin : C}

/-- The existing IPO transition family as a payload-free instance. -/
def ipoSystem (rules : ReactionRule origin → Prop) :
    System (literalVocabulary (fun source target : C => source ⟶ target))
      (fun interface => origin ⟶ interface) where
  act label := ActIPO rules label.skeleton
  Atom := fun _ => Empty
  observes atom := Empty.elim atom

/-- Empty payloads recover the existing context-labelled relation exactly.
This connects two definitions, rather than replacing either by an alias. -/
theorem ipo_bisimilar_iff (rules : ReactionRule origin → Prop) {interface : C}
    (left right : origin ⟶ interface) :
    (ipoSystem rules).Bisimilar interface left right ↔ IPOBisimilar rules left right := by
  constructor
  · intro related
    refine ⟨(ipoSystem rules).Bisimilar, ?_, related⟩
    intro current first second pair
    obtain ⟨forward, backward, -⟩ := (ipoSystem rules).bisimilar_unfold.mp pair
    constructor
    · intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
        forward (literalLabel label) next step
      have equal := Label.skeleton_eq labels
      change label = matchedLabel.skeleton at equal
      change ActIPO rules matchedLabel.skeleton second matched at matchedStep
      rw [← equal] at matchedStep
      exact ⟨matched, matchedStep, successors⟩
    · intro nextInterface label next step
      obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
        backward (literalLabel label) next step
      have equal := Label.skeleton_eq labels
      change matchedLabel.skeleton = label at equal
      change ActIPO rules matchedLabel.skeleton first matched at matchedStep
      rw [equal] at matchedStep
      exact ⟨matched, matchedStep, successors⟩
  · rintro ⟨relation, closed, pair⟩
    apply (ipoSystem rules).coinduction (relation := relation) ?_ interface left right pair
    intro current first second related
    obtain ⟨forward, backward⟩ := closed first second related
    refine ⟨?_, ?_, fun atom => Empty.elim atom⟩
    · intro nextInterface label next step
      obtain ⟨matched, matchedStep, successors⟩ := forward label.skeleton next step
      exact ⟨literalLabel label.skeleton, matched, matchedStep,
        (relates_literal_iff relation label (literalLabel label.skeleton)).mpr rfl, successors⟩
    · intro nextInterface label next step
      obtain ⟨matched, matchedStep, successors⟩ := backward label.skeleton next step
      exact ⟨literalLabel label.skeleton, matched, matchedStep,
        (relates_literal_iff relation (literalLabel label.skeleton) label).mpr rfl, successors⟩

end IPO

namespace PayloadControls

/-- Terminal identities are unobserved; alarms are observed. Sends carry processes. -/
inductive Process where
  | halt (identity : Bool)
  | send (channel : Bool) (payload : Process)
  | alarm
  deriving DecidableEq

inductive Code where
  | halt
  | send (channel : Bool) (payload : Code)
  | alarm
  deriving DecidableEq

/-- Erase only the terminal identity, retaining channels and nested payloads. -/
def code : Process → Code
  | .halt _ => .halt
  | .send channel payload => .send channel (code payload)
  | .alarm => .alarm

def controlVocabulary : Vocabulary Unit where
  Skeleton := fun _ _ => Bool
  Slot := fun _ => Unit
  interface := fun _ _ => ()

abbrev States := fun _ : Unit => Process

def sendLabel (channel : Bool) (payload : Process) : Label controlVocabulary States () () :=
  ⟨channel, fun _ => payload⟩

/-- Each send performs a real transition bearing its process payload. -/
def system : System controlVocabulary States where
  act label source target := source = .send label.skeleton (label.payload ()) ∧ target = .halt false
  Atom := fun _ => Unit
  observes _ state := state = .alarm

private theorem matching_of_code_eq {sourceInterface targetInterface : Unit}
    {left right : Process} (same : code left = code right)
    (label : Label controlVocabulary States sourceInterface targetInterface) {next : Process}
    (step : system.act label left next) :
    ∃ matchedLabel matched, system.act matchedLabel right matched ∧
      Label.Relates (fun _ first second => code first = code second) label matchedLabel ∧
        code next = code matched := by
  cases sourceInterface
  cases targetInterface
  change left = .send label.skeleton (label.payload ()) ∧ next = .halt false at step
  obtain ⟨rfl, rfl⟩ := step
  cases right with
  | halt identity => simp [code] at same
  | alarm => simp [code] at same
  | send channel payload =>
    change Code.send label.skeleton (code (label.payload ())) = Code.send channel (code payload) at same
    obtain ⟨sameChannel, samePayload⟩ := Code.send.inj same
    refine ⟨⟨label.skeleton, fun _ => payload⟩, .halt false, ?_,
      .mk label.skeleton label.payload (fun _ => payload) (fun slot => by
        cases slot
        exact samePayload), rfl⟩
    exact ⟨by rw [sameChannel], rfl⟩

/-- A coinductive proof justifies identity erasure, including nested labels. -/
theorem bisimilar_of_code_eq {left right : Process} (same : code left = code right) :
    system.Bisimilar () left right := by
  apply system.coinduction (relation := fun _ first second => code first = code second)
    ?_ () left right same
  intro interface first second pair
  refine ⟨?_, ?_, ?_⟩
  · intro nextInterface label next step
    exact matching_of_code_eq pair label step
  · intro nextInterface label next step
    obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
      matching_of_code_eq pair.symm label step
    exact ⟨matchedLabel, matched, matchedStep,
      Label.relates_mono (fun _ _ _ equal => equal.symm) (Label.relates_converse labels),
      successors.symm⟩
  · intro atom
    change first = .alarm ↔ second = .alarm
    cases first <;> cases second <;> simp_all [code]

/-- Both labels and their payload labels differ literally, but behavior agrees. -/
theorem nested_payloads_are_bisimilar :
    system.Bisimilar () (.send false (.send true (.halt false)))
      (.send false (.send true (.halt true))) :=
  bisimilar_of_code_eq rfl

theorem nested_payloads_are_not_equal :
    Process.send false (.send true (.halt false)) ≠ .send false (.send true (.halt true)) := by
  decide

/-- Literal label comparison separates two sends of behaviorally identical terminals. -/
theorem literal_matching_is_stricter :
    ¬ system.literalSystem.Bisimilar () (.send false (.halt false)) (.send false (.halt true)) := by
  intro related
  have step : system.literalSystem.act (literalLabel (sendLabel false (.halt false)))
      (.send false (.halt false)) (.halt false) := ⟨rfl, rfl⟩
  obtain ⟨matchedLabel, matched, matchedStep, labels, -⟩ :=
    (system.literalSystem.bisimilar_unfold.mp related).1 _ _ step
  have same := Label.skeleton_eq labels
  change sendLabel false (.halt false) = matchedLabel.skeleton at same
  change system.act matchedLabel.skeleton (.send false (.halt true)) matched at matchedStep
  rw [← same] at matchedStep
  simp [system, sendLabel] at matchedStep

/-- Channel skeletons remain observable through transition matching. -/
theorem different_channels_are_distinguished :
    ¬ system.Bisimilar () (.send false (.halt false)) (.send true (.halt false)) := by
  intro related
  have step : system.act (sendLabel false (.halt false)) (.send false (.halt false))
      (.halt false) := ⟨rfl, rfl⟩
  obtain ⟨matchedLabel, matched, matchedStep, labels, -⟩ :=
    (system.bisimilar_unfold.mp related).1 _ _ step
  have same := Label.skeleton_eq labels
  change false = matchedLabel.skeleton at same
  have channel := (Process.send.inj matchedStep.1).1
  exact Bool.false_ne_true (same.trans channel.symm)

/-- Equal transition shapes do not erase differing payload observations. -/
theorem observed_payloads_are_distinguished :
    ¬ system.Bisimilar () (.send false .alarm) (.send false (.halt false)) := by
  intro related
  have step : system.act (sendLabel false .alarm) (.send false .alarm) (.halt false) :=
    ⟨rfl, rfl⟩
  obtain ⟨matchedLabel, matched, matchedStep, labels, -⟩ :=
    (system.bisimilar_unfold.mp related).1 _ _ step
  have payload := (Process.send.inj matchedStep.1).2
  cases labels with
  | mk shape leftBody rightBody pairs =>
    have compared := pairs ()
    have observed := system.observes_iff compared ()
    change Process.alarm = .alarm ↔ rightBody () = .alarm at observed
    have impossible := observed.mp rfl
    change Process.halt false = rightBody () at payload
    rw [← payload] at impossible
    cases impossible

/-- Class steps lift, but requiring a prescribed literal label would be false. -/
theorem class_step_needs_label_class :
    system.quotientStep (system.toLabelClass (sendLabel false (.halt false)))
      (system.toClass (.send false (.halt true))) (system.toClass (.halt false)) ∧
    ¬ ∃ next, system.act (sendLabel false (.halt false)) (.send false (.halt true)) next := by
  constructor
  · have labels : system.toLabelClass (sendLabel false (.halt true)) =
        system.toLabelClass (sendLabel false (.halt false)) :=
      (system.labelClass_eq_iff _ _).mpr (by
        exact .mk (vocabulary := controlVocabulary) (relation := system.Bisimilar) false
          (fun _ => Process.halt true) (fun _ => Process.halt false)
          (fun _ => bisimilar_of_code_eq (left := .halt true) (right := .halt false) rfl))
    exact ⟨sendLabel false (.halt true), .send false (.halt true), .halt false,
      labels, rfl, ⟨rfl, rfl⟩, rfl⟩
  · rintro ⟨next, step⟩
    simp [system, sendLabel] at step

end PayloadControls

namespace TypedPayloadControls

/-- Two genuinely different carriers, not two names for one state type. -/
abbrev States : Bool → Type
  | false => Bool
  | true => Nat

def typedVocabulary : Vocabulary Bool where
  Skeleton := fun _ _ => Unit
  Slot := fun _ => Bool
  interface := fun _ slot => slot

/-- The two positions carry a Boolean input and a natural-number output. -/
def pairLabel (input : Bool) (output : Nat) : Label typedVocabulary States false true where
  skeleton := ()
  payload
    | false => input
    | true => output

/-- An interface-changing computation whose result depends on its input. -/
def system : System typedVocabulary States where
  act {source target} :=
    match source, target with
    | false, true => fun label input output =>
        label.payload false = input ∧ label.payload true = output ∧
          output = if input then 1 else 0
    | _, _ => fun _ _ _ => False
  Atom := States
  observes atom state := atom = state

theorem false_computes_zero : system.act (pairLabel false 0) false 0 :=
  ⟨rfl, rfl, rfl⟩

theorem true_computes_one : system.act (pairLabel true 1) true 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The Boolean slot cannot be ignored. -/
theorem wrong_input_is_rejected : ¬ system.act (pairLabel false 1) true 1 := by
  intro step
  exact Bool.false_ne_true step.1

/-- The Nat slot cannot be ignored, and a constant-zero implementation fails. -/
theorem wrong_output_is_rejected : ¬ system.act (pairLabel true 0) true 1 := by
  intro step
  exact Nat.zero_ne_one step.2.1

theorem constant_result_is_rejected : ¬ system.act (pairLabel true 0) true 0 := by
  intro step
  exact Nat.zero_ne_one step.2.2

/-- The two actual successors remain distinct after behavioral quotienting. -/
theorem successor_classes_are_distinct :
    system.toClass (interface := true) 0 ≠ system.toClass (interface := true) 1 := by
  intro equal
  have related := (system.class_eq_iff (interface := true) 0 1).mp equal
  have observed := system.observes_iff related (0 : Nat)
  exact Nat.zero_ne_one (observed.mp rfl)

end TypedPayloadControls

#print axioms System.progress_mono
#print axioms System.bisimilar_unfold
#print axioms System.bisimilar_trans
#print axioms System.quotientStep_from_class_iff
#print axioms System.bisimilar_classLabel_iff
#print axioms ipo_bisimilar_iff
#print axioms PayloadControls.nested_payloads_are_bisimilar
#print axioms PayloadControls.literal_matching_is_stricter
#print axioms PayloadControls.observed_payloads_are_distinguished
#print axioms PayloadControls.class_step_needs_label_class
#print axioms TypedPayloadControls.successor_classes_are_distinct

end Mettapedia.GSLT.HigherOrderBisimulation
