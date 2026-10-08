import Mettapedia.OSLF.Framework.InstrumentEquationMeasure

/-!
# Actual equation-class decomposition and freely adjoined argument bundles

An opening retains a supplied raw constructor decomposition of the actual
source equation class. Its target bundle contains the corresponding component
classes. Bundles are freely adjoined with distinct constructor profiles and
componentwise equation classes, so projection is deterministic up to the
authored congruence. Cross-root equations are interpreted directly rather
than required to preserve a raw structural view.

These labels record only the nullary probe and its argument position. A
comparison with derived minimal-context labels is a separate construction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentEquations

open InstrumentObservations

universe u v

variable {Symbols : Type u} {arity : Symbols → Nat}
variable (generators : Tree Symbols arity → Tree Symbols arity → Prop)

theorem representative_exists (value : TermClass generators) :
    ∃ term : Tree Symbols arity, classOf generators term = value := by
  refine Quotient.inductionOn value ?_
  intro term
  exact ⟨term, rfl⟩

def representative (value : TermClass generators) : Tree Symbols arity :=
  Classical.choose (representative_exists generators value)

@[simp]
theorem representative_readout (value : TermClass generators) :
    classOf generators (representative generators value) = value :=
  Classical.choose_spec (representative_exists generators value)

def nodeClass (constructor : Symbols)
    (arguments : Fin (arity constructor) → TermClass generators) : TermClass generators :=
  classOf generators (.node constructor (fun position => representative generators (arguments position)))

theorem nodeClass_readout (constructor : Symbols)
    (arguments : Fin (arity constructor) → Tree Symbols arity) :
    nodeClass generators constructor (fun position => classOf generators (arguments position)) =
      classOf generators (.node constructor arguments) := by
  apply Quotient.sound
  apply Equation.congruence
  intro position
  exact Quotient.exact (representative_readout generators (classOf generators (arguments position)))

theorem nodeClass_of_component_classes (constructor : Symbols)
    (first second : Fin (arity constructor) → Tree Symbols arity)
    (same : ∀ position, classOf generators (first position) = classOf generators (second position)) :
    classOf generators (.node constructor first) = classOf generators (.node constructor second) :=
  Quotient.sound (Equation.congruence constructor first second
    (fun position => Quotient.exact (same position)))

inductive ClassState where
  | term (value : TermClass generators)
  | bundle (constructor : Symbols) (arguments : Fin (arity constructor) → TermClass generators)

def classTag : ClassState generators → Option Symbols
  | .term _ => none
  | .bundle constructor _ => some constructor

inductive ClassEvent (opened : Policy Symbols) :
    ClassState generators → Label Symbols arity → ClassState generators → Type u where
  | ask (constructor : Symbols)
      (arguments : Fin (arity constructor) → Tree Symbols arity)
      (permission : opened constructor) (source : TermClass generators)
      (decomposes : classOf generators (.node constructor arguments) = source) :
      ClassEvent opened (.term source) (.ask constructor)
        (.bundle constructor (fun position => classOf generators (arguments position)))
  | get (constructor : Symbols)
      (arguments : Fin (arity constructor) → TermClass generators)
      (permission : opened constructor) (position : Fin (arity constructor)) :
      ClassEvent opened (.bundle constructor arguments) (.get constructor position)
        (.term (arguments position))
  | build (constructor : Symbols)
      (arguments : Fin (arity constructor) → TermClass generators)
      (permission : opened constructor) :
      ClassEvent opened (.bundle constructor arguments) (.build constructor)
        (.term (nodeClass generators constructor arguments))

abbrev ClassResponse (opened : Policy Symbols) (source : ClassState generators)
    (label : Label Symbols arity) (target : ClassState generators) : Prop :=
  Nonempty (ClassEvent generators opened source label target)

theorem ask_response_iff (opened : Policy Symbols) (source : TermClass generators)
    (constructor : Symbols) (arguments : Fin (arity constructor) → TermClass generators) :
    ClassResponse generators opened (.term source) (.ask constructor) (.bundle constructor arguments) ↔
      opened constructor ∧ nodeClass generators constructor arguments = source := by
  constructor
  · rintro ⟨event⟩
    cases event with
    | ask _ supplied permission _ decomposes =>
      exact ⟨permission, (nodeClass_readout generators constructor supplied).trans decomposes⟩
  · rintro ⟨permission, decomposes⟩
    have event := ClassEvent.ask (generators := generators) constructor
      (fun position => representative generators (arguments position)) permission source decomposes
    exact ⟨by simpa only [representative_readout] using event⟩

theorem opening_iff_equation (opened : Policy Symbols) (source : Tree Symbols arity)
    (constructor : Symbols) (arguments : Fin (arity constructor) → Tree Symbols arity) :
    ClassResponse generators opened (.term (classOf generators source)) (.ask constructor)
        (.bundle constructor (fun position => classOf generators (arguments position))) ↔
      opened constructor ∧ Equation generators source (.node constructor arguments) := by
  rw [ask_response_iff, nodeClass_readout]
  constructor
  · rintro ⟨permission, decomposes⟩
    exact ⟨permission, Quotient.exact decomposes.symm⟩
  · rintro ⟨permission, equation⟩
    exact ⟨permission, Quotient.sound equation.symm⟩

theorem ask_target_supplied (opened : Policy Symbols) (source : TermClass generators)
    (constructor : Symbols) {target : ClassState generators}
    (response : ClassResponse generators opened (.term source) (.ask constructor) target) :
    ∃ arguments : Fin (arity constructor) → Tree Symbols arity,
      target = .bundle constructor (fun position => classOf generators (arguments position)) ∧
        classOf generators (.node constructor arguments) = source := by
  obtain ⟨event⟩ := response
  cases event with
  | ask _ arguments _ _ decomposes => exact ⟨arguments, rfl, decomposes⟩

theorem get_response_iff (opened : Policy Symbols) (constructor : Symbols)
    (arguments : Fin (arity constructor) → TermClass generators)
    (position : Fin (arity constructor)) (target : TermClass generators) :
    ClassResponse generators opened (.bundle constructor arguments) (.get constructor position)
      (.term target) ↔ opened constructor ∧ arguments position = target := by
  constructor
  · rintro ⟨event⟩
    cases event with
    | get _ _ permission _ => exact ⟨permission, rfl⟩
  · rintro ⟨permission, rfl⟩
    exact ⟨.get constructor arguments permission position⟩

theorem get_response_unique (opened : Policy Symbols) (constructor : Symbols)
    (arguments : Fin (arity constructor) → TermClass generators)
    (position : Fin (arity constructor)) {first second : TermClass generators}
    (firstResponse : ClassResponse generators opened (.bundle constructor arguments)
      (.get constructor position) (.term first))
    (secondResponse : ClassResponse generators opened (.bundle constructor arguments)
      (.get constructor position) (.term second)) : first = second :=
  ((get_response_iff generators opened constructor arguments position first).1 firstResponse).2.symm.trans
    ((get_response_iff generators opened constructor arguments position second).1 secondResponse).2

theorem get_target (opened : Policy Symbols) (constructor : Symbols)
    (arguments : Fin (arity constructor) → TermClass generators)
    (position : Fin (arity constructor)) {target : ClassState generators}
    (response : ClassResponse generators opened (.bundle constructor arguments)
      (.get constructor position) target) : target = .term (arguments position) := by
  obtain ⟨event⟩ := response
  cases event
  rfl

structure ClassReceipt (Origins : Type v) (opened : Policy Symbols)
    (source : ClassState generators) (label : Label Symbols arity)
    (target : ClassState generators) where
  origin : Origins
  event : ClassEvent generators opened source label target

structure RetainedOpening (Origins : Type v) (source : TermClass generators)
    (constructor : Symbols) where
  origin : Origins
  arguments : Fin (arity constructor) → Tree Symbols arity
  decomposes : classOf generators (.node constructor arguments) = source

section RetainedOperations

variable {generators}

def RetainedOpening.target {Origins : Type v} {source : TermClass generators} {constructor : Symbols}
    (opening : RetainedOpening generators Origins source constructor) : ClassState generators :=
  .bundle constructor (fun position => classOf generators (opening.arguments position))

def RetainedOpening.event {Origins : Type v} {source : TermClass generators} {constructor : Symbols}
    (opening : RetainedOpening generators Origins source constructor)
    (opened : Policy Symbols) (permission : opened constructor) :
    ClassEvent generators opened (.term source) (.ask constructor) opening.target :=
  .ask constructor opening.arguments permission source opening.decomposes

def RetainedOpening.receipt {Origins : Type v} {source : TermClass generators} {constructor : Symbols}
    (opening : RetainedOpening generators Origins source constructor)
    (opened : Policy Symbols) (permission : opened constructor) :
    ClassReceipt generators Origins opened (.term source) (.ask constructor) opening.target :=
  ⟨opening.origin, opening.event opened permission⟩

theorem retainedOpening_origin {Origins : Type v} {source : TermClass generators} {constructor : Symbols}
    (opening : RetainedOpening generators Origins source constructor)
    (opened : Policy Symbols) (permission : opened constructor) :
    (opening.receipt opened permission).origin = opening.origin := rfl

end RetainedOperations

theorem classReceipt_support_iff (Origins : Type v) [Nonempty Origins]
    (opened : Policy Symbols) (source : ClassState generators)
    (label : Label Symbols arity) (target : ClassState generators) :
    Nonempty (ClassReceipt generators Origins opened source label target) ↔
      ClassResponse generators opened source label target := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receipt.event⟩
  · rintro ⟨event⟩
    exact ⟨⟨Classical.choice inferInstance, event⟩⟩

structure IsClassBisimulation (opened : Policy Symbols)
    (relation : ClassState generators → ClassState generators → Prop) : Prop where
  tags : ∀ {source other}, relation source other → classTag generators source = classTag generators other
  forward : ∀ {source other}, relation source other → ∀ {label target},
    ClassResponse generators opened source label target →
      ∃ matched, ClassResponse generators opened other label matched ∧ relation target matched
  backward : ∀ {source other}, relation source other → ∀ {label target},
    ClassResponse generators opened other label target →
      ∃ matched, ClassResponse generators opened source label matched ∧ relation matched target

def ClassBisimilar (opened : Policy Symbols) (source other : ClassState generators) : Prop :=
  ∃ relation, IsClassBisimulation generators opened relation ∧ relation source other

theorem class_equality_bisimulation (opened : Policy Symbols) :
    IsClassBisimulation generators opened (fun first second => first = second) where
  tags same := congrArg (classTag generators) same
  forward := by
    rintro source other rfl label target response
    exact ⟨target, response, rfl⟩
  backward := by
    rintro source other rfl label target response
    exact ⟨target, response, rfl⟩

theorem class_bisimilar_refl (opened : Policy Symbols) (source : ClassState generators) :
    ClassBisimilar generators opened source source :=
  ⟨Eq, class_equality_bisimulation generators opened, rfl⟩

theorem class_equation_calibration (opened : Policy Symbols)
    {first second : Tree Symbols arity} (equation : Equation generators first second) :
    ClassBisimilar generators opened (.term (classOf generators first))
      (.term (classOf generators second)) := by
  have equal : classOf generators first = classOf generators second := Quotient.sound equation
  rw [equal]
  exact class_bisimilar_refl generators opened _

end Mettapedia.OSLF.Framework.InstrumentEquations
