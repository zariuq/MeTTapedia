import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeFamilyInversion

/-!
# Complete ask, get and build characterizations for the whole typed family

The inspected labels range over the actual administrative rule family,
including competing heads and coordinates. Minimality recovers a complete
authored tuple, not a root decoder. A supplied bundle determines every child
class, so get and build have exact complete readouts whenever origins are
inhabited. Ask retains all AC1 decompositions of its actual source input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

theorem bundle_class_eq_iff (head : SourceHead source Parallel) (first second : Arguments head) :
    classOf (bundle head first) = classOf (bundle head second) ↔
      ∀ position, classOf (first position) = classOf (second position) :=
  node_class_eq_iff (signature := signature source Parallel) (Parallel := NativeParallel)
    (Constructor.arguments head) first second

theorem sourceNode_class_congruence (head : SourceHead source Parallel) (first second : Arguments head)
    (coordinates : ∀ position, classOf (first position) = classOf (second position)) :
    classOf (sourceNode head first) = classOf (sourceNode head second) := by
  cases head with
  | ordinary constructor =>
    exact (node_class_eq_iff (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.original constructor) first second).mpr coordinates
  | properCut sort parallel =>
    exact Quotient.sound (Equation.cut (signature := signature source Parallel)
      (Parallel := NativeParallel) (sort := .original sort) parallel
      (Quotient.exact (coordinates 0)) (Quotient.exact (coordinates 1)))
  | unit => rfl

theorem ask_step_iff (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.arguments head)) :
    ActIPO (rules source Parallel Origins) (probeLabel (.ask head))
      (RawArrow.value supplied) (RawArrow.value observed) ↔
    ∃ _origin : Origins, ∃ arguments : Arguments head,
      supplied = classOf (sourceNode head arguments) ∧ observed = classOf (bundle head arguments) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.ask head) supplied observed step
    cases occurrence with
    | ask origin found arguments =>
      change Probe.ask found = Probe.ask head at instrumentRead
      have same : found = head := Probe.ask.inj instrumentRead
      subst found
      exact ⟨origin, arguments, (eq_of_heq inputRead).symm, (eq_of_heq outputRead).symm⟩
    | get => cases instrumentRead
    | build => cases instrumentRead
  · rintro ⟨origin, arguments, rfl, rfl⟩
    exact (Occurrence.ask origin head arguments).direct_step

theorem get_step_iff (head : SourceHead source Parallel) (position : Fin (headArity head))
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.arguments head))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position))) :
    ActIPO (rules source Parallel Origins) (probeLabel (.get head position))
      (RawArrow.value supplied) (RawArrow.value observed) ↔
    ∃ _origin : Origins, ∃ arguments : Arguments head,
      supplied = classOf (bundle head arguments) ∧ observed = classOf (arguments position) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.get head position) supplied observed step
    cases occurrence with
    | ask => cases instrumentRead
    | get origin found arguments selected =>
      change Probe.get found selected = Probe.get head position at instrumentRead
      obtain ⟨same, selectedRead⟩ := Probe.get.inj instrumentRead
      subst found
      have selectedSame : selected = position := eq_of_heq selectedRead
      subst selected
      exact ⟨origin, arguments, (eq_of_heq inputRead).symm, (eq_of_heq outputRead).symm⟩
    | build => cases instrumentRead
  · rintro ⟨origin, arguments, rfl, rfl⟩
    exact (Occurrence.get origin head arguments position).direct_step

theorem build_step_iff (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.arguments head))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head))) :
    ActIPO (rules source Parallel Origins) (probeLabel (.build head))
      (RawArrow.value supplied) (RawArrow.value observed) ↔
    ∃ _origin : Origins, ∃ arguments : Arguments head,
      supplied = classOf (bundle head arguments) ∧ observed = classOf (sourceNode head arguments) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.build head) supplied observed step
    cases occurrence with
    | ask => cases instrumentRead
    | get => cases instrumentRead
    | build origin found arguments =>
      change Probe.build found = Probe.build head at instrumentRead
      have same : found = head := Probe.build.inj instrumentRead
      subst found
      exact ⟨origin, arguments, (eq_of_heq inputRead).symm, (eq_of_heq outputRead).symm⟩
  · rintro ⟨origin, arguments, rfl, rfl⟩
    exact (Occurrence.build origin head arguments).direct_step

theorem get_bundle_step_iff (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position))) :
    ActIPO (rules source Parallel Origins) (probeLabel (.get head position))
      (RawArrow.value (classOf (bundle head arguments))) (RawArrow.value observed) ↔
    Nonempty Origins ∧ observed = classOf (arguments position) := by
  rw [get_step_iff]
  constructor
  · rintro ⟨origin, found, inputRead, outputRead⟩
    have coordinates := (bundle_class_eq_iff head arguments found).mp inputRead
    exact ⟨⟨origin⟩, outputRead.trans (coordinates position).symm⟩
  · rintro ⟨⟨origin⟩, outputRead⟩
    exact ⟨origin, arguments, rfl, outputRead⟩

theorem build_bundle_step_iff (head : SourceHead source Parallel) (arguments : Arguments head)
    (observed : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head))) :
    ActIPO (rules source Parallel Origins) (probeLabel (.build head))
      (RawArrow.value (classOf (bundle head arguments))) (RawArrow.value observed) ↔
    Nonempty Origins ∧ observed = classOf (sourceNode head arguments) := by
  rw [build_step_iff]
  constructor
  · rintro ⟨origin, found, inputRead, outputRead⟩
    have coordinates := (bundle_class_eq_iff head arguments found).mp inputRead
    exact ⟨⟨origin⟩, outputRead.trans (sourceNode_class_congruence head arguments found coordinates).symm⟩
  · rintro ⟨⟨origin⟩, outputRead⟩
    exact ⟨origin, arguments, rfl, outputRead⟩

theorem no_probe_step_without_origins (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (observed : ValueClass (source := source) (Parallel := Parallel) (result instrument)) :
    ¬ActIPO (rules source Parallel Empty) (probeLabel instrument)
      (RawArrow.value supplied) (RawArrow.value observed) := by
  intro step
  obtain ⟨occurrence, _⟩ := administrative_probe_step_inversion instrument supplied observed step
  exact Empty.elim occurrence.origin

end Mettapedia.OSLF.Framework.SortedTypedInstruments
