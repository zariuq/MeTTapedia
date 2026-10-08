import Mettapedia.OSLF.Framework.SortedCommutativeProbeFamilyInversion

/-!
# Whole native argument readout of the actual probe family

Administrative IPO inversion reads arbitrary native argument tuples, not
only pure source values. The exact ask head and the complete selected get
coordinate survive the independent AC1 quotient. A get may return an
observer-bearing child; no source retraction or purity assumption is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

theorem ask_native_step_iff (constructor : SourceSymbol Symbols)
    (supplied : ValueClass arity .base) (result : ValueClass arity (.arguments constructor)) :
    ActIPO (rules arity Origins) (askLabel constructor) (RawArrow.value supplied) (RawArrow.value result) ↔
      ∃ _origin : Origins, ∃ arguments : Fin (sourceArity arity constructor) → Value arity .base,
        supplied = classOf (sourceNode arity constructor arguments) ∧
          result = classOf (bundle arity constructor arguments) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.ask constructor) supplied result step
    cases occurrence with
    | ask origin found arguments =>
      have same := InstrumentCutContexts.Probe.ask.inj instrumentRead
      subst found
      exact ⟨origin, arguments, (eq_of_heq inputRead).symm, (eq_of_heq outputRead).symm⟩
    | get => cases instrumentRead
    | build => cases instrumentRead
  · rintro ⟨origin, arguments, inputRead, outputRead⟩
    rw [inputRead, outputRead]
    exact (Occurrence.ask origin constructor arguments).direct_step

theorem get_native_step_iff (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base)
    (position : Fin (sourceArity arity constructor)) (result : ValueClass arity .base) :
    ActIPO (rules arity Origins) (getLabel constructor position)
      (RawArrow.value (classOf (bundle arity constructor arguments))) (RawArrow.value result) ↔
        Nonempty Origins ∧ result = classOf (arguments position) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.get constructor position)
        (classOf (bundle arity constructor arguments)) result step
    cases occurrence with
    | ask => cases instrumentRead
    | get origin found before selected =>
      obtain ⟨same, selectedRead⟩ := InstrumentCutContexts.Probe.get.inj instrumentRead
      subst found
      have selectedSame : selected = position := eq_of_heq selectedRead
      subst selected
      have bodyRead : classOf (bundle arity constructor before) = classOf (bundle arity constructor arguments) :=
        eq_of_heq inputRead
      have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.arguments constructor) before arguments).mp bodyRead
      exact ⟨⟨origin⟩, (eq_of_heq outputRead).symm.trans (coordinates position)⟩
    | build => cases instrumentRead
  · rintro ⟨⟨origin⟩, outputRead⟩
    rw [outputRead]
    exact (Occurrence.get origin constructor arguments position).direct_step

theorem sourceNode_class_congruence (constructor : SourceSymbol Symbols)
    (first second : Fin (sourceArity arity constructor) → Value arity .base)
    (coordinates : ∀ position, classOf (first position) = classOf (second position)) :
    classOf (sourceNode arity constructor first) = classOf (sourceNode arity constructor second) := by
  cases constructor with
  | ordinary symbol =>
    exact (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
      (Constructor.original symbol) first second).mpr coordinates
  | properCut =>
    have firstRead : Equation (first 0) (second 0) := Quotient.exact (coordinates 0)
    have secondRead : Equation (first 1) (second 1) := Quotient.exact (coordinates 1)
    exact Quotient.sound (Equation.cut (signature := signature arity) (Parallel := Parallel arity)
      rfl firstRead secondRead)
  | unit => rfl

theorem build_native_step_iff (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) (result : ValueClass arity .base) :
    ActIPO (rules arity Origins) (buildLabel constructor)
      (RawArrow.value (classOf (bundle arity constructor arguments))) (RawArrow.value result) ↔
        Nonempty Origins ∧ result = classOf (sourceNode arity constructor arguments) := by
  constructor
  · intro step
    obtain ⟨occurrence, instrumentRead, inputRead, outputRead⟩ :=
      administrative_probe_step_inversion (.build constructor)
        (classOf (bundle arity constructor arguments)) result step
    cases occurrence with
    | ask => cases instrumentRead
    | get => cases instrumentRead
    | build origin found before =>
      have same := InstrumentCutContexts.Probe.build.inj instrumentRead
      subst found
      have bodyRead : classOf (bundle arity constructor before) = classOf (bundle arity constructor arguments) :=
        eq_of_heq inputRead
      have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.arguments constructor) before arguments).mp bodyRead
      exact ⟨⟨origin⟩, (eq_of_heq outputRead).symm.trans
        (sourceNode_class_congruence constructor before arguments coordinates)⟩
  · rintro ⟨⟨origin⟩, outputRead⟩
    rw [outputRead]
    exact (Occurrence.build origin constructor arguments).direct_step

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
