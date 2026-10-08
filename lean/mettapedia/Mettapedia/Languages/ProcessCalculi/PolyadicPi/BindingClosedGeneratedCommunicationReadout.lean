import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunication
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedCommunicationValues

/-!
# Generated communication evidence on arbitrary whole function inputs

The independent unary and binary COMM declarations are supplied with their
complete receiver functions and ordered channel arguments. Both endpoints
are read in the final guest's actual process object. These arrows remain
defined at arbitrary categorical stages, including variable identifications.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunicationReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open BindingClosedPrimitiveOperations

universe k

abbrev Target := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev binding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev ordinary := BindingClosedGeneratedOperationalModel.ordinary.{k}
abbrev category := BindingClosedGeneratedOperationalModel.category.{k}
abbrev comparison := BindingClosedGeneratedOperationalModel.processComparison.{k}

def source : category.{k}.edge ⟶ ordinary.processes := category.source ≫ comparison.inv
def target : category.{k}.edge ⟶ ordinary.processes := category.target ≫ comparison.inv

variable {Z : Target.{k}}

def unaryParameters (function : Z ⟶ ordinary.termObject) :
    Z ⟶ binding.family (AllArity.communicationMetas 1) :=
  lift (function ≫ unaryBody binding) (toUnit Z)

def unaryEnvironment (channel argument : Z ⟶ ordinary.names) :
    binding.model.Env Z (AllArity.comm 1).ctx :=
  fun sort position => match sort, position with
    | .nm, .zero => channel
    | .nm, .succ .zero => argument

def unary (channel argument : Z ⟶ ordinary.names) (function : Z ⟶ ordinary.termObject) :
    Z ⟶ category.edge :=
  BindingClosedGeneratedCommunication.suppliedFiring 1 (unaryParameters function)
    (unaryEnvironment channel argument)

theorem unary_source (channel argument : Z ⟶ ordinary.names)
    (function : Z ⟶ ordinary.termObject) :
    unary channel argument function ≫ source =
      lift (lift channel argument ≫ ordinary.output)
        (lift channel function ≫ ordinary.input) ≫ ordinary.parallel := by
  rw [unary, source, ← Category.assoc,
    BindingClosedGeneratedCommunication.supplied_source]
  rw [BindingClosedCommunicationValues.unary_before_value binding
    (unaryParameters function) (unaryEnvironment channel argument) function (lift_fst _ _)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem unary_target (channel argument : Z ⟶ ordinary.names)
    (function : Z ⟶ ordinary.termObject) :
    unary channel argument function ≫ target =
      lift argument function ≫ (ihom.ev ordinary.names).app ordinary.processes := by
  rw [unary, target, ← Category.assoc,
    BindingClosedGeneratedCommunication.supplied_target]
  rw [BindingClosedCommunicationValues.unary_after_value binding
    (unaryParameters function) (unaryEnvironment channel argument) function (lift_fst _ _)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

def binaryParameters (function : Z ⟶ ((ordinary.names ⊗ ordinary.names) ⟶[Target] ordinary.processes)) :
    Z ⟶ binding.family (AllArity.communicationMetas 2) :=
  lift (function ≫ binaryBody binding) (toUnit Z)

def binaryEnvironment (channel first second : Z ⟶ ordinary.names) :
    binding.model.Env Z (AllArity.comm 2).ctx :=
  fun sort position => match sort, position with
    | .nm, .zero => channel
    | .nm, .succ .zero => first
    | .nm, .succ (.succ .zero) => second

def binary (channel first second : Z ⟶ ordinary.names)
    (function : Z ⟶ ((ordinary.names ⊗ ordinary.names) ⟶[Target] ordinary.processes)) :
    Z ⟶ category.edge :=
  BindingClosedGeneratedCommunication.suppliedFiring 2 (binaryParameters function)
    (binaryEnvironment channel first second)

theorem binary_source (channel first second : Z ⟶ ordinary.names)
    (function : Z ⟶ ((ordinary.names ⊗ ordinary.names) ⟶[Target] ordinary.processes)) :
    binary channel first second function ≫ source =
      lift (lift channel (lift first second) ≫ ordinary.send)
        (lift channel function ≫ ordinary.receive) ≫ ordinary.parallel := by
  rw [binary, source, ← Category.assoc,
    BindingClosedGeneratedCommunication.supplied_source]
  rw [BindingClosedCommunicationValues.binary_before_value binding
    (binaryParameters function) (binaryEnvironment channel first second) function (lift_fst _ _)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem binary_target (channel first second : Z ⟶ ordinary.names)
    (function : Z ⟶ ((ordinary.names ⊗ ordinary.names) ⟶[Target] ordinary.processes)) :
    binary channel first second function ≫ target =
      lift (lift first second) function ≫ (ihom.ev (ordinary.names ⊗ ordinary.names)).app ordinary.processes := by
  rw [binary, target, ← Category.assoc,
    BindingClosedGeneratedCommunication.supplied_target]
  rw [BindingClosedCommunicationValues.binary_after_value binding
    (binaryParameters function) (binaryEnvironment channel first second) function (lift_fst _ _)]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem unary_substitution {W : Target.{k}} (change : W ⟶ Z)
    (channel argument : Z ⟶ ordinary.names) (function : Z ⟶ ordinary.termObject) :
    unary (change ≫ channel) (change ≫ argument) (change ≫ function) =
      change ≫ unary channel argument function := by
  unfold unary
  have parameters : unaryParameters (change ≫ function) = change ≫ unaryParameters function := by
    simp only [unaryParameters, comp_lift, Category.assoc, comp_toUnit]
  have environment : unaryEnvironment (change ≫ channel) (change ≫ argument) =
      binding.model.restage change (unaryEnvironment channel argument) := by
    funext sort position
    match sort, position with
    | .nm, .zero => rfl
    | .nm, .succ .zero => rfl
  rw [parameters, environment, BindingClosedGeneratedCommunication.supplied_substitution]

theorem binary_substitution {W : Target.{k}} (change : W ⟶ Z)
    (channel first second : Z ⟶ ordinary.names)
    (function : Z ⟶ ((ordinary.names ⊗ ordinary.names) ⟶[Target] ordinary.processes)) :
    binary (change ≫ channel) (change ≫ first) (change ≫ second) (change ≫ function) =
      change ≫ binary channel first second function := by
  unfold binary
  have parameters : binaryParameters (change ≫ function) = change ≫ binaryParameters function := by
    simp only [binaryParameters, comp_lift, Category.assoc, comp_toUnit]
  have environment : binaryEnvironment (change ≫ channel) (change ≫ first) (change ≫ second) =
      binding.model.restage change (binaryEnvironment channel first second) := by
    funext sort position
    match sort, position with
    | .nm, .zero => rfl
    | .nm, .succ .zero => rfl
    | .nm, .succ (.succ .zero) => rfl
  rw [parameters, environment, BindingClosedGeneratedCommunication.supplied_substitution]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunicationReadout
