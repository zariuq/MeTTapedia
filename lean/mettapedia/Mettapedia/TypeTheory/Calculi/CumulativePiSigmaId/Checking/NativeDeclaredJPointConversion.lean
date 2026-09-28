import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayContextConversion

/-!
# Retyping a declared J telescope after replacing its base point

A checked point replacement changes the expected motive and method types in
the existing `A, X, P, D` telescope. One checked conversion of the point
generates conversions of both dependent lookup types by pointwise substitution.
Given checked formations of those two new types, the construction retains
casts for P and D and checks all four argument images as one telescope.

The formations and the point certificate are inputs. No erased term is
elaborated and no conversion or formation is silently inferred.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeDeclaredJPointConversion

open Presentation StructuralTypingReplay NativeIndexedFamilies NativeJudgmentReplay

def substitutePoint (point : Tower.Tm 4) : Sub Tower.Head 4 4 :=
  fun index => if index = 2 then point else .var index

def expectedMotive (point : Tower.Tm 4) : Tower.Tm 4 :=
  subst (substitutePoint point) (Intrinsic.contextAXPD.lookup (1 : Fin 4))

def expectedMethod (point : Tower.Tm 4) : Tower.Tm 4 :=
  subst (substitutePoint point) (Intrinsic.contextAXPD.lookup (0 : Fin 4))

def componentConversions (pointConversion : NativeRelatorConversionChecking.Code 4) :
    Fin 4 → NativeRelatorConversionChecking.Code 4 :=
  fun index => if index = 2 then pointConversion else .refl (.var index)

theorem component_conversions_checked (point : Tower.Tm 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) (index : Fin 4) :
    NativeRelatorConversionChecking.check (componentConversions pointConversion index)
      (ids index) (substitutePoint point index) = true := by
  by_cases changed : index = 2
  · subst index
    simpa [componentConversions, substitutePoint, ids] using pointConverted
  · simp [componentConversions, substitutePoint, ids, changed,
      NativeRelatorConversionChecking.check, StructuralConversionCode.Code.check,
      StructuralConversionCode.Code.decode]

def lookupConversion (point : Tower.Tm 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (index : Fin 4) : NativeRelatorConversionChecking.Code 4 :=
  NativeRelatorConversionChecking.substitutePointwise ids (substitutePoint point)
    (componentConversions pointConversion) (Intrinsic.contextAXPD.lookup index)

theorem lookup_conversion_checked (point : Tower.Tm 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true) (index : Fin 4) :
    NativeRelatorConversionChecking.check (lookupConversion point pointConversion index)
      (Intrinsic.contextAXPD.lookup index)
      (subst (substitutePoint point) (Intrinsic.contextAXPD.lookup index)) = true := by
  have checked := NativeRelatorConversionChecking.check_substitutePointwise
    ids (substitutePoint point) (componentConversions pointConversion)
    (Intrinsic.contextAXPD.lookup index)
    (component_conversions_checked point pointConversion pointConverted)
  simpa only [lookupConversion, subst_ids] using checked

def imageCodes (pointCode : Code 4)
    (point : Tower.Tm 4) (pointConversion : NativeRelatorConversionChecking.Code 4)
    (motiveLevel methodLevel : Tower.Head)
    (motiveFormation methodFormation : Code 4) : Fin 4 → Code 4 :=
  fun index =>
    if index = 0 then
      .convert (Intrinsic.contextAXPD.lookup 0) methodLevel
        .var methodFormation (lookupConversion point pointConversion 0)
    else if index = 1 then
      .convert (Intrinsic.contextAXPD.lookup 1) motiveLevel
        .var motiveFormation (lookupConversion point pointConversion 1)
    else if index = 2 then pointCode else .var

theorem images_check (point : Tower.Tm 4) (pointCode : Code 4)
    (pointConversion : NativeRelatorConversionChecking.Code 4)
    (motiveLevel methodLevel : Tower.Head)
    (motiveFormation methodFormation : Code 4)
    (pointChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      point (.var 3) pointCode = true)
    (pointConverted : NativeRelatorConversionChecking.check pointConversion
      (.var 2) point = true)
    (motiveUniverse : IntrinsicRelator.rules.isUniverse motiveLevel)
    (methodUniverse : IntrinsicRelator.rules.isUniverse methodLevel)
    (motiveFormed : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (expectedMotive point) (.head motiveLevel) motiveFormation = true)
    (methodFormed : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (expectedMethod point) (.head methodLevel) methodFormation = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD (substitutePoint point)
        (imageCodes pointCode point pointConversion motiveLevel methodLevel
          motiveFormation methodFormation) = true := by
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  fin_cases index
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 0) (expectedMethod point)
        (.convert (Intrinsic.contextAXPD.lookup 0) methodLevel .var methodFormation
          (lookupConversion point pointConversion 0)) = true
    have source : StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 0) (Intrinsic.contextAXPD.lookup 0) (.var : Code 4) = true := by
      decide +kernel
    have converted := lookup_conversion_checked point pointConversion pointConverted 0
    simpa only [StructuralTypingReplay.check, decide_eq_true methodUniverse,
      source, methodFormed, converted, Bool.true_and, Bool.and_true]
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 1) (expectedMotive point)
        (.convert (Intrinsic.contextAXPD.lookup 1) motiveLevel .var motiveFormation
          (lookupConversion point pointConversion 1)) = true
    have source : StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 1) (Intrinsic.contextAXPD.lookup 1) (.var : Code 4) = true := by
      decide +kernel
    have converted := lookup_conversion_checked point pointConversion pointConverted 1
    simpa only [StructuralTypingReplay.check, decide_eq_true motiveUniverse,
      source, motiveFormed, converted, Bool.true_and, Bool.and_true]
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        point (.var 3) pointCode = true
    exact pointChecked
  · change StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        (.var 3) (Intrinsic.contextAXPD.lookup 3) (.var : Code 4) = true
    decide +kernel

#print axioms lookup_conversion_checked
#print axioms images_check

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeDeclaredJPointConversion
