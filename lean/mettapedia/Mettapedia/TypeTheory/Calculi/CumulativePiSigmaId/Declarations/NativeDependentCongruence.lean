import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayContextConversion

/-!
# Computed typing certificates across dependent term contexts

Changing a child of a dependent term can change the parent's inferred type.
The transformations below rebuild the actual parent proof and restore its
original annotation by a computed conversion and extracted formation proof.
They consume checked replacement children; they neither search for those
children nor select certificates from propositional subject reduction.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DependentCongruence

open Presentation StructuralTypingReplay NativeIndexedFamilies

/-- Recover the old result's formation and explicitly cast the replacement
from its new type. The original subject is used only for formation recovery. -/
def restoreResult {n : Nat} (contextCode : ContextCode n)
    (source displayed replacementType : Tower.Tm n) (sourceCode replacementCode : Code n)
    (conversion : NativeRelatorConversionChecking.Code n) : Option (Code n) :=
  (resultFormation contextCode source displayed sourceCode).map fun formed =>
    .convert replacementType formed.1 replacementCode formed.2 conversion

theorem restoreResult_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source displayed replacement replacementType : Tower.Tm n}
    {sourceCode replacementCode : Code n} {conversion : NativeRelatorConversionChecking.Code n}
    (accepted : check context source displayed contextCode sourceCode = true)
    (replaced : check context replacement replacementType contextCode replacementCode = true)
    (converted : NativeRelatorConversionChecking.check conversion replacementType displayed = true) :
    ∃ output, restoreResult contextCode source displayed replacementType sourceCode replacementCode
        conversion = some output ∧ check context replacement displayed contextCode output = true := by
  obtain ⟨level, formation, computed, isUniverse, formed⟩ := resultFormation_checked accepted
  refine ⟨.convert replacementType level replacementCode formation conversion, ?_, ?_⟩
  · simp only [restoreResult, computed, Option.map_some]
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at replaced formed ⊢
    exact ⟨replaced.1, ⟨⟨⟨isUniverse, replaced.2⟩, formed.2⟩, converted⟩⟩

def appArgument {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n)
    (B : Tower.Tm (n + 1)) (function old next : Tower.Tm n)
    (functionCode oldCode nextCode : Code n) (forward : NativeRelatorConversionChecking.Code n) :
    Option (Code n) :=
  restoreResult contextCode (.app function old) (inst0 old B) (inst0 next B)
    (.appElim A B functionCode oldCode) (.appElim A B functionCode nextCode)
    (.symm (NativeRelatorConversionChecking.inst0Argument old next forward B))

theorem appArgument_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A function old next : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {functionCode oldCode nextCode : Code n} {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.app function old) (inst0 old B) contextCode
      (.appElim A B functionCode oldCode) = true)
    (replaced : check context next A contextCode nextCode = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    ∃ output, appArgument contextCode A B function old next functionCode oldCode nextCode forward =
      some output ∧ check context (.app function next) (inst0 old B) contextCode output = true := by
  apply restoreResult_checked accepted
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at accepted replaced ⊢
    exact ⟨accepted.1, ⟨⟨accepted.2.1.1, replaced.2⟩, True.intro⟩⟩
  · exact StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode
      (NativeRelatorConversionChecking.check_inst0Argument converted B)

def sndArgument {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n)
    (B : Tower.Tm (n + 1)) (old next : Tower.Tm n) (oldCode nextCode : Code n)
    (forward : NativeRelatorConversionChecking.Code n) : Option (Code n) :=
  restoreResult contextCode (.snd old) (inst0 (.fst old) B) (inst0 (.fst next) B)
    (.sndElim A B oldCode) (.sndElim A B nextCode)
    (.symm (NativeRelatorConversionChecking.inst0Argument (.fst old) (.fst next)
      (StructuralConversionCode.Code.mapContext (.fst) (.congFst) forward) B))

theorem sndArgument_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A old next : Tower.Tm n} {B : Tower.Tm (n + 1)} {oldCode nextCode : Code n}
    {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.snd old) (inst0 (.fst old) B) contextCode (.sndElim A B oldCode) = true)
    (replaced : check context next (.sigma A B) contextCode nextCode = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    ∃ output, sndArgument contextCode A B old next oldCode nextCode forward = some output ∧
      check context (.snd next) (inst0 (.fst old) B) contextCode output = true := by
  apply restoreResult_checked accepted
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at replaced ⊢
    exact ⟨replaced.1, replaced.2, True.intro⟩
  · exact StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode
      (NativeRelatorConversionChecking.check_inst0Argument
        (StructuralConversionCode.Code.check_mapContext Tower.HeadEq NativeRelatorRootConversionCode.decode
          (.fst) (.congFst) (fun _ => rfl) converted) B)

def reflArgument {n : Nat} (contextCode : ContextCode n) (A old next : Tower.Tm n)
    (oldCode nextCode : Code n) (forward : NativeRelatorConversionChecking.Code n) : Option (Code n) :=
  restoreResult contextCode (.refl old) (.id A old old) (.id A next next)
    (.reflIntro A oldCode) (.reflIntro A nextCode)
    (.symm (StructuralConversionCode.Code.congId A old next old (.refl A) forward forward))

theorem reflArgument_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A old next : Tower.Tm n} {oldCode nextCode : Code n}
    {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.refl old) (.id A old old) contextCode (.reflIntro A oldCode) = true)
    (replaced : check context next A contextCode nextCode = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    ∃ output, reflArgument contextCode A old next oldCode nextCode forward = some output ∧
      check context (.refl next) (.id A old old) contextCode output = true := by
  apply restoreResult_checked accepted
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
      decide_eq_true_eq] at replaced ⊢
    exact ⟨replaced.1, replaced.2, True.intro⟩
  · exact StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode
      (StructuralConversionCode.Code.check_congId Tower.HeadEq NativeRelatorRootConversionCode.decode
        (StructuralConversionCode.Code.check_refl Tower.HeadEq NativeRelatorRootConversionCode.decode A)
        converted converted)

def pairFirst {n : Nat} (B : Tower.Tm (n + 1)) (old next : Tower.Tm n) (level : Tower.Head)
    (formation nextCode secondCode : Code n) (forward : NativeRelatorConversionChecking.Code n) :
    Option (Code n) := do
  let (_, bodyLevel, _, bodyFormation) ← formation.sigmaFormation
  let newFormation := bodyFormation.instantiateFormation NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute B bodyLevel next nextCode
  return .pairIntro level formation nextCode
    (.convert (inst0 old B) bodyLevel secondCode newFormation
      (NativeRelatorConversionChecking.inst0Argument old next forward B))

theorem pairFirst_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A old next second : Tower.Tm n} {B : Tower.Tm (n + 1)} {level : Tower.Head}
    {formation oldCode nextCode secondCode : Code n} {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.pair old second) (.sigma A B) contextCode
      (.pairIntro level formation oldCode secondCode) = true)
    (replaced : check context next A contextCode nextCode = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    ∃ output, pairFirst B old next level formation nextCode secondCode forward = some output ∧
      check context (.pair next second) (.sigma A B) contextCode output = true := by
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at accepted replaced
  obtain ⟨u, v, domain, body, computed, _, isV, _, bodyChecked⟩ :=
    Code.sigmaFormation_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
      formation accepted.2.1.1.2
  refine ⟨.pairIntro level formation nextCode
    (.convert (inst0 old B) v secondCode
      (body.instantiateFormation NativeRelatorConversionChecking.rename
        NativeRelatorConversionChecking.substitute B v next nextCode)
      (NativeRelatorConversionChecking.inst0Argument old next forward B)), ?_, ?_⟩
  · simp only [pairFirst, computed, bind, Option.bind, pure]
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨accepted.1, ⟨⟨⟨accepted.2.1.1.1, accepted.2.1.1.2⟩, replaced.2⟩,
      ⟨⟨⟨isV, accepted.2.2⟩, ?_⟩, NativeRelatorConversionChecking.check_inst0Argument converted B⟩⟩⟩
    exact Code.instantiateFormation_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
      NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.check_rename
      NativeRelatorConversionChecking.substitute NativeRelatorConversionChecking.check_substitute
      bodyChecked replaced.2

def identityType {n : Nat} (old : Tower.Tm n) (level : Tower.Head)
    (newFormation leftCode rightCode : Code n) (forward : NativeRelatorConversionChecking.Code n) : Code n :=
  .idForm level newFormation (.convert old level leftCode newFormation forward)
    (.convert old level rightCode newFormation forward)

theorem identityType_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next left right : Tower.Tm n} {level : Tower.Head}
    {oldFormation newFormation leftCode rightCode : Code n} {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.id old left right) (.head level) contextCode
      (.idForm level oldFormation leftCode rightCode) = true)
    (replaced : check context next (.head level) contextCode newFormation = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    check context (.id next left right) (.head level) contextCode
      (identityType old level newFormation leftCode rightCode forward) = true := by
  simp only [check, checkJudgment, StructuralTypingReplay.check, identityType, Bool.and_eq_true,
    decide_eq_true_eq] at accepted replaced ⊢
  exact ⟨accepted.1, ⟨⟨⟨⟨accepted.2.1.1.1.1, replaced.2⟩,
    ⟨⟨⟨accepted.2.1.1.1.1, accepted.2.1.1.2⟩, replaced.2⟩, converted⟩⟩,
    ⟨⟨⟨accepted.2.1.1.1.1, accepted.2.1.2⟩, replaced.2⟩, converted⟩⟩, True.intro⟩⟩

def piDomain {n : Nat} (next : Tower.Tm n) (body : Tower.Tm (n + 1)) (u v : Tower.Head)
    (oldFormation newFormation : Code n) (bodyCode : Code (n + 1))
    (forward : NativeRelatorConversionChecking.Code n) : Code n :=
  .piForm u v newFormation (convertNewest next u oldFormation forward body (.head v) bodyCode)

theorem piDomain_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm n} {body : Tower.Tm (n + 1)} {u v w : Tower.Head}
    {oldFormation newFormation : Code n} {bodyCode : Code (n + 1)}
    {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.pi old body) (.head w) contextCode
      (.piForm u v oldFormation bodyCode) = true)
    (replaced : check context next (.head u) contextCode newFormation = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    check context (.pi next body) (.head w) contextCode
      (piDomain next body u v oldFormation newFormation bodyCode forward) = true := by
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have original : check (.snoc context old) body (.head v)
      (.snoc contextCode u oldFormation) bodyCode = true := by
    simp only [check, checkJudgment, checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨inputs.1, inputs.2.1.1.1.1⟩, inputs.2.1.2⟩, inputs.2.2⟩
  have bodyChecked := check_convertNewest original replaced inputs.2.1.1.1.1 converted
  simp only [check, checkJudgment, Bool.and_eq_true] at bodyChecked replaced
  simp only [check, checkJudgment, StructuralTypingReplay.check, piDomain, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨inputs.1, ⟨⟨⟨⟨inputs.2.1.1.1.1, inputs.2.1.1.1.2⟩, inputs.2.1.1.2⟩,
    replaced.2⟩, bodyChecked.2⟩⟩

def sigmaDomain {n : Nat} (next : Tower.Tm n) (body : Tower.Tm (n + 1)) (u v : Tower.Head)
    (oldFormation newFormation : Code n) (bodyCode : Code (n + 1))
    (forward : NativeRelatorConversionChecking.Code n) : Code n :=
  .sigmaForm u v newFormation (convertNewest next u oldFormation forward body (.head v) bodyCode)

theorem sigmaDomain_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm n} {body : Tower.Tm (n + 1)} {u v w : Tower.Head}
    {oldFormation newFormation : Code n} {bodyCode : Code (n + 1)}
    {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check context (.sigma old body) (.head w) contextCode
      (.sigmaForm u v oldFormation bodyCode) = true)
    (replaced : check context next (.head u) contextCode newFormation = true)
    (converted : NativeRelatorConversionChecking.check forward old next = true) :
    check context (.sigma next body) (.head w) contextCode
      (sigmaDomain next body u v oldFormation newFormation bodyCode forward) = true := by
  have piAccepted : check context (.pi old body) (.head w) contextCode
      (.piForm u v oldFormation bodyCode) = true := accepted
  exact piDomain_checked piAccepted replaced converted

#print axioms restoreResult_checked
#print axioms appArgument_checked
#print axioms sndArgument_checked
#print axioms reflArgument_checked
#print axioms pairFirst_checked
#print axioms identityType_checked
#print axioms piDomain_checked
#print axioms sigmaDomain_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DependentCongruence
