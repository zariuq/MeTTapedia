import Mettapedia.Languages.PartrecMachine.HistoryEquations
import Mettapedia.Languages.PartrecMachine.Adequacy
import Mettapedia.GSLT.LanguageDef.TypingInversion
import Mettapedia.GSLT.LanguageDef.EquationInvariant

/-!
# The closed histories of the history machine

The interacting fibre of the history theory consists of the closed,
well-sorted patterns of sort `Hist`.  This module describes that fibre
exactly.

* Every encoded number, list, code, continuation and configuration of the
  machine is a closed term of its sort in the history language, and contains
  no history constructor.
* A history term is one of the six history constructors applied to encoded
  configurations and history terms (`HistTerm`).  Every history term is a
  closed term of sort `Hist`.
* Conversely, every closed object term of a machine sort is an encoding, and
  every closed object term of sort `Hist` is a history term
  (`canonical_forms`).  The typing judgment admits nothing else.

The converse is what lets a statement about arbitrary members of the fibre be
proved by induction on history terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Turing.ToPartrec

/-! ## Inverting argument lists

These facts hold in every language.  They read the arguments of a
constructor whose parameters are plain operands of base sorts. -/

/-- No argument is typed by an empty parameter list. -/
theorem arguments_nil_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    (typed : ArgumentsHaveTypes language free bound arguments []) : arguments = [] := by
  cases typed
  rfl

/-- One plain parameter types exactly one argument. -/
theorem arguments_one_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {name sort : String}
    (typed : ArgumentsHaveTypes language free bound arguments
      [.simple name (.base sort)]) :
    ∃ first, arguments = [first] ∧ HasSort language free bound first sort := by
  match arguments, typed with
  | first :: rest, typed =>
      obtain ⟨firstTyped, restTyped⟩ := typed.simple_cons_inv
      obtain rfl := arguments_nil_inv restTyped
      exact ⟨first, rfl, firstTyped⟩

/-- Two plain parameters type exactly two arguments. -/
theorem arguments_two_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {firstName firstSort secondName secondSort : String}
    (typed : ArgumentsHaveTypes language free bound arguments
      [.simple firstName (.base firstSort), .simple secondName (.base secondSort)]) :
    ∃ first second, arguments = [first, second] ∧
      HasSort language free bound first firstSort ∧
        HasSort language free bound second secondSort := by
  match arguments, typed with
  | first :: rest, typed =>
      obtain ⟨firstTyped, restTyped⟩ := typed.simple_cons_inv
      obtain ⟨second, rfl, secondTyped⟩ := arguments_one_inv restTyped
      exact ⟨first, second, rfl, firstTyped, secondTyped⟩

/-- Three plain parameters type exactly three arguments. -/
theorem arguments_three_inv {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {firstName firstSort secondName secondSort thirdName thirdSort : String}
    (typed : ArgumentsHaveTypes language free bound arguments
      [.simple firstName (.base firstSort), .simple secondName (.base secondSort),
        .simple thirdName (.base thirdSort)]) :
    ∃ first second third, arguments = [first, second, third] ∧
      HasSort language free bound first firstSort ∧
        HasSort language free bound second secondSort ∧
          HasSort language free bound third thirdSort := by
  match arguments, typed with
  | first :: rest, typed =>
      obtain ⟨firstTyped, restTyped⟩ := typed.simple_cons_inv
      obtain ⟨second, third, rfl, secondTyped, thirdTyped⟩ := arguments_two_inv restTyped
      exact ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩

/-! ## The signature has plain parameters only -/

/-- Every parameter of the constructor is a plain operand of a base sort. -/
def plainParameters (rule : GrammarRule) : Bool :=
  rule.params.all fun parameter =>
    match parameter with
    | .simple _ (.base _) => true
    | _ => false

theorem historyTerms_plainParameters : historyTerms.all plainParameters = true := by
  decide +kernel

/-- No constructor of the history language is represented by a bare
collection. -/
theorem historyTerms_notBare {rule : GrammarRule} (membership : rule ∈ historyTerms) :
    ¬ UsesBareCollection rule := by
  rintro ⟨name, collectionType, elementType, parameters⟩
  have plain := List.all_eq_true.mp historyTerms_plainParameters rule membership
  simp [plainParameters, parameters] at plain

/-- Typing an application of the constructor at a given position of the
signature. -/
theorem hasType_constructor (index : Nat) (inBounds : index < historyTerms.length)
    {arguments : List Pattern}
    (typed : ArgumentsHaveTypes historyMachine FreeTypeContext.empty [] arguments
      (historyTerms[index]).params) :
    HasType historyMachine FreeTypeContext.empty []
      (.apply (historyTerms[index]).label arguments)
      (.base (historyTerms[index]).category) :=
  HasType.constructor (List.getElem_mem inBounds)
    (historyTerms_notBare (List.getElem_mem inBounds)) typed

/-! ## Encoded machine terms -/

/-- The weight that counts history constructors. -/
def histWeight (label : String) : Nat :=
  if label = "Now" ∨ label = "Then" ∨ label = "Flag" ∨ label = "Meet" ∨ label = "Wait" ∨
      label = "Give" then 1 else 0

/-- A closed first-order term of a machine sort: typed in the history
language, an object pattern with canonical binder metadata, and free of
history constructors. -/
def MachineTerm (sort : String) (pattern : Pattern) : Prop :=
  HasSort historyMachine FreeTypeContext.empty [] pattern sort ∧
    isObjectPattern pattern = true ∧
      pattern.hasCanonicalBinderMetadata = true ∧
        pattern.weigh histWeight = 0

theorem encNat_machineTerm : ∀ value : ℕ, MachineTerm "Nat" (encNat value)
  | 0 => ⟨hasType_constructor 0 (by decide) .nil, by decide, by decide, by decide⟩
  | value + 1 => by
      obtain ⟨typed, object, canonical, weightless⟩ := encNat_machineTerm value
      refine ⟨hasType_constructor 1 (by decide) (.cons trivial rfl typed .nil), ?_, ?_, ?_⟩
      · simpa [encNat, isObjectPattern, isObjectPatternList] using object
      · simpa [encNat, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical
      · simp [encNat, Pattern.weigh, Pattern.weighList, histWeight, weightless]

theorem encNats_machineTerm : ∀ values : List ℕ, MachineTerm "Nats" (encNats values)
  | [] => ⟨hasType_constructor 2 (by decide) .nil, by decide, by decide, by decide⟩
  | head :: tail => by
      obtain ⟨headTyped, headObject, headCanonical, headWeightless⟩ := encNat_machineTerm head
      obtain ⟨tailTyped, tailObject, tailCanonical, tailWeightless⟩ := encNats_machineTerm tail
      refine ⟨hasType_constructor 3 (by decide)
        (.cons trivial rfl headTyped (.cons trivial rfl tailTyped .nil)), ?_, ?_, ?_⟩
      · simp [encNats, isObjectPattern, isObjectPatternList, headObject, tailObject]
      · simp [encNats, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, headCanonical, tailCanonical]
      · simp [encNats, Pattern.weigh, Pattern.weighList, histWeight, headWeightless,
          tailWeightless]

theorem encCode_machineTerm : ∀ code : Code, MachineTerm "Code" (encCode code)
  | .zero' => ⟨hasType_constructor 4 (by decide) .nil, by decide, by decide, by decide⟩
  | .succ => ⟨hasType_constructor 5 (by decide) .nil, by decide, by decide, by decide⟩
  | .tail => ⟨hasType_constructor 6 (by decide) .nil, by decide, by decide, by decide⟩
  | .cons first rest => by
      obtain ⟨firstTyped, firstObject, firstCanonical, firstWeightless⟩ :=
        encCode_machineTerm first
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ := encCode_machineTerm rest
      refine ⟨hasType_constructor 7 (by decide)
        (.cons trivial rfl firstTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCode, isObjectPattern, isObjectPatternList, firstObject, restObject]
      · simp [encCode, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, firstCanonical, restCanonical]
      · simp [encCode, Pattern.weigh, Pattern.weighList, histWeight, firstWeightless,
          restWeightless]
  | .comp first rest => by
      obtain ⟨firstTyped, firstObject, firstCanonical, firstWeightless⟩ :=
        encCode_machineTerm first
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ := encCode_machineTerm rest
      refine ⟨hasType_constructor 8 (by decide)
        (.cons trivial rfl firstTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCode, isObjectPattern, isObjectPatternList, firstObject, restObject]
      · simp [encCode, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, firstCanonical, restCanonical]
      · simp [encCode, Pattern.weigh, Pattern.weighList, histWeight, firstWeightless,
          restWeightless]
  | .case first rest => by
      obtain ⟨firstTyped, firstObject, firstCanonical, firstWeightless⟩ :=
        encCode_machineTerm first
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ := encCode_machineTerm rest
      refine ⟨hasType_constructor 9 (by decide)
        (.cons trivial rfl firstTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCode, isObjectPattern, isObjectPatternList, firstObject, restObject]
      · simp [encCode, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, firstCanonical, restCanonical]
      · simp [encCode, Pattern.weigh, Pattern.weighList, histWeight, firstWeightless,
          restWeightless]
  | .fix body => by
      obtain ⟨typed, object, canonical, weightless⟩ := encCode_machineTerm body
      refine ⟨hasType_constructor 10 (by decide) (.cons trivial rfl typed .nil), ?_, ?_, ?_⟩
      · simpa [encCode, isObjectPattern, isObjectPatternList] using object
      · simpa [encCode, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical
      · simp [encCode, Pattern.weigh, Pattern.weighList, histWeight, weightless]

theorem encCont_machineTerm : ∀ continuation : Cont, MachineTerm "Cont" (encCont continuation)
  | .halt => ⟨hasType_constructor 11 (by decide) .nil, by decide, by decide, by decide⟩
  | .cons₁ code values continuation => by
      obtain ⟨codeTyped, codeObject, codeCanonical, codeWeightless⟩ := encCode_machineTerm code
      obtain ⟨valuesTyped, valuesObject, valuesCanonical, valuesWeightless⟩ :=
        encNats_machineTerm values
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
        encCont_machineTerm continuation
      refine ⟨hasType_constructor 12 (by decide)
        (.cons trivial rfl codeTyped (.cons trivial rfl valuesTyped
          (.cons trivial rfl restTyped .nil))), ?_, ?_, ?_⟩
      · simp [encCont, isObjectPattern, isObjectPatternList, codeObject, valuesObject,
          restObject]
      · simp [encCont, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, codeCanonical, valuesCanonical,
          restCanonical]
      · simp [encCont, Pattern.weigh, Pattern.weighList, histWeight, codeWeightless,
          valuesWeightless, restWeightless]
  | .cons₂ values continuation => by
      obtain ⟨valuesTyped, valuesObject, valuesCanonical, valuesWeightless⟩ :=
        encNats_machineTerm values
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
        encCont_machineTerm continuation
      refine ⟨hasType_constructor 13 (by decide)
        (.cons trivial rfl valuesTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCont, isObjectPattern, isObjectPatternList, valuesObject, restObject]
      · simp [encCont, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, valuesCanonical, restCanonical]
      · simp [encCont, Pattern.weigh, Pattern.weighList, histWeight, valuesWeightless,
          restWeightless]
  | .comp code continuation => by
      obtain ⟨codeTyped, codeObject, codeCanonical, codeWeightless⟩ := encCode_machineTerm code
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
        encCont_machineTerm continuation
      refine ⟨hasType_constructor 14 (by decide)
        (.cons trivial rfl codeTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCont, isObjectPattern, isObjectPatternList, codeObject, restObject]
      · simp [encCont, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, codeCanonical, restCanonical]
      · simp [encCont, Pattern.weigh, Pattern.weighList, histWeight, codeWeightless,
          restWeightless]
  | .fix code continuation => by
      obtain ⟨codeTyped, codeObject, codeCanonical, codeWeightless⟩ := encCode_machineTerm code
      obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
        encCont_machineTerm continuation
      refine ⟨hasType_constructor 15 (by decide)
        (.cons trivial rfl codeTyped (.cons trivial rfl restTyped .nil)), ?_, ?_, ?_⟩
      · simp [encCont, isObjectPattern, isObjectPatternList, codeObject, restObject]
      · simp [encCont, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, codeCanonical, restCanonical]
      · simp [encCont, Pattern.weigh, Pattern.weighList, histWeight, codeWeightless,
          restWeightless]

/-- Every encoded configuration and pending evaluation is a closed
configuration of the history language. -/
theorem inImage_machineTerm {configuration : Pattern} (image : InImage configuration) :
    MachineTerm "Cfg" configuration := by
  rcases image with ⟨code, continuation, values, rfl⟩ | ⟨cfg, rfl⟩
  · obtain ⟨codeTyped, codeObject, codeCanonical, codeWeightless⟩ := encCode_machineTerm code
    obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
      encCont_machineTerm continuation
    obtain ⟨valuesTyped, valuesObject, valuesCanonical, valuesWeightless⟩ :=
      encNats_machineTerm values
    refine ⟨hasType_constructor 18 (by decide)
      (.cons trivial rfl codeTyped (.cons trivial rfl restTyped
        (.cons trivial rfl valuesTyped .nil))), ?_, ?_, ?_⟩
    · simp [normalTerm, isObjectPattern, isObjectPatternList, codeObject, restObject,
        valuesObject]
    · simp [normalTerm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, codeCanonical, restCanonical,
        valuesCanonical]
    · simp [normalTerm, Pattern.weigh, Pattern.weighList, histWeight, codeWeightless,
        restWeightless, valuesWeightless]
  · cases cfg with
    | halt values =>
        obtain ⟨valuesTyped, valuesObject, valuesCanonical, valuesWeightless⟩ :=
          encNats_machineTerm values
        refine ⟨hasType_constructor 16 (by decide) (.cons trivial rfl valuesTyped .nil),
          ?_, ?_, ?_⟩
        · simpa [encCfg, isObjectPattern, isObjectPatternList] using valuesObject
        · simpa [encCfg, Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList] using valuesCanonical
        · simp [encCfg, Pattern.weigh, Pattern.weighList, histWeight, valuesWeightless]
    | ret continuation values =>
        obtain ⟨restTyped, restObject, restCanonical, restWeightless⟩ :=
          encCont_machineTerm continuation
        obtain ⟨valuesTyped, valuesObject, valuesCanonical, valuesWeightless⟩ :=
          encNats_machineTerm values
        refine ⟨hasType_constructor 17 (by decide)
          (.cons trivial rfl restTyped (.cons trivial rfl valuesTyped .nil)), ?_, ?_, ?_⟩
        · simp [encCfg, isObjectPattern, isObjectPatternList, restObject, valuesObject]
        · simp [encCfg, Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList, restCanonical, valuesCanonical]
        · simp [encCfg, Pattern.weigh, Pattern.weighList, histWeight, restWeightless,
            valuesWeightless]

/-- An encoded configuration is ground. -/
theorem inImage_isGround {configuration : Pattern} (image : InImage configuration) :
    configuration.isGround = true := by
  obtain ⟨typed, object, -, -⟩ := inImage_machineTerm image
  exact typed.empty_isGroundAt object typed.isWellScopedAt

/-! ## History terms -/

/-- The history terms: histories built from encoded configurations. -/
inductive HistTerm : Pattern → Prop where
  | ofNow {configuration : Pattern} :
      InImage configuration → HistTerm (now configuration)
  | ofThen {configuration history : Pattern} :
      InImage configuration → HistTerm history → HistTerm (andThen configuration history)
  | ofFlag {configuration : Pattern} :
      InImage configuration → HistTerm (flag configuration)
  | ofMeet {left right : Pattern} :
      HistTerm left → HistTerm right → HistTerm (meet left right)
  | ofWait {history : Pattern} : HistTerm history → HistTerm (wait history)
  | ofGive {history : Pattern} : HistTerm history → HistTerm (give history)

/-- A history term is one of the six history constructors applied to encoded
configurations and history terms. -/
theorem HistTerm.apply_inv {label : String} {arguments : List Pattern}
    (term : HistTerm (.apply label arguments)) :
    (label = "Now" ∧ ∃ configuration, arguments = [configuration] ∧ InImage configuration) ∨
      (label = "Then" ∧ ∃ configuration history,
        arguments = [configuration, history] ∧ InImage configuration ∧ HistTerm history) ∨
      (label = "Flag" ∧ ∃ configuration, arguments = [configuration] ∧ InImage configuration) ∨
      (label = "Meet" ∧ ∃ left right,
        arguments = [left, right] ∧ HistTerm left ∧ HistTerm right) ∨
      (label = "Wait" ∧ ∃ history, arguments = [history] ∧ HistTerm history) ∨
      (label = "Give" ∧ ∃ history, arguments = [history] ∧ HistTerm history) := by
  generalize shape : Pattern.apply label arguments = pattern at term
  cases term with
  | ofNow image =>
      simp only [now, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inl ⟨rfl, _, rfl, image⟩
  | ofThen image history =>
      simp only [andThen, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inr (.inl ⟨rfl, _, _, rfl, image, history⟩)
  | ofFlag image =>
      simp only [flag, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inr (.inr (.inl ⟨rfl, _, rfl, image⟩))
  | ofMeet left right =>
      simp only [meet, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inr (.inr (.inr (.inl ⟨rfl, _, _, rfl, left, right⟩)))
  | ofWait history =>
      simp only [wait, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inr (.inr (.inr (.inr (.inl ⟨rfl, _, rfl, history⟩))))
  | ofGive history =>
      simp only [give, Pattern.apply.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact .inr (.inr (.inr (.inr (.inr ⟨rfl, _, rfl, history⟩))))

/-- A history term is a constructor application. -/
theorem HistTerm.exists_apply {pattern : Pattern} (term : HistTerm pattern) :
    ∃ label arguments, pattern = .apply label arguments := by
  cases term with
  | ofNow _ => exact ⟨_, _, rfl⟩
  | ofThen _ _ => exact ⟨_, _, rfl⟩
  | ofFlag _ => exact ⟨_, _, rfl⟩
  | ofMeet _ _ => exact ⟨_, _, rfl⟩
  | ofWait _ => exact ⟨_, _, rfl⟩
  | ofGive _ => exact ⟨_, _, rfl⟩

/-- The configuration under `Now` in a history term is encoded. -/
theorem HistTerm.now_inv {configuration : Pattern} (term : HistTerm (now configuration)) :
    InImage configuration := by
  rcases HistTerm.apply_inv term with ⟨-, _, same, image⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ |
    ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩
  · obtain rfl : configuration = _ := by simpa using same
    exact image
  all_goals exact absurd wrong (by decide)

/-- The parts of a `Then` history term. -/
theorem HistTerm.andThen_inv {configuration history : Pattern}
    (term : HistTerm (andThen configuration history)) :
    InImage configuration ∧ HistTerm history := by
  rcases HistTerm.apply_inv term with ⟨wrong, -⟩ | ⟨-, _, _, same, image, rest⟩ | ⟨wrong, -⟩ |
    ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩
  · exact absurd wrong (by decide)
  · simp only [List.cons.injEq, and_true] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨image, rest⟩
  all_goals exact absurd wrong (by decide)

/-- The parts of a `Meet` history term. -/
theorem HistTerm.meet_inv {left right : Pattern} (term : HistTerm (meet left right)) :
    HistTerm left ∧ HistTerm right := by
  rcases HistTerm.apply_inv term with ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ |
    ⟨-, _, _, same, first, second⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · simp only [List.cons.injEq, and_true] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨first, second⟩
  all_goals exact absurd wrong (by decide)

/-- The body of a `Wait` history term. -/
theorem HistTerm.wait_inv {history : Pattern} (term : HistTerm (wait history)) :
    HistTerm history := by
  rcases HistTerm.apply_inv term with ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ |
    ⟨-, _, same, body⟩ | ⟨wrong, -⟩
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · obtain rfl : history = _ := by simpa using same
    exact body
  · exact absurd wrong (by decide)

/-- The body of a `Give` history term. -/
theorem HistTerm.give_inv {history : Pattern} (term : HistTerm (give history)) :
    HistTerm history := by
  rcases HistTerm.apply_inv term with ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ | ⟨wrong, -⟩ |
    ⟨wrong, -⟩ | ⟨-, _, same, body⟩
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · exact absurd wrong (by decide)
  · obtain rfl : history = _ := by simpa using same
    exact body

/-- A history term is typed at `Hist`, and is an object pattern with canonical
binder metadata. -/
theorem HistTerm.typed {pattern : Pattern} (term : HistTerm pattern) :
    HasSort historyMachine FreeTypeContext.empty [] pattern "Hist" ∧
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
  induction term with
  | ofNow image =>
      obtain ⟨typed, object, canonical, -⟩ := inImage_machineTerm image
      refine ⟨hasType_constructor 19 (by decide) (.cons trivial rfl typed .nil), ?_, ?_⟩
      · simpa [now, isObjectPattern, isObjectPatternList] using object
      · simpa [now, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical
  | ofThen image _ recurse =>
      obtain ⟨typed, object, canonical, -⟩ := inImage_machineTerm image
      obtain ⟨historyTyped, historyObject, historyCanonical⟩ := recurse
      refine ⟨hasType_constructor 20 (by decide)
        (.cons trivial rfl typed (.cons trivial rfl historyTyped .nil)), ?_, ?_⟩
      · simp [andThen, isObjectPattern, isObjectPatternList, object, historyObject]
      · simp [andThen, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, canonical, historyCanonical]
  | ofFlag image =>
      obtain ⟨typed, object, canonical, -⟩ := inImage_machineTerm image
      refine ⟨hasType_constructor 21 (by decide) (.cons trivial rfl typed .nil), ?_, ?_⟩
      · simpa [flag, isObjectPattern, isObjectPatternList] using object
      · simpa [flag, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical
  | ofMeet _ _ leftRecurse rightRecurse =>
      obtain ⟨leftTyped, leftObject, leftCanonical⟩ := leftRecurse
      obtain ⟨rightTyped, rightObject, rightCanonical⟩ := rightRecurse
      refine ⟨hasType_constructor 22 (by decide)
        (.cons trivial rfl leftTyped (.cons trivial rfl rightTyped .nil)), ?_, ?_⟩
      · simp [meet, isObjectPattern, isObjectPatternList, leftObject, rightObject]
      · simp [meet, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, leftCanonical, rightCanonical]
  | ofWait _ recurse =>
      obtain ⟨typed, object, canonical⟩ := recurse
      refine ⟨hasType_constructor 23 (by decide) (.cons trivial rfl typed .nil), ?_, ?_⟩
      · simpa [wait, isObjectPattern, isObjectPatternList] using object
      · simpa [wait, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical
  | ofGive _ recurse =>
      obtain ⟨typed, object, canonical⟩ := recurse
      refine ⟨hasType_constructor 24 (by decide) (.cons trivial rfl typed .nil), ?_, ?_⟩
      · simpa [give, isObjectPattern, isObjectPatternList] using object
      · simpa [give, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using canonical

/-- **Every history term is a member of the interacting fibre.** -/
theorem HistTerm.closed {pattern : Pattern} (term : HistTerm pattern) :
    ClosedTermWellSorted historyMachine historyPresentation.interactingLangSort pattern := by
  obtain ⟨typed, object, canonical⟩ := term.typed
  exact ⟨typed, typed.empty_isGroundAt object typed.isWellScopedAt, canonical, object,
    typed.isWellScopedAt⟩

/-! ## Canonical forms -/

/-- What a closed object term of each sort must be. -/
def Canon (sort : String) (pattern : Pattern) : Prop :=
  (sort = "Nat" → ∃ value : ℕ, pattern = encNat value) ∧
    (sort = "Nats" → ∃ values : List ℕ, pattern = encNats values) ∧
    (sort = "Code" → ∃ code : Code, pattern = encCode code) ∧
    (sort = "Cont" → ∃ continuation : Cont, pattern = encCont continuation) ∧
    (sort = "Cfg" → InImage pattern) ∧
    (sort = "Hist" → HistTerm pattern)

/-- Close a canonical-form goal whose sort is a literal: one conjunct is the
stated fact, the other five have a false hypothesis. -/
local macro "canon_close" main:ident : tactic =>
  `(tactic|
    (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro sortEq <;>
      first
        | exact $main
        | exact absurd sortEq (by decide)))

/-- **Canonical forms.**  A closed object term typed at a sort of the history
language is an encoding of that sort: a number, a list, a code, a
continuation, a configuration or pending evaluation, or a history term. -/
theorem canonical_forms (pattern : Pattern) :
    isObjectPattern pattern = true →
      ∀ sort, HasSort historyMachine FreeTypeContext.empty [] pattern sort →
        Canon sort pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ sort typed
      cases typed with
      | bvar lookup => simp at lookup
  | hfvar name =>
      intro _ sort typed
      cases typed with
      | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | hlambda binderName body _ =>
      intro _ sort typed
      cases typed
  | hmultiLambda arity binderNames body _ =>
      intro _ sort typed
      cases typed
  | hsubst body replacement _ _ =>
      intro object
      simp [isObjectPattern] at object
  | hcollection collectionType elements rest _ =>
      intro _ sort typed
      cases typed with
      | collectionConstructor membership parameters _ =>
          exact absurd ⟨_, _, _, parameters⟩ (historyTerms_notBare membership)
  | happly label arguments recurse =>
      intro object sort typed
      obtain ⟨rule, membership, ruleLabel, typeEq, -, argumentsTyped⟩ := typed.apply_inv
      simp only [TypeExpr.base.injEq] at typeEq
      subst typeEq ruleLabel
      simp only [isObjectPattern] at object
      change rule ∈ historyTerms at membership
      simp only [historyTerms, terms, historyConstructors, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- Zero
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ value : ℕ, Pattern.apply "Zero" [] = encNat value := ⟨0, rfl⟩
        canon_close main
      · -- Succ
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        obtain ⟨value, rfl⟩ :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).1 rfl
        have main : ∃ next : ℕ, Pattern.apply "Succ" [encNat value] = encNat next :=
          ⟨value + 1, rfl⟩
        canon_close main
      · -- Nil
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ values : List ℕ, Pattern.apply "Nil" [] = encNats values := ⟨[], rfl⟩
        canon_close main
      · -- Cons
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨head, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).1 rfl
        obtain ⟨tail, rfl⟩ := (recurse second (by simp) object.2 _ secondTyped).2.1 rfl
        have main : ∃ values : List ℕ,
            Pattern.apply "Cons" [encNat head, encNats tail] = encNats values :=
          ⟨head :: tail, rfl⟩
        canon_close main
      · -- ZeroCode
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ code : Code, Pattern.apply "ZeroCode" [] = encCode code := ⟨.zero', rfl⟩
        canon_close main
      · -- SuccCode
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ code : Code, Pattern.apply "SuccCode" [] = encCode code := ⟨.succ, rfl⟩
        canon_close main
      · -- TailCode
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ code : Code, Pattern.apply "TailCode" [] = encCode code := ⟨.tail, rfl⟩
        canon_close main
      · -- ConsCode
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨firstCode, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨secondCode, rfl⟩ :=
          (recurse second (by simp) object.2 _ secondTyped).2.2.1 rfl
        have main : ∃ code : Code,
            Pattern.apply "ConsCode" [encCode firstCode, encCode secondCode] = encCode code :=
          ⟨.cons firstCode secondCode, rfl⟩
        canon_close main
      · -- CompCode
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨firstCode, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨secondCode, rfl⟩ :=
          (recurse second (by simp) object.2 _ secondTyped).2.2.1 rfl
        have main : ∃ code : Code,
            Pattern.apply "CompCode" [encCode firstCode, encCode secondCode] = encCode code :=
          ⟨.comp firstCode secondCode, rfl⟩
        canon_close main
      · -- CaseCode
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨firstCode, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨secondCode, rfl⟩ :=
          (recurse second (by simp) object.2 _ secondTyped).2.2.1 rfl
        have main : ∃ code : Code,
            Pattern.apply "CaseCode" [encCode firstCode, encCode secondCode] = encCode code :=
          ⟨.case firstCode secondCode, rfl⟩
        canon_close main
      · -- FixCode
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        obtain ⟨body, rfl⟩ :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.2.1 rfl
        have main : ∃ code : Code, Pattern.apply "FixCode" [encCode body] = encCode code :=
          ⟨.fix body, rfl⟩
        canon_close main
      · -- HaltCont
        obtain rfl := arguments_nil_inv argumentsTyped
        have main : ∃ continuation : Cont,
            Pattern.apply "HaltCont" [] = encCont continuation := ⟨.halt, rfl⟩
        canon_close main
      · -- Cons1Cont
        obtain ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩ :=
          arguments_three_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨code, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨values, rfl⟩ := (recurse second (by simp) object.2.1 _ secondTyped).2.1 rfl
        obtain ⟨rest, rfl⟩ := (recurse third (by simp) object.2.2 _ thirdTyped).2.2.2.1 rfl
        have main : ∃ continuation : Cont,
            Pattern.apply "Cons1Cont" [encCode code, encNats values, encCont rest] =
              encCont continuation :=
          ⟨.cons₁ code values rest, rfl⟩
        canon_close main
      · -- Cons2Cont
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨values, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.1 rfl
        obtain ⟨rest, rfl⟩ := (recurse second (by simp) object.2 _ secondTyped).2.2.2.1 rfl
        have main : ∃ continuation : Cont,
            Pattern.apply "Cons2Cont" [encNats values, encCont rest] = encCont continuation :=
          ⟨.cons₂ values rest, rfl⟩
        canon_close main
      · -- CompCont
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨code, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨rest, rfl⟩ := (recurse second (by simp) object.2 _ secondTyped).2.2.2.1 rfl
        have main : ∃ continuation : Cont,
            Pattern.apply "CompCont" [encCode code, encCont rest] = encCont continuation :=
          ⟨.comp code rest, rfl⟩
        canon_close main
      · -- FixCont
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨code, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨rest, rfl⟩ := (recurse second (by simp) object.2 _ secondTyped).2.2.2.1 rfl
        have main : ∃ continuation : Cont,
            Pattern.apply "FixCont" [encCode code, encCont rest] = encCont continuation :=
          ⟨.fix code rest, rfl⟩
        canon_close main
      · -- Halt
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        obtain ⟨values, rfl⟩ :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.1 rfl
        have main : InImage (Pattern.apply "Halt" [encNats values]) :=
          .inr ⟨.halt values, rfl⟩
        canon_close main
      · -- Ret
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨rest, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.2.1 rfl
        obtain ⟨values, rfl⟩ := (recurse second (by simp) object.2 _ secondTyped).2.1 rfl
        have main : InImage (Pattern.apply "Ret" [encCont rest, encNats values]) :=
          .inr ⟨.ret rest values, rfl⟩
        canon_close main
      · -- Normal
        obtain ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩ :=
          arguments_three_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        obtain ⟨code, rfl⟩ := (recurse first (by simp) object.1 _ firstTyped).2.2.1 rfl
        obtain ⟨rest, rfl⟩ := (recurse second (by simp) object.2.1 _ secondTyped).2.2.2.1 rfl
        obtain ⟨values, rfl⟩ := (recurse third (by simp) object.2.2 _ thirdTyped).2.1 rfl
        have main : InImage
            (Pattern.apply "Normal" [encCode code, encCont rest, encNats values]) :=
          .inl ⟨code, rest, values, rfl⟩
        canon_close main
      · -- Now
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        have image :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.2.2.2.1 rfl
        have main : HistTerm (Pattern.apply "Now" [first]) := HistTerm.ofNow image
        canon_close main
      · -- Then
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        have image := (recurse first (by simp) object.1 _ firstTyped).2.2.2.2.1 rfl
        have history := (recurse second (by simp) object.2 _ secondTyped).2.2.2.2.2 rfl
        have main : HistTerm (Pattern.apply "Then" [first, second]) :=
          HistTerm.ofThen image history
        canon_close main
      · -- Flag
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        have image :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.2.2.2.1 rfl
        have main : HistTerm (Pattern.apply "Flag" [first]) := HistTerm.ofFlag image
        canon_close main
      · -- Meet
        obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ :=
          arguments_two_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
        have left := (recurse first (by simp) object.1 _ firstTyped).2.2.2.2.2 rfl
        have right := (recurse second (by simp) object.2 _ secondTyped).2.2.2.2.2 rfl
        have main : HistTerm (Pattern.apply "Meet" [first, second]) := HistTerm.ofMeet left right
        canon_close main
      · -- Wait
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        have body :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.2.2.2.2 rfl
        have main : HistTerm (Pattern.apply "Wait" [first]) := HistTerm.ofWait body
        canon_close main
      · -- Give
        obtain ⟨first, rfl, firstTyped⟩ := arguments_one_inv argumentsTyped
        simp only [isObjectPatternList, Bool.and_true] at object
        have body :=
          (recurse first (List.mem_singleton.mpr rfl) object _ firstTyped).2.2.2.2.2 rfl
        have main : HistTerm (Pattern.apply "Give" [first]) := HistTerm.ofGive body
        canon_close main

/-- **Every member of the interacting fibre is a history term.** -/
theorem histTerm_of_closed {pattern : Pattern}
    (closed : ClosedTermWellSorted historyMachine historyPresentation.interactingLangSort
      pattern) : HistTerm pattern :=
  (canonical_forms pattern closed.2.2.2.1 _ closed.1).2.2.2.2.2 rfl

/-- A closed object term typed at `Hist` is a history term. -/
theorem histTerm_of_typed {pattern : Pattern}
    (typed : HasSort historyMachine FreeTypeContext.empty [] pattern "Hist")
    (object : isObjectPattern pattern = true) : HistTerm pattern :=
  (canonical_forms pattern object _ typed).2.2.2.2.2 rfl

/-- A term that does not encode a number is not typed at `Nat`: the
canonical-form statement excludes it. -/
theorem nil_not_typed_at_nat :
    ¬ HasSort historyMachine FreeTypeContext.empty [] (encNats []) "Nat" := by
  intro typed
  obtain ⟨value, same⟩ := (canonical_forms _ (by decide) _ typed).1 rfl
  cases value <;> simp [encNats, encNat] at same

end Mettapedia.Languages.PartrecMachine
