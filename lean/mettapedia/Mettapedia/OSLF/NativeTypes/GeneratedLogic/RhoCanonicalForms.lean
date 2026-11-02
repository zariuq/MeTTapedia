import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations
import Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical

/-!
# ρ through canonical forms, in its own reading

ρ is read with its equations as the typed judgment between closed terms of a sort that keep its scope policy (a
quotation seals what it quotes), and its rules through its reflection profile: matching modulo canonical names and
semantic substitution (`reading`). In this reading:

- **The admitted processes are ρ's closed carrier** (`domain`, `admitted_iff`): closed processes, sealed. The
  carrier is closed under the equivalence, since a step of the typed judgment between terms of one sort keeps the
  sort, which a process determines (`invariant`), and under ρ's steps (`stepsAdmitted`).
- **Canonicalization gives canonical forms on the carrier** (`canonical`): every admitted process is equivalent to its
  canonical form through sealed processes, and equivalent terms have one canonical form.
- **The forms are coherent for plain steps at fuel one** (`coherentPlain`): a step from any process equivalent to a
  canonical one is matched, up to canonical form, by a communication at the top of the canonical bag. This is the
  completeness of ρ's canonical stepper.

So the front door decides ρ's behavioural formulas over closed canonical regions (`forms`), and its verdicts are
about ρ's own semantics. The forms compute canonical forms with an insertion sort of bag elements
(`canonicalizeSorted`), equal to ρ's canonicalization (`canonicalizeSorted_eq`), so that the kernel can evaluate the
front door's verdicts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt isWellScopedAt_of_binderSafeAt)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (ProcWellSorted FreeSortContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
  (canonicalize_proc_hasSort canonicalize_name_hasSort canonicalize_isObjectPattern)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (RhoStep RhoStepAt rhoRuleInterpretation rhoBasePremises rhoStep_preserves_closed rhoComm_match_shape
    rhoParCong_match_shape)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

/-! ## ρ's reading -/

/-- **ρ's reading**: its equations as the typed judgment between closed terms of an element type (a sort, or the type
of a constructor's parameter) that keep its scope policy; its rules through its reflection profile. -/
def reading : LanguageReading where
  equations := .typed .raw rhoReflectionProfile .elements none
  rules := .interpreted rhoRuleInterpretation rhoBasePremises

/-! ## ρ's elements -/

/-- **The admitted processes**: ρ's closed carrier. -/
abbrev process : Pattern → Bool := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit

/-- **The admitted names**: closed names, sealed. -/
def name (term : Pattern) : Bool :=
  checkOpenPatternWellSorted rhoCalc FreeTypeContext.empty [] TypeExpr.name term && binderSafeAt "NQuote" 0 term

/-- **The admitted continuations**: abstractions of a process over one name, sealed, with no binder name. -/
def continuation : Pattern → Bool
  | .lambda none body =>
    checkOpenPatternWellSorted rhoCalc FreeTypeContext.empty [TypeExpr.name] TypeExpr.proc body &&
      binderSafeAt "NQuote" 1 body
  | _ => false

/-- **ρ's admitted elements**: its closed processes, names and input continuations, sealed. -/
def domain (term : Pattern) : Bool :=
  process term || name term || continuation term

/-- **An admitted process** is a closed object of sort `Proc`, sealed. -/
theorem process_iff {term : Pattern} :
    process term = true ↔
      HasSort rhoCalc FreeTypeContext.empty [] term "Proc" ∧ isObjectPattern term = true ∧ Sealed 0 term := by
  simp only [process, Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit, Bool.and_eq_true,
    checkOpenPatternWellSorted_eq_true_iff, OpenPatternWellSorted]
  constructor
  · rintro ⟨⟨typed, -, object, -⟩, sealed⟩
    exact ⟨typed, object, sealed⟩
  · rintro ⟨typed, object, sealed⟩
    exact ⟨⟨typed, metadata_proc typed object, object, isWellScopedAt_of_binderSafeAt "NQuote" sealed⟩, sealed⟩

/-- **An admitted name** is a closed object of sort `Name`, sealed. -/
theorem name_iff {term : Pattern} :
    name term = true ↔
      HasSort rhoCalc FreeTypeContext.empty [] term "Name" ∧ isObjectPattern term = true ∧ Sealed 0 term := by
  simp only [name, Bool.and_eq_true, checkOpenPatternWellSorted_eq_true_iff, OpenPatternWellSorted]
  constructor
  · rintro ⟨⟨typed, -, object, -⟩, sealed⟩
    exact ⟨typed, object, sealed⟩
  · rintro ⟨typed, object, sealed⟩
    exact ⟨⟨typed, metadata_name typed object, object, isWellScopedAt_of_binderSafeAt "NQuote" sealed⟩, sealed⟩

/-- **An admitted continuation** abstracts a formed process over one name. -/
theorem continuation_lambda_iff {body : Pattern} :
    continuation (.lambda none body) = true ↔ Good FreeTypeContext.empty [TypeExpr.name] 1 body := by
  simp only [continuation, Bool.and_eq_true, checkOpenPatternWellSorted_eq_true_iff, OpenPatternWellSorted]
  constructor
  · rintro ⟨⟨typed, -, object, -⟩, sealed⟩
    exact ⟨object, typed, sealed⟩
  · rintro ⟨object, typed, sealed⟩
    exact ⟨⟨typed, metadata_proc typed object, object, isWellScopedAt_of_binderSafeAt "NQuote" sealed⟩, sealed⟩

theorem continuation_cases {term : Pattern} (admitted : continuation term = true) :
    ∃ body, term = .lambda none body ∧ Good FreeTypeContext.empty [TypeExpr.name] 1 body := by
  match term, admitted with
  | .lambda none body, admitted => exact ⟨body, rfl, continuation_lambda_iff.mp admitted⟩

/-- A lambda has no sort. -/
theorem not_hasSort_lambda {free : FreeTypeContext} {bound : List TypeExpr} {binder : Option String}
    {body : Pattern} {sort : String} : ¬ HasSort rhoCalc free bound (.lambda binder body) sort := by
  intro typed
  change HasType rhoCalc free bound (.lambda binder body) (.base sort) at typed
  generalize typeEquality : TypeExpr.base sort = type at typed
  generalize patternEquality : Pattern.lambda binder body = pattern at typed
  cases typed <;> first | (cases patternEquality; done) | cases typeEquality

/-- **A term formed at the type of input continuations abstracts a formed process over one name.** -/
theorem lambda_of_arrow {term : Pattern}
    (formed : Formed rhoCalc FreeTypeContext.empty [] (.arrow TypeExpr.name TypeExpr.proc) (Sealed 0) term) :
    ∃ binder body, term = .lambda binder body ∧ Good FreeTypeContext.empty [TypeExpr.name] 1 body := by
  obtain ⟨object, typed, sealed⟩ := formed
  generalize typeEquality : TypeExpr.arrow TypeExpr.name TypeExpr.proc = type at typed
  cases typed with
  | lambda bodyTyped =>
    cases typeEquality
    exact ⟨_, _, rfl, by simpa [isObjectPattern] using object, bodyTyped, by simpa [Sealed, binderSafeAt] using sealed⟩
  | bvar lookup => simp at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | subst => simp [isObjectPattern] at object
  | multiLambda => cases typeEquality
  | constructor => cases typeEquality
  | collection => cases typeEquality
  | collectionConstructor => cases typeEquality

/-- An admitted continuation is formed at the type of input continuations. -/
theorem formed_of_continuation {term : Pattern} (admitted : continuation term = true) :
    Formed rhoCalc FreeTypeContext.empty [] (.arrow TypeExpr.name TypeExpr.proc) (Sealed 0) term := by
  obtain ⟨body, rfl, good⟩ := continuation_cases admitted
  exact ⟨by simpa [isObjectPattern] using good.object, .lambda good.typed,
    by simpa [Sealed, binderSafeAt] using good.formed⟩

/-- **A collection of ρ with a sort is a process**: only the parallel constructor is a bare collection. -/
theorem collection_sort {free : FreeTypeContext} {bound : List TypeExpr} {kind : CollType} {elements : List Pattern}
    {rest : Option String} {sort : String} (typed : HasSort rhoCalc free bound (.collection kind elements rest) sort) :
    sort = "Proc" ∧ kind = .hashBag := by
  change HasType rhoCalc free bound (.collection kind elements rest) (.base sort) at typed
  generalize typeEquality : TypeExpr.base sort = type at typed
  generalize patternEquality : Pattern.collection kind elements rest = pattern at typed
  cases typed with
  | collectionConstructor member shape =>
    cases typeEquality
    cases patternEquality
    simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [GrammarRule.bareParams, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType, TypeExpr.bag]
  | _ => first | (cases patternEquality; done) | cases typeEquality

/-- **An admitted collection is a parallel bag of processes.** -/
theorem process_of_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (admitted : domain (.collection kind elements rest) = true) :
    process (.collection kind elements rest) = true ∧ kind = .hashBag ∧ rest = none := by
  simp only [domain, Bool.or_eq_true] at admitted
  rcases admitted with (admitted | admitted) | admitted
  · obtain ⟨typed, object, -⟩ := process_iff.mp admitted
    simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
    exact ⟨admitted, (collection_sort typed).2, object.1⟩
  · obtain ⟨typed, -, -⟩ := name_iff.mp admitted
    exact absurd (collection_sort typed).1 (by decide)
  · simp [continuation] at admitted

theorem domain_of_process {term : Pattern} (admitted : process term = true) : domain term = true := by
  simp [domain, admitted]

/-- **An admitted element is formed, sealed, at one of ρ's element types.** -/
theorem formed_of_domain {term : Pattern} (admitted : domain term = true) :
    Formed rhoCalc FreeTypeContext.empty [] TypeExpr.proc (Sealed 0) term ∨
      Formed rhoCalc FreeTypeContext.empty [] TypeExpr.name (Sealed 0) term ∨
      Formed rhoCalc FreeTypeContext.empty [] (.arrow TypeExpr.name TypeExpr.proc) (Sealed 0) term := by
  simp only [domain, Bool.or_eq_true] at admitted
  rcases admitted with (admitted | admitted) | admitted
  · obtain ⟨typed, object, sealed⟩ := process_iff.mp admitted
    exact Or.inl ⟨object, typed, sealed⟩
  · obtain ⟨typed, object, sealed⟩ := name_iff.mp admitted
    exact Or.inr (Or.inl ⟨object, typed, sealed⟩)
  · exact Or.inr (Or.inr (formed_of_continuation admitted))

theorem sealed_iff_scopeSafe {term : Pattern} :
    Sealed 0 term ↔ Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted.ReflectiveScopeSafeAt rhoReflectionProfile 0 term :=
  (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement.rho_scopeSafe_iff term).symm

/-- An admitted process in the form ρ's step theory reads. -/
theorem procWellSorted_of_process {term : Pattern} (admitted : process term = true) :
    ProcWellSorted rhoReflectivePresentation
      FreeSortContext.empty [] term ∧ binderSafeAt "NQuote" 0 term = true :=
  (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
    term).mp ((Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact term).mp admitted)

theorem process_of_procWellSorted {term : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation
      FreeSortContext.empty [] term) (sealed : binderSafeAt "NQuote" 0 term = true) : process term = true :=
  (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact term).mpr
    ((Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
      term).mpr ⟨typed, sealed⟩)

/-- Canonicalization keeps a binder. -/
theorem canonicalize_lambda (binder : Option String) (body : Pattern) :
    canonicalize (.lambda binder body) = .lambda binder (canonicalize body) := by
  simp [canonicalize]

/-! ## The elements under the equivalence -/

/-- **ρ's judgment types**: its sorts, bags of processes, and the type of input continuations. -/
theorem judged_cases {type : TypeExpr} (judged : JudgmentTypes.elements.Admits rhoCalc type) :
    (∃ sort, type = .base sort) ∨ type = .collection .hashBag TypeExpr.proc ∨
      type = .arrow TypeExpr.name TypeExpr.proc := by
  rcases judged with base | ⟨rule, member, param, paramMember, typeOf⟩
  · exact Or.inl base
  · simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at paramMember <;>
      (try rcases paramMember with rfl | rfl) <;>
      simp [parameterType?, TypeExpr.funType] at typeOf <;> subst typeOf <;>
      simp [TypeExpr.proc, TypeExpr.name, TypeExpr.baseType, TypeExpr.bag]

/-- The judgment type of processes. -/
theorem judged_proc : JudgmentTypes.elements.Admits rhoCalc TypeExpr.proc := Or.inl ⟨"Proc", rfl⟩

/-- The judgment type of names. -/
theorem judged_name : JudgmentTypes.elements.Admits rhoCalc TypeExpr.name := Or.inl ⟨"Name", rfl⟩

/-- The judgment type of input continuations. -/
theorem judged_continuation : JudgmentTypes.elements.Admits rhoCalc (.arrow TypeExpr.name TypeExpr.proc) :=
  Or.inr (by decide)

variable {relEnv : RelationEnv}

/-- **Equivalent terms have one canonical form**, in every reading. -/
theorem canonicalize_eq_of_objectEquivalent {anyReading : LanguageReading} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv rhoCalc anyReading first second) :
    canonicalize first = canonicalize second :=
  canonicalize_eq_of_equivalent equivalent.equivalent

/-- **A step of ρ's equivalence is between terms formed, sealed, at one judgment type.** -/
theorem step_formed {first second : Pattern} (step : ObjectStep relEnv rhoCalc reading first second) :
    ∃ type, ((∃ sort, type = .base sort) ∨ type = .collection .hashBag TypeExpr.proc ∨
        type = .arrow TypeExpr.name TypeExpr.proc) ∧
      Formed rhoCalc FreeTypeContext.empty [] type (Sealed 0) first ∧
      Formed rhoCalc FreeTypeContext.empty [] type (Sealed 0) second := by
  obtain ⟨-, -, type, judged, firstFormed, secondFormed, -⟩ := step
  exact ⟨type, judged_cases judged, ⟨firstFormed.object, firstFormed.typed, sealed_iff_scopeSafe.mpr firstFormed.formed⟩,
    ⟨secondFormed.object, secondFormed.typed, sealed_iff_scopeSafe.mpr secondFormed.formed⟩⟩

/-- A term formed as a bag of processes is a process. -/
theorem process_of_bag {term : Pattern}
    (formed : Formed rhoCalc FreeTypeContext.empty [] (.collection .hashBag TypeExpr.proc) (Sealed 0) term) :
    process term = true ∧ ∃ elements, term = .collection .hashBag elements none := by
  obtain ⟨object, typed, sealed⟩ := formed
  generalize typeEquality : TypeExpr.collection .hashBag TypeExpr.proc = type at typed
  cases typed with
  | collection elementsTyped =>
    cases typeEquality
    rename_i elements rest
    simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
    obtain ⟨rfl, objects⟩ := object
    have good := bag_good (good_of_elements elementsTyped objects (sealed_collection.mp sealed))
    exact ⟨process_iff.mpr ⟨good.typed, good.object, good.formed⟩, elements, rfl⟩
  | bvar lookup => simp at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | subst => simp [isObjectPattern] at object
  | lambda => cases typeEquality
  | multiLambda => cases typeEquality
  | constructor => cases typeEquality
  | collectionConstructor => cases typeEquality

/-- A process is not a name. -/
theorem not_name_of_process {term : Pattern} (admitted : process term = true) : name term = false := by
  cases nameAdmitted : name term
  · rfl
  · obtain ⟨processTyped, object, -⟩ := process_iff.mp admitted
    obtain ⟨nameTyped, -, -⟩ := name_iff.mp nameAdmitted
    exact absurd (sort_unique object processTyped nameTyped) (by decide)

/-- A continuation has no sort. -/
theorem not_sorted_of_lambda {binder : Option String} {body : Pattern} :
    process (.lambda binder body) = false ∧ name (.lambda binder body) = false := by
  constructor
  · cases admitted : process (.lambda binder body)
    · rfl
    · exact absurd (process_iff.mp admitted).1 not_hasSort_lambda
  · cases admitted : name (.lambda binder body)
    · rfl
    · exact absurd (name_iff.mp admitted).1 not_hasSort_lambda

/-- A term with a sort is no continuation. -/
theorem not_continuation_of_sorted {term : Pattern} {sort : String}
    (typed : HasSort rhoCalc FreeTypeContext.empty [] term sort) : continuation term = false := by
  cases admitted : continuation term
  · rfl
  · obtain ⟨body, rfl, -⟩ := continuation_cases admitted
    exact absurd typed not_hasSort_lambda

/-- **A step of ρ's equivalence keeps each kind of element, both ways**: processes, names and continuations. -/
theorem kinds_of_step {first second : Pattern} (step : ObjectStep relEnv rhoCalc reading first second) :
    (process first = true ↔ process second = true) ∧ (name first = true ↔ name second = true) ∧
      (continuation first = true ↔ continuation second = true) := by
  have same := canonicalize_eq_of_objectEquivalent (Relation.EqvGen.rel _ _ step)
  obtain ⟨type, kind, firstFormed, secondFormed⟩ := step_formed step
  rcases kind with ⟨sort, rfl⟩ | rfl | rfl
  · have sorted : ∀ {one other : Pattern} {target : String},
        Formed rhoCalc FreeTypeContext.empty [] (.base sort) (Sealed 0) one →
        Formed rhoCalc FreeTypeContext.empty [] (.base sort) (Sealed 0) other →
        (HasSort rhoCalc FreeTypeContext.empty [] one target ∧ isObjectPattern one = true ∧ Sealed 0 one) →
        HasSort rhoCalc FreeTypeContext.empty [] other target ∧ isObjectPattern other = true ∧ Sealed 0 other := by
      rintro one other target oneFormed otherFormed ⟨typed, object, -⟩
      have equal := sort_unique object oneFormed.typed typed
      subst equal
      exact ⟨otherFormed.typed, otherFormed.object, otherFormed.formed⟩
    refine ⟨⟨fun admitted => process_iff.mpr (sorted firstFormed secondFormed (process_iff.mp admitted)),
        fun admitted => process_iff.mpr (sorted secondFormed firstFormed (process_iff.mp admitted))⟩,
      ⟨fun admitted => name_iff.mpr (sorted firstFormed secondFormed (name_iff.mp admitted)),
        fun admitted => name_iff.mpr (sorted secondFormed firstFormed (name_iff.mp admitted))⟩, ?_⟩
    rw [not_continuation_of_sorted firstFormed.typed, not_continuation_of_sorted secondFormed.typed]
  · obtain ⟨firstProcess, firstElements, rfl⟩ := process_of_bag firstFormed
    obtain ⟨secondProcess, secondElements, rfl⟩ := process_of_bag secondFormed
    refine ⟨iff_of_true firstProcess secondProcess, ?_, ?_⟩
    · rw [not_name_of_process firstProcess, not_name_of_process secondProcess]
    · simp [continuation]
  · obtain ⟨firstBinder, firstBody, rfl, firstGood⟩ := lambda_of_arrow firstFormed
    obtain ⟨secondBinder, secondBody, rfl, secondGood⟩ := lambda_of_arrow secondFormed
    rw [canonicalize_lambda, canonicalize_lambda] at same
    obtain ⟨rfl, -⟩ := Pattern.lambda.inj same
    refine ⟨?_, ?_, ?_⟩
    · rw [not_sorted_of_lambda.1, not_sorted_of_lambda.1]
    · rw [not_sorted_of_lambda.2, not_sorted_of_lambda.2]
    · cases firstBinder with
      | none => exact iff_of_true (continuation_lambda_iff.mpr firstGood) (continuation_lambda_iff.mpr secondGood)
      | some _ => simp [continuation]

theorem kinds_of_equivalent {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv rhoCalc reading first second) :
    (process first = true ↔ process second = true) ∧ (name first = true ↔ name second = true) ∧
      (continuation first = true ↔ continuation second = true) := by
  induction equivalent with
  | rel _ _ step => exact kinds_of_step step
  | refl => exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  | symm _ _ _ same => exact ⟨same.1.symm, same.2.1.symm, same.2.2.symm⟩
  | trans _ _ _ _ _ first second =>
    exact ⟨first.1.trans second.1, first.2.1.trans second.2.1, first.2.2.trans second.2.2⟩

/-- **The admitted elements are closed under ρ's equivalence.** -/
theorem invariant {first second : Pattern} (admitted : domain first = true)
    (equivalent : ObjectEquivalent relEnv rhoCalc reading first second) : domain second = true := by
  obtain ⟨processes, names, continuations⟩ := kinds_of_equivalent equivalent
  simp only [domain, Bool.or_eq_true] at admitted ⊢
  rcases admitted with (admitted | admitted) | admitted
  · exact Or.inl (Or.inl (processes.mp admitted))
  · exact Or.inl (Or.inr (names.mp admitted))
  · exact Or.inr (continuations.mp admitted)

/-- **So are the admitted processes.** -/
theorem process_invariant {first second : Pattern} (admitted : process first = true)
    (equivalent : ObjectEquivalent relEnv rhoCalc reading first second) : process second = true :=
  (kinds_of_equivalent equivalent).1.mp admitted

/-- **A chain of ρ's typed equations at a judgment type, between closed sealed terms, is equivalence in ρ's
reading.** -/
theorem objectEquivalent_of_chain {type : TypeExpr} (judged : JudgmentTypes.elements.Admits rhoCalc type)
    {first second : Pattern} (chain : Chain relEnv FreeTypeContext.empty [] type 0 first second) :
    ObjectEquivalent relEnv rhoCalc reading first second := by
  refine Relation.EqvGen.mono (fun one other step => ?_) _ _ chain
  obtain ⟨oneFormed, otherFormed, disciplined⟩ := step
  exact ⟨oneFormed.object, otherFormed.object, type, judged,
    ⟨oneFormed.object, oneFormed.typed, sealed_iff_scopeSafe.mp oneFormed.formed⟩,
    ⟨otherFormed.object, otherFormed.typed, sealed_iff_scopeSafe.mp otherFormed.formed⟩, disciplined⟩

/-- An input continuation is equivalent to the abstraction of its body's canonical form, through sealed
continuations. -/
theorem chain_continuation {binder : Option String} {body : Pattern}
    (good : Good FreeTypeContext.empty [TypeExpr.name] 1 body) :
    Chain relEnv FreeTypeContext.empty [] (.arrow TypeExpr.name TypeExpr.proc) 0 (.lambda binder body)
      (.lambda binder (canonicalize body)) :=
  TypedEquivalent.fill (.lambda binder .hole) (fun _ formed =>
    ⟨by simpa [OneHoleContext.fill, isObjectPattern] using formed.object, .lambda formed.typed,
      by simpa [OneHoleContext.fill, Sealed, binderSafeAt] using formed.formed⟩)
    (typed_canonicalize_proc (relEnv := relEnv) good.typed good.object good.formed)

/-- **An admitted element is equivalent to its canonical form**, through sealed terms of its type. -/
theorem equivalent_canonicalize {term : Pattern} (admitted : domain term = true) :
    ObjectEquivalent relEnv rhoCalc reading term (canonicalize term) := by
  simp only [domain, Bool.or_eq_true] at admitted
  rcases admitted with (admitted | admitted) | admitted
  · obtain ⟨typed, object, sealed⟩ := process_iff.mp admitted
    exact objectEquivalent_of_chain judged_proc (typed_canonicalize_proc (relEnv := relEnv) typed object sealed)
  · obtain ⟨typed, object, sealed⟩ := name_iff.mp admitted
    exact objectEquivalent_of_chain judged_name (typed_canonicalize_name (relEnv := relEnv) typed object sealed)
  · obtain ⟨body, rfl, good⟩ := continuation_cases admitted
    rw [canonicalize_lambda]
    exact objectEquivalent_of_chain judged_continuation (chain_continuation (relEnv := relEnv) good)

/-- **On admitted elements, ρ's equivalence is canonical equality.** -/
theorem objectEquivalent_iff {first second : Pattern} (firstAdmitted : domain first = true)
    (secondAdmitted : domain second = true) :
    ObjectEquivalent relEnv rhoCalc reading first second ↔ canonicalize first = canonicalize second := by
  constructor
  · exact canonicalize_eq_of_objectEquivalent
  · intro same
    have toCanonical := equivalent_canonicalize (relEnv := relEnv) firstAdmitted
    have fromCanonical := equivalent_canonicalize (relEnv := relEnv) secondAdmitted
    rw [same] at toCanonical
    exact .trans _ _ _ toCanonical (.symm _ _ fromCanonical)

theorem process_canonicalize {term : Pattern} (admitted : process term = true) :
    process (canonicalize term) = true := by
  obtain ⟨typed, object, sealed⟩ := process_iff.mp admitted
  exact process_iff.mpr ⟨canonicalize_proc_hasSort typed object, canonicalize_isObjectPattern object,
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _ sealed⟩

theorem admitted_canonicalize {term : Pattern} (admitted : domain term = true) :
    domain (canonicalize term) = true := by
  simp only [domain, Bool.or_eq_true] at admitted
  rcases admitted with (admitted | admitted) | admitted
  · exact domain_of_process (process_canonicalize admitted)
  · obtain ⟨typed, object, sealed⟩ := name_iff.mp admitted
    have canonName := name_iff.mpr ⟨canonicalize_name_hasSort typed object, canonicalize_isObjectPattern object,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _ sealed⟩
    simp [domain, canonName]
  · obtain ⟨body, rfl, good⟩ := continuation_cases admitted
    have canonGood : Good FreeTypeContext.empty [TypeExpr.name] 1 (canonicalize body) :=
      ⟨canonicalize_isObjectPattern good.object, canonicalize_proc_hasSort good.typed good.object,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _ good.formed⟩
    simp [domain, canonicalize_lambda, continuation_lambda_iff.mpr canonGood]

theorem closed_of_admitted {term : Pattern} (admitted : domain term = true) : term.isWellScopedAt 0 = true := by
  rcases formed_of_domain admitted with formed | formed | formed <;>
    exact isWellScopedAt_of_binderSafeAt "NQuote" formed.formed

theorem closed_of_process {term : Pattern} (admitted : process term = true) : term.isWellScopedAt 0 = true :=
  closed_of_admitted (domain_of_process admitted)

/-- **A ρ step starts at a bag.** -/
theorem rhoStep_collection {source target : Pattern} (step : RhoStep source target) :
    ∃ elements rest, source = .collection .hashBag elements rest := by
  obtain ⟨fuel, bounded⟩ := step
  cases bounded with
  | rule member matched _ _ =>
    change _ ∈ [rhoCommRewrite, rhoParCongRewrite] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨elements, rest, -, -, -, -, -, -, -, -, -, same, -⟩ := rhoComm_match_shape matched
      exact ⟨elements, rest, same⟩
    · obtain ⟨elements, rest, -, -, -, same, -⟩ := rhoParCong_match_shape matched
      exact ⟨elements, rest, same⟩

/-- **An admitted element that steps is a process.** -/
theorem process_of_rhoStep {redex contractum : Pattern} (admitted : domain redex = true)
    (step : RhoStep redex contractum) : process redex = true := by
  obtain ⟨elements, rest, rfl⟩ := rhoStep_collection step
  exact (process_of_collection admitted).1

/-- **ρ's steps keep the processes.** -/
theorem process_of_step {redex contractum : Pattern} (admitted : process redex = true)
    (step : RhoStep redex contractum) : process contractum = true := by
  obtain ⟨typed, sealed⟩ := procWellSorted_of_process admitted
  obtain ⟨contractumTyped, contractumSealed⟩ := rhoStep_preserves_closed typed sealed step
  exact process_of_procWellSorted contractumTyped contractumSealed

/-! ## Canonical forms -/

/-- **Canonicalization gives canonical forms on ρ's elements**, in its reading. -/
theorem canonical (relEnv : RelationEnv) : Canonical relEnv rhoCalc canonicalize domain reading where
  object admitted := by
    rcases formed_of_domain admitted with formed | formed | formed <;> exact formed.object
  admitted_canon := admitted_canonicalize
  invariant := invariant
  stepsAdmitted admitted _ valid _ :=
    domain_of_process (process_of_step (process_of_rhoStep admitted valid.2) valid.2)
  equivalent := equivalent_canonicalize
  same _ equivalent := canonicalize_eq_of_objectEquivalent equivalent
  closed admitted := by
    rw [closed_of_admitted admitted, closed_of_admitted (admitted_canonicalize admitted)]

/-- **The forms are coherent for plain steps at fuel one**: a step from any process equivalent to a canonical
admitted one is matched, up to canonical form, by a communication at the top of the canonical bag. -/
theorem coherentPlain (relEnv : RelationEnv) :
    CoherentPlain relEnv rhoCalc 1 canonicalize domain List.singleton reading := by
  intro state redex witness contractum _ stateAdmitted canonState _ before _ valid
  have redexAdmitted := process_of_rhoStep (invariant stateAdmitted before) valid.2
  have sameCanon : canonicalize redex = state :=
    (canonicalize_eq_of_objectEquivalent before).symm.trans canonState
  obtain ⟨typed, sealed⟩ := procWellSorted_of_process redexAdmitted
  obtain ⟨target, topStep, canonTarget⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep
      typed sealed valid.2
  rw [sameCanon] at topStep
  refine ⟨(.base [], target), ?_, canonTarget⟩
  simp only [listedAt, List.singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil, ruleSteps, reading]
  exact List.mem_map.mpr
    ⟨target, Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.mem_rewriteAt_iff_stepAt.mpr topStep, rfl⟩

/-! ## Canonical forms the kernel evaluates -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalizeList normalizeQuote collapseBag bagContents patternCode sortPatterns canonicalizeList_eq_map
    patternCode_injective normalizeBagElements_eq_sort_bagContents canonicalize_apply_general
    canonicalize_collection_general)

/-- **Sorting by pattern code, by insertion.** -/
def sortByInsertion (patterns : List Pattern) : List Pattern :=
  patterns.insertionSort fun first second => patternCode first ≤ patternCode second

/-- **It is ρ's sort**, the order being total, transitive and antisymmetric. -/
theorem sortByInsertion_eq (patterns : List Pattern) : sortByInsertion patterns = sortPatterns patterns := by
  let relation : Pattern → Pattern → Prop := fun first second => patternCode first ≤ patternCode second
  let : Std.Total relation := ⟨fun first second => Nat.le_total (patternCode first) (patternCode second)⟩
  let : IsTrans Pattern relation := ⟨fun _ _ _ firstLe secondLe => Nat.le_trans firstLe secondLe⟩
  let : Std.Antisymm relation :=
    ⟨fun first second firstLe secondLe => patternCode_injective (Nat.le_antisymm firstLe secondLe)⟩
  have same := List.mergeSort_eq_insertionSort relation patterns
  simpa [sortPatterns, sortByInsertion, relation] using same.symm

mutual
  /-- **ρ's canonicalization with an insertion sort of bag elements.** -/
  def canonicalizeSorted : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply "NQuote" [argument] => normalizeQuote (canonicalizeSorted argument)
    | .apply constructor arguments => .apply constructor (canonicalizeSortedList arguments)
    | .lambda binderName body => .lambda binderName (canonicalizeSorted body)
    | .multiLambda arity binderNames body => .multiLambda arity binderNames (canonicalizeSorted body)
    | .subst body replacement => .subst (canonicalizeSorted body) (canonicalizeSorted replacement)
    | .collection .hashBag elements none =>
        collapseBag (sortByInsertion (bagContents (canonicalizeSortedList elements)))
    | .collection collectionType elements rest =>
        .collection collectionType (canonicalizeSortedList elements) rest

  def canonicalizeSortedList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => canonicalizeSorted pattern :: canonicalizeSortedList patterns
end

theorem canonicalizeSortedList_eq_map (patterns : List Pattern) :
    canonicalizeSortedList patterns = patterns.map canonicalizeSorted := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis => simp [canonicalizeSortedList, inductionHypothesis]

theorem canonicalizeSorted_apply_general (constructor : String) (arguments : List Pattern)
    (notQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, arguments = [argument])) :
    canonicalizeSorted (.apply constructor arguments) = .apply constructor (canonicalizeSortedList arguments) := by
  unfold canonicalizeSorted
  split <;> simp_all

theorem canonicalizeSorted_collection_general (collectionType : CollType) (elements : List Pattern)
    (rest : Option String) (notParallel : ¬ (collectionType = .hashBag ∧ rest = none)) :
    canonicalizeSorted (.collection collectionType elements rest) =
      .collection collectionType (canonicalizeSortedList elements) rest := by
  unfold canonicalizeSorted
  split <;> simp_all

/-- **The insertion-sort canonicalization is ρ's canonicalization.** -/
theorem canonicalizeSorted_eq (pattern : Pattern) : canonicalizeSorted pattern = canonicalize pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments inductionHypothesis =>
    have list : canonicalizeSortedList arguments = canonicalizeList arguments := by
      rw [canonicalizeSortedList_eq_map, canonicalizeList_eq_map]
      exact List.map_congr_left inductionHypothesis
    by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
    · obtain ⟨rfl, argument, rfl⟩ := isQuote
      simp [canonicalizeSorted, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize,
        inductionHypothesis argument (by simp)]
    · rw [canonicalize_apply_general _ _ isQuote, canonicalizeSorted_apply_general _ _ isQuote, list]
  | hlambda binder body inductionHypothesis =>
    simp [canonicalizeSorted, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize,
      inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
    simp [canonicalizeSorted, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize,
      inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
    simp [canonicalizeSorted, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize,
      bodyHypothesis, replacementHypothesis]
  | hcollection kind elements rest inductionHypothesis =>
    have list : canonicalizeSortedList elements = canonicalizeList elements := by
      rw [canonicalizeSortedList_eq_map, canonicalizeList_eq_map]
      exact List.map_congr_left inductionHypothesis
    by_cases parallel : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := parallel
      simp only [canonicalizeSorted, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize, list,
        sortByInsertion_eq, normalizeBagElements_eq_sort_bagContents]
    · rw [canonicalize_collection_general _ _ _ parallel, canonicalizeSorted_collection_general _ _ _ parallel, list]

theorem canonicalizeSorted_eq_fun : canonicalizeSorted = canonicalize :=
  funext canonicalizeSorted_eq

/-- **ρ's canonical forms**, for the front door, computed by the insertion-sort canonicalization. -/
def forms (relEnv : RelationEnv) : CanonicalForms relEnv rhoCalc 1 :=
  .ofPlain (reading := reading) (canon := canonicalizeSorted) (canonicalizeSorted_eq_fun ▸ canonical relEnv)
    (canonicalizeSorted_eq_fun ▸ coherentPlain relEnv)

theorem forms_reading (relEnv : RelationEnv) : (forms relEnv).reading = reading :=
  rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho
