import Mettapedia.OSLF.MeTTaIL.ReferenceStepDisciplines
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping

/-!
# ρ's equations, read as a typed judgment

In the typed reading an equation relates two formed terms of one type in one context
(`ReferenceStep.TypedEquivalent`). A ρ term is formed when it is an object of its type that keeps ρ's scope policy:
a quotation seals the process it quotes, so no variable bound outside a quotation occurs inside it (`Sealed`, at the
number of binders crossed since the last quotation). This is the reading ρ's runtime computes.

- **Every formed term is typed-equivalent to its canonical form** (`typed_canonicalize_proc`,
  `typed_canonicalize_name`), through formed terms of its type: canonicalization is a chain of instances of the
  authored quote/drop equation and of the laws the parallel algebra derives, each read in the binder context of the
  place it rewrites.
- **Every step of the syntax theory keeps the canonical form** (`canonicalize_eq_of_equationStep`), so in particular
  every typed step does.

So formed terms of one type in one context are typed-equivalent exactly when their canonical forms agree
(`typedEquivalent_proc_iff`, `typedEquivalent_name_iff`). The syntax theory, which instantiates the quote/drop
equation at any pattern, also relates a process to the ill-sorted `@(*P)` (`syntax_relates_process_to_quote`); the
typed reading does not.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (PremisesAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt binderSafeListAt binderSafeAt_mono)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

/-! ## ρ's equation as a reference equation -/

/-- ρ's one authored equation has no premises. -/
theorem rhoCalc_unconditional : UnconditionalEquations rhoCalc := by
  intro equation member
  simp only [rhoCalc, List.mem_singleton] at member
  subst member
  rfl

theorem rhoCalc_equationsAligned : EquationsAligned rhoCalc := by
  intro equation member
  simp only [rhoCalc, List.mem_singleton] at member
  subst member
  rfl

variable {relEnv : RelationEnv}

/-- **The authored quote/drop equation** `@(*n) = n`, at any pattern `n`. -/
theorem quoteDrop_generator (name : Pattern) :
    Generator relEnv rhoCalc (.apply "NQuote" [.apply "PDrop" [name]]) name := by
  refine (generator_iff_unconditional rhoCalc_unconditional rhoCalc_equationsAligned).mp (Or.inl ⟨0, ?_⟩)
  refine EquationInstanceAt.forward (equation := quoteDropEquation) (initialBindings := [("N", name)])
    (finalBindings := [("N", name)]) quoteDropEquation_mem
    (Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl) ?_ (PremisesAt.nil _) ?_
  · rw [matchPattern_iff_matchRel]
    exact MatchRel.apply
      (MatchArgsRel.cons (MatchRel.apply (MatchArgsRel.cons MatchRel.fvar MatchArgsRel.nil rfl) rfl)
        MatchArgsRel.nil rfl)
      rfl
  · simp [quoteDropEquation, applyBindings]

/-- **The syntax theory relates a process to its ill-sorted quote of a drop**: the quote/drop equation read from
right to left, binding its name variable to a process. -/
theorem syntax_relates_process_to_quote (process : Pattern) :
    EquationStep relEnv rhoCalc process (.apply "NQuote" [.apply "PDrop" [process]]) := by
  have reversed : Generator relEnv rhoCalc process (.apply "NQuote" [.apply "PDrop" [process]]) := by
    refine (generator_iff_unconditional rhoCalc_unconditional rhoCalc_equationsAligned).mp (Or.inl ⟨0, ?_⟩)
    refine EquationInstanceAt.reverse (equation := quoteDropEquation) (initialBindings := [("N", process)])
      (finalBindings := [("N", process)]) quoteDropEquation_mem
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.readsRaw_of_none rfl) ?_ (PremisesAt.nil _) ?_
    · rw [matchPattern_iff_matchRel]
      exact MatchRel.fvar
    · simp [quoteDropEquation, applyBindings]
  exact .inContext .hole reversed

/-! ## Formed terms -/

/-- **Sealed at a depth**: no variable bound outside a quotation occurs inside it, `depth` binders having been crossed
since the last quotation. -/
abbrev Sealed (depth : ℕ) (pattern : Pattern) : Prop := binderSafeAt "NQuote" depth pattern = true

/-- A formed process in a context, sealed at a depth. -/
abbrev Good (free : FreeTypeContext) (bound : List TypeExpr) (depth : ℕ) : Pattern → Prop :=
  Formed rhoCalc free bound TypeExpr.proc (Sealed depth)

variable (relEnv) in
/-- **ρ's typed equivalence** at a type in a context, through terms sealed at a depth. -/
abbrev Chain (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr) (depth : ℕ) :
    Pattern → Pattern → Prop :=
  TypedEquivalent relEnv rhoCalc .raw free bound type (Sealed depth)

theorem sealed_quote {depth : ℕ} {process : Pattern} : Sealed depth (.apply "NQuote" [process]) ↔ Sealed 0 process := by
  simp [Sealed, binderSafeAt]

theorem sealed_unary {depth : ℕ} {label : String} (notQuote : label ≠ "NQuote") {argument : Pattern} :
    Sealed depth (.apply label [argument]) ↔ Sealed depth argument := by
  simp [Sealed, binderSafeAt, binderSafeListAt, notQuote]

theorem sealed_binary {depth : ℕ} {label : String} {first second : Pattern} :
    Sealed depth (.apply label [first, second]) ↔ Sealed depth first ∧ Sealed depth second := by
  simp [Sealed, binderSafeAt, binderSafeListAt]

theorem sealed_lambda {depth : ℕ} {body : Pattern} : Sealed depth (.lambda none body) ↔ Sealed (depth + 1) body := by
  simp [Sealed, binderSafeAt]

theorem sealedList_iff {depth : ℕ} {patterns : List Pattern} :
    binderSafeListAt "NQuote" depth patterns = true ↔ ∀ pattern ∈ patterns, Sealed depth pattern := by
  induction patterns with
  | nil => simp [binderSafeListAt]
  | cons pattern patterns inductionHypothesis =>
    simp [binderSafeListAt, inductionHypothesis, or_imp, forall_and]

theorem sealed_collection {depth : ℕ} {kind : CollType} {elements : List Pattern} {rest : Option String} :
    Sealed depth (.collection kind elements rest) ↔ ∀ element ∈ elements, Sealed depth element := by
  rw [← sealedList_iff]
  simp [Sealed, binderSafeAt]

theorem objectList_iff {patterns : List Pattern} :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons pattern patterns inductionHypothesis =>
    simp [isObjectPatternList, inductionHypothesis, or_imp, forall_and]

theorem good_of_elements {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc)
    (objects : isObjectPatternList elements = true) (sealed : ∀ element ∈ elements, Sealed depth element) :
    ∀ element ∈ elements, Good free bound depth element :=
  fun element member => ⟨objectList_iff.mp objects element member, procTyped_of_mem typed member,
    sealed element member⟩

theorem elements_of_good {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : ∀ element ∈ elements, Good free bound depth element) :
    ElementsHaveType rhoCalc free bound elements TypeExpr.proc ∧ isObjectPatternList elements = true :=
  ⟨procTyped_of_forall_mem fun element member => (good element member).typed,
    objectList_iff.mpr fun element member => (good element member).object⟩

/-- A bag of processes is a process. -/
theorem bag_good {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : ∀ element ∈ elements, Good free bound depth element) :
    Good free bound depth (.collection .hashBag elements none) :=
  ⟨by simpa [isObjectPattern] using (elements_of_good good).2, rho_parallel_hasSort (elements_of_good good).1,
    sealed_collection.mpr fun element member => (good element member).formed⟩

/-- The elements of a formed bag are formed. -/
theorem good_of_bag {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : Good free bound depth (.collection .hashBag elements none)) :
    ∀ element ∈ elements, Good free bound depth element :=
  good_of_elements (rhoParallel_elementsHaveType good.typed) (by simpa [isObjectPattern] using good.object)
    (sealed_collection.mp good.formed)

/-! ## Typed steps -/

/-- One generator at the root between formed terms of one type is a typed step. -/
theorem typed_of_generator {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {formed : Pattern → Prop} {source target : Pattern} (sourceFormed : Formed rhoCalc free bound type formed source)
    (targetFormed : Formed rhoCalc free bound type formed target) (generator : Generator relEnv rhoCalc source target) :
    TypedEquivalent relEnv rhoCalc .raw free bound type formed source target :=
  .rel _ _ ⟨sourceFormed, targetFormed, disciplinedStep_raw_iff.mpr (EquationStep.inContext .hole generator)⟩

/-- A derived law between processes is a typed step. -/
theorem typed_of_derived {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {source target : Pattern}
    (sourceGood : Good free bound depth source) (targetGood : Good free bound depth target)
    (derived : DerivedInstance rhoCalc source target) :
    Chain relEnv free bound TypeExpr.proc depth source target :=
  typed_of_generator sourceGood targetGood (Or.inr derived)

/-- **Quote/drop at a name**, sealed inside its quotation, is a typed step at any depth. -/
theorem typed_quoteDrop {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {name : Pattern}
    (typed : HasSort rhoCalc free bound name "Name") (object : isObjectPattern name = true) (sealed : Sealed 0 name) :
    Chain relEnv free bound TypeExpr.name depth (.apply "NQuote" [.apply "PDrop" [name]]) name :=
  typed_of_generator
    ⟨by simpa [isObjectPattern, isObjectPatternList] using object, rho_quote_hasSort (rho_drop_hasSort typed),
      sealed_quote.mpr ((sealed_unary (by decide)).mpr sealed)⟩
    ⟨object, typed, binderSafeAt_mono "NQuote" sealed (Nat.zero_le _)⟩ (quoteDrop_generator name)

/-- Quote normalization at a process sealed inside its quotation is quote/drop or nothing. -/
theorem typed_normalizeQuote {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {process : Pattern}
    (typed : HasSort rhoCalc free bound process "Proc") (object : isObjectPattern process = true)
    (sealed : Sealed 0 process) :
    Chain relEnv free bound TypeExpr.name depth (.apply "NQuote" [process]) (normalizeQuote process) := by
  by_cases isDrop : ∃ name, process = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := isDrop
    have nameTyped : HasSort rhoCalc free bound name "Name" := by
      simpa [normalizeQuote] using normalizeQuote_hasSort typed
    exact typed_quoteDrop nameTyped (by simpa [isObjectPattern, isObjectPatternList] using object)
      ((sealed_unary (by decide)).mp sealed)
  · have same : normalizeQuote process = .apply "NQuote" [process] := by
      unfold normalizeQuote
      split
      · rename_i name
        exact absurd ⟨name, rfl⟩ isDrop
      · rfl
    rw [same]
    exact .refl _

/-! ## Frames -/

theorem typed_quote_congr {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {first second : Pattern}
    (equivalent : Chain relEnv free bound TypeExpr.proc 0 first second) :
    Chain relEnv free bound TypeExpr.name depth (.apply "NQuote" [first]) (.apply "NQuote" [second]) :=
  TypedEquivalent.fill (.apply "NQuote" [] .hole []) (fun _ formed =>
    ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using formed.object,
      rho_quote_hasSort formed.typed, sealed_quote.mpr formed.formed⟩) equivalent

theorem typed_drop_congr {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {first second : Pattern}
    (equivalent : Chain relEnv free bound TypeExpr.name depth first second) :
    Chain relEnv free bound TypeExpr.proc depth (.apply "PDrop" [first]) (.apply "PDrop" [second]) :=
  TypedEquivalent.fill (.apply "PDrop" [] .hole []) (fun _ formed =>
    ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using formed.object,
      rho_drop_hasSort formed.typed, (sealed_unary (by decide)).mpr formed.formed⟩) equivalent

theorem typed_output_congr {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ}
    {channel channel' payload payload' : Pattern}
    (channelFormed : Formed rhoCalc free bound TypeExpr.name (Sealed depth) channel')
    (payloadFormed : Good free bound depth payload)
    (channels : Chain relEnv free bound TypeExpr.name depth channel channel')
    (payloads : Chain relEnv free bound TypeExpr.proc depth payload payload') :
    Chain relEnv free bound TypeExpr.proc depth (.apply "POutput" [channel, payload])
      (.apply "POutput" [channel', payload']) :=
  .trans _ _ _
    (TypedEquivalent.fill (.apply "POutput" [] .hole [payload]) (fun _ formed =>
      ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using ⟨formed.object, payloadFormed.object⟩,
        rho_output_hasSort formed.typed payloadFormed.typed,
        sealed_binary.mpr ⟨formed.formed, payloadFormed.formed⟩⟩) channels)
    (TypedEquivalent.fill (.apply "POutput" [channel'] .hole []) (fun _ formed =>
      ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using ⟨channelFormed.object, formed.object⟩,
        rho_output_hasSort channelFormed.typed formed.typed,
        sealed_binary.mpr ⟨channelFormed.formed, formed.formed⟩⟩) payloads)

theorem typed_input_congr {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ}
    {channel channel' body body' : Pattern}
    (channelFormed : Formed rhoCalc free bound TypeExpr.name (Sealed depth) channel')
    (bodyFormed : Good free (TypeExpr.name :: bound) (depth + 1) body)
    (channels : Chain relEnv free bound TypeExpr.name depth channel channel')
    (bodies : Chain relEnv free (TypeExpr.name :: bound) TypeExpr.proc (depth + 1) body body') :
    Chain relEnv free bound TypeExpr.proc depth (.apply "PInput" [channel, .lambda none body])
      (.apply "PInput" [channel', .lambda none body']) :=
  .trans _ _ _
    (TypedEquivalent.fill (.apply "PInput" [] .hole [.lambda none body]) (fun _ formed =>
      ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using ⟨formed.object, bodyFormed.object⟩,
        rho_input_hasSort formed.typed bodyFormed.typed,
        sealed_binary.mpr ⟨formed.formed, sealed_lambda.mpr bodyFormed.formed⟩⟩) channels)
    (TypedEquivalent.fill (.apply "PInput" [channel'] (.lambda none .hole) []) (fun _ formed =>
      ⟨by simpa [OneHoleContext.fill, isObjectPattern, isObjectPatternList] using ⟨channelFormed.object, formed.object⟩,
        rho_input_hasSort channelFormed.typed formed.typed,
        sealed_binary.mpr ⟨channelFormed.formed, sealed_lambda.mpr formed.formed⟩⟩) bodies)

/-- **Changing the elements of a bag one at a time.** -/
theorem typed_bag_of_forall₂ {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} :
    ∀ (done : List Pattern) {left right : List Pattern}, (∀ element ∈ done, Good free bound depth element) →
      (∀ element ∈ left, Good free bound depth element) →
      List.Forall₂ (Chain relEnv free bound TypeExpr.proc depth) left right →
      Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag (done ++ left) none)
        (.collection .hashBag (done ++ right) none)
  | _, [], [], _, _, .nil => .refl _
  | done, first :: left, second :: right, doneGood, leftGood, .cons head tail => by
    have firstGood := leftGood first List.mem_cons_self
    have secondGood : Good free bound depth second := head.formed_right firstGood
    have step : Chain relEnv free bound TypeExpr.proc depth
        (.collection .hashBag (done ++ first :: left) none) (.collection .hashBag (done ++ second :: left) none) :=
      TypedEquivalent.fill (.collection .hashBag done .hole left none) (fun term formed => by
        refine bag_good fun element member => ?_
        rcases List.mem_append.mp member with inDone | inRest
        · exact doneGood element inDone
        · rcases List.mem_cons.mp inRest with rfl | inLeft
          · exact formed
          · exact leftGood element (List.mem_cons_of_mem _ inLeft)) head
    have rest := typed_bag_of_forall₂ (done ++ [second]) (fun element member => by
        rcases List.mem_append.mp member with inDone | inSecond
        · exact doneGood element inDone
        · rw [List.mem_singleton] at inSecond
          subst inSecond
          exact secondGood)
      (fun element member => leftGood element (List.mem_cons_of_mem _ member)) tail
    simp only [List.append_assoc, List.singleton_append] at rest
    exact .trans _ _ _ step rest

/-! ## Bag normalization is a chain of typed derived laws -/

theorem typed_flatMapSplice {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} :
    ∀ (pre elements : List Pattern), (∀ element ∈ pre ++ elements, Good free bound depth element) →
      Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag (pre ++ elements) none)
        (.collection .hashBag (pre ++ elements.flatMap bagSplice) none)
  | pre, [], _ => by
    simp only [List.flatMap_nil, List.append_nil]
    exact .refl _
  | pre, element :: elements, good => by
    by_cases isBag : ∃ inner, element = .collection .hashBag inner none
    · obtain ⟨inner, rfl⟩ := isBag
      have innerGood := good_of_bag (good (.collection .hashBag inner none) (by simp))
      have splicedGood : ∀ other ∈ pre ++ inner ++ elements, Good free bound depth other := by
        intro other member
        simp only [List.mem_append] at member
        rcases member with (inPre | inInner) | inElements
        · exact good other (by simp [inPre])
        · exact innerGood other inInner
        · exact good other (by simp [inElements])
      have flattened : Chain relEnv free bound TypeExpr.proc depth
          (.collection .hashBag (pre ++ .collection .hashBag inner none :: elements) none)
          (.collection .hashBag (pre ++ inner ++ elements) none) :=
        typed_of_derived (bag_good good) (bag_good splicedGood)
          (DerivedInstance.flatten rhoParallelAlgebra rfl (sortedAt_bag (elements_of_good good).1))
      have tail := typed_flatMapSplice (pre ++ inner) elements splicedGood
      simp only [List.flatMap_cons, bagSplice, List.append_assoc] at tail flattened ⊢
      exact .trans _ _ _ flattened tail
    · have notBag : ∀ inner, element ≠ .collection .hashBag inner none :=
        fun inner equal => isBag ⟨inner, equal⟩
      have tail := typed_flatMapSplice (pre ++ [element]) elements (by simpa [List.append_assoc] using good)
      rw [List.flatMap_cons, bagSplice_eq_singleton notBag]
      simp only [List.append_assoc, List.singleton_append] at tail
      exact tail

theorem typed_filterZero {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} :
    ∀ (pre elements : List Pattern), (∀ element ∈ pre ++ elements, Good free bound depth element) →
      Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag (pre ++ elements) none)
        (.collection .hashBag (pre ++ elements.filter (fun pattern => pattern ≠ .apply "PZero" [])) none)
  | pre, [], _ => by
    simp only [List.filter_nil, List.append_nil]
    exact .refl _
  | pre, element :: elements, good => by
    by_cases isZero : element = .apply "PZero" []
    · subst isZero
      have restGood : ∀ other ∈ pre ++ elements, Good free bound depth other := by
        intro other member
        apply good
        simp only [List.mem_append, List.mem_cons] at member ⊢
        rcases member with inPre | inElements
        · exact Or.inl inPre
        · exact Or.inr (Or.inr inElements)
      have absorbed : Chain relEnv free bound TypeExpr.proc depth
          (.collection .hashBag (pre ++ .apply "PZero" [] :: elements) none)
          (.collection .hashBag (pre ++ elements) none) :=
        typed_of_derived (bag_good good) (bag_good restGood)
          (DerivedInstance.unitElim rhoParallelAlgebra rfl (sortedAt_bag (elements_of_good good).1))
      have tail := typed_filterZero pre elements restGood
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact .trans _ _ _ absorbed tail
    · have tail := typed_filterZero (pre ++ [element]) elements (by simpa [List.append_assoc] using good)
      have keep : (element :: elements).filter (fun pattern => pattern ≠ .apply "PZero" []) =
          element :: elements.filter (fun pattern => pattern ≠ .apply "PZero" []) := by
        simp [isZero]
      rw [keep]
      simp only [List.append_assoc, List.singleton_append] at tail
      exact tail

/-- The members of a flattened list of formed processes are formed. -/
theorem good_of_mem_flatMap {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : ∀ element ∈ elements, Good free bound depth element) :
    ∀ element ∈ elements.flatMap bagSplice, Good free bound depth element := by
  intro element member
  obtain ⟨source, sourceMember, inSplice⟩ := List.mem_flatMap.mp member
  have sourceGood := good source sourceMember
  cases source with
  | collection kind inner rest =>
    cases kind <;> cases rest <;> simp only [bagSplice, List.mem_singleton] at inSplice
    all_goals first
      | (subst inSplice; exact sourceGood)
      | exact good_of_bag sourceGood element inSplice
  | _ =>
    simp only [bagSplice, List.mem_singleton] at inSplice
    subst inSplice
    exact sourceGood

/-- **The parallel normalization of a bag of processes** is a chain of typed derived laws. -/
theorem typed_normalizeBagElements {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ}
    {elements : List Pattern} (good : ∀ element ∈ elements, Good free bound depth element) :
    Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag elements none)
      (.collection .hashBag (normalizeBagElements elements) none) := by
  have spliced := typed_flatMapSplice (relEnv := relEnv) [] elements (by simpa using good)
  have splicedGood := good_of_mem_flatMap good
  have filtered := typed_filterZero (relEnv := relEnv) [] (elements.flatMap bagSplice) (by simpa using splicedGood)
  have contentsGood : ∀ element ∈ bagContents elements, Good free bound depth element := fun element member =>
    splicedGood element (List.mem_of_mem_filter member)
  have sorted : Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag (bagContents elements) none)
      (.collection .hashBag (normalizeBagElements elements) none) := by
    rw [normalizeBagElements_eq_sort_bagContents]
    exact typed_of_derived (bag_good contentsGood)
      (bag_good fun element member => contentsGood element (sortPatterns_mem_iff.mp member))
      (DerivedInstance.bagPerm_of_sorted (sortedAt_bag (elements_of_good contentsGood).1)
        (sortPatterns_perm (bagContents elements)))
  simp only [List.nil_append] at spliced filtered
  exact .trans _ _ _ spliced (.trans _ _ _ filtered sorted)

/-- The members of a normalized list of formed processes are formed. -/
theorem good_of_mem_normalize {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : ∀ element ∈ elements, Good free bound depth element) :
    ∀ element ∈ normalizeBagElements elements, Good free bound depth element := fun element member =>
  good_of_mem_flatMap good element
    (List.mem_of_mem_filter (sortPatterns_mem_iff.mp (normalizeBagElements_eq_sort_bagContents elements ▸ member)))

/-- **Collapsing the empty or singleton wrapper** is a typed derived law. -/
theorem typed_collapseBag {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {elements : List Pattern}
    (good : ∀ element ∈ elements, Good free bound depth element) :
    Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag elements none) (collapseBag elements) := by
  match elements, good with
  | [], good =>
    exact typed_of_derived (bag_good good)
      ⟨rfl, rho_zero_hasSort free bound, by simp [Sealed, collapseBag, binderSafeAt, binderSafeListAt]⟩
      (DerivedInstance.emptyUnit rhoParallelAlgebra rfl
        (sortedAt_bag (free := FreeTypeContext.empty) (.nil [] TypeExpr.proc)))
  | [element], good =>
    exact typed_of_derived (bag_good good) (good element List.mem_cons_self)
      (DerivedInstance.singleton rhoParallelAlgebra rfl (sortedAt_bag (elements_of_good good).1))
  | first :: second :: rest, _ =>
    simp only [collapseBag]
    exact .refl _

/-! ## Every formed term is typed-equivalent to its canonical form -/

mutual
  /-- **Canonicalization of a name is a chain of typed equations.** -/
  theorem typed_canonicalize_name {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {name : Pattern}
      (typed : HasSort rhoCalc free bound name "Name") (object : isObjectPattern name = true)
      (sealed : Sealed depth name) :
      Chain relEnv free bound TypeExpr.name depth name (canonicalize name) := by
    change HasType rhoCalc free bound name TypeExpr.name at typed
    generalize resultTypeEquality : TypeExpr.name = resultType at typed
    cases typed with
    | bvar lookup => exact .refl _
    | fvar lookup => exact .refl _
    | @constructor bound rule arguments membership notBare argumentsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected representation parameterType argumentTyped
            argumentsTyped =>
          cases argumentsTyped
          have expectedEquality : expected = TypeExpr.proc := by
            simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using parameterType.symm
          subst expected
          simp [isObjectPattern, isObjectPatternList] at object
          have argumentSealed : Sealed 0 argument := sealed_quote.mp sealed
          have inner := typed_canonicalize_proc argumentTyped object argumentSealed
          change Chain relEnv free bound TypeExpr.name depth (.apply "NQuote" [argument])
            (normalizeQuote (canonicalize argument))
          exact .trans _ _ _ (typed_quote_congr inner)
            (typed_normalizeQuote (canonicalize_proc_hasSort argumentTyped object)
              (canonicalize_isObjectPattern object)
              (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _
                argumentSealed))
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest elementType membership parameterShape
        elementsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp at parameterShape
      · simp at parameterShape

  /-- **Canonicalization of a process is a chain of typed equations.** -/
  theorem typed_canonicalize_proc {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {process : Pattern}
      (typed : HasSort rhoCalc free bound process "Proc") (object : isObjectPattern process = true)
      (sealed : Sealed depth process) :
      Chain relEnv free bound TypeExpr.proc depth process (canonicalize process) := by
    change HasType rhoCalc free bound process TypeExpr.proc at typed
    generalize resultTypeEquality : TypeExpr.proc = resultType at typed
    cases typed with
    | bvar lookup => exact .refl _
    | fvar lookup => exact .refl _
    | @constructor bound rule arguments membership notBare argumentsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · cases argumentsTyped
        exact .refl _
      · cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected representation parameterType argumentTyped
            argumentsTyped =>
          cases argumentsTyped
          have expectedEquality : expected = TypeExpr.name := by
            simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using parameterType.symm
          subst expected
          simp [isObjectPattern, isObjectPatternList] at object
          exact typed_drop_congr (typed_canonicalize_name argumentTyped object
            ((sealed_unary (by decide)).mp sealed))
      · simp [TypeExpr.proc, TypeExpr.baseType] at resultTypeEquality
      · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at notBare
      · cases argumentsTyped with
        | @cons _ channel arguments parameter parameters channelType channelRepresentation channelParameterType
            channelTyped argumentsTyped =>
          cases argumentsTyped with
          | @cons _ payload arguments parameter parameters payloadType payloadRepresentation payloadParameterType
              payloadTyped argumentsTyped =>
            cases argumentsTyped
            have channelTypeEquality : channelType = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
            have payloadTypeEquality : payloadType = TypeExpr.proc := by
              simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using payloadParameterType.symm
            subst channelType
            subst payloadType
            simp [isObjectPattern, isObjectPatternList] at object
            obtain ⟨channelSealed, payloadSealed⟩ := sealed_binary.mp sealed
            exact typed_output_congr
              ⟨canonicalize_isObjectPattern object.1, canonicalize_name_hasSort channelTyped object.1,
                Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _
                  channelSealed⟩
              ⟨object.2, payloadTyped, payloadSealed⟩
              (typed_canonicalize_name channelTyped object.1 channelSealed)
              (typed_canonicalize_proc payloadTyped object.2 payloadSealed)
      · cases argumentsTyped with
        | @cons _ channel arguments parameter parameters channelType channelRepresentation channelParameterType
            channelTyped argumentsTyped =>
          cases argumentsTyped with
          | @cons _ abstraction arguments parameter parameters bodyType bodyRepresentation bodyParameterType
              abstractionTyped argumentsTyped =>
            cases argumentsTyped
            have channelTypeEquality : channelType = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
            have bodyTypeEquality : bodyType = TypeExpr.arrow TypeExpr.name TypeExpr.proc := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType] using
                bodyParameterType.symm
            subst channelType
            subst bodyType
            cases abstraction with
            | lambda binder body =>
              cases binder with
              | none =>
                cases abstractionTyped with
                | lambda bodyTyped =>
                  simp [isObjectPattern, isObjectPatternList] at object
                  obtain ⟨channelSealed, abstractionSealed⟩ := sealed_binary.mp sealed
                  have bodySealed := sealed_lambda.mp abstractionSealed
                  exact typed_input_congr
                    ⟨canonicalize_isObjectPattern object.1, canonicalize_name_hasSort channelTyped object.1,
                      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _
                        channelSealed⟩
                    ⟨object.2, bodyTyped, bodySealed⟩
                    (typed_canonicalize_name channelTyped object.1 channelSealed)
                    (typed_canonicalize_proc bodyTyped object.2 bodySealed)
              | some binderName => simp [MatchesParameterRepresentation] at bodyRepresentation
            | bvar index => simp [MatchesParameterRepresentation] at bodyRepresentation
            | fvar name => simp [MatchesParameterRepresentation] at bodyRepresentation
            | apply name arguments => simp [MatchesParameterRepresentation] at bodyRepresentation
            | multiLambda arity binders body => simp [MatchesParameterRepresentation] at bodyRepresentation
            | subst body replacement => simp [MatchesParameterRepresentation] at bodyRepresentation
            | collection collectionType elements rest => simp [MatchesParameterRepresentation] at bodyRepresentation
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest elementType membership parameterShape
        elementsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
        rcases parameterShape with ⟨rfl, rfl, rfl⟩
        cases rest with
        | none =>
          simp only [isObjectPattern, Option.isNone_none, Bool.true_and] at object
          have elementsSealed := sealed_collection.mp sealed
          have pointwise := typed_canonicalizeList_procElements elementsTyped object elementsSealed
          have good := good_of_elements elementsTyped object elementsSealed
          have canonicalGood : ∀ element ∈ canonicalizeList elements, Good free bound depth element := by
            rw [canonicalizeList_eq_map]
            intro element member
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            have originalGood := good original originalMember
            exact ⟨canonicalize_isObjectPattern originalGood.object,
              canonicalize_proc_hasSort originalGood.typed originalGood.object,
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping.canonicalize_binderSafeAt _ _
                originalGood.formed⟩
          have congruence := typed_bag_of_forall₂ (relEnv := relEnv) [] (fun _ member => by cases member) good
            pointwise
          have normalized := typed_normalizeBagElements (relEnv := relEnv) canonicalGood
          have collapsed := typed_collapseBag (relEnv := relEnv) (good_of_mem_normalize canonicalGood)
          simp only [List.nil_append] at congruence
          change Chain relEnv free bound TypeExpr.proc depth (.collection .hashBag elements none)
            (collapseBag (normalizeBagElements (canonicalizeList elements)))
          exact .trans _ _ _ congruence (.trans _ _ _ normalized collapsed)
        | some restName => simp [isObjectPattern] at object
      · simp at parameterShape
      · simp at parameterShape

  /-- Pointwise, for the elements of a parallel bag. -/
  theorem typed_canonicalizeList_procElements {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ}
      {processes : List Pattern} (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
      (object : isObjectPatternList processes = true) (sealed : ∀ process ∈ processes, Sealed depth process) :
      List.Forall₂ (Chain relEnv free bound TypeExpr.proc depth) processes (canonicalizeList processes) := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
      simp only [isObjectPatternList, Bool.and_eq_true] at object
      exact .cons (typed_canonicalize_proc processTyped object.1 (sealed _ List.mem_cons_self))
        (typed_canonicalizeList_procElements processesTyped object.2
          (fun process member => sealed process (List.mem_cons_of_mem _ member)))
end

/-! ## Every step of the syntax theory keeps the canonical form -/

/-- An instance of ρ's equation needs no premise evaluator: the equation has no premises. -/
theorem equationInstanceAt_base {base base' : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {fuel : ℕ} {source target : Pattern} (instance_ : EquationInstanceAt base rhoCalc fuel source target) :
    EquationInstanceAt base' rhoCalc fuel source target := by
  cases instance_ with
  | forward member raw matched premises applied =>
    have none := rhoCalc_unconditional _ member
    rw [none] at premises
    cases premises
    exact .forward member raw matched (by rw [none]; exact PremisesAt.nil _) applied
  | reverse member raw matched premises applied =>
    have none := rhoCalc_unconditional _ member
    rw [none] at premises
    cases premises
    exact .reverse member raw matched (by rw [none]; exact PremisesAt.nil _) applied
  | declared member notRaw _ =>
    exact absurd (Mettapedia.OSLF.MeTTaIL.ReferenceStep.equationAligned_parts (rhoCalc_equationsAligned _ member)).1
      (by simp [notRaw])

/-- **A step of the syntax theory keeps the canonical form**, whatever it binds its variables to. -/
theorem canonicalize_eq_of_equationStep {source target : Pattern} (step : EquationStep relEnv rhoCalc source target) :
    canonicalize source = canonicalize target := by
  cases (equationStep_iff_unconditional rhoCalc_unconditional rhoCalc_equationsAligned).mpr step with
  | inContext context generator =>
    exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement.rhoEquationContextStep_canonicalize_eq
      (.core (.inContext context
        (generator.imp (fun ⟨fuel, instance_⟩ => ⟨fuel, equationInstanceAt_base instance_⟩) id)))

/-- **Equivalence in the syntax theory keeps the canonical form.** -/
theorem canonicalize_eq_of_equivalent {source target : Pattern} (equivalent : Equivalent relEnv rhoCalc source target) :
    canonicalize source = canonicalize target := by
  induction equivalent with
  | rel _ _ step => exact canonicalize_eq_of_equationStep step
  | refl => rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **And so does every disciplined equivalence.** -/
theorem canonicalize_eq_of_disciplinedEquivalent {discipline : EquationDiscipline} {source target : Pattern}
    (equivalent : DisciplinedEquivalent relEnv rhoCalc discipline source target) :
    canonicalize source = canonicalize target :=
  canonicalize_eq_of_equivalent equivalent.toEquivalent

/-! ## The typed reading is canonical equality -/

/-- **Formed processes are typed-equivalent exactly when their canonical forms agree.** -/
theorem typedEquivalent_proc_iff {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {first second : Pattern}
    (firstGood : Good free bound depth first) (secondGood : Good free bound depth second) :
    Chain relEnv free bound TypeExpr.proc depth first second ↔ canonicalize first = canonicalize second := by
  constructor
  · exact fun equivalent => canonicalize_eq_of_disciplinedEquivalent equivalent.toDisciplined
  · intro same
    have toCanonical := typed_canonicalize_proc (relEnv := relEnv) firstGood.typed firstGood.object firstGood.formed
    have fromCanonical := typed_canonicalize_proc (relEnv := relEnv) secondGood.typed secondGood.object
      secondGood.formed
    rw [same] at toCanonical
    exact .trans _ _ _ toCanonical (.symm _ _ fromCanonical)

/-- **Formed names are typed-equivalent exactly when their canonical forms agree.** -/
theorem typedEquivalent_name_iff {free : FreeTypeContext} {bound : List TypeExpr} {depth : ℕ} {first second : Pattern}
    (firstFormed : Formed rhoCalc free bound TypeExpr.name (Sealed depth) first)
    (secondFormed : Formed rhoCalc free bound TypeExpr.name (Sealed depth) second) :
    Chain relEnv free bound TypeExpr.name depth first second ↔ canonicalize first = canonicalize second := by
  constructor
  · exact fun equivalent => canonicalize_eq_of_disciplinedEquivalent equivalent.toDisciplined
  · intro same
    have toCanonical := typed_canonicalize_name (relEnv := relEnv) firstFormed.typed firstFormed.object
      firstFormed.formed
    have fromCanonical := typed_canonicalize_name (relEnv := relEnv) secondFormed.typed secondFormed.object
      secondFormed.formed
    rw [same] at toCanonical
    exact .trans _ _ _ toCanonical (.symm _ _ fromCanonical)

/-! ## Sorts and binder metadata of typed terms -/

/-- **ρ's constructors have distinct labels.** -/
theorem rhoCalc_labelDeterministic : LabelDeterministic rhoCalc := by
  intro left right leftMember rightMember sameLabel
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases rightMember with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | simp at sameLabel

/-- **An object of ρ has at most one sort**: its sort is read off its head. -/
theorem sort_unique {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {first second : String}
    (object : isObjectPattern term = true) (firstTyped : HasSort rhoCalc free bound term first)
    (secondTyped : HasSort rhoCalc free bound term second) : first = second := by
  cases term with
  | bvar index =>
    cases firstTyped with
    | bvar firstLookup =>
      cases secondTyped with
      | bvar secondLookup =>
        rw [firstLookup] at secondLookup
        cases secondLookup
        rfl
  | fvar name =>
    cases firstTyped with
    | fvar firstLookup =>
      cases secondTyped with
      | fvar secondLookup =>
        rw [firstLookup] at secondLookup
        cases secondLookup
        rfl
  | apply label arguments =>
    obtain ⟨firstRule, firstMember, firstLabel, -, firstType, -⟩ := hasType_apply_inversion firstTyped
    obtain ⟨secondRule, secondMember, secondLabel, -, secondType, -⟩ := hasType_apply_inversion secondTyped
    have same := rhoCalc_labelDeterministic firstMember secondMember (firstLabel.symm.trans secondLabel)
    subst same
    cases firstType
    cases secondType
    rfl
  | lambda binder body => cases firstTyped
  | multiLambda arity binders body => cases firstTyped
  | subst body replacement => simp [isObjectPattern] at object
  | collection kind elements rest =>
    rcases hasType_collection_inversion firstTyped with ⟨_, impossible, -⟩ |
        ⟨firstRule, _, _, firstMember, firstShape, firstType, -⟩
    · cases impossible
    rcases hasType_collection_inversion secondTyped with ⟨_, impossible, -⟩ |
        ⟨secondRule, _, _, secondMember, secondShape, secondType, -⟩
    · cases impossible
    have category : ∀ {rule : GrammarRule} {parameter : String} {element : TypeExpr}, rule ∈ rhoCalc.terms →
        rule.bareParams = [.simple parameter (.collection kind element)] → rule.category = "Proc" := by
      intro rule parameter element member shape
      simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [TypeExpr.proc, TypeExpr.name, TypeExpr.baseType, TypeExpr.funType, TypeExpr.bag] at shape ⊢
    have firstProc := category firstMember firstShape
    have secondProc := category secondMember secondShape
    injection firstType with firstEq
    injection secondType with secondEq
    rw [firstEq, secondEq, firstProc, secondProc]

mutual
  /-- **A typed name has canonical binder metadata.** -/
  theorem metadata_name {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
      (typed : HasSort rhoCalc free bound name "Name") (object : isObjectPattern name = true) :
      name.hasCanonicalBinderMetadata = true := by
    change HasType rhoCalc free bound name TypeExpr.name at typed
    generalize resultTypeEquality : TypeExpr.name = resultType at typed
    cases typed with
    | bvar lookup => rfl
    | fvar lookup => rfl
    | @constructor bound rule arguments membership notBare argumentsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected representation parameterType argumentTyped
            argumentsTyped =>
          cases argumentsTyped
          have expectedEquality : expected = TypeExpr.proc := by
            simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using parameterType.symm
          subst expected
          simp [isObjectPattern, isObjectPatternList] at object
          simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
            metadata_proc argumentTyped object]
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest elementType membership parameterShape
        elementsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
      · simp at parameterShape
      · simp at parameterShape

  /-- **A typed process has canonical binder metadata**: its only binders are the unnamed ones of its inputs. -/
  theorem metadata_proc {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
      (typed : HasSort rhoCalc free bound process "Proc") (object : isObjectPattern process = true) :
      process.hasCanonicalBinderMetadata = true := by
    change HasType rhoCalc free bound process TypeExpr.proc at typed
    generalize resultTypeEquality : TypeExpr.proc = resultType at typed
    cases typed with
    | bvar lookup => rfl
    | fvar lookup => rfl
    | @constructor bound rule arguments membership notBare argumentsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · cases argumentsTyped
        rfl
      · cases argumentsTyped with
        | @cons _ argument arguments parameter parameters expected representation parameterType argumentTyped
            argumentsTyped =>
          cases argumentsTyped
          have expectedEquality : expected = TypeExpr.name := by
            simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using parameterType.symm
          subst expected
          simp [isObjectPattern, isObjectPatternList] at object
          simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
            metadata_name argumentTyped object]
      · simp [TypeExpr.proc, TypeExpr.baseType] at resultTypeEquality
      · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at notBare
      · cases argumentsTyped with
        | @cons _ channel arguments parameter parameters channelType channelRepresentation channelParameterType
            channelTyped argumentsTyped =>
          cases argumentsTyped with
          | @cons _ payload arguments parameter parameters payloadType payloadRepresentation payloadParameterType
              payloadTyped argumentsTyped =>
            cases argumentsTyped
            have channelTypeEquality : channelType = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
            have payloadTypeEquality : payloadType = TypeExpr.proc := by
              simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using payloadParameterType.symm
            subst channelType
            subst payloadType
            simp [isObjectPattern, isObjectPatternList] at object
            simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
              metadata_name channelTyped object.1, metadata_proc payloadTyped object.2]
      · cases argumentsTyped with
        | @cons _ channel arguments parameter parameters channelType channelRepresentation channelParameterType
            channelTyped argumentsTyped =>
          cases argumentsTyped with
          | @cons _ abstraction arguments parameter parameters bodyType bodyRepresentation bodyParameterType
              abstractionTyped argumentsTyped =>
            cases argumentsTyped
            have channelTypeEquality : channelType = TypeExpr.name := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using channelParameterType.symm
            have bodyTypeEquality : bodyType = TypeExpr.arrow TypeExpr.name TypeExpr.proc := by
              simpa [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType] using
                bodyParameterType.symm
            subst channelType
            subst bodyType
            cases abstraction with
            | lambda binder body =>
              cases binder with
              | none =>
                cases abstractionTyped with
                | lambda bodyTyped =>
                  simp [isObjectPattern, isObjectPatternList] at object
                  simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
                    metadata_name channelTyped object.1, metadata_proc bodyTyped object.2]
              | some binderName => simp [MatchesParameterRepresentation] at bodyRepresentation
            | bvar index => simp [MatchesParameterRepresentation] at bodyRepresentation
            | fvar name => simp [MatchesParameterRepresentation] at bodyRepresentation
            | apply name arguments => simp [MatchesParameterRepresentation] at bodyRepresentation
            | multiLambda arity binders body => simp [MatchesParameterRepresentation] at bodyRepresentation
            | subst body replacement => simp [MatchesParameterRepresentation] at bodyRepresentation
            | collection collectionType elements rest => simp [MatchesParameterRepresentation] at bodyRepresentation
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest elementType membership parameterShape
        elementsTyped =>
      simp [rhoCalc] at membership
      rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp at parameterShape
      · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
      · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
        rcases parameterShape with ⟨rfl, rfl, rfl⟩
        simp only [isObjectPattern, Bool.and_eq_true] at object
        simp [Pattern.hasCanonicalBinderMetadata, metadata_elements elementsTyped object.2]
      · simp at parameterShape
      · simp at parameterShape

  /-- Pointwise, for the elements of a parallel bag. -/
  theorem metadata_elements {free : FreeTypeContext} {bound : List TypeExpr} {processes : List Pattern}
      (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
      (object : isObjectPatternList processes = true) : Pattern.hasCanonicalBinderMetadataList processes = true := by
    cases typed with
    | nil => rfl
    | cons processTyped processesTyped =>
      simp only [isObjectPatternList, Bool.and_eq_true] at object
      simp [Pattern.hasCanonicalBinderMetadataList, metadata_proc processTyped object.1,
        metadata_elements processesTyped object.2]
end

end Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations
