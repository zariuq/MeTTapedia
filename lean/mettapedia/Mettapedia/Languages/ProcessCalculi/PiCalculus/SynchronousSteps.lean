import Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousStepReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSteps

/-!
# Synchronous π's restriction blocks and steps

`piSyncCalc` is a calculus with restriction and replication in the sense of the restriction-block theory, with π's
blocks: parallel composition is a bare bag of processes with inaction as unit, `PiNu` binds a name over a process,
`PiRep` replicates a process, its declared laws are exactly those of restriction and of replication, and its other
constructors take names, processes and abstractions of processes over names (`piSyncReplicationLanguage`). Its
canonical form is the replication theory's (`canonR`), sound at every sort and complete on object terms.

Its steps are reactions (`piSyncReactions`): an input and an output on its channel followed by a process leave the
reception and the process that followed the output. A replicated process takes part through the copy its unfolding
puts beside it. A step reaches a block with a redex at its front (`step_block`), so some unfolding of its canonical
form steps to an equivalent contractum (`simulation`), and so does a presentation of the canonical form (`presented`).

Components read alike to the canonical forms of a redex's parts are an input and an output on the same channel, the
input's body and the output's continuation read canonically as the originals' (`shown_input`, `shown_output`), so they
react to an equivalent reception beside an equivalent continuation (`Redex.alike`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSteps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute_single_eq_instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_lambda)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous (piSyncCalc piSyncOutputRule PiSyncRawStep)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (canonP_name canonR_listener canonArgument_var
  recanon_eq_of_alike)

/-! ## Synchronous π is a calculus with restriction and replication -/

/-- The parallel constructor declares the bag monoid with inaction as its unit. -/
theorem piSyncBagPresentation : BagPresentation piSyncCalc piSyncCalc.terms[1] (some "PiNil") where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [piCalc] at present
    · exact False.elim (different rfl)
    all_goals
      simp only [piCalc, piSyncOutputRule, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl
      all_goals rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨piSyncCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- The parameters of synchronous π's constructors, by label. -/
theorem params_of_label {rule : GrammarRule} (member : rule ∈ piSyncCalc.terms) :
    (rule.label = "PiInp" →
      rule.params = [.simple "x" (.base "Name"), .abstraction "body" (.arrow (.base "Name") (.base "Proc"))]) ∧
    (rule.label = "PiRep" → rule.params = [.simple "p" (.base "Proc")]) ∧
    (rule.label = "PiOutK" →
      rule.params = [.simple "x" (.base "Name"), .simple "z" (.base "Name"), .simple "k" (.base "Proc")]) := by
  simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [piCalc, piSyncOutputRule]

theorem category_of_member {rule : GrammarRule} (member : rule ∈ piSyncCalc.terms) : rule.category = "Proc" := by
  simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Synchronous π declares exactly the laws of restriction and of replication. -/
theorem piSyncCalc_equations : piSyncCalc.equations = replicationBlockLaws piRepBlock := rfl

/-- **Synchronous π is a calculus with restriction and replication.** -/
instance piSyncReplicationLanguage : ReplicationLanguage piSyncCalc piRepBlock where
  bag := ⟨piSyncCalc.terms[1], ParallelBag.ofBare (piSyncBagPresentation.asBare rfl), rfl⟩
  equations := rfl
  restrictAuthored := ⟨piSyncCalc.terms[4], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [piCalc, piSyncOutputRule]
  unitShape := by
    intro rule member labelIs
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [piCalc, piSyncOutputRule]
  multisetShape := by
    intro rule member listed
    simp at listed
  emptyUnitShape := by
    intro label listed
    simp at listed
  emptyUnitAuthored := by
    intro label listed
    simp at listed
  labelsUnique := by decide
  params := by
    intro rule member notBare _ parameter present
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [piCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [piCalc, piSyncOutputRule, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [piCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [piCalc, piSyncOutputRule, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨piSyncCalc.terms[5], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [piSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [piCalc, piSyncOutputRule]
  replicateFresh := by decide

/-- **Synchronous π's signature is a restriction-block signature.** -/
instance piSyncBlockSignature : BlockSignature piSyncCalc piBlock := piSyncReplicationLanguage.toBlockSignature

/-! ## A communication -/

/-- **A synchronous communication**: an input on a channel; an output of a datum on it, followed by a process. -/
structure Redex where
  channel : Pattern
  body : Pattern
  datum : Pattern
  continuation : Pattern

namespace Redex

def listener (redex : Redex) : Pattern := .apply "PiInp" [redex.channel, .lambda none redex.body]

def output (redex : Redex) : Pattern := .apply "PiOutK" [redex.channel, redex.datum, redex.continuation]

/-- The reception, and the process after the output. -/
def result (redex : Redex) : List Pattern := [instantiateBVar redex.datum redex.body, redex.continuation]

end Redex

theorem listener_parts {free : FreeTypeContext} {bound : List TypeExpr} {channel body : Pattern}
    {binder : Option String}
    (typed : HasType piSyncCalc free bound (.apply "PiInp" [channel, .lambda binder body]) (.base "Proc")) :
    HasType piSyncCalc free bound channel (.base "Name") ∧
      HasType piSyncCalc free (.base "Name" :: bound) body (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).1 labelIs.symm] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
      cases rest with
      | cons _ bodyType bodyTyped _ =>
          simp only [parameterType?, Option.some.injEq] at channelType bodyType
          subst channelType bodyType
          cases bodyTyped with
          | lambda inner => exact ⟨channelTyped, inner⟩

theorem output_parts {free : FreeTypeContext} {bound : List TypeExpr} {channel datum continuation : Pattern}
    (typed : HasType piSyncCalc free bound (.apply "PiOutK" [channel, datum, continuation]) (.base "Proc")) :
    HasType piSyncCalc free bound channel (.base "Name") ∧ HasType piSyncCalc free bound datum (.base "Name") ∧
      HasType piSyncCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).2.2 labelIs.symm] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
      cases rest with
      | cons _ datumType datumTyped rest =>
          cases rest with
          | cons _ continuationType continuationTyped _ =>
              simp only [parameterType?, Option.some.injEq] at channelType datumType continuationType
              subst channelType datumType continuationType
              exact ⟨channelTyped, datumTyped, continuationTyped⟩

/-- **What a communication leaves are processes.** -/
theorem Redex.result_members {free : FreeTypeContext} {bound : List TypeExpr} {redex : Redex}
    (listenerTyped : HasType piSyncCalc free bound redex.listener (.base "Proc"))
    (outputTyped : HasType piSyncCalc free bound redex.output (.base "Proc")) :
    Members piSyncCalc piBlock free bound redex.result := by
  obtain ⟨-, bodyTyped⟩ := listener_parts listenerTyped
  obtain ⟨-, datumTyped, continuationTyped⟩ := output_parts outputTyped
  have received : HasType piSyncCalc free bound (instantiateBVar redex.datum redex.body) (.base "Proc") := by
    rw [← substitute_single_eq_instantiateBVar]
    refine HasType.substituteBoundOnSupport bodyTyped _ fun index type _ lookup => ?_
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
        subst lookup
        exact datumTyped
    | succ index => exact HasType.bvar (by simpa using lookup)
  intro element member
  simp only [Redex.result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact received
  · exact continuationTyped

/-- **What a communication leaves uses the variables of the input and the output.** -/
theorem Redex.freeIn_result {redex : Redex} {index : Nat} {element : Pattern} (member : element ∈ redex.result)
    (free : FreeIn index element) : FreeIn index redex.listener ∨ FreeIn index redex.output := by
  simp only [Redex.result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rcases freeIn_instantiate free with inBody | inDatum
    · exact .inl (freeIn_apply.mpr ⟨.lambda none redex.body, by simp, freeIn_lambda.mpr inBody⟩)
    · exact .inr (freeIn_apply.mpr ⟨redex.datum, by simp, inDatum⟩)
  · exact .inr (freeIn_apply.mpr ⟨redex.continuation, by simp, free⟩)

theorem binder_of_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {channel body : Pattern}
    {binder : Option String}
    (typed : HasType piSyncCalc free bound (.apply label [channel, .lambda binder body]) (.base "Proc"))
    (object : isObjectPattern (.apply label [channel, .lambda binder body]) = true) : binder = none := by
  have canonical := (metadata_of_typed (block := piBlock) _ typed object).1 ⟨_, rfl⟩
  simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_true,
    Bool.and_eq_true, Option.isNone_iff_eq_none] at canonical
  exact canonical.2.1

/-- The two selected members of a bag, first. -/
theorem perm_two (elements : List Pattern) (first : Nat) (firstInside : first < elements.length) (second : Nat)
    (secondInside : second < (elements.eraseIdx first).length) :
    elements.Perm (elements[first] :: (elements.eraseIdx first)[second] ::
      (elements.eraseIdx first).eraseIdx second) :=
  (perm_getElem_eraseIdx elements first firstInside).trans
    ((perm_getElem_eraseIdx (elements.eraseIdx first) second secondInside).cons _)

/-! ## Renaming a redex -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

namespace Redex

/-- Rename a redex's variables. -/
def rename (relabel : Nat → Nat) (redex : Redex) : Redex :=
  ⟨Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel redex.channel,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename (liftIndex 1 relabel) redex.body,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel redex.datum,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel redex.continuation⟩

theorem rename_listener (relabel : Nat → Nat) (redex : Redex) :
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel redex.listener = (redex.rename relabel).listener := by
  simp only [listener, rename_apply, List.map_cons, List.map_nil, rename_lambda]
  rfl

theorem rename_output (relabel : Nat → Nat) (redex : Redex) :
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel redex.output = (redex.rename relabel).output := by
  simp [output, Redex.rename, rename_apply]

theorem rename_result (relabel : Nat → Nat) (redex : Redex) :
    redex.result.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) = (redex.rename relabel).result := by
  simp [result, Redex.rename, rename_instantiate]

theorem listener_ne_output (first second : Redex) : first.listener ≠ second.output := by
  simp [listener, output]

end Redex

/-- **A redex in a bag communicates**, wherever its input and output stand. -/
theorem Redex.step_at (redex : Redex) {elements : List Pattern} (first : Nat) (firstInside : first < elements.length)
    (second : Nat) (secondInside : second < (elements.eraseIdx first).length)
    (listenerAt : elements[first] = redex.listener) (outputAt : (elements.eraseIdx first)[second] = redex.output) :
    PiSyncRawStep (.collection .hashBag elements none)
      (.collection .hashBag (redex.result ++ (elements.eraseIdx first).eraseIdx second) none) := by
  have stepped := PiSyncRawStep.comm (tail := none) first firstInside second secondInside redex.channel none
    redex.body redex.datum redex.continuation (by rw [listenerAt]; rfl) (by rw [outputAt]; rfl)
  simpa [Redex.result] using stepped

theorem Redex.listener_atom (redex : Redex) : decompose piBlock redex.listener = Prenex.atom redex.listener := by
  apply decompose_atom
  · simp [Redex.listener]
  · intro binder body equal
    simp [Redex.listener] at equal
  · intro elements equal
    simp [Redex.listener] at equal
  · intro label argument _ listed
    simp at listed

theorem Redex.output_atom (redex : Redex) : decompose piBlock redex.output = Prenex.atom redex.output := by
  apply decompose_atom
  · simp [Redex.output]
  · intro binder body equal
    simp [Redex.output] at equal
  · intro elements equal
    simp [Redex.output] at equal
  · intro label argument _ listed
    simp at listed

/-- **A typed object name is a variable**: synchronous π has no constructor of names. -/
theorem name_cases {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType piSyncCalc free bound name (.base "Name")) (object : isObjectPattern name = true) :
    (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name' := by
  cases name with
  | bvar index => exact .inl ⟨index, rfl⟩
  | fvar name' => exact .inr ⟨name', rfl⟩
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | apply =>
      obtain ⟨rule, member, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      exact absurd (typeIs.trans (category_of_member member)) (by decide)
  | collection =>
      have sortIs := (piSyncBlockSignature.bag_members typed).2.1
      exact absurd sortIs (by simp)

theorem Redex.objects_of {redex : Redex} (listenerObject : isObjectPattern redex.listener = true)
    (outputObject : isObjectPattern redex.output = true) : ∀ element ∈ redex.result, isObjectPattern element = true := by
  have bodyObject : isObjectPattern redex.body = true := by
    simp only [Redex.listener, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at listenerObject
    exact listenerObject.2
  simp only [Redex.output, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at outputObject
  obtain ⟨-, datumObject, continuationObject⟩ := outputObject
  have received : isObjectPattern (instantiateBVar redex.datum redex.body) = true := by
    rw [← substitute_single_eq_instantiateBVar]
    refine isObject_substitute _ (fun index => ?_) bodyObject
    cases index with
    | zero => exact datumObject
    | succ => rfl
  intro element member
  simp only [Redex.result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact received
  · exact continuationObject

/-! ## The canonical forms of a redex's parts -/

/-- An application of three arguments reads canonically as one component with canonical arguments. -/
theorem canonP_triple (label : String) (first second third : Pattern) :
    canonP piRepBlock (.apply label [first, second, third]) =
      Prenex.atom (.apply label (List.zipWith (argumentOf piRepBlock label) [first, second, third]
        (canonsP piRepBlock [first, second, third]))) :=
  canonP_apply (by simp) (by simp) (by simp) (by simp)

theorem canonR_output {channel datum continuation : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name')
    (datumName : (∃ index, datum = .bvar index) ∨ ∃ name', datum = .fvar name') :
    canonR piRepBlock (.apply "PiOutK" [channel, datum, continuation]) =
      .apply "PiOutK" [channel, datum, canonR piRepBlock continuation] := by
  unfold canonR
  rw [canonP_triple]
  simp [canonsP, canonP_name channelName, canonP_name datumName, argumentOf]
  rfl

/-- **A typed argument read canonically is equivalent to it.** -/
theorem canonArgument_canonicalOf_equivalent {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {argument : Pattern} {sort : String}
    (typed : HasType piSyncCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc
      (canonArgument (canonicalOf piRepBlock) argument) argument := by
  cases argument with
  | lambda => cases typed
  | multiLambda => cases typed
  | bvar => exact .refl _
  | fvar => exact .refl _
  | subst => exact .refl _
  | apply => exact .symm _ _ (canonicalOf_sound (block := piRepBlock) context typed).2.toEquationEquiv
  | collection => exact .symm _ _ (canonicalOf_sound (block := piRepBlock) context typed).2.toEquationEquiv

/-! ## Components alike to the canonical parts -/

/-- **A component read again as an input reads is an input on that channel**, its body read canonically as that
input's body. -/
theorem shown_input {free : FreeTypeContext} {bound : List TypeExpr} {shown channel reading : Pattern}
    (shownTyped : HasType piSyncCalc free bound shown (.base "Proc")) (shownObject : isObjectPattern shown = true)
    (read : recanon piRepBlock shown = .apply "PiInp" [channel, .lambda none reading]) :
    ∃ body, shown = .apply "PiInp" [channel, .lambda none body] ∧ canonicalOf piRepBlock body = reading := by
  cases shown with
  | apply label arguments =>
      by_cases isRestrict : label = piRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp at read
      rw [recanon_apply_other isRestrict (by simp)] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthTwo : arguments.length = 2 := by simpa using congrArg List.length mapped
      obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp lengthTwo
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨channelIs, bodyIs⟩ := mapped
      obtain ⟨rule, member, labelIs, -, -, argumentsTyped⟩ := hasType_apply_inversion shownTyped
      rw [(params_of_label member).1 labelIs.symm] at argumentsTyped
      cases argumentsTyped with
      | cons _ channelType channelTyped rest =>
          cases rest with
          | cons representation bodyType bodyTyped _ =>
              simp only [parameterType?, Option.some.injEq] at channelType bodyType
              subst channelType bodyType
              obtain ⟨inner, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
              have firstObject : isObjectPattern first = true := by
                simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at shownObject
                exact shownObject.1
              rw [canonArgument_var (name_cases channelTyped firstObject)] at channelIs
              subst channelIs
              simp only [canonArgument, Pattern.lambda.injEq] at bodyIs
              exact ⟨inner, rfl, bodyIs.2⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases shownTyped

/-- **A component read again as an output reads is an output of that datum on that channel**, its continuation read
canonically as that output's continuation. -/
theorem shown_output {free : FreeTypeContext} {bound : List TypeExpr} {shown channel datum reading : Pattern}
    (shownTyped : HasType piSyncCalc free bound shown (.base "Proc")) (shownObject : isObjectPattern shown = true)
    (read : recanon piRepBlock shown = .apply "PiOutK" [channel, datum, reading]) :
    ∃ continuation, shown = .apply "PiOutK" [channel, datum, continuation] ∧
      canonArgument (canonicalOf piRepBlock) continuation = reading := by
  cases shown with
  | apply label arguments =>
      by_cases isRestrict : label = piRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp at read
      rw [recanon_apply_other isRestrict (by simp)] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthThree : arguments.length = 3 := by simpa using congrArg List.length mapped
      obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp lengthThree
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨channelIs, datumIs, continuationIs⟩ := mapped
      obtain ⟨channelTyped, datumTyped, -⟩ := output_parts shownTyped
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at shownObject
      rw [canonArgument_var (name_cases channelTyped shownObject.1)] at channelIs
      rw [canonArgument_var (name_cases datumTyped shownObject.2.1)] at datumIs
      subst channelIs datumIs
      exact ⟨third, rfl, continuationIs⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases shownTyped

/-- **Components read alike to the canonical forms of a redex's parts are a redex** whose reception and continuation
are equivalent to the original ones. -/
theorem Redex.alike {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound) (redex : Redex)
    (shown : List Pattern) (partsMembers : Members piSyncCalc piBlock free bound [redex.listener, redex.output])
    (partsObjects : ∀ part ∈ [redex.listener, redex.output], isObjectPattern part = true)
    (shownMembers : Members piSyncCalc piBlock free bound shown)
    (shownObjects : ∀ part ∈ shown, isObjectPattern part = true)
    (related : List.Forall₂ (fun part original => AlikeR piRepBlock part (canonR piRepBlock original)) shown
      [redex.listener, redex.output]) :
    ∃ redex' : Redex, [redex'.listener, redex'.output] = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc) redex'.result redex.result := by
  obtain ⟨channel, body, datum, continuation⟩ := redex
  cases related with
  | cons listenerAlike rest =>
      cases rest with
      | cons outputAlike last =>
          cases last
          rename_i listenerShown outputShown
          have listenerTyped := partsMembers (Redex.listener ⟨channel, body, datum, continuation⟩) (by simp)
          have outputTyped := partsMembers (Redex.output ⟨channel, body, datum, continuation⟩) (by simp)
          have listenerObject := partsObjects (Redex.listener ⟨channel, body, datum, continuation⟩) (by simp)
          have outputObject := partsObjects (Redex.output ⟨channel, body, datum, continuation⟩) (by simp)
          simp only [Redex.listener, Redex.output] at listenerTyped outputTyped listenerObject outputObject
          obtain ⟨channelTyped, bodyTyped⟩ := listener_parts listenerTyped
          obtain ⟨-, datumTyped, continuationTyped⟩ := output_parts outputTyped
          simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at listenerObject
          simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at outputObject
          have channelName := name_cases channelTyped listenerObject.1
          have datumName := name_cases datumTyped outputObject.2.1
          have bodyObject : isObjectPattern body = true := listenerObject.2
          -- the exposed input
          have listenerRead := recanon_eq_of_alike listenerAlike
          simp only [Redex.listener] at listenerRead
          rw [canonR_listener channelName, recanon_apply_other (by simp) (by simp)] at listenerRead
          simp only [List.map_cons, List.map_nil] at listenerRead
          rw [canonArgument_var channelName] at listenerRead
          simp only [canonArgument] at listenerRead
          have listenerShownTyped := shownMembers listenerShown (by simp)
          have listenerShownObject := shownObjects listenerShown (by simp)
          obtain ⟨body', rfl, bodyRead⟩ := shown_input listenerShownTyped listenerShownObject listenerRead
          -- the exposed output
          have outputRead := recanon_eq_of_alike outputAlike
          simp only [Redex.output] at outputRead
          rw [canonR_output channelName datumName, recanon_apply_other (by simp) (by simp)] at outputRead
          simp only [List.map_cons, List.map_nil] at outputRead
          rw [canonArgument_var channelName, canonArgument_var datumName] at outputRead
          have outputShownTyped := shownMembers outputShown (by simp)
          have outputShownObject := shownObjects outputShown (by simp)
          obtain ⟨continuation', rfl, continuationRead⟩ := shown_output outputShownTyped outputShownObject outputRead
          refine ⟨⟨channel, body', datum, continuation'⟩, rfl, ?_⟩
          -- the bodies are equivalent, and stay so once the datum is received
          obtain ⟨-, body'Typed⟩ := listener_parts listenerShownTyped
          obtain ⟨-, -, continuation'Typed⟩ := output_parts outputShownTyped
          have body'Object : isObjectPattern body' = true := by
            simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at listenerShownObject
            exact listenerShownObject.2
          have bodyContext := context.cons "Name"
          have toCanonical := (canonicalOf_sound (block := piRepBlock) bodyContext body'Typed).2.toEquationEquiv
          obtain ⟨canonRTyped, toCanonR⟩ := canonR_sound (block := piRepBlock) bodyContext bodyTyped
          have canonRCanonical := (canonicalOf_sound (block := piRepBlock) bodyContext canonRTyped).2.toEquationEquiv
          rw [bodyRead] at toCanonical
          have chain : EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc body' body :=
            .trans _ _ _ toCanonical (.trans _ _ _ (.symm _ _ canonRCanonical) (.symm _ _ toCanonR.toEquationEquiv))
          have datumObject : isObjectPattern datum = true := outputObject.2.1
          -- the continuations are equivalent
          obtain ⟨continuationCanonTyped, toContinuationCanon⟩ :=
            canonR_sound (block := piRepBlock) context continuationTyped
          have continued : EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc continuation'
              continuation := by
            have shownSide := canonArgument_canonicalOf_equivalent context continuation'Typed
            have originalSide := canonArgument_canonicalOf_equivalent context continuationCanonTyped
            rw [continuationRead] at shownSide
            exact .trans _ _ _ (.symm _ _ shownSide)
              (.trans _ _ _ originalSide (.symm _ _ toContinuationCanon.toEquationEquiv))
          exact .cons (sortedEquiv_instantiate_replication (block := piRepBlock) context datumTyped datumObject
            body'Typed bodyTyped body'Object bodyObject chain) (.cons continued .nil)

/-! ## Synchronous π's reactions -/

/-- **Synchronous π's reactions, with replication**: an input and an output on its channel, followed by a process. -/
abbrev piSyncReactions : ReplicationReactions piSyncCalc piRepBlock PiSyncRawStep where
  Redex := Redex
  parts redex := [redex.listener, redex.output]
  result := Redex.result
  rename := Redex.rename
  parts_rename relabel redex := by simp [Redex.rename_listener, Redex.rename_output]
  result_rename relabel redex := (Redex.rename_result relabel redex).symm
  canonicalAtoms redex part member _ _ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [Redex.listener, canonR, PrenexForm.canonP_pair]
      rfl
    · simp only [Redex.output, canonR, canonP_triple]
      rfl
  plain redex part member _ _ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [Redex.listener, canonR, PrenexForm.canonP_pair]
      rfl
    · simp only [Redex.output, canonR, canonP_triple]
      rfl
  arity := 2
  arity_le redex := by simp
  result_members redex members := Redex.result_members (members _ (by simp)) (members _ (by simp))
  result_objects redex objects := Redex.objects_of (objects _ (by simp)) (objects _ (by simp))
  freeIn_result := by
    intro redex index element member free
    rcases Redex.freeIn_result member free with inListener | inOutput
    · exact ⟨_, by simp, inListener⟩
    · exact ⟨_, by simp, inOutput⟩
  alike context redex shown members objects shownMembers shownObjects related :=
    Redex.alike context redex shown members objects shownMembers shownObjects related
  react := by
    intro free bound redex components rest permutation members _
    simp only [List.cons_append, List.nil_append] at permutation
    have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
    have listenerMember : redex.listener ∈ components := permutation.mem_iff.mpr (by simp)
    obtain ⟨first, firstInside, firstAt⟩ := List.getElem_of_mem listenerMember
    have outputMember : redex.output ∈ components.eraseIdx first := by
      have inComponents : redex.output ∈ components := permutation.mem_iff.mpr (by simp)
      rcases List.mem_cons.mp ((perm_getElem_eraseIdx components first firstInside).mem_iff.mp inComponents) with
        same | other
      · rw [firstAt] at same
        exact absurd same.symm (Redex.listener_ne_output _ _)
      · exact other
    obtain ⟨second, secondInside, secondAt⟩ := List.getElem_of_mem outputMember
    refine ⟨.collection .hashBag (redex.result ++ (components.eraseIdx first).eraseIdx second) none, ?_, ?_⟩
    · rw [body_of_long long]
      exact redex.step_at first firstInside second secondInside firstAt secondAt
    · have twoPerm := perm_two components first firstInside second secondInside
      rw [firstAt, secondAt] at twoPerm
      have restPerm : ((components.eraseIdx first).eraseIdx second).Perm rest :=
        ((twoPerm.symm.trans permutation).cons_inv).cons_inv
      have contractumMembers : Members piSyncCalc piBlock free bound
          (redex.result ++ (components.eraseIdx first).eraseIdx second) := by
        intro element member
        rcases List.mem_append.mp member with inResult | inRest
        · exact Redex.result_members (members _ listenerMember) (members _ (permutation.mem_iff.mpr (by simp)))
            element inResult
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
        ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ (restPerm.append_left redex.result))
  restrict stepped := .res none stepped

/-- **A step is a reaction between two components of a block**, up to synchronous π's static theory. -/
theorem step_block {source target : Pattern} (step : PiSyncRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType piSyncCalc free bound source (.base "Proc") → isObjectPattern source = true →
        ∃ count redex rest, ReplicationStepAt piSyncReactions free bound source target count redex rest := by
  induction step with
  | @comm elements tail i hi j hj channel binder body datum continuation input output =>
      intro free bound _ typed object
      cases bag_tail_none object
      have members := members_of_bag (block := piBlock) typed
      have objects := bag_objects object
      have inputTyped := members _ (List.getElem_mem hi)
      have inputObject := objects _ (List.getElem_mem hi)
      rw [input] at inputTyped inputObject
      cases binder_of_typed inputTyped inputObject
      let redex : Redex := ⟨channel, body, datum, continuation⟩
      have permutation := perm_two elements i hi j hj
      rw [input, output] at permutation
      exact ⟨0, redex, (elements.eraseIdx i).eraseIdx j,
        ReactsAt.ofPerm typed members objects permutation (.refl _)⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := piBlock) typed
      have objects := bag_objects object
      obtain ⟨count, redex, rest, stepBlock⟩ :=
        recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      exact ⟨count, redex, _, ReactsAt.inBag i hi (piSyncReactions.result_members redex) typed objects stepBlock⟩
  | @res binder source target inner recurse =>
      intro free bound context typed object
      cases restriction_binder (block := piBlock) typed
      have bodyTyped := (piSyncBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨count, redex, rest, stepBlock⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      exact ⟨count + 1, redex, rest, ReactsAt.restrict stepBlock⟩

/-- **A step of a process is matched by a step of an unfolding of its canonical form**, within twice the ceiling read
off that form, to an equivalent contractum. -/
theorem simulation {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : PiSyncRawStep source target)
    (typed : HasType piSyncCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin piRepBlock (2 * ceilingOf piRepBlock (canonP piRepBlock source))
        (canonP piRepBlock source) unfolded ∧
      ∃ target', PiSyncRawStep (unfolded.toPattern piBlock) target' ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_simulation piSyncReactions context reached typed object

/-- **A step of a process is matched by a step of a presentation of its canonical form**, to an equivalent
contractum: within two unfoldings when every replicated component of the canonical form copies one component. -/
theorem presented {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : PiSyncRawStep source target)
    (typed : HasType piSyncCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ shown ∈ replicationPresentations piRepBlock 2 (canonR piRepBlock source), ∃ target',
      PiSyncRawStep shown target' ∧ EquationEquiv (engineBasePremises RelationEnv.empty) piSyncCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_presented piSyncReactions context reached typed object

/-- **A step keeps a typed object process a typed object.** -/
theorem typed_of_raw {source target : Pattern} (step : PiSyncRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType piSyncCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType piSyncCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @comm elements tail i hi j hj channel binder body datum continuation input output =>
      intro free bound typed object
      have members := members_of_bag (block := piBlock) typed
      have objects := bag_objects object
      have inputTyped := members _ (List.getElem_mem hi)
      have inputObject := objects _ (List.getElem_mem hi)
      have outputTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have outputObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [input] at inputTyped inputObject
      rw [output] at outputTyped outputObject
      cases binder_of_typed inputTyped inputObject
      let redex : Redex := ⟨channel, body, datum, continuation⟩
      have resultMembers := Redex.result_members (redex := redex) inputTyped outputTyped
      have resultObjects := Redex.objects_of (redex := redex) inputObject outputObject
      have contractumMembers : Members piSyncCalc piBlock free bound
          (redex.result ++ (elements.eraseIdx i).eraseIdx j) := by
        intro element member
        rcases List.mem_append.mp member with inResult | inRest
        · exact resultMembers element inResult
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      show isObjectPattern (.collection .hashBag (redex.result ++ (elements.eraseIdx i).eraseIdx j) none) = true
      rw [isObject_bag]
      intro element member
      rcases List.mem_append.mp member with inResult | inRest
      · exact resultObjects element inResult
      · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @par elements tail i hi target inner recurse =>
      intro free bound typed object
      have members := members_of_bag (block := piBlock) typed
      have objects := bag_objects object
      obtain ⟨targetTyped, targetObject⟩ :=
        recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      have contractumMembers : Members piSyncCalc piBlock free bound (target :: elements.eraseIdx i) := by
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact targetTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      rw [isObject_bag]
      intro element member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact targetObject
      · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
      intro free bound typed object
      have bodyTyped := (piSyncBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨targetTyped, targetObject⟩ := recurse bodyTyped bodyObject
      exact ⟨restricts_typed (block := piBlock) 1 (by simpa [Prenex.restricts] using targetTyped),
        by rw [isObject_restriction]; exact targetObject⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSteps
