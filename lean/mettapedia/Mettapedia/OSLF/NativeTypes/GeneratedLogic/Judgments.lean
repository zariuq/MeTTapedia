import Mettapedia.OSLF.NativeTypes.GeneratedLogic.OpenTerms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Judgments at the front door: `Γ ⊢ t : φ`, `φ ⊑ ψ`, inhabitation, Σ and Π

Each judgment has a front-door entry whose answers carry evidence, and a soundness theorem for each answer.

- **Fibres** (`Fibre`): the closed values of a type, listed completely. A sort whose constructors are all constants
  has one in an equation-free language (`constantFibre`).
- **The open judgment** `Γ ⊢ t : φ` (`askOpen`): over complete fibres it is the front door's verdict at each
  instance (`openHolds_iff_instances`), so it is decided there; otherwise a closed term is judged at itself, and a
  valuation that the front door types refutes the judgment at its instance (`askOpen_proved`, `askOpen_refuted`).
- **Entailment** `φ ⊑ ψ` at a type (`Entails`) is the open judgment of a variable of the type at `dual φ ∨ ψ`
  (`entails_iff_openHolds`). It is proved by a finite-model certificate, for an existential premise and a universal
  conclusion (`entailsBy_sound`), or by the open judgment, and refuted by a separating value (`askEntails_proved`,
  `askEntails_refuted`).
- **Inhabitation** (`Inhabited`): a witness the front door proves is of the type and satisfies the formula, or
  emptiness as entailment of falsity (`askInhabited_proved`, `askInhabited_refuted`).
- **Σ and Π over a type** of a family of formulas indexed by its values (`SigmaHolds`, `PiHolds`): over a complete
  fibre, the disjunction and the conjunction of the family (`sigmaHolds_iff`, `piHolds_iff`), decided by the front
  door; otherwise proved by a witness, or refuted by a counter-value (`askSigma_*`, `askPi_*`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.FiniteModels (Certificate Signature value)
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext isObjectPattern HasType
  ArgumentsHaveTypes UsesBareCollection)

/-! ## Fibres -/

/-- **A fibre of a type**: a list of closed values containing every closed value of the type, each of the type. -/
structure Fibre (T : NativeStructure Pattern) (type : TypeExpr) where
  values : List Pattern
  complete : ∀ value, ClosedValue value → T.typed value type → value ∈ values
  sound : ∀ value ∈ values, ClosedValue value ∧ T.typed value type

/-- **A sort whose constructors are all constants**, declared with no builtin carrier, whose atoms would be terms of
it. -/
def constantSort (language : LanguageDef) (sort : String) : Bool :=
  (language.types.all fun declaration => declaration.name != sort || !CarrierTyping.acceptsAtoms declaration.carrier) &&
    language.terms.all fun rule => rule.category != sort || rule.params.isEmpty

/-- The constants of a sort. -/
def constants (language : LanguageDef) (sort : String) : List Pattern :=
  (language.terms.filter fun rule => rule.category == sort).map fun rule => .apply rule.label []

theorem params_of_constantSort {language : LanguageDef} {sort : String} (constant : constantSort language sort = true)
    {rule : GrammarRule} (member : rule ∈ language.terms) (category : rule.category = sort) : rule.params = [] := by
  have := List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp constant).2 rule member
  simp only [category, bne_self_eq_false, Bool.false_or, List.isEmpty_iff] at this
  exact this

/-- A constant sort has no builtin atoms. -/
theorem not_builtinAtom_of_constantSort {language : LanguageDef} {sort : String}
    (constant : constantSort language sort = true) {atom : String} :
    ¬ Mettapedia.GSLT.LanguageDef.CarrierWellSorted.BuiltinAtomHasType language atom (.base sort) := by
  rintro ⟨declaration, member, same, accepts⟩
  have declared := List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp constant).1 declaration member
  have named : declaration.name = sort := by injection same with same; exact same.symm
  simp [named, CarrierTyping.acceptsAtoms_of_accepts accepts] at declared

/-- **A closed typed term of a constant sort is one of its constants.** -/
theorem mem_constants_of_carrierTyped {language : LanguageDef} {sort : String}
    (constant : constantSort language sort = true) {term : Pattern} (wellSorted : CarrierTyped language (.base sort) term) :
    term ∈ constants language sort := by
  obtain ⟨typed, -, object, -⟩ := wellSorted
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | builtinAtom atom => exact absurd atom (not_builtinAtom_of_constantSort constant)
  | @constructor _ rule arguments member _ typedArguments =>
    have noParams := params_of_constantSort constant member rfl
    rw [noParams] at typedArguments
    cases typedArguments
    exact List.mem_map.mpr ⟨rule, List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩
  | subst => simp [isObjectPattern] at object
  | @collectionConstructor _ rule _ _ _ _ _ member bare _ =>
    have noParams := params_of_constantSort constant member rfl
    unfold GrammarRule.bareParams at bare
    split at bare
    · rw [noParams] at bare
      cases bare
    · cases bare

/-- **The fibre of a constant sort** in an equation-free language. -/
def constantFibre (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) (sort : String)
    (constant : constantSort language sort = true) (free : language.isEquationFree = true) :
    Fibre (referenceStructure relEnv language reading) (.base sort) where
  values := constants language sort
  complete value _ typed := by
    obtain ⟨_, representative, equivalent, wellSorted⟩ := typed
    rw [(objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent]
    exact mem_constants_of_carrierTyped constant wellSorted
  sound value member := by
    obtain ⟨rule, ruleMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨inTerms, category⟩ := List.mem_filter.mp ruleMem
    have category : rule.category = sort := by simpa using category
    have noParams := params_of_constantSort constant inTerms category
    have notBare : ¬ UsesBareCollection rule := by
      rintro ⟨_, _, _, bare⟩
      unfold GrammarRule.bareParams at bare
      split at bare
      · rw [noParams] at bare
        cases bare
      · cases bare
    refine ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, .apply rule.label [], Relation.EqvGen.refl _, carrierTyped_of_wellSorted ⟨?_, rfl, rfl, rfl⟩⟩
    rw [← category]
    exact HasType.constructor inTerms notBare (noParams ▸ ArgumentsHaveTypes.nil)

/-- **The fibres of the constant sorts** of an equation-free language. -/
def constantFibres (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) :
    (type : TypeExpr) → Option (Fibre (referenceStructure relEnv language reading) type)
  | .base sort => if h : constantSort language sort = true ∧ language.isEquationFree = true then
      some (constantFibre relEnv language reading sort h.1 h.2) else none
  | _ => none

/-! ## Instances over fibres -/

variable {T : NativeStructure Pattern}

/-- The values of a type's fibre, or none. -/
def fibreValues (fibreOf : (type : TypeExpr) → Option (Fibre T type)) (type : TypeExpr) : List Pattern :=
  match fibreOf type with
  | some fibre => fibre.values
  | none => []

/-- Every type of the context has a fibre. -/
def covered (fibreOf : (type : TypeExpr) → Option (Fibre T type)) (context : Context) : Bool :=
  context.all fun entry => (fibreOf entry.2).isSome

/-- **The instances of a term over the fibres of its context**, one variable at a time. -/
def fibreInstances (fibreOf : (type : TypeExpr) → Option (Fibre T type)) : Context → Pattern → List Pattern
  | [], term => [term]
  | (name, type) :: context, term =>
    (fibreValues fibreOf type).flatMap fun value => fibreInstances fibreOf context (freeSubst (single name value) term)

theorem freeWithin_single {name : String} {names : List String} {value : Pattern} (closed : freeWithin [] value = true)
    {term : Pattern} (within : freeWithin (name :: names) term = true) :
    freeWithin names (freeSubst (single name value) term) = true := by
  refine freeWithin_freeSubst (names := name :: names) (fun other member => ?_) within
  unfold single
  split
  · exact freeWithin_mono (fun _ impossible => absurd impossible List.not_mem_nil) closed
  · rename_i different
    exact decide_eq_true ((List.mem_cons.mp member).resolve_left different)

/-- **Over complete fibres, the open judgment is the formula at every instance.** -/
theorem openHolds_iff_instances (fibreOf : (type : TypeExpr) → Option (Fibre T type)) (formula : Formula 0) :
    ∀ (context : Context) (term : Pattern), context.names.Nodup → covered fibreOf context = true →
      freeWithin context.names term = true →
        (OpenHolds T context formula term ↔ ∀ instantiated ∈ fibreInstances fibreOf context term, T.sat Env.closed formula instantiated)
  | [], term, _, _, _ => by
    simp only [fibreInstances, List.mem_singleton, forall_eq]
    exact openHolds_nil_iff
  | (name, type) :: context, term, nodup, covers, within => by
    have names : Context.names ((name, type) :: context) = name :: Context.names context := rfl
    rw [names] at nodup within
    have fresh := (List.nodup_cons.mp nodup).1
    have nodup' := (List.nodup_cons.mp nodup).2
    simp only [covered, List.all_cons, Bool.and_eq_true] at covers
    obtain ⟨fibre, found⟩ := Option.isSome_iff_exists.mp covers.1
    have covers' : covered fibreOf context = true := covers.2
    rw [openHolds_cons fresh within]
    simp only [fibreInstances, fibreValues, found, List.mem_flatMap]
    constructor
    · rintro holds instantiated ⟨value, member, instanceMem⟩
      obtain ⟨closedValue, typedValue⟩ := fibre.sound value member
      exact (openHolds_iff_instances fibreOf formula context _ nodup' covers'
        (freeWithin_single closedValue.2 within)).mp (holds value closedValue typedValue) instantiated instanceMem
    · intro holds value closedValue typedValue
      exact (openHolds_iff_instances fibreOf formula context _ nodup' covers'
        (freeWithin_single closedValue.2 within)).mpr fun instantiated instanceMem =>
          holds instantiated ⟨value, fibre.complete value closedValue typedValue, instanceMem⟩

/-! ## Evidence and answers for judgments -/

/-- **Evidence for a judgment.** -/
inductive JudgmentEvidence where
  /-- The front door's evidence at a closed term. -/
  | closed (evidence : Evidence)
  /-- The front door's evidence at every one of this many instances over complete fibres. -/
  | instances (count : ℕ)
  /-- An instance, and the front door's evidence there. -/
  | atInstance (instantiated : Pattern) (evidence : Evidence)
  /-- A predicate, given by the values it holds of, and the front door's evidence at the instance there. -/
  | atPredicate (members : List Pattern) (evidence : Evidence)
  /-- A finite-model certificate. -/
  | certificate (candidate : CertificateCandidate)
  /-- A formula compiled over a complete fibre, and the front door's evidence for it. -/
  | compiled (evidence : Evidence)
  /-- The evidence of the judgment this one reduces to. -/
  | reduced (evidence : JudgmentEvidence)
  deriving DecidableEq, Repr

/-- **An answer to a judgment**: proved or refuted with evidence, or open. -/
inductive JudgmentAnswer where
  | proved (evidence : JudgmentEvidence)
  | refuted (evidence : JudgmentEvidence)
  | unknown
  deriving DecidableEq, Repr

/-- Whether an answer proves. -/
def Answer.isProved : Answer → Bool
  | .proved _ => true
  | _ => false

/-- The evidence of a proof. -/
def Answer.proof : Answer → Option Evidence
  | .proved evidence => some evidence
  | _ => none

theorem Answer.proof_eq {answer : Answer} {evidence : Evidence} (found : answer.proof = some evidence) :
    answer = .proved evidence := by
  cases answer <;> simp_all [Answer.proof]

/-- The evidence of a refutation. -/
def Answer.refutation : Answer → Option Evidence
  | .refuted evidence => some evidence
  | _ => none

theorem Answer.isProved_iff {answer : Answer} : answer.isProved = true ↔ ∃ evidence, answer = .proved evidence := by
  cases answer <;> simp [Answer.isProved]

theorem Answer.refutation_eq {answer : Answer} {evidence : Evidence} (found : answer.refutation = some evidence) :
    answer = .refuted evidence := by
  cases answer <;> simp_all [Answer.refutation]

/-- **The verdict over a list of instances**: proved when every instance is proved, refuted at the first instance
that is refuted. -/
def instancesAnswer (askAt : Pattern → Answer) (instances : List Pattern) : JudgmentAnswer :=
  if instances.all fun instantiated => (askAt instantiated).isProved then .proved (.instances instances.length)
  else match instances.findSome? fun instantiated => (askAt instantiated).refutation.map fun evidence => (instantiated, evidence) with
    | some (instantiated, evidence) => .refuted (.atInstance instantiated evidence)
    | none => .unknown

theorem instancesAnswer_proved {askAt : Pattern → Answer} {instances : List Pattern} {evidence : JudgmentEvidence}
    (answered : instancesAnswer askAt instances = .proved evidence) :
    ∀ instantiated ∈ instances, ∃ evidence, askAt instantiated = .proved evidence := by
  unfold instancesAnswer at answered
  split at answered
  · rename_i all
    exact fun instantiated member => Answer.isProved_iff.mp (List.all_eq_true.mp all instantiated member)
  · split at answered <;> cases answered

theorem instancesAnswer_refuted {askAt : Pattern → Answer} {instances : List Pattern} {evidence : JudgmentEvidence}
    (answered : instancesAnswer askAt instances = .refuted evidence) :
    ∃ instantiated ∈ instances, ∃ evidence, askAt instantiated = .refuted evidence := by
  unfold instancesAnswer at answered
  split at answered
  · cases answered
  · cases found : instances.findSome? (fun instantiated =>
        (askAt instantiated).refutation.map fun evidence => (instantiated, evidence)) with
    | none => simp only [found] at answered; cases answered
    | some pair =>
      obtain ⟨candidate, member, mapped⟩ := List.exists_of_findSome?_eq_some found
      obtain ⟨evidence', refutation, _⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨candidate, member, evidence', Answer.refutation_eq refutation⟩

/-! ## Valuations given as hints -/

/-- The assignment a list of values gives a context: its value for each variable, every other name left as it is. -/
def hintAssignment (context : Context) (values : List (String × Pattern)) : String → Pattern :=
  fun name => if name ∈ context.names then (values.lookup name).getD (.fvar name) else .fvar name

/-- Whether the hint gives each variable a closed value that a check types. -/
def checkValuation (context : Context) (values : List (String × Pattern)) (typedBy : Pattern → TypeExpr → Bool) : Bool :=
  context.all fun entry =>
    decide (ClosedValue (hintAssignment context values entry.1)) && typedBy (hintAssignment context values entry.1) entry.2

theorem valuation_of_checkValuation {context : Context} {values : List (String × Pattern)}
    {typedBy : Pattern → TypeExpr → Bool} (sound : ∀ value type, typedBy value type = true → T.typed value type)
    (checked : checkValuation context values typedBy = true) : Valuation T context (hintAssignment context values) := by
  refine ⟨fun entry member => ?_, fun name outside => ?_⟩
  · have := List.all_eq_true.mp checked entry member
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, sound _ _ this.2⟩
  · simp only [hintAssignment, outside, if_false]

/-! ## The front door for open judgments -/

section FrontDoor

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ)

/-- The structure the front door's verdicts are about: the language read as its canonical forms read it. -/
abbrev FrontStructure (forms : Option (CanonicalForms relEnv language fuel)) : NativeStructure Pattern :=
  referenceStructure relEnv language (formsReading forms)

/-- The refutation a valuation hint gives: the front door types its values and refutes the formula at the term's
instance. -/
def counterAnswer (forms : Option (CanonicalForms relEnv language fuel)) (context : Context) (formula : Formula 0)
    (term : Pattern) (hint : Option CertificateCandidate) (rounds : ℕ) : Option (List (String × Pattern)) → JudgmentAnswer
  | some values =>
    if checkValuation context values fun value type =>
        (ask relEnv signature language fuel (.typed type) value hint rounds forms).isProved then
      match ask relEnv signature language fuel formula (freeSubst (hintAssignment context values) term) hint rounds forms with
      | .refuted evidence => .refuted (.atInstance (freeSubst (hintAssignment context values) term) evidence)
      | _ => .unknown
    else .unknown
  | none => .unknown

/-- **The front door for the open judgment `Γ ⊢ t : φ`**: over complete fibres, its verdict at every instance;
otherwise a closed term judged at itself, and a refutation at the instance of a valuation hint. -/
def askOpen (forms : Option (CanonicalForms relEnv language fuel))
    (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)) (context : Context)
    (formula : Formula 0) (term : Pattern) (hint : Option CertificateCandidate) (rounds : ℕ)
    (counter : Option (List (String × Pattern)) := none) : JudgmentAnswer :=
  if decide context.names.Nodup && freeWithin context.names term && covered fibreOf context then
    instancesAnswer (fun instantiated => ask relEnv signature language fuel formula instantiated hint rounds forms)
      (fibreInstances fibreOf context term)
  else if freeWithin [] term then
    match ask relEnv signature language fuel formula term hint rounds forms with
    | .proved evidence => .proved (.closed evidence)
    | _ => counterAnswer relEnv signature language fuel forms context formula term hint rounds counter
  else counterAnswer relEnv signature language fuel forms context formula term hint rounds counter

variable {relEnv signature language fuel}

/-- What the front door proves a type of holds. -/
theorem typed_of_ask {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds : ℕ} (value : Pattern) (type : TypeExpr)
    (proved : (ask relEnv signature language fuel (.typed type) value hint rounds forms).isProved = true) :
    (FrontStructure relEnv language fuel forms).typed value type := by
  obtain ⟨evidence, answered⟩ := Answer.isProved_iff.mp proved
  exact ask_proved answered

theorem counterAnswer_not_proved {forms : Option (CanonicalForms relEnv language fuel)} {context : Context}
    {formula : Formula 0} {term : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counter : Option (List (String × Pattern))} {evidence : JudgmentEvidence} :
    counterAnswer relEnv signature language fuel forms context formula term hint rounds counter ≠ .proved evidence := by
  intro answered
  unfold counterAnswer at answered
  split at answered
  · split at answered
    · split at answered <;> cases answered
    · cases answered
  · cases answered

theorem counterAnswer_refuted {forms : Option (CanonicalForms relEnv language fuel)} {context : Context}
    {formula : Formula 0} {term : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counter : Option (List (String × Pattern))} {evidence : JudgmentEvidence}
    (answered : counterAnswer relEnv signature language fuel forms context formula term hint rounds counter =
      .refuted evidence) :
    ¬ OpenHolds (FrontStructure relEnv language fuel forms) context formula term := by
  unfold counterAnswer at answered
  split at answered
  · split at answered
    · rename_i checked
      split at answered
      · rename_i refutation found
        intro holds
        exact ask_refuted found (holds _ (valuation_of_checkValuation (fun value type => typed_of_ask value type) checked))
      · cases answered
    · cases answered
  · cases answered

/-- **A proved open judgment holds.** -/
theorem askOpen_proved {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {context : Context}
    {formula : Formula 0} {term : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counter : Option (List (String × Pattern))} {evidence : JudgmentEvidence}
    (answered : askOpen relEnv signature language fuel forms fibreOf context formula term hint rounds counter =
      .proved evidence) :
    OpenHolds (FrontStructure relEnv language fuel forms) context formula term := by
  unfold askOpen at answered
  split at answered
  · rename_i exact
    simp only [Bool.and_eq_true, decide_eq_true_eq] at exact
    refine (openHolds_iff_instances fibreOf formula context term exact.1.1 exact.2 exact.1.2).mpr fun instantiated member => ?_
    obtain ⟨_, proved⟩ := instancesAnswer_proved answered instantiated member
    exact ask_proved proved
  · split at answered
    · rename_i closed
      split at answered
      · rename_i proof proved
        intro assignment _
        rw [freeSubst_of_closed closed]
        exact ask_proved proved
      · exact absurd answered counterAnswer_not_proved
    · exact absurd answered counterAnswer_not_proved

/-- **A refuted open judgment fails.** -/
theorem askOpen_refuted {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {context : Context}
    {formula : Formula 0} {term : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counter : Option (List (String × Pattern))} {evidence : JudgmentEvidence}
    (answered : askOpen relEnv signature language fuel forms fibreOf context formula term hint rounds counter =
      .refuted evidence) :
    ¬ OpenHolds (FrontStructure relEnv language fuel forms) context formula term := by
  unfold askOpen at answered
  split at answered
  · rename_i exact
    simp only [Bool.and_eq_true, decide_eq_true_eq] at exact
    rw [openHolds_iff_instances fibreOf formula context term exact.1.1 exact.2 exact.1.2]
    obtain ⟨instantiated, member, _, refuted⟩ := instancesAnswer_refuted answered
    exact fun holds => ask_refuted refuted (holds instantiated member)
  · split at answered
    · split at answered
      · cases answered
      · exact counterAnswer_refuted answered
    · exact counterAnswer_refuted answered

end FrontDoor

/-! ## Entailment -/

/-- **Entailment at a type**: every closed value of the type where the premise holds satisfies the conclusion. -/
def Entails (T : NativeStructure Pattern) (type : TypeExpr) (premise conclusion : Formula 0) : Prop :=
  ∀ value, ClosedValue value → T.typed value type → T.sat Env.closed premise value → T.sat Env.closed conclusion value

/-- The variable an entailment is judged at. -/
def entailmentVariable : String := "x"

/-- **Entailment is an open judgment**: a variable of the type has the type `dual φ ∨ ψ`. -/
theorem entails_iff_openHolds (type : TypeExpr) (premise conclusion : Formula 0) :
    Entails T type premise conclusion ↔
      OpenHolds T [(entailmentVariable, type)] (.or premise.dual conclusion) (.fvar entailmentVariable) := by
  rw [openHolds_cons (by simp [Context.names]) (by simp [freeWithin, Context.names])]
  simp only [freeSubst, single, if_true]
  constructor
  · intro entails value closedValue typedValue
    rw [openHolds_closed_iff closedValue.2 ⟨_, valuation_nil T⟩]
    by_cases holds : T.sat Env.closed premise value
    · exact .inr (entails value closedValue typedValue holds)
    · exact .inl ((T.sat_dual_closed premise value).mpr holds)
  · intro holds value closedValue typedValue premiseHolds
    have := (openHolds_closed_iff closedValue.2 ⟨_, valuation_nil T⟩).mp (holds value closedValue typedValue)
    exact this.resolve_left fun dualHolds => (T.sat_dual_closed premise value).mp dualHolds premiseHolds

section Certificates

variable {A : Type} [DecidableEq A] {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

/-- **A certificate proves an entailment**: it is valid, it respects the equations, the rules are aligned, the premise is
existential, the conclusion universal, and at every value of the certificate where the premise holds the conclusion
holds. -/
def entailsBy (certificate : Certificate A) (language : LanguageDef) (premise conclusion : Formula 0) : Bool :=
  certificate.contextualValid language && Certificate.equationsValid certificate language && aligned language &&
    premise.existential && conclusion.universal &&
      (certificateStructure certificate).elements.all fun element =>
        !(certificateStructure certificate).check premise element || (certificateStructure certificate).check conclusion element

/-- **What a certificate proves of an entailment holds at every term.** -/
theorem entailsBy_sound {certificate : Certificate A} {premise conclusion : Formula 0}
    (checked : entailsBy certificate language premise conclusion = true) (reference : reading.rules = .reference)
    (term : Pattern) (holds : (referenceStructure relEnv language reading).sat Env.closed premise term) :
    (referenceStructure relEnv language reading).sat Env.closed conclusion term := by
  simp only [entailsBy, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨valid, equations⟩, isAligned⟩, existential⟩, universal⟩, all⟩ := checked
  let hom := certificateHom (relEnv := relEnv) certificate valid (profile_of_aligned isAligned)
    ((respectsEquations_of_equationsValid valid equations).reading reading) reference
  have image := hom.sat_of_hom premise existential (sourceEnv := Env.closed) (targetEnv := Env.closed)
    (fun index => index.elim0) term holds
  have atImage := List.all_eq_true.mp all (hom.map term) ((certificateStructure certificate).complete _)
  rw [← (certificateStructure certificate).check_iff] at image
  simp only [image, Bool.not_true, Bool.false_or] at atImage
  exact hom.sat_of_hom_universal conclusion universal (sourceEnv := Env.closed) (targetEnv := Env.closed)
    (fun index => index.elim0) term (((certificateStructure certificate).check_iff conclusion _).mp atImage)

end Certificates

section EntailmentFrontDoor

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ)

/-- **The front door for entailment at a type**: a certificate's proof, or the open judgment of a variable of the type
at `dual φ ∨ ψ`, refuted at a separating value. -/
def askEntails (forms : Option (CanonicalForms relEnv language fuel))
    (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)) (type : TypeExpr)
    (premise conclusion : Formula 0) (hint : Option CertificateCandidate) (rounds : ℕ)
    (certificate : Option CertificateCandidate := none) (separating : Option Pattern := none) : JudgmentAnswer :=
  match certificate with
  | some candidate =>
    if formsReference forms && entailsBy (candidate.certificate signature language) language premise conclusion then
      .proved (.certificate candidate)
    else judged
  | none => judged
where
  /-- The entailment as an open judgment. -/
  judged : JudgmentAnswer :=
    match askOpen relEnv signature language fuel forms fibreOf [(entailmentVariable, type)] (.or premise.dual conclusion)
        (.fvar entailmentVariable) hint rounds (separating.map fun value => [(entailmentVariable, value)]) with
    | .proved evidence => .proved (.reduced evidence)
    | .refuted evidence => .refuted (.reduced evidence)
    | .unknown => .unknown

variable {relEnv signature language fuel}

/-- **A proved entailment holds.** -/
theorem askEntails_proved {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {premise conclusion : Formula 0} {hint : Option CertificateCandidate} {rounds : ℕ}
    {certificate : Option CertificateCandidate} {separating : Option Pattern} {evidence : JudgmentEvidence}
    (answered : askEntails relEnv signature language fuel forms fibreOf type premise conclusion hint rounds certificate
      separating = .proved evidence) :
    Entails (FrontStructure relEnv language fuel forms) type premise conclusion := by
  have fromJudged : askEntails.judged relEnv signature language fuel forms fibreOf type premise conclusion hint rounds
      separating = .proved evidence → Entails (FrontStructure relEnv language fuel forms) type premise conclusion := by
    intro judged
    unfold askEntails.judged at judged
    split at judged
    · rename_i proved
      exact (entails_iff_openHolds type premise conclusion).mpr (askOpen_proved proved)
    · cases judged
    · cases judged
  unfold askEntails at answered
  split at answered
  · split at answered
    · rename_i checked
      simp only [Bool.and_eq_true] at checked
      exact fun value _ _ holds => entailsBy_sound checked.2
        (reference_of_formsFor (formsFor_formsReading forms) checked.1) value holds
    · exact fromJudged answered
  · exact fromJudged answered

/-- **A refuted entailment fails.** -/
theorem askEntails_refuted {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {premise conclusion : Formula 0} {hint : Option CertificateCandidate} {rounds : ℕ}
    {certificate : Option CertificateCandidate} {separating : Option Pattern} {evidence : JudgmentEvidence}
    (answered : askEntails relEnv signature language fuel forms fibreOf type premise conclusion hint rounds certificate
      separating = .refuted evidence) :
    ¬ Entails (FrontStructure relEnv language fuel forms) type premise conclusion := by
  have fromJudged : askEntails.judged relEnv signature language fuel forms fibreOf type premise conclusion hint rounds
      separating = .refuted evidence → ¬ Entails (FrontStructure relEnv language fuel forms) type premise conclusion := by
    intro judged
    unfold askEntails.judged at judged
    split at judged
    · cases judged
    · rename_i refuted
      rw [entails_iff_openHolds]
      exact askOpen_refuted refuted
    · cases judged
  unfold askEntails at answered
  split at answered
  · split at answered
    · cases answered
    · exact fromJudged answered
  · exact fromJudged answered

end EntailmentFrontDoor

/-! ## Inhabitation -/

/-- **A type inhabited at a formula**: some closed value of the type satisfies it. -/
def Inhabited (T : NativeStructure Pattern) (type : TypeExpr) (formula : Formula 0) : Prop :=
  ∃ value, ClosedValue value ∧ T.typed value type ∧ T.sat Env.closed formula value

/-- **Emptiness is entailment of falsity.** -/
theorem not_inhabited_iff (type : TypeExpr) (formula : Formula 0) :
    ¬ Inhabited T type formula ↔ Entails T type formula .bot := by
  constructor
  · intro empty value closedValue typedValue holds
    exact empty ⟨value, closedValue, typedValue, holds⟩
  · rintro entails ⟨value, closedValue, typedValue, holds⟩
    exact entails value closedValue typedValue holds

section InhabitationFrontDoor

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ)

/-- The first candidate the front door proves is a closed value of the type, with the evidence a test gives it. -/
def findValue (forms : Option (CanonicalForms relEnv language fuel)) (type : TypeExpr) (hint : Option CertificateCandidate)
    (rounds : ℕ) (test : Pattern → Option Evidence) (candidates : List Pattern) : Option (Pattern × Evidence) :=
  candidates.findSome? fun value =>
    if decide (ClosedValue value) && (ask relEnv signature language fuel (.typed type) value hint rounds forms).isProved then
      (test value).map fun evidence => (value, evidence)
    else none

/-- The first candidate the front door proves is a closed value of the type satisfying the formula. -/
def findWitness (forms : Option (CanonicalForms relEnv language fuel)) (type : TypeExpr) (formula : Formula 0)
    (hint : Option CertificateCandidate) (rounds : ℕ) (candidates : List Pattern) : Option (Pattern × Evidence) :=
  findValue relEnv signature language fuel forms type hint rounds
    (fun value => (ask relEnv signature language fuel formula value hint rounds forms).proof) candidates

/-- **The front door for inhabitation**: a witness among the candidates and the fibre's values, or emptiness as
entailment of falsity. -/
def askInhabited (forms : Option (CanonicalForms relEnv language fuel))
    (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)) (type : TypeExpr)
    (formula : Formula 0) (hint : Option CertificateCandidate) (rounds : ℕ) (candidates : List Pattern)
    (certificate : Option CertificateCandidate := none) : JudgmentAnswer :=
  match findWitness relEnv signature language fuel forms type formula hint rounds (candidates ++ fibreValues fibreOf type) with
  | some (value, evidence) => .proved (.atInstance value evidence)
  | none =>
    match askEntails relEnv signature language fuel forms fibreOf type formula .bot hint rounds certificate with
    | .proved evidence => .refuted (.reduced evidence)
    | _ => .unknown

variable {relEnv signature language fuel}

theorem findValue_sound {forms : Option (CanonicalForms relEnv language fuel)} {type : TypeExpr}
    {hint : Option CertificateCandidate} {rounds : ℕ} {test : Pattern → Option Evidence} {candidates : List Pattern}
    {value : Pattern} {evidence : Evidence}
    (found : findValue relEnv signature language fuel forms type hint rounds test candidates = some (value, evidence)) :
    ClosedValue value ∧ (FrontStructure relEnv language fuel forms).typed value type ∧ test value = some evidence := by
  obtain ⟨candidate, _, mapped⟩ := List.exists_of_findSome?_eq_some found
  by_cases checked : (decide (ClosedValue candidate) &&
      (ask relEnv signature language fuel (.typed type) candidate hint rounds forms).isProved) = true
  · rw [if_pos checked] at mapped
    obtain ⟨evidence', tested, same⟩ := Option.map_eq_some_iff.mp mapped
    cases same
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨checked.1, typed_of_ask _ _ checked.2, tested⟩
  · rw [if_neg checked] at mapped
    cases mapped

theorem findWitness_sound {forms : Option (CanonicalForms relEnv language fuel)} {type : TypeExpr} {formula : Formula 0}
    {hint : Option CertificateCandidate} {rounds : ℕ} {candidates : List Pattern} {value : Pattern} {evidence : Evidence}
    (found : findWitness relEnv signature language fuel forms type formula hint rounds candidates = some (value, evidence)) :
    ClosedValue value ∧ (FrontStructure relEnv language fuel forms).typed value type ∧
      (FrontStructure relEnv language fuel forms).sat Env.closed formula value := by
  obtain ⟨closedValue, typedValue, tested⟩ := findValue_sound found
  exact ⟨closedValue, typedValue, ask_proved (Answer.proof_eq tested)⟩

/-- **A proved inhabitation holds.** -/
theorem askInhabited_proved {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {formula : Formula 0} {hint : Option CertificateCandidate} {rounds : ℕ} {candidates : List Pattern}
    {certificate : Option CertificateCandidate} {evidence : JudgmentEvidence}
    (answered : askInhabited relEnv signature language fuel forms fibreOf type formula hint rounds candidates certificate =
      .proved evidence) :
    Inhabited (FrontStructure relEnv language fuel forms) type formula := by
  unfold askInhabited at answered
  split at answered
  · rename_i value evidence' found
    exact ⟨value, findWitness_sound found⟩
  · split at answered <;> cases answered

/-- **A refuted inhabitation is empty.** -/
theorem askInhabited_refuted {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {formula : Formula 0} {hint : Option CertificateCandidate} {rounds : ℕ} {candidates : List Pattern}
    {certificate : Option CertificateCandidate} {evidence : JudgmentEvidence}
    (answered : askInhabited relEnv signature language fuel forms fibreOf type formula hint rounds candidates certificate =
      .refuted evidence) :
    ¬ Inhabited (FrontStructure relEnv language fuel forms) type formula := by
  unfold askInhabited at answered
  split at answered
  · cases answered
  · split at answered
    · rename_i proved
      exact (not_inhabited_iff type formula).mpr (askEntails_proved proved)
    · cases answered

end InhabitationFrontDoor

/-! ## Σ and Π over a type -/

/-- **Σ over a type**: the subject satisfies the family's formula at some closed value of the type. -/
def SigmaHolds (T : NativeStructure Pattern) (type : TypeExpr) (family : Pattern → Formula 0) (subject : Pattern) : Prop :=
  ∃ value, ClosedValue value ∧ T.typed value type ∧ T.sat Env.closed (family value) subject

/-- **Π over a type**: the subject satisfies the family's formula at every closed value of the type. -/
def PiHolds (T : NativeStructure Pattern) (type : TypeExpr) (family : Pattern → Formula 0) (subject : Pattern) : Prop :=
  ∀ value, ClosedValue value → T.typed value type → T.sat Env.closed (family value) subject

/-- The disjunction of a list of formulas. -/
def bigOr : List (Formula 0) → Formula 0
  | [] => .bot
  | formula :: formulas => .or formula (bigOr formulas)

/-- The conjunction of a list of formulas. -/
def bigAnd : List (Formula 0) → Formula 0
  | [] => .top
  | formula :: formulas => .and formula (bigAnd formulas)

theorem sat_bigOr (subject : Pattern) :
    ∀ formulas : List (Formula 0), T.sat Env.closed (bigOr formulas) subject ↔ ∃ formula ∈ formulas, T.sat Env.closed formula subject
  | [] => by simp [bigOr, NativeStructure.sat]
  | formula :: formulas => by
    simp only [bigOr, NativeStructure.sat, sat_bigOr subject formulas, List.mem_cons, exists_eq_or_imp]

theorem sat_bigAnd (subject : Pattern) :
    ∀ formulas : List (Formula 0), T.sat Env.closed (bigAnd formulas) subject ↔ ∀ formula ∈ formulas, T.sat Env.closed formula subject
  | [] => by simp [bigAnd, NativeStructure.sat]
  | formula :: formulas => by
    simp only [bigAnd, NativeStructure.sat, sat_bigAnd subject formulas, List.mem_cons, forall_eq_or_imp]

/-- **Over a complete fibre, Σ is the disjunction of the family.** -/
theorem sigmaHolds_iff {type : TypeExpr} (fibre : Fibre T type) (family : Pattern → Formula 0) (subject : Pattern) :
    SigmaHolds T type family subject ↔ T.sat Env.closed (bigOr (fibre.values.map family)) subject := by
  rw [sat_bigOr]
  constructor
  · rintro ⟨value, closedValue, typedValue, holds⟩
    exact ⟨family value, List.mem_map.mpr ⟨value, fibre.complete value closedValue typedValue, rfl⟩, holds⟩
  · rintro ⟨_, member, holds⟩
    obtain ⟨value, valueMem, rfl⟩ := List.mem_map.mp member
    exact ⟨value, (fibre.sound value valueMem).1, (fibre.sound value valueMem).2, holds⟩

/-- **Over a complete fibre, Π is the conjunction of the family.** -/
theorem piHolds_iff {type : TypeExpr} (fibre : Fibre T type) (family : Pattern → Formula 0) (subject : Pattern) :
    PiHolds T type family subject ↔ T.sat Env.closed (bigAnd (fibre.values.map family)) subject := by
  rw [sat_bigAnd]
  constructor
  · intro holds _ member
    obtain ⟨value, valueMem, rfl⟩ := List.mem_map.mp member
    exact holds value (fibre.sound value valueMem).1 (fibre.sound value valueMem).2
  · intro holds value closedValue typedValue
    exact holds _ (List.mem_map.mpr ⟨value, fibre.complete value closedValue typedValue, rfl⟩)

section FamilyFrontDoor

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ)

/-- **The front door for Σ**: over a complete fibre, the disjunction of the family; otherwise a witness. -/
def askSigma (forms : Option (CanonicalForms relEnv language fuel))
    (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)) (type : TypeExpr)
    (family : Pattern → Formula 0) (subject : Pattern) (hint : Option CertificateCandidate) (rounds : ℕ)
    (witnesses : List Pattern := []) : JudgmentAnswer :=
  match fibreOf type with
  | some fibre =>
    match ask relEnv signature language fuel (bigOr (fibre.values.map family)) subject hint rounds forms with
    | .proved evidence => .proved (.compiled evidence)
    | .refuted evidence => .refuted (.compiled evidence)
    | .unknown _ => .unknown
  | none =>
    match findValue relEnv signature language fuel forms type hint rounds
        (fun value => (ask relEnv signature language fuel (family value) subject hint rounds forms).proof) witnesses with
    | some (value, evidence) => .proved (.atInstance value evidence)
    | none => .unknown

/-- **The front door for Π**: over a complete fibre, the conjunction of the family; otherwise a counter-value. -/
def askPi (forms : Option (CanonicalForms relEnv language fuel))
    (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)) (type : TypeExpr)
    (family : Pattern → Formula 0) (subject : Pattern) (hint : Option CertificateCandidate) (rounds : ℕ)
    (counters : List Pattern := []) : JudgmentAnswer :=
  match fibreOf type with
  | some fibre =>
    match ask relEnv signature language fuel (bigAnd (fibre.values.map family)) subject hint rounds forms with
    | .proved evidence => .proved (.compiled evidence)
    | .refuted evidence => .refuted (.compiled evidence)
    | .unknown _ => .unknown
  | none =>
    match findValue relEnv signature language fuel forms type hint rounds
        (fun value => (ask relEnv signature language fuel (family value) subject hint rounds forms).refutation) counters with
    | some (value, evidence) => .refuted (.atInstance value evidence)
    | none => .unknown

variable {relEnv signature language fuel}

theorem askSigma_proved {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {family : Pattern → Formula 0} {subject : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {witnesses : List Pattern} {evidence : JudgmentEvidence}
    (answered : askSigma relEnv signature language fuel forms fibreOf type family subject hint rounds witnesses =
      .proved evidence) :
    SigmaHolds (FrontStructure relEnv language fuel forms) type family subject := by
  unfold askSigma at answered
  split at answered
  · rename_i fibre _
    split at answered
    · rename_i proof proved
      exact (sigmaHolds_iff fibre family subject).mpr (ask_proved proved)
    · cases answered
    · cases answered
  · split at answered
    · rename_i value evidence' found
      obtain ⟨closedValue, typedValue, tested⟩ := findValue_sound found
      exact ⟨value, closedValue, typedValue, ask_proved (Answer.proof_eq tested)⟩
    · cases answered

theorem askSigma_refuted {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {family : Pattern → Formula 0} {subject : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {witnesses : List Pattern} {evidence : JudgmentEvidence}
    (answered : askSigma relEnv signature language fuel forms fibreOf type family subject hint rounds witnesses =
      .refuted evidence) :
    ¬ SigmaHolds (FrontStructure relEnv language fuel forms) type family subject := by
  unfold askSigma at answered
  split at answered
  · rename_i fibre _
    split at answered
    · cases answered
    · rename_i refutation refuted
      rw [sigmaHolds_iff fibre family subject]
      exact ask_refuted refuted
    · cases answered
  · split at answered <;> cases answered

theorem askPi_proved {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {family : Pattern → Formula 0} {subject : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counters : List Pattern} {evidence : JudgmentEvidence}
    (answered : askPi relEnv signature language fuel forms fibreOf type family subject hint rounds counters =
      .proved evidence) :
    PiHolds (FrontStructure relEnv language fuel forms) type family subject := by
  unfold askPi at answered
  split at answered
  · rename_i fibre _
    split at answered
    · rename_i proof proved
      exact (piHolds_iff fibre family subject).mpr (ask_proved proved)
    · cases answered
    · cases answered
  · split at answered <;> cases answered

theorem askPi_refuted {forms : Option (CanonicalForms relEnv language fuel)}
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)} {type : TypeExpr}
    {family : Pattern → Formula 0} {subject : Pattern} {hint : Option CertificateCandidate} {rounds : ℕ}
    {counters : List Pattern} {evidence : JudgmentEvidence}
    (answered : askPi relEnv signature language fuel forms fibreOf type family subject hint rounds counters =
      .refuted evidence) :
    ¬ PiHolds (FrontStructure relEnv language fuel forms) type family subject := by
  unfold askPi at answered
  split at answered
  · rename_i fibre _
    split at answered
    · cases answered
    · rename_i refutation refuted
      rw [piHolds_iff fibre family subject]
      exact ask_refuted refuted
    · cases answered
  · split at answered
    · rename_i value evidence' found
      obtain ⟨closedValue, typedValue, tested⟩ := findValue_sound found
      exact fun holds => ask_refuted (Answer.refutation_eq tested) (holds value closedValue typedValue)
    · cases answered

end FamilyFrontDoor

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
