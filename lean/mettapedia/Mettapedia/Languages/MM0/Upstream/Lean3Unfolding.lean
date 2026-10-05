import Mettapedia.Languages.MM0.Upstream.Lean3Admissibility
import Mettapedia.Languages.MM0.Presentation.UnfoldingTheory

/-!
# Stored definition bodies and the pinned MM0 unfolding premises

The historical dummy-image guard is adapted from `conv'.unfold`, lines
196--201 of `mm0-lean/mm0/mm0.lean`, revision
`6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/mm0-lean/mm0/mm0.lean

That guard checks only dummy sorts. The specified unfolding request also
requires freshness for all parameter images and distinct dummy images.
Checked admissions establish the exact stored body and its typing, so the
historical total substitution is used only within its real image domain.

This module connects these premises to the existing authored `mm0:unfold`
operation. It does not define a new checker or equate the full historical
curried conversion relation with the current saturated conversion relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3Unfolding

open Lean3Typing Lean3Typing.Reference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies computationalHost)

namespace Reference

theorem getTerm_body_iff (environment : Env) (symbol : Nat) (formal : Context)
    (returned : DepType) (dummies : List Nat) (body : SExpr) :
    GetTerm environment symbol formal returned (some (dummies, body)) ↔
      Decl.defn symbol formal returned (some (dummies, body)) ∈ environment := by
  constructor
  · intro known; cases known with | defn member => exact member
  · exact GetTerm.defn

/-- The exact dummy-sort vector in the historical unfolding constructor. -/
def dummySortImages (target : Context) (sorts images : List Nat) : Prop :=
  List.Forall₂ (fun sort image => target[image]? = some (.bound sort)) sorts images

/-- The historical constructor's request premises and its substituted left
side, before its recursive conversion premise is supplied. -/
def historicalUnfolds (environment : Env) (target : Context) (symbol : Nat)
    (arguments : List SExpr) (images : List Nat) (result : SExpr) : Prop :=
  ∃ formal returned dummies body,
    GetTerm environment symbol formal returned (some (dummies, body)) ∧
    List.Forall₂ (FitsBinder environment target) arguments formal ∧
    dummySortImages target dummies images ∧
    Lean3Dependencies.Reference.substitute (arguments ++ images.map SExpr.var) body = result

/-- Current specified freshness added to the actual historical request,
without changing its stored-body or simultaneous-substitution observations. -/
def specifiedUnfolds (environment : Env) (target : Context) (symbol : Nat)
    (arguments : List SExpr) (images : List Nat) (result : SExpr) : Prop :=
  historicalUnfolds environment target symbol arguments images result ∧
    images.Nodup ∧
    ∀ image ∈ images, ∀ expression ∈ arguments,
      ¬ Lean3Dependencies.Reference.hasVar target expression image

end Reference

/-- Definition-body observations, separately from the declaration-profile
observations already supplied by `EnvironmentRelated`. -/
structure DefinitionsRelated (environment : Env) (theory : Kernel.Theory) : Prop where
  definitions : ∀ symbol dummies body,
    (∃ formal returned, GetTerm environment symbol formal returned (some (dummies, body))) ↔
      theory.definitionSignature symbol = some ⟨dummies, body.toKernel⟩

private theorem getBody_append (environment : Env) (declaration : Decl) (symbol : Nat)
    (dummies : List Nat) (body : SExpr) :
    (∃ formal returned, GetTerm (environment ++ [declaration]) symbol formal returned
      (some (dummies, body))) ↔
    (∃ formal returned, GetTerm environment symbol formal returned (some (dummies, body))) ∨
      (∃ formal returned, GetTerm [declaration] symbol formal returned (some (dummies, body))) := by
  simp only [Reference.getTerm_body_iff, List.mem_append]
  aesop

private theorem bodyLookup_insert_iff (entries : List (Nat × Kernel.Definition.Body))
    (key symbol : Nat) (entry : Kernel.Definition.Body) (dummies : List Nat) (body : SExpr)
    (fresh : entries.lookup key = none) :
    ((key, entry) :: entries).lookup symbol = some ⟨dummies, body.toKernel⟩ ↔
      (symbol = key ∧ entry.dummies = dummies ∧ SExpr.ofKernel entry.expression = body) ∨
        entries.lookup symbol = some ⟨dummies, body.toKernel⟩ := by
  have bodyEq : entry = (⟨dummies, body.toKernel⟩ : Kernel.Definition.Body) ↔
      entry.dummies = dummies ∧ SExpr.ofKernel entry.expression = body := by
    cases entry with
    | mk sorts expression =>
        constructor
        · intro same
          have parts := Kernel.Definition.Body.mk.inj same
          exact ⟨parts.1, by rw [parts.2]; simp⟩
        · rintro ⟨rfl, same⟩
          have same' := congrArg SExpr.toKernel same
          simp only [SExpr.toKernel_ofKernel] at same'
          exact congrArg (Kernel.Definition.Body.mk sorts) same'
  by_cases same : symbol = key
  · subst symbol
    simp [fresh, bodyEq]
  · have unequal : (symbol == key) = false := by simp [same]
    simp [List.lookup_cons, unequal, same]

theorem empty_definitions_related : DefinitionsRelated [] ({} : Kernel.Theory) := by
  constructor
  intro symbol dummies body
  simp [Reference.getTerm_body_iff, Kernel.Theory.definitionSignature]

theorem step_definitions_related {environment : Env} {before after : Kernel.Theory}
    {admission : Kernel.Admission} (related : DefinitionsRelated environment before)
    (checked : Kernel.Theory.Step before admission after) :
    DefinitionsRelated (environment ++ [projectAdmission admission]) after := by
  cases checked with
  | intro authorized =>
      cases authorized with
      | sort fresh =>
          constructor
          intro symbol dummies body
          rw [getBody_append]
          simpa [Reference.getTerm_body_iff, projectAdmission, Kernel.Admission.insert,
            Kernel.Theory.definitionSignature] using related.definitions symbol dummies body
      | term fresh admitted =>
          constructor
          intro symbol dummies body
          rw [getBody_append]
          simpa [Reference.getTerm_body_iff, projectAdmission, Kernel.Admission.insert,
            Kernel.Theory.definitionSignature] using related.definitions symbol dummies body
      | @definition key declaration stored fresh freshBody admitted bodyAdmitted =>
          constructor
          intro symbol dummies body
          rw [getBody_append]
          change (∃ formal returned, GetTerm environment symbol formal returned (some (dummies, body))) ∨
            (∃ formal returned, GetTerm [Decl.defn key (ofContext declaration.arguments)
              (declaration.resultSort, declaration.dependencies)
              (some (stored.dummies, SExpr.ofKernel stored.expression))] symbol formal returned
              (some (dummies, body))) ↔
            ((key, stored) :: before.definitions).lookup symbol = some ⟨dummies, body.toKernel⟩
          rw [bodyLookup_insert_iff _ _ _ _ _ _ freshBody, related.definitions]
          simp only [Reference.getTerm_body_iff, List.mem_singleton, Decl.defn.injEq,
            Option.some.injEq, Prod.mk.injEq]
          aesop
      | axiomDecl fresh admitted =>
          constructor
          intro symbol dummies body
          rw [getBody_append]
          simpa [Reference.getTerm_body_iff, projectAdmission, Kernel.Admission.insert,
            Kernel.Theory.definitionSignature] using related.definitions symbol dummies body
      | theoremDecl fresh admitted allowed checkedProof =>
          constructor
          intro symbol dummies body
          rw [getBody_append]
          simpa [Reference.getTerm_body_iff, projectAdmission, Kernel.Admission.insert,
            Kernel.Theory.definitionSignature] using related.definitions symbol dummies body

theorem runs_definitions_related {environment : Env} {before after : Kernel.Theory}
    {admissions : List Kernel.Admission} (related : DefinitionsRelated environment before)
    (checked : Kernel.Theory.Runs before admissions after) :
    DefinitionsRelated (environment ++ projectRun admissions) after := by
  induction checked generalizing environment with
  | nil theory => simpa [projectRun] using related
  | cons step _ ih =>
      simpa [projectRun, List.append_assoc] using ih (step_definitions_related related step)

theorem checked_run_definitions_related {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) :
    DefinitionsRelated (projectRun admissions) theory := by
  simpa using runs_definitions_related empty_definitions_related
    ((Kernel.Theory.run_eq_some_iff _ _ _).mp checked)

/-- Both stored observations recover the exact profile and body. No global
key-uniqueness assumption is added to the historical membership environment. -/
theorem getTerm_body_iff_lookups {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory) (bodies : DefinitionsRelated environment theory)
    (symbol : Nat) (formal : Context) (returned : DepType) (dummies : List Nat) (body : SExpr) :
    GetTerm environment symbol formal returned (some (dummies, body)) ↔
      theory.termSignature symbol = some (Reference.termDecl formal returned) ∧
        theory.definitionSignature symbol = some ⟨dummies, body.toKernel⟩ := by
  constructor
  · intro known
    exact ⟨(terms.terms _ _ _).mp ⟨_, known⟩,
      (bodies.definitions _ _ _).mp ⟨_, _, known⟩⟩
  · rintro ⟨declared, stored⟩
    obtain ⟨actualFormal, actualReturn, known⟩ := (bodies.definitions _ _ _).mpr stored
    have profile := (terms.terms _ _ _).mp ⟨_, known⟩
    have same := Option.some.inj (profile.symm.trans declared)
    have parts := (Reference.termDecl_eq_iff _ _ _).mp same
    have actualFormalEq : actualFormal = formal := by simpa [Reference.termDecl] using parts.1
    have actualReturnEq : actualReturn = returned := by
      simpa only [Reference.termDecl] using parts.2
    simpa only [actualFormalEq, actualReturnEq] using known

private theorem arguments_supported {signature : Kernel.TermSignature} {target formal : Kernel.Context}
    {arguments : List Kernel.Preterm}
    (typed : List.Forall₂ (Kernel.Preterm.FitsBinder signature target) arguments formal) :
    ∀ expression ∈ arguments, ∃ support, Kernel.Preterm.Supports target expression support := by
  induction typed with
  | nil => simp
  | cons fits rest ih =>
      intro expression member
      rcases List.mem_cons.mp member with rfl | later
      · exact fits.support_exists
      · exact ih expression later

/-- Sorted images, exclusion from parameters and pairwise distinctness are
exactly ordered dummy freshness when the parameter supports are defined. -/
theorem freshDummies_iff {target : Kernel.Context} {arguments : List Kernel.Preterm}
    (supported : ∀ expression ∈ arguments, ∃ support, Kernel.Preterm.Supports target expression support)
    (sorts images : List Nat) :
    Kernel.Definition.FreshDummies target arguments sorts images ↔
      List.Forall₂ (fun sort image => target[image]? = some (.bound sort)) sorts images ∧
        images.Nodup ∧
        ∀ image ∈ images, ∀ expression ∈ arguments, ¬ Kernel.Preterm.HasVar target image expression := by
  constructor
  · intro fresh
    refine ⟨?_, fresh.distinct, fresh.excludes_arguments⟩
    clear supported
    induction fresh with
    | nil => exact .nil
    | cons lookup fresh rest ih => exact .cons lookup ih
  · intro conditions
    induction sorts generalizing arguments images with
    | nil =>
        rcases conditions with ⟨typed, _, _⟩
        cases typed
        exact .nil _
    | cons sort sorts ih =>
        rcases conditions with ⟨typed, distinct, excludes⟩
        cases images with
        | nil => cases typed
        | cons image images =>
            obtain ⟨lookup, rest⟩ := List.forall₂_cons.mp typed
            obtain ⟨newImage, laterDistinct⟩ := List.nodup_cons.mp distinct
            refine .cons lookup (fun expression member =>
              ⟨supported expression member, excludes image (by simp) expression member⟩) ?_
            apply ih
            · intro expression member
              rcases List.mem_append.mp member with old | added
              · exact supported expression old
              · have same : expression = .var image := by simpa using added
                subst expression
                exact ⟨{image}, .bound lookup⟩
            · refine ⟨rest, laterDistinct, ?_⟩
              intro next member expression argument
              rcases List.mem_append.mp argument with old | added
              · exact excludes next (by simp [member]) expression old
              · have same : expression = .var image := by simpa using added
                subst expression
                intro occurs
                have different : image ≠ next := by intro same; subst next; exact newImage member
                cases occurs with
                | bound actual => exact different rfl
                | regular actual member => simp [lookup] at actual

theorem dummySortImages_iff (target : Kernel.Context) (sorts images : List Nat) :
    Reference.dummySortImages (ofContext target) sorts images ↔
      List.Forall₂ (fun sort image => target[image]? = some (.bound sort)) sorts images := by
  induction sorts generalizing images with
  | nil => cases images <;> simp [Reference.dummySortImages]
  | cons sort sorts ih =>
      cases images with
      | nil => simp [Reference.dummySortImages]
      | cons image images =>
          simp only [Reference.dummySortImages, List.forall₂_cons]
          refine and_congr ?_ (ih images)
          constructor
          · intro known
            simpa only [toContext_ofContext, Binder.toKernel] using toContext_lookup known
          · exact ofContext_lookup

private theorem excludes_images_iff (target : Kernel.Context) (arguments : List Kernel.Preterm)
    (images : List Nat) :
    (∀ image ∈ images, ∀ expression ∈ arguments.map SExpr.ofKernel,
      ¬ Lean3Dependencies.Reference.hasVar (ofContext target) expression image) ↔
      ∀ image ∈ images, ∀ expression ∈ arguments, ¬ Kernel.Preterm.HasVar target image expression := by
  constructor
  · intro excludes image member expression argument occurs
    exact excludes image member (SExpr.ofKernel expression) (List.mem_map.mpr ⟨_, argument, rfl⟩)
      ((Lean3Dependencies.hasVar_ofKernel_iff target expression image).mpr occurs)
  · intro excludes image member expression argument occurs
    obtain ⟨source, inArguments, rfl⟩ := List.mem_map.mp argument
    exact excludes image member source inArguments
      ((Lean3Dependencies.hasVar_ofKernel_iff target source image).mp occurs)

theorem specified_freshness_iff {signature : Kernel.TermSignature} {target formal : Kernel.Context}
    {arguments : List Kernel.Preterm}
    (typed : List.Forall₂ (Kernel.Preterm.FitsBinder signature target) arguments formal)
    (sorts images : List Nat) :
    Reference.dummySortImages (ofContext target) sorts images ∧ images.Nodup ∧
      (∀ image ∈ images, ∀ expression ∈ arguments.map SExpr.ofKernel,
        ¬ Lean3Dependencies.Reference.hasVar (ofContext target) expression image) ↔
      Kernel.Definition.FreshDummies target arguments sorts images := by
  rw [dummySortImages_iff, excludes_images_iff]
  exact (freshDummies_iff (arguments_supported typed) sorts images).symm

private theorem typed_values_domain {signature : Kernel.TermSignature} {formal target : Kernel.Context}
    {source : Kernel.Preterm} {remaining : Kernel.Context} {sort : Nat} {values : List Kernel.Preterm}
    (bodyTyped : Kernel.Preterm.HasType signature formal source remaining sort)
    (valuesTyped : List.Forall₂ (Kernel.Preterm.FitsBinder signature target) values formal) :
    Lean3Dependencies.Reference.withinImages values.length (SExpr.ofKernel source) := by
  apply (Lean3Dependencies.withinImages_iff source values.length).mpr
  obtain ⟨support, supported⟩ := bodyTyped.support_exists
  intro index occurs
  obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
  rw [valuesTyped.length_eq]
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-- Actual admitted body typing discharges the historical substitution domain.
The request retains the exact supplied symbol, images and claimed result. -/
theorem specified_unfolds_iff {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory) (bodies : DefinitionsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) (target : Kernel.Context) (symbol : Nat)
    (arguments : List Kernel.Preterm) (images : List Nat) (result : Kernel.Preterm) :
    Reference.specifiedUnfolds environment (ofContext target) symbol
      (arguments.map SExpr.ofKernel) images (SExpr.ofKernel result) ↔
      Kernel.Definition.Unfolds theory.termSignature theory.definitionSignature target
        symbol arguments images result := by
  constructor
  · rintro ⟨⟨formal, returned, dummies, body, known, fitted, sorted, substituted⟩, distinct, excluded⟩
    have lookups := (getTerm_body_iff_lookups terms bodies _ _ _ _ _).mp known
    have typed : List.Forall₂ (Kernel.Preterm.FitsBinder theory.termSignature target)
        arguments (toContext formal) := by
      apply (Lean3Admissibility.fits_vector_iff terms (toContext formal) target arguments).mp
      simpa only [ofContext_toContext] using fitted
    have fresh : Kernel.Definition.FreshDummies target arguments dummies images :=
      (specified_freshness_iff typed dummies images).mp ⟨sorted, distinct, excluded⟩
    obtain ⟨storedDeclaration, declared, admitted⟩ := valid.definitions _ _ lookups.2
    have same := Option.some.inj (declared.symm.trans lookups.1)
    subst storedDeclaration
    have valuesTyped := fresh.typed_substitution typed
    have domain := typed_values_domain admitted.typed valuesTyped
    refine .intro lookups.1 lookups.2 typed fresh (Kernel.Preterm.substitute_sound ?_)
    apply (Lean3Dependencies.substitution_iff
      (Kernel.Definition.substitutionValues arguments images) body.toKernel result).mpr
    refine ⟨by simpa only [SExpr.ofKernel_toKernel] using domain, ?_⟩
    simpa only [Kernel.Definition.substitutionValues, List.map_append, List.map_map,
      Function.comp_def, SExpr.ofKernel, SExpr.ofKernel_toKernel] using substituted
  · intro unfolded
    cases unfolded with
    | @intro declaration body result declared stored typed fresh substituted =>
        have known : GetTerm environment symbol (ofContext declaration.arguments)
            (declaration.resultSort, declaration.dependencies)
            (some (body.dummies, SExpr.ofKernel body.expression)) := by
          apply (getTerm_body_iff_lookups terms bodies _ _ _ _ _).mpr
          exact ⟨by simpa only [Reference.termDecl_ofKernel] using declared,
            by simpa only [SExpr.toKernel_ofKernel] using stored⟩
        have freshness := (specified_freshness_iff typed body.dummies images).mpr fresh
        refine ⟨⟨_, _, _, _, known,
          (Lean3Admissibility.fits_vector_iff terms _ _ _).mpr typed, freshness.1, ?_⟩,
          freshness.2.1, freshness.2.2⟩
        simpa only [Kernel.Definition.substitutionValues, List.map_append, List.map_map,
          Function.comp_def, SExpr.ofKernel] using Lean3Dependencies.substitution_of_derivation substituted

theorem checked_run_specified_unfolds_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (target : Kernel.Context) (symbol : Nat)
    (arguments : List Kernel.Preterm) (images : List Nat) (result : Kernel.Preterm) :
    Reference.specifiedUnfolds (projectRun admissions) (ofContext target) symbol
      (arguments.map SExpr.ofKernel) images (SExpr.ofKernel result) ↔
      Kernel.Definition.Unfolds theory.termSignature theory.definitionSignature target
        symbol arguments images result :=
  specified_unfolds_iff (checked_run_environment_related checked) (checked_run_definitions_related checked)
    (Kernel.Theory.run_from_empty_wellFormed checked) target symbol arguments images result

/-- The named authored entry, on the actual theory returned by checked
admission, accepts precisely this specified upstream-style request. -/
theorem checked_run_authored_unfolding_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (target : Kernel.Context) (symbol : Nat)
    (arguments : List Kernel.Preterm) (images : List Nat) (result : Kernel.Preterm) :
    Applies Presentation.ComputationalDefinitions.unfoldingProgram computationalHost "mm0:unfold"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
        Presentation.ComputationalContext.encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural symbol,
        Presentation.ComputationalArguments.encodeExpressions arguments,
        Presentation.ComputationalContext.encodeNaturals images]
      (Presentation.encodeResult (some result)) ↔
      Reference.specifiedUnfolds (projectRun admissions) (ofContext target) symbol
        (arguments.map SExpr.ofKernel) images (SExpr.ofKernel result) := by
  rw [Presentation.ComputationalDefinitions.theory_unfolding_accepts_iff]
  exact (checked_run_specified_unfolds_iff checked target symbol arguments images result).symm

theorem checked_run_authored_unfolding_refuses_iff {theory : Kernel.Theory}
    {admissions : List Kernel.Admission} (checked : Kernel.Theory.run? {} admissions = some theory)
    (target : Kernel.Context) (symbol : Nat) (arguments : List Kernel.Preterm) (images : List Nat) :
    Applies Presentation.ComputationalDefinitions.unfoldingProgram computationalHost "mm0:unfold"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
        Presentation.ComputationalContext.encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural symbol,
        Presentation.ComputationalArguments.encodeExpressions arguments,
        Presentation.ComputationalContext.encodeNaturals images] (.sym "None") ↔
      ¬ ∃ result, Reference.specifiedUnfolds (projectRun admissions) (ofContext target) symbol
        (arguments.map SExpr.ofKernel) images (SExpr.ofKernel result) := by
  have refused := Presentation.ComputationalDefinitions.unfolding_refuses_iff
    theory.terms theory.definitions target symbol arguments images
  simp only [Presentation.ComputationalTyping.theory_signature,
    Presentation.ComputationalDefinitions.theory_definitions] at refused
  rw [refused]
  exact not_congr (exists_congr (fun result =>
    (checked_run_specified_unfolds_iff checked target symbol arguments images result).symm))

theorem checked_run_unfolding_is_typed {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) {target : Kernel.Context}
    {symbol : Nat} {formal : Context} {returned : DepType} {dummies : List Nat} {body : SExpr}
    (known : GetTerm (projectRun admissions) symbol formal returned (some (dummies, body)))
    {arguments : List Kernel.Preterm} {images : List Nat} {result : Kernel.Preterm}
    (requested : Reference.specifiedUnfolds (projectRun admissions) (ofContext target) symbol
      (arguments.map SExpr.ofKernel) images (SExpr.ofKernel result)) :
    Reference.Typed (projectRun admissions) (ofContext target) (SExpr.ofKernel result) [] returned.1 := by
  have terms := checked_run_environment_related checked
  have bodyRelated := checked_run_definitions_related checked
  have declared := (getTerm_body_iff_lookups terms bodyRelated _ _ _ _ _).mp known
  have authored := (checked_run_authored_unfolding_iff checked _ _ _ _ _).mpr requested
  have typed := Presentation.ComputationalDefinitions.checked_theory_unfolding_is_typed
    checked declared.1 authored
  simpa only [ofContext, List.map_nil, Reference.termDecl] using typed_ofKernel terms typed

namespace Controls

open Kernel
open Presentation ComputationalContext ComputationalArguments ComputationalTyping ComputationalDefinitions

private def setSort : Admission := .sort 0 {}
private def propositionSort : Admission := .sort 1 { provable := true }
private def relation : Admission := .term 0 ⟨[.regular 0 ∅, .regular 0 ∅], 1, ∅⟩
private def quantifier : Admission := .term 1 ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩
private def rel (left right : Nat) : Preterm := .app (.app (.term 0) (.var left)) (.var right)
private def all (image : Nat) (expression : Preterm) : Preterm := .app (.app (.term 1) (.var image)) expression
private def binderBody : Definition.Body := ⟨[0], all 1 (rel 0 1)⟩
private def closedBody : Definition.Body := ⟨[0, 0], all 0 (all 1 (rel 0 1))⟩
private def binderDefinition : Admission := .definition 2 ⟨[.bound 0], 1, {0}⟩ binderBody
private def closedDefinition : Admission := .definition 3 ⟨[], 1, ∅⟩ closedBody
private def beforeBodies : Theory := [setSort, propositionSort, relation, quantifier].foldl Admission.insert {}
private def history : List Admission :=
  [setSort, propositionSort, relation, quantifier, binderDefinition, closedDefinition]
private def admitted : Theory := history.foldl Admission.insert {}
private def target : Kernel.Context := [.bound 0, .bound 0]

theorem concrete_definitions_are_admitted : Theory.run? {} history = some admitted := by
  apply (Theory.run_eq_some_iff _ _ _).mpr
  refine .cons (.intro ((Admission.check_iff _ _).mp ?_))
    (.cons (.intro ((Admission.check_iff _ _).mp ?_))
      (.cons (.intro ((Admission.check_iff _ _).mp ?_))
        (.cons (.intro ((Admission.check_iff _ _).mp ?_))
          (.cons (.intro ((Admission.check_iff _ _).mp ?_))
            (.cons (.intro ((Admission.check_iff _ _).mp ?_)) (.nil _)))))) <;> decide +kernel

theorem admitted_body_storage_is_exact :
    GetTerm (projectRun history) 2 [.bound 0] (1, {0})
      (some ([0], SExpr.ofKernel binderBody.expression)) := by
  apply (getTerm_body_iff_lookups (checked_run_environment_related concrete_definitions_are_admitted)
    (checked_run_definitions_related concrete_definitions_are_admitted) _ _ _ _ _).mpr
  exact ⟨rfl, rfl⟩

theorem fresh_dummy_computes_exact_result :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 2,
        encodeExpressions [.var 0], encodeNaturals [1]] (encodeResult (some (all 1 (rel 0 1)))) := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      target 2 [.var 0] [1] = some (all 1 (rel 0 1)) := by decide +kernel
  simpa only [computed] using theory_unfolding_computes admitted target 2 [.var 0] [1]

theorem fresh_result_has_upstream_style_type :
    Reference.Typed (projectRun history) (ofContext target)
      (SExpr.ofKernel (all 1 (rel 0 1))) [] 1 := by
  exact checked_run_unfolding_is_typed concrete_definitions_are_admitted admitted_body_storage_is_exact
    ((checked_run_authored_unfolding_iff concrete_definitions_are_admitted _ _ _ _ _).mp
      fresh_dummy_computes_exact_result)

theorem wrong_submitted_result_is_refused :
    ¬ Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 2,
        encodeExpressions [.var 0], encodeNaturals [1]] (encodeResult (some (all 0 (rel 0 0)))) := by
  intro accepted
  have same := encodeResult_injective (accepted.deterministic fresh_dummy_computes_exact_result)
  cases same

theorem historical_sort_guard_allows_capture :
    Reference.dummySortImages (ofContext target) [0] [0] :=
  .cons rfl .nil

theorem historical_request_allows_capture :
    Reference.historicalUnfolds (projectRun history) (ofContext target) 2
      [.var 0] [0] (SExpr.ofKernel (all 0 (rel 0 0))) := by
  exact ⟨[.bound 0], (1, {0}), [0], SExpr.ofKernel binderBody.expression,
    admitted_body_storage_is_exact, .cons ⟨0, rfl, rfl⟩ .nil,
    historical_sort_guard_allows_capture, rfl⟩

theorem capturing_dummy_is_not_specified_fresh :
    ¬ Reference.specifiedUnfolds (projectRun history) (ofContext target) 2
      [.var 0] [0] (SExpr.ofKernel (all 0 (rel 0 0))) := by
  intro requested
  exact requested.2.2 0 (by simp) (.var 0) (by simp) ⟨.bound 0, rfl, rfl⟩

theorem capturing_request_completes_with_none :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 2,
        encodeExpressions [.var 0], encodeNaturals [0]] (.sym "None") := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      target 2 [.var 0] [0] = none := by decide +kernel
  simpa only [computed, encodeResult] using theory_unfolding_computes admitted target 2 [.var 0] [0]

theorem duplicate_dummies_pass_the_historical_guard :
    Reference.historicalUnfolds (projectRun history) (ofContext target) 3 [] [0, 0]
      (SExpr.ofKernel (all 0 (all 0 (rel 0 0)))) := by
  have known : GetTerm (projectRun history) 3 [] (1, ∅)
      (some ([0, 0], SExpr.ofKernel closedBody.expression)) := by
    apply (getTerm_body_iff_lookups (checked_run_environment_related concrete_definitions_are_admitted)
      (checked_run_definitions_related concrete_definitions_are_admitted) _ _ _ _ _).mpr
    exact ⟨rfl, rfl⟩
  exact ⟨[], (1, ∅), [0, 0], SExpr.ofKernel closedBody.expression, known, .nil,
    .cons rfl (.cons rfl .nil), rfl⟩

theorem parameter_freshness_alone_does_not_exclude_duplicates :
    (∀ image ∈ ([0, 0] : List Nat), ∀ expression ∈ ([] : List SExpr),
      ¬ Lean3Dependencies.Reference.hasVar (ofContext target) expression image) ∧
      ¬ ([0, 0] : List Nat).Nodup := by
  simp

theorem duplicate_dummy_request_completes_with_none :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 3,
        encodeExpressions [], encodeNaturals [0, 0]] (.sym "None") := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      target 3 [] [0, 0] = none := by decide +kernel
  simpa only [computed, encodeResult] using theory_unfolding_computes admitted target 3 [] [0, 0]

theorem distinct_dummies_compute_closed_result :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 3,
        encodeExpressions [], encodeNaturals [0, 1]] (encodeResult (some (all 0 (all 1 (rel 0 1))))) := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      target 3 [] [0, 1] = some (all 0 (all 1 (rel 0 1))) := by decide +kernel
  simpa only [computed] using theory_unfolding_computes admitted target 3 [] [0, 1]

theorem declaration_without_a_body_cannot_unfold :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 1,
        encodeExpressions [.var 0, rel 0 1], encodeNaturals []] (.sym "None") := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      target 1 [.var 0, rel 0 1] [] = none := by decide +kernel
  simpa only [computed, encodeResult] using theory_unfolding_computes admitted target 1 [.var 0, rel 0 1] []

theorem prior_theory_cannot_publish_a_later_body :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable beforeBodies.terms, encodeDefinitions beforeBodies.definitions, encodeContext target,
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 2,
        encodeExpressions [.var 0], encodeNaturals [1]] (.sym "None") := by
  have computed : Definition.unfold? beforeBodies.termSignature beforeBodies.definitionSignature
      target 2 [.var 0] [1] = none := by decide +kernel
  simpa only [computed, encodeResult] using theory_unfolding_computes beforeBodies target 2 [.var 0] [1]

theorem wrong_dummy_sort_completes_with_none :
    Applies unfoldingProgram computationalHost "mm0:unfold"
      [encodeTable admitted.terms, encodeDefinitions admitted.definitions,
        encodeContext [.bound 0, .bound 1], Mettapedia.GSLT.LanguageDef.DeterministicEquations.natural 2,
        encodeExpressions [.var 0], encodeNaturals [1]] (.sym "None") := by
  have computed : Definition.unfold? admitted.termSignature admitted.definitionSignature
      [.bound 0, .bound 1] 2 [.var 0] [1] = none := by decide +kernel
  simpa only [computed, encodeResult] using theory_unfolding_computes admitted [.bound 0, .bound 1] 2 [.var 0] [1]

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3Unfolding
