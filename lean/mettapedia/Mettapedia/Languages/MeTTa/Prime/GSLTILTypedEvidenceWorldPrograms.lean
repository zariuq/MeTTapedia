import Mettapedia.GSLT.LanguageDef.GSLTILTypedEvidenceRoutes
import Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax

/-!
# Proof-world interpretation of intrinsic Prime route programs

A finite Prime language-operation signature already supplies independently
typed endpoint-indexed route programs and a structural interpretation into
validated language definitions.  This module adds the displayed data needed
to transport proof-relevant GSLT-IL elaboration worlds.

Each primitive generator receives a typed evidence route whose structural
projection is exactly the signature's authored structural morphism.  The free
path syntax then extends that data uniquely by identity and composition.
Consequently every intrinsic route program constructs a command/evidence map,
an `EvidenceWorldMap` at each source command, and an internal action proved to
agree with the program's structural interpretation.

The negative control is essential.  The same typed route program and the same
structural morphism admit both a history-reflecting evidence interpretation
and a history-collapsing one.  Typed route syntax determines the structural
action, but proof-world transport and reflection are additional capabilities;
neither may be inferred from the route name alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms

open CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes.TypedEvidenceRoute
open Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature
open Mettapedia.Languages.MeTTa.Prime.LanguageDef
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## A displayed interpretation of a finite typed route signature -/

/-- Evidence-valued hosted profiles over every language of one finite
signature, plus a proof-world action for every authored primitive route.  The
last field prevents an evidence route from silently selecting a different
structural language transformation. -/
structure SignatureEvidenceInterpretation (signature : Signature) where
  profileAt : forall language,
    EvidenceProfileOver (signature.presentation language)
  onGenerator : forall {source target},
    signature.Generator source target ->
      TypedEvidenceRoute (profileAt source) (profileAt target)
  onGenerator_structural : forall {source target}
      (generator : signature.Generator source target),
    (onGenerator generator).structural =
      signature.structuralPrefunctor.map generator

namespace SignatureEvidenceInterpretation

variable {signature : Signature}

/-- Interpret an intrinsically endpoint-indexed free route program by
composing its primitive evidence routes. -/
def mapProgram (interpretation : SignatureEvidenceInterpretation signature) :
    forall {source target}, signature.Program source target ->
      TypedEvidenceRoute (interpretation.profileAt source)
        (interpretation.profileAt target)
  | _, _, .nil => TypedEvidenceRoute.id (interpretation.profileAt _)
  | _, _, .cons prior generator =>
      TypedEvidenceRoute.comp (interpretation.mapProgram prior)
        (interpretation.onGenerator generator)

/-- The displayed proof-world interpretation projects to exactly the
signature's existing structural path interpretation. -/
theorem mapProgram_structural
    (interpretation : SignatureEvidenceInterpretation signature)
    {source target : signature.Language}
    (program : signature.Program source target) :
    (interpretation.mapProgram program).structural =
      signature.structuralInterpretation.map program := by
  induction program with
  | nil =>
      simp [mapProgram, Signature.structuralInterpretation,
        TypedEvidenceRoute.id]
      apply StructuralMorphism.ext
      rfl
  | cons prior generator inductionHypothesis =>
      simp [mapProgram, Signature.structuralInterpretation,
        TypedEvidenceRoute.comp, inductionHypothesis,
        interpretation.onGenerator_structural generator]
      apply StructuralMorphism.ext
      rfl

/-- Therefore the executable internal map carried by the interpreted route is
exactly the structural pattern action selected by the same typed program. -/
theorem mapProgram_internal_structural
    (interpretation : SignatureEvidenceInterpretation signature)
    {source target : signature.Language}
    (program : signature.Program source target) (internal : Pattern) :
    (interpretation.mapProgram program).mapInternal internal =
      mapPattern (signature.structuralInterpretation.map program).symbols
        internal := by
  calc
    (interpretation.mapProgram program).mapInternal internal =
        mapPattern (interpretation.mapProgram program).structural.symbols
          internal :=
      (interpretation.mapProgram program).mapInternal_structural internal
    _ = mapPattern (signature.structuralInterpretation.map program).symbols
          internal := by rw [interpretation.mapProgram_structural program]

/-- Identity programs act identically on complete command histories. -/
@[simp] theorem mapProgram_identity_history
    (interpretation : SignatureEvidenceInterpretation signature)
    (language : signature.Language)
    (state : Sigma fun command =>
      List ((interpretation.profileAt language).profile.World command)) :
    (interpretation.mapProgram (signature.identityProgram language)).mapCommandHistory
        state = state := by
  simpa only [Signature.identityProgram, mapProgram] using
    TypedEvidenceRoute.mapCommandHistory_id
      (interpretation.profileAt language) state

/-- Free-path composition is interpreted as literal composition of complete
command-history transport. -/
theorem mapProgram_comp_history
    (interpretation : SignatureEvidenceInterpretation signature)
    {first middle last : signature.Language}
    (earlier : signature.Program first middle)
    (later : signature.Program middle last)
    (state : Sigma fun command =>
      List ((interpretation.profileAt first).profile.World command)) :
    (interpretation.mapProgram (Quiver.Path.comp earlier later)).mapCommandHistory
        state =
      (interpretation.mapProgram later).mapCommandHistory
        ((interpretation.mapProgram earlier).mapCommandHistory state) := by
  induction later with
  | nil =>
      simp [mapProgram]
  | cons prior generator inductionHypothesis =>
      simp only [Quiver.Path.comp_cons, mapProgram,
        TypedEvidenceRoute.mapCommandHistory_comp]
      rw [inductionHypothesis]

/-! ## Reflection inherited from primitive capabilities -/

/-- Every authored generator reflects command identity and complete worlds. -/
def GeneratorReflects
    (interpretation : SignatureEvidenceInterpretation signature) : Prop :=
  forall {source target}
      (generator : signature.Generator source target),
    (interpretation.onGenerator generator).ReflectsCommands /\
      (interpretation.onGenerator generator).ReflectsWorlds

/-- Reflection capabilities compose over the same free route syntax. -/
theorem mapProgram_reflects
    (interpretation : SignatureEvidenceInterpretation signature)
    (generatorReflects : interpretation.GeneratorReflects)
    {source target : signature.Language}
    (program : signature.Program source target) :
    (interpretation.mapProgram program).ReflectsCommands /\
      (interpretation.mapProgram program).ReflectsWorlds := by
  induction program with
  | nil =>
      simpa only [mapProgram] using
        ⟨
          TypedEvidenceRoute.id_reflectsCommands _,
          TypedEvidenceRoute.id_reflectsWorlds _
        ⟩
  | cons prior generator inductionHypothesis =>
      have generatorCapabilities := generatorReflects generator
      simpa only [mapProgram] using
        ⟨
          TypedEvidenceRoute.comp_reflectsCommands _ _
            inductionHypothesis.1 generatorCapabilities.1,
          TypedEvidenceRoute.comp_reflectsWorlds _ _
            inductionHypothesis.2 generatorCapabilities.2
        ⟩

/-- When every primitive earns reflection, every typed route program reflects
its complete dependent command histories. -/
theorem mapProgram_history_injective
    (interpretation : SignatureEvidenceInterpretation signature)
    (generatorReflects : interpretation.GeneratorReflects)
    {source target : signature.Language}
    (program : signature.Program source target) :
    Function.Injective
      (interpretation.mapProgram program).mapCommandHistory := by
  have reflected := interpretation.mapProgram_reflects generatorReflects program
  exact TypedEvidenceRoute.mapCommandHistory_injective _
    reflected.1 reflected.2

/-! ## Positive and negative controls on one genuine Prime route -/

namespace Canary

def atom (name : String) : Pattern := .apply name []
def space : Pattern := atom "world-space"
def state : Pattern := atom "world-state"

def authoredProgram : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program where
  spaceRules := []
  routes := []
  routeRules := []

def surface : Pattern := inSpace space state
def internal : Pattern := atPattern space state

theorem surface_elaborates : Elaborates authoredProgram surface internal := by
  exact Elaborates.inSpace space state

inductive RichEvidence : Pattern -> Type
  | first : RichEvidence internal
  | second : RichEvidence internal

inductive ThinEvidence : Pattern -> Type
  | only : ThinEvidence internal

def richProfile : Profile authoredProgram where
  Command := Unit
  surface := fun _ => surface
  Evidence := fun _ result => RichEvidence result
  sound := by
    intro command result evidence
    cases evidence <;> exact surface_elaborates

def thinProfile : Profile authoredProgram where
  Command := Unit
  surface := fun _ => surface
  Evidence := fun _ result => ThinEvidence result
  sound := by
    intro command result evidence
    cases evidence
    exact surface_elaborates

def richAt (presentation : ValidatedLanguageDef) :
    EvidenceProfileOver presentation where
  program := authoredProgram
  profile := richProfile

def thinAt (presentation : ValidatedLanguageDef) :
    EvidenceProfileOver presentation where
  program := authoredProgram
  profile := thinProfile

def firstWorld : richProfile.World () :=
  ⟨internal, RichEvidence.first⟩

def secondWorld : richProfile.World () :=
  ⟨internal, RichEvidence.second⟩

theorem sourceWorlds_distinct : firstWorld ≠ secondWorld := by
  intro equal
  injection equal with _ evidenceEqual
  cases evidenceEqual

/-- The current Zero-to-Prime route has identity symbol action and can retain
both proof histories exactly. -/
def richRoute :
    TypedEvidenceRoute
      (richAt currentZeroPresentation)
      (richAt currentPrimePresentation) where
  structural := currentZeroToPrimePresentation
  mapCommand := _root_.id
  mapInternal := _root_.id
  mapInternal_structural := by
    intro value
    change value = mapPattern LanguageDefSymbolMap.id value
    exact (mapPattern_id value).symm
  surface_natural := fun _ => rfl
  mapEvidence := _root_.id

@[simp] theorem richRoute_atCommand_mapWorld
    (world : richProfile.World ()) :
    (richRoute.atCommand ()).mapWorld world = world := by
  rcases world with ⟨internal, evidence⟩
  rfl

@[simp] theorem richRoute_atCommand_mapHistory
    (history : List (richProfile.World ())) :
    (richRoute.atCommand ()).mapHistory history = history := by
  induction history with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (richRoute.atCommand ()).mapWorld head ::
            (richRoute.atCommand ()).mapHistory tail =
          head :: tail
      rw [richRoute_atCommand_mapWorld, inductionHypothesis]
      rfl

/-- The same structural route may soundly retain only a coarser target proof
history.  It remains a forward route but does not reflect source history. -/
def collapseRoute :
    TypedEvidenceRoute
      (richAt currentZeroPresentation)
      (thinAt currentPrimePresentation) where
  structural := currentZeroToPrimePresentation
  mapCommand := _root_.id
  mapInternal := _root_.id
  mapInternal_structural := by
    intro value
    change value = mapPattern LanguageDefSymbolMap.id value
    exact (mapPattern_id value).symm
  surface_natural := fun _ => rfl
  mapEvidence := by
    intro command result evidence
    cases evidence <;> exact ThinEvidence.only

def richInterpretation :
    SignatureEvidenceInterpretation currentOperationSignature where
  profileAt := fun language =>
    richAt (currentOperationSignature.presentation language)
  onGenerator := by
    intro source target generator
    cases generator with
    | named route =>
        have routeEqual : route = 0 := Subsingleton.elim _ _
        subst route
        exact richRoute
  onGenerator_structural := by
    intro source target generator
    cases generator with
    | named route =>
        have routeEqual : route = 0 := Subsingleton.elim _ _
        subst route
        rfl

def collapseProfileAt (language : Language) :
    EvidenceProfileOver (currentOperationSignature.presentation language) :=
  match language with
  | .zero => richAt currentZeroPresentation
  | .prime => thinAt currentPrimePresentation

def collapseInterpretation :
    SignatureEvidenceInterpretation currentOperationSignature where
  profileAt := collapseProfileAt
  onGenerator := by
    intro source target generator
    cases generator with
    | named route =>
        have routeEqual : route = 0 := Subsingleton.elim _ _
        subst route
        exact collapseRoute
  onGenerator_structural := by
    intro source target generator
    cases generator with
    | named route =>
        have routeEqual : route = 0 := Subsingleton.elim _ _
        subst route
        rfl

def richSourceHistory :
    Sigma fun command => List (richProfile.World command) :=
  ⟨(), [firstWorld, secondWorld]⟩

def richTargetHistory :
    Sigma fun command => List (richProfile.World command) :=
  ⟨(), [firstWorld, secondWorld]⟩

/-- The displayed route selected for the genuine typed Prime `promote`
generator retains both proof histories, their order, and their occurrence
multiplicity. -/
theorem rich_promote_retains_complete_history :
    richRoute.mapCommandHistory richSourceHistory = richTargetHistory :=
  by
    rfl

theorem richRoute_reflectsCommands : richRoute.ReflectsCommands := by
  intro first second equal
  exact equal

theorem richRoute_reflectsWorlds : richRoute.ReflectsWorlds := by
  intro command first second equal
  exact equal

theorem richInterpretation_generatorReflects :
    richInterpretation.GeneratorReflects := by
  intro source target generator
  cases generator with
  | named route =>
      have routeEqual : route = 0 := Subsingleton.elim _ _
      subst route
      exact ⟨richRoute_reflectsCommands, richRoute_reflectsWorlds⟩

theorem rich_promote_history_injective :
    Function.Injective richRoute.mapCommandHistory :=
  TypedEvidenceRoute.mapCommandHistory_injective richRoute
    richRoute_reflectsCommands richRoute_reflectsWorlds

def firstSourceSingleton :
    Sigma fun command => List (richProfile.World command) :=
  ⟨(), [firstWorld]⟩

def secondSourceSingleton :
    Sigma fun command => List (richProfile.World command) :=
  ⟨(), [secondWorld]⟩

theorem sourceSingletons_distinct :
    firstSourceSingleton ≠ secondSourceSingleton := by
  intro equal
  have historiesEqual : [firstWorld] = [secondWorld] := by
    exact eq_of_heq (Sigma.mk.inj equal).2
  exact sourceWorlds_distinct (List.cons.inj historiesEqual).1

/-- The same typed `promote` program may carry a forward evidence capability
that identifies the two source histories. -/
theorem collapse_promote_identifies_source_histories :
    collapseRoute.mapCommandHistory firstSourceSingleton =
      collapseRoute.mapCommandHistory secondSourceSingleton :=
  by
    rfl

theorem collapse_promote_not_history_reflecting :
    ¬ Function.Injective collapseRoute.mapCommandHistory := by
  intro injective
  exact sourceSingletons_distinct
    (injective collapse_promote_identifies_source_histories)

/-- Both capabilities lie over the structural interpretation of the exact
same intrinsic typed `promote` program.  Route syntax and structural
preservation alone therefore do not determine proof-history reflection. -/
theorem same_typed_program_different_history_capabilities :
    richRoute.structural =
      currentOperationSignature.structuralInterpretation.map promoteProgram /\
    collapseRoute.structural =
      currentOperationSignature.structuralInterpretation.map promoteProgram /\
    Function.Injective richRoute.mapCommandHistory /\
    ¬ Function.Injective collapseRoute.mapCommandHistory := by
  have programStructural :=
    currentOperationSignature.structuralInterpretation_named 0
  exact ⟨programStructural.symm, programStructural.symm,
    rich_promote_history_injective,
    collapse_promote_not_history_reflecting⟩

end Canary

#print axioms mapProgram_structural
#print axioms mapProgram_internal_structural
#print axioms mapProgram_comp_history
#print axioms mapProgram_reflects
#print axioms mapProgram_history_injective
#print axioms Canary.rich_promote_retains_complete_history
#print axioms Canary.collapse_promote_identifies_source_histories
#print axioms Canary.collapse_promote_not_history_reflecting
#print axioms Canary.same_typed_program_different_history_capabilities

end SignatureEvidenceInterpretation

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms
