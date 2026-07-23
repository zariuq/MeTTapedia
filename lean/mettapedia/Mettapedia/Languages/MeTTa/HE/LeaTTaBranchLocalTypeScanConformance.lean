import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance

/-!
# Branch-local freshening boundary for argument applicability

The runtime recomputes every later argument's fresh candidate family under
the binding state of the successful branch that reaches it.  Distinct
branches therefore need not share literal tail candidate lists.  The
independent specification keeps one static ordered family; this bridge alone
admits a branch-local runtime alpha sibling at each recursive node.

Private spellings are quotiented only in the scoped simulation state and the
actual-type field of diagnostics.  Candidate order, multiplicity, branch
success positions, and error-ledger order remain exact data.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBranchLocalTypeScanConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationSelectionConformance

/-- Pointwise alpha siblinghood between one static specification family and
the candidate family prepared under a particular runtime branch. -/
def PrivateCandidateFamilyAlphaRel
    (fixedScope : List String) (spec runtime : List Atom) : Prop :=
  List.Forall₂ (PrivateCandidateAlphaRel fixedScope) spec runtime

/-- Every candidate is a lawful private alpha sibling of itself when no name
is reserved. -/
theorem PrivateCandidateAlphaRel.refl_empty (candidate : Atom) :
    PrivateCandidateAlphaRel [] candidate candidate := by
  have variant : TypeCandidateAlphaVariantRel [] candidate candidate := by
    rcases TypeVariableRenamingOf.refl candidate with
      ⟨rename, injective, equation⟩
    exact ⟨rename, injective, equation, by simp⟩
  exact ⟨candidate, variant, variant⟩

/-- Pointwise empty-scope reflexivity for an ordered candidate family. -/
theorem PrivateCandidateFamilyAlphaRel.refl_empty (candidates : List Atom) :
    PrivateCandidateFamilyAlphaRel [] candidates candidates := by
  induction candidates with
  | nil => exact .nil
  | cons candidate candidates inductionHypothesis =>
      exact .cons (PrivateCandidateAlphaRel.refl_empty candidate)
        inductionHypothesis

/-! ## Two-history presentation support -/

/-- Variables available to one private presentation: the public boundary
plus the selected candidate at each earlier argument position.  Candidate
history contains no generator or counter; those belong only to the concrete
realization theorem. -/
def argumentPresentationSupport
    (publicScope : List String) (selectedCandidates : List Atom) :
    List String :=
  publicScope ++ TypeSubst.typeVarsList selectedCandidates

/-- The weakest literal scope protected at one branch node: the variables
actually present in the two incoming presentations, plus the theory and
formal observed at this step.  Candidate histories justify these supports;
they do not pad the scope with names absent from the presentations. -/
def twoHistoryCandidateNodeScope
    (specPresentation branchPresentation : TypeSubst)
    (theoryScope : List String) (formal : Atom) : List String :=
  specBindingVars (⟨specPresentation, []⟩ : Bindings) ++
    specBindingVars (⟨branchPresentation, []⟩ : Bindings) ++
      theoryScope ++ TypeSubst.typeVars formal

/-- Every key and stored variable in one finite presentation lies in its
side's selected-candidate history. -/
def TypePresentationSupportedByCandidateHistory
    (publicScope : List String) (selectedCandidates : List Atom)
    (presentation : TypeSubst) : Prop :=
  ∀ name, name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
    name ∈ argumentPresentationSupport publicScope selectedCandidates

/-- Proof-side recursive state for independently freshened static and
runtime candidate histories.

The two histories are deliberately distinct: a successful static branch may
store `uStatic`, while the corresponding runtime branch stores the private
alpha sibling `uRuntime`.  Each history has exactly one selected candidate
per completed argument position.  Their pointwise link reuses
`PrivateCandidateAlphaRel`; private spellings are never equated. -/
def TwoHistoryScopedTypePresentationSimulationState
    (theoryScope publicScope : List String) (position : Nat)
    (staticHistory runtimeHistory : List Atom)
    (specPresentation branchPresentation : TypeSubst)
    (runtimeBindings : Metta.Bindings) : Prop :=
  staticHistory.length = position ∧
    runtimeHistory.length = position ∧
    List.Forall₂
      (fun specCandidate runtimeCandidate =>
        ∃ fixedScope,
          PrivateCandidateAlphaRel fixedScope
            specCandidate runtimeCandidate)
      staticHistory runtimeHistory ∧
    specPresentation.Normal ∧
    ∃ specBindings,
      TypePresentationSimulationState
          branchPresentation specBindings runtimeBindings ∧
        TypePresentationTheoryEquivAt
          theoryScope specPresentation branchPresentation ∧
        TypePresentationSupportedByCandidateHistory
          publicScope staticHistory specPresentation ∧
        TypePresentationSupportedByCandidateHistory
          publicScope runtimeHistory branchPresentation

/-- Forgetting the two private histories recovers the existing scoped
simulation boundary. -/
theorem TwoHistoryScopedTypePresentationSimulationState.toScoped
    {theoryScope publicScope : List String} {position : Nat}
    {staticHistory runtimeHistory : List Atom}
    {specPresentation branchPresentation : TypeSubst}
    {runtimeBindings : Metta.Bindings}
    (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope position staticHistory runtimeHistory specPresentation
        branchPresentation runtimeBindings) :
    ScopedTypePresentationSimulationState theoryScope specPresentation
      runtimeBindings := by
  rcases state with ⟨_, _, _, normal, specBindings,
    branchState, theoryEquiv, _, _⟩
  exact ⟨normal, branchPresentation, specBindings, branchState,
    theoryEquiv⟩

/-- An opaque predicate over the two-history recursive proof state. -/
abbrev TwoHistoryScanStateInvariant :=
  Nat → List Atom → List Atom → TypeSubst → Metta.Bindings → Prop

/-- Position-indexed pointwise alignment between source arguments and their
static candidate families.  The index names a family-list position only; it
does not expose the runtime fresh-name counter. -/
inductive PositionedArgumentCandidateFamiliesRel
    (candidateFamily : Nat → Atom → List Atom → Prop) :
    Nat → List Atom → List (List Atom) → Prop where
  | nil (position : Nat) :
      PositionedArgumentCandidateFamiliesRel candidateFamily position [] []
  | cons {position : Nat} {argument : Atom} {arguments : List Atom}
      {candidates : List Atom} {candidateLists : List (List Atom)} :
      candidateFamily position argument candidates →
      PositionedArgumentCandidateFamiliesRel candidateFamily
        (position + 1) arguments candidateLists →
      PositionedArgumentCandidateFamiliesRel candidateFamily position
        (argument :: arguments) (candidates :: candidateLists)

/-- An ordinary pointwise family relation embeds into the position-indexed
boundary when the family predicate itself is position-independent.  This is
the adapter used by the abstract preparation service; runtime position is
carried only by the recursive scan. -/
theorem PositionedArgumentCandidateFamiliesRel.ofForall₂
    {candidateFamily : Atom → List Atom → Prop}
    {arguments : List Atom} {candidateLists : List (List Atom)}
    (families : List.Forall₂ candidateFamily arguments candidateLists)
    (position : Nat) :
    PositionedArgumentCandidateFamiliesRel
      (fun _ => candidateFamily) position arguments candidateLists := by
  induction families generalizing position with
  | nil => exact .nil position
  | cons head _ inductionHypothesis =>
      exact .cons head (inductionHypothesis (position + 1))

/-- Two position-indexed views over the same ordered families combine
pointwise without changing their list structure. -/
theorem PositionedArgumentCandidateFamiliesRel.and
    {left right : Nat → Atom → List Atom → Prop}
    {position : Nat} {arguments : List Atom}
    {candidateLists : List (List Atom)}
    (leftFamilies : PositionedArgumentCandidateFamiliesRel left position
      arguments candidateLists)
    (rightFamilies : PositionedArgumentCandidateFamiliesRel right position
      arguments candidateLists) :
    PositionedArgumentCandidateFamiliesRel
      (fun position argument candidates =>
        left position argument candidates ∧
          right position argument candidates)
      position arguments candidateLists := by
  induction leftFamilies with
  | nil position => cases rightFamilies; exact .nil position
  | cons leftHead _ inductionHypothesis =>
      cases rightFamilies with
      | cons rightHead rightTail =>
          exact .cons ⟨leftHead, rightHead⟩
            (inductionHypothesis rightTail)

/-- Empty histories, presentations, and runtime bindings establish the
two-history simulation state at an application boundary. -/
theorem twoHistoryScopedTypePresentationSimulationState_empty
    (theoryScope publicScope : List String) :
    TwoHistoryScopedTypePresentationSimulationState theoryScope publicScope
      0 [] [] [] [] Metta.Bindings.empty := by
  refine ⟨rfl, rfl, .nil, TypeSubst.normal_empty, Bindings.empty,
    typePresentationSimulationState_empty,
    TypePresentationTheoryEquivAt.refl theoryScope [], ?_, ?_⟩
  · simp [TypePresentationSupportedByCandidateHistory,
      argumentPresentationSupport, specBindingVars]
  · simp [TypePresentationSupportedByCandidateHistory,
      argumentPresentationSupport, specBindingVars]

/-- Avoiding a singleton is exactly absence of that name from a finite
presentation's keys and stored values. -/
theorem typeSubst_avoids_singleton_iff
    (presentation : TypeSubst) (name : String) :
    presentation.Avoids [name] ↔
      name ∉ specBindingVars (⟨presentation, []⟩ : Bindings) := by
  have varsEquation :
      specBindingVars (⟨presentation, []⟩ : Bindings) =
        presentation.flatMap
          (fun entry => entry.1 :: TypeSubst.typeVars entry.2) := by
    simp [specBindingVars]
  constructor
  · intro avoids member
    rw [varsEquation, List.mem_flatMap] at member
    obtain ⟨⟨key, value⟩, entryMember, occurrence⟩ := member
    simp only [List.mem_cons] at occurrence
    rcases occurrence with keyEquation | valueOccurrence
    · subst key
      exact avoids.keys name
        (by
          simp only [TypeSubst.keys, List.mem_map]
          exact ⟨(name, value), entryMember, rfl⟩)
        (by simp)
    · exact avoids.values key value entryMember name valueOccurrence
        (by simp)
  · intro absent
    constructor
    · intro key keyMember singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst key
      apply absent
      rw [varsEquation, List.mem_flatMap]
      obtain ⟨⟨key, value⟩, entryMember, keyEquation⟩ :=
        List.mem_map.mp keyMember
      simp only at keyEquation
      subst key
      exact ⟨(name, value), entryMember, by simp⟩
    · intro key value entryMember candidate candidateMember
        singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst candidate
      apply absent
      rw [varsEquation, List.mem_flatMap]
      exact ⟨(key, value), entryMember, by simp [candidateMember]⟩

/-- A presentation match can mention only names already present in its
incoming presentation or in the two matched atoms.  This support theorem is
derived from the general freshness theorem, so it covers every current and
future presentation constructor uniformly. -/
theorem corePlusR2TypePresentationMatch_output_support
    {incoming output : TypeSubst} {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      incoming left right output) :
    ∀ name,
      name ∈ specBindingVars (⟨output, []⟩ : Bindings) →
      name ∈ specBindingVars (⟨incoming, []⟩ : Bindings) ∨
        name ∈ TypeSubst.typeVars left ∨
        name ∈ TypeSubst.typeVars right := by
  intro name outputMember
  by_cases incomingMember :
      name ∈ specBindingVars (⟨incoming, []⟩ : Bindings)
  · exact Or.inl incomingMember
  by_cases leftMember : name ∈ TypeSubst.typeVars left
  · exact Or.inr (Or.inl leftMember)
  by_cases rightMember : name ∈ TypeSubst.typeVars right
  · exact Or.inr (Or.inr rightMember)
  exfalso
  have incomingAvoids : incoming.Avoids [name] :=
    (typeSubst_avoids_singleton_iff incoming name).mpr incomingMember
  have leftAvoids : AtomAvoids left [name] := by
    intro candidate occurrence singletonMember
    simp only [List.mem_singleton] at singletonMember
    subst candidate
    exact leftMember occurrence
  have rightAvoids : AtomAvoids right [name] := by
    intro candidate occurrence singletonMember
    simp only [List.mem_singleton] at singletonMember
    subst candidate
    exact rightMember occurrence
  have outputAvoids := corePlusR2TypePresentationMatch_output_avoids
    derivation incomingAvoids leftAvoids rightAvoids
  exact (typeSubst_avoids_singleton_iff output name).mp outputAvoids
    outputMember

/-- Variable support distributes over list append. -/
theorem typeVarsList_append (left right : List Atom) :
    TypeSubst.typeVarsList (left ++ right) =
      TypeSubst.typeVarsList left ++ TypeSubst.typeVarsList right := by
  induction left with
  | nil => rfl
  | cons atom left inductionHypothesis =>
      simp only [List.cons_append, TypeSubst.typeVarsList,
        inductionHypothesis, List.append_assoc]

/-- Matching one selected candidate extends a presentation's support history
by exactly that candidate.  No unselected alternative is added to the proof
state. -/
theorem TypePresentationSupportedByCandidateHistory.step
    {publicScope : List String} {selectedCandidates : List Atom}
    {incoming output : TypeSubst} {formal candidate : Atom}
    (supported : TypePresentationSupportedByCandidateHistory publicScope
      selectedCandidates incoming)
    (formalPublic : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ publicScope)
    (derivation : CorePlusR2TypePresentationMatchRel
      incoming formal candidate output) :
    TypePresentationSupportedByCandidateHistory publicScope
      (selectedCandidates ++ [candidate]) output := by
  intro name outputMember
  obtain incomingMember | formalMember | candidateOccurrence :=
    corePlusR2TypePresentationMatch_output_support derivation name
      outputMember
  · have previous := supported name incomingMember
    simp only [argumentPresentationSupport, List.mem_append] at previous ⊢
    rcases previous with publicMember | earlier
    · exact Or.inl publicMember
    · exact Or.inr (by
        rw [typeVarsList_append, List.mem_append]
        exact Or.inl earlier)
  · simp only [argumentPresentationSupport, List.mem_append]
    exact Or.inl (formalPublic name formalMember)
  · simp only [argumentPresentationSupport, List.mem_append]
    exact Or.inr (by
      rw [typeVarsList_append, List.mem_append]
      exact Or.inr (by
        simpa [TypeSubst.typeVarsList] using candidateOccurrence))

/-! ## Realization-side positional candidate families -/

/-- Freshen every alternative at one argument position with one private
counter.  This is an implementation-side witness constructor, not part of
the independent candidate relation. -/
def freshenCandidateFamily
    (avoid : List String) (position : Nat) (sources : List Atom) :
    List Atom :=
  sources.map fun source =>
    renameTypeVars
      (Metta.Minimal.captureAvoidingName avoid position) source

/-- Freshen an ordered list of alternative families left-to-right.  Every
position extends the avoid set by all variables emitted at that position;
alternatives within one position intentionally share its counter. -/
def freshenArgumentCandidateFamilies :
    List String → Nat → List (List Atom) → List (List Atom)
  | _, _, [] => []
  | avoid, position, sources :: remaining =>
      let targets := freshenCandidateFamily avoid position sources
      targets :: freshenArgumentCandidateFamilies
        (avoid ++ TypeSubst.typeVarsList targets) (position + 1) remaining

/-- One realization-side family translates exactly to pointwise runtime
freshening of the translated source family. -/
theorem toLeaTTaAtoms_freshenCandidateFamily
    (avoid : List String) (position : Nat) (sources : List Atom) :
    toLeaTTaAtoms (freshenCandidateFamily avoid position sources) =
      (toLeaTTaAtoms sources).map
        (Metta.Minimal.freshenTypeCandidate avoid position) := by
  induction sources with
  | nil => rfl
  | cons source sources inductionHypothesis =>
      simp only [freshenCandidateFamily, List.map_cons, toLeaTTaAtoms]
      exact congrArg₂ List.cons
        (LeaTTaTypePresentationExactConformance.toLeaTTaAtom_renameTypeVars
          (Metta.Minimal.captureAvoidingName avoid position) source)
        inductionHypothesis

/-- Pointwise realization-side freshening is a lawful alpha presentation at
the exact avoid set used to generate it. -/
theorem freshenCandidateFamily_alphaVariants
    (avoid : List String) (position : Nat) (sources : List Atom) :
    List.Forall₂ (TypeCandidateAlphaVariantRel avoid) sources
      (freshenCandidateFamily avoid position sources) := by
  induction sources with
  | nil => exact .nil
  | cons source sources inductionHypothesis =>
      apply List.Forall₂.cons
      · exact ⟨Metta.Minimal.captureAvoidingName avoid position,
          Metta.Minimal.captureAvoidingName_injective avoid position,
          rfl, fun name _ =>
            Metta.Minimal.captureAvoidingName_not_mem avoid position name⟩
      · exact inductionHypothesis

/-- Every generated variable in one candidate family records that family's
single argument-position counter. -/
theorem freshenCandidateFamily_var_generated
    (avoid : List String) (position : Nat) (sources : List Atom) :
    ∀ name ∈ TypeSubst.typeVarsList
        (freshenCandidateFamily avoid position sources),
      ∃ sourceName ∈ TypeSubst.typeVarsList sources,
        name = Metta.Minimal.captureAvoidingName
          avoid position sourceName := by
  intro name member
  rw [freshenCandidateFamily,
    Spec.Type.Presentation.ScopeObservation.typeVarsList_renameTypeVars]
    at member
  obtain ⟨sourceName, sourceMember, rfl⟩ := List.mem_map.mp member
  exact ⟨sourceName, sourceMember, rfl⟩

/-- Families produced at distinct generator positions realize the shared
semantic separation interface.  The statement forgets the generator after
the proof, so specification-side consumers depend only on
`FreshFamiliesSeparated`. -/
theorem freshenCandidateFamily_separated_of_position_ne
    {leftPosition rightPosition : Nat}
    (positionNe : leftPosition ≠ rightPosition)
    (leftAvoid rightAvoid : List String)
    (leftSources rightSources : List Atom) :
    FreshFamiliesSeparated
      (freshenCandidateFamily leftAvoid leftPosition leftSources)
      (freshenCandidateFamily rightAvoid rightPosition rightSources) := by
  intro name leftMember rightMember
  obtain ⟨leftSource, _leftSourceMember, leftEquation⟩ :=
    freshenCandidateFamily_var_generated leftAvoid leftPosition leftSources
      name leftMember
  obtain ⟨rightSource, _rightSourceMember, rightEquation⟩ :=
    freshenCandidateFamily_var_generated rightAvoid rightPosition rightSources
      name rightMember
  exact Metta.Minimal.captureAvoidingName_ne_of_counter_ne positionNe
    (leftEquation.symm.trans rightEquation)

/-- A family generated immediately after all ordered argument positions is
separated from their complete flattened output.  This is the common
realization theorem for a localized operator signature versus independently
freshened argument candidates; neither avoid set needs to mention the other
generated family. -/
theorem freshenCandidateFamily_separated_from_argumentFamilies
    (signatureAvoid argumentAvoid : List String) (position : Nat)
    (signatureSources : List Atom) (argumentSources : List (List Atom)) :
    FreshFamiliesSeparated
      (freshenCandidateFamily signatureAvoid
        (position + argumentSources.length) signatureSources)
      (freshenArgumentCandidateFamilies argumentAvoid position
        argumentSources).flatten := by
  induction argumentSources generalizing argumentAvoid position with
  | nil =>
      simp [freshenArgumentCandidateFamilies, FreshFamiliesSeparated,
        AtomsAvoid, TypeSubst.typeVarsList]
  | cons sourceFamily remaining inductionHypothesis =>
      let targetFamily :=
        freshenCandidateFamily argumentAvoid position sourceFamily
      let tailAvoid := argumentAvoid ++ TypeSubst.typeVarsList targetFamily
      have headSeparated : FreshFamiliesSeparated
          (freshenCandidateFamily signatureAvoid
            (position + (sourceFamily :: remaining).length) signatureSources)
          targetFamily := by
        apply freshenCandidateFamily_separated_of_position_ne
        simp
      have tailSeparated := inductionHypothesis tailAvoid (position + 1)
      have positionEquation :
          (position + 1) + remaining.length =
            position + (sourceFamily :: remaining).length := by
        simp
        omega
      rw [positionEquation] at tailSeparated
      intro name signatureOccurrence argumentOccurrence
      obtain ⟨argument, argumentMember, variableMember⟩ :=
        exists_mem_of_mem_typeVarsList argumentOccurrence
      simp only [freshenArgumentCandidateFamilies, List.flatten_cons,
        List.mem_append] at argumentMember
      rcases argumentMember with headMember | tailMember
      · exact headSeparated name signatureOccurrence
          (typeVars_mem_typeVarsList_of_mem headMember name variableMember)
      · exact tailSeparated name signatureOccurrence
          (typeVars_mem_typeVarsList_of_mem tailMember name variableMember)

/-- An alpha presentation that avoids a larger scope also avoids any
pointwise smaller scope. -/
theorem TypeCandidateAlphaVariantRel.mono
    {small large : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel large source target)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    TypeCandidateAlphaVariantRel small source target := by
  rcases variant with ⟨rename, injective, equation, fresh⟩
  exact ⟨rename, injective, equation,
    fun name occurrence smallMember =>
      fresh name occurrence (subset (rename name) smallMember)⟩

/-- Replace an alpha variant's protected scope using a direct freshness proof
for its target.  The source renaming and injectivity evidence are unchanged. -/
theorem TypeCandidateAlphaVariantRel.changeScope
    {oldScope newScope : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel oldScope source target)
    (targetAvoids : AtomAvoids target newScope) :
    TypeCandidateAlphaVariantRel newScope source target := by
  rcases variant with ⟨rename, injective, equation, _⟩
  refine ⟨rename, injective, equation, ?_⟩
  intro name occurrence scopeMember
  apply targetAvoids (rename name)
  · rw [equation,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    exact List.mem_map_of_mem occurrence
  · exact scopeMember

/-- Pointwise alpha variants can all be retargeted to a new protected scope
when their complete target family avoids it. -/
theorem candidateFamilyAlphaVariants_changeScope
    {oldScope newScope : List String} {sources targets : List Atom}
    (variants : List.Forall₂
      (TypeCandidateAlphaVariantRel oldScope) sources targets)
    (targetsAvoid : AtomsAvoid targets newScope) :
    List.Forall₂ (TypeCandidateAlphaVariantRel newScope)
      sources targets := by
  induction variants with
  | nil => exact .nil
  | @cons source target sources targets head tail inductionHypothesis =>
      have headAvoid : AtomAvoids target newScope := by
        intro name occurrence scopeMember
        exact targetsAvoid name
          (by
            simp only [TypeSubst.typeVarsList, List.mem_append]
            exact Or.inl occurrence)
          scopeMember
      have tailAvoid : AtomsAvoid targets newScope := by
        intro name occurrence scopeMember
        exact targetsAvoid name
          (by
            simp only [TypeSubst.typeVarsList, List.mem_append]
            exact Or.inr occurrence)
          scopeMember
      exact .cons (TypeCandidateAlphaVariantRel.changeScope head headAvoid)
        (inductionHypothesis tailAvoid)

/-- Two ordered alpha presentations of one source family form pointwise
private siblings at their common protected scope. -/
theorem privateCandidateFamilyAlpha_of_variants
    {fixedScope : List String} {sources left right : List Atom}
    (leftVariants : List.Forall₂
      (TypeCandidateAlphaVariantRel fixedScope) sources left)
    (rightVariants : List.Forall₂
      (TypeCandidateAlphaVariantRel fixedScope) sources right) :
    PrivateCandidateFamilyAlphaRel fixedScope left right := by
  induction leftVariants generalizing right with
  | nil => cases rightVariants; exact .nil
  | cons leftHead _ inductionHypothesis =>
      cases rightVariants with
      | cons rightHead rightTail =>
          exact .cons ⟨_, leftHead, rightHead⟩
            (inductionHypothesis rightTail)

/-- Generator-produced presentations of the same ordered source family are
private siblings once each target family is fresh from the requested scope.
Their local avoid sets and even their counter spellings may differ. -/
theorem freshenCandidateFamilies_privateAlpha
    (fixedScope : List String) (sources : List Atom)
    (leftAvoid rightAvoid : List String)
    (leftPosition rightPosition : Nat)
    (leftFresh : AtomsAvoid
      (freshenCandidateFamily leftAvoid leftPosition sources) fixedScope)
    (rightFresh : AtomsAvoid
      (freshenCandidateFamily rightAvoid rightPosition sources) fixedScope) :
    PrivateCandidateFamilyAlphaRel fixedScope
      (freshenCandidateFamily leftAvoid leftPosition sources)
      (freshenCandidateFamily rightAvoid rightPosition sources) := by
  apply privateCandidateFamilyAlpha_of_variants
  · exact candidateFamilyAlphaVariants_changeScope
      (freshenCandidateFamily_alphaVariants leftAvoid leftPosition sources)
      leftFresh
  · exact candidateFamilyAlphaVariants_changeScope
      (freshenCandidateFamily_alphaVariants rightAvoid rightPosition sources)
      rightFresh

/-! ### Realization-only positional provenance -/

/-- One selected candidate was generated at a particular argument position.
This implementation witness is never a field of the independent scan. -/
def CandidateGeneratedAt (position : Nat) (candidate : Atom) : Prop :=
  ∃ avoid source,
    candidate = renameTypeVars
      (Metta.Minimal.captureAvoidingName avoid position) source

/-- Every member of a generated family carries its common position. -/
def CandidateFamilyGeneratedAt
    (position : Nat) (candidates : List Atom) : Prop :=
  ∀ candidate ∈ candidates, CandidateGeneratedAt position candidate

/-- Selected candidates accumulated from positions `0 .. position - 1`.
The semantic two-history state remains generator-free; this provenance is
consumed only by the concrete realization theorem. -/
inductive CandidateGenerationHistory : Nat → List Atom → Prop where
  | nil : CandidateGenerationHistory 0 []
  | snoc {position : Nat} {history : List Atom} {candidate : Atom} :
      CandidateGenerationHistory position history →
      CandidateGeneratedAt position candidate →
      CandidateGenerationHistory (position + 1)
        (history ++ [candidate])

/-- Generated-family membership exposes the shared positional witness. -/
theorem freshenCandidateFamily_generatedAt
    (avoid : List String) (position : Nat) (sources : List Atom) :
    CandidateFamilyGeneratedAt position
      (freshenCandidateFamily avoid position sources) := by
  intro candidate member
  rw [freshenCandidateFamily, List.mem_map] at member
  obtain ⟨source, _sourceMember, rfl⟩ := member
  exact ⟨avoid, source, rfl⟩

/-- Positional freshening of ordered source families exposes generated-at
provenance at exactly the corresponding list position.  The source-family
relation is used only to align the argument and family lists. -/
theorem freshenArgumentCandidateFamilies_positionedGenerated
    {sourceFamily : Atom → List Atom → Prop}
    {arguments : List Atom} {sources : List (List Atom)}
    (families : List.Forall₂ sourceFamily arguments sources)
    (avoid : List String) (position : Nat) :
    PositionedArgumentCandidateFamiliesRel
      (fun position _ candidates =>
        CandidateFamilyGeneratedAt position candidates)
      position arguments
      (freshenArgumentCandidateFamilies avoid position sources) := by
  induction families generalizing avoid position with
  | nil => exact .nil position
  | @cons argument source arguments sources _ _ inductionHypothesis =>
      exact .cons
        (freshenCandidateFamily_generatedAt avoid position source)
        (inductionHypothesis
          (avoid ++ TypeSubst.typeVarsList
            (freshenCandidateFamily avoid position source))
          (position + 1))

/-- Candidates generated at distinct positions are structurally disjoint. -/
theorem CandidateGeneratedAt.varsDisjoint_of_position_ne
    {leftPosition rightPosition : Nat} {left right : Atom}
    (positionNe : leftPosition ≠ rightPosition)
    (leftGenerated : CandidateGeneratedAt leftPosition left)
    (rightGenerated : CandidateGeneratedAt rightPosition right) :
    VarsDisjoint left right := by
  obtain ⟨leftAvoid, leftSource, rfl⟩ := leftGenerated
  obtain ⟨rightAvoid, rightSource, rfl⟩ := rightGenerated
  intro name leftMember rightMember
  rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars,
      Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    at leftMember rightMember
  obtain ⟨leftName, _leftNameMember, leftEquation⟩ :=
    List.mem_map.mp leftMember
  obtain ⟨rightName, _rightNameMember, rightEquation⟩ :=
    List.mem_map.mp rightMember
  exact Metta.Minimal.captureAvoidingName_ne_of_counter_ne positionNe
    (leftEquation.trans rightEquation.symm)

/-- Every selected history member was generated at a strictly earlier
position. -/
theorem CandidateGenerationHistory.member_generated_lt
    {position : Nat} {history : List Atom}
    (generated : CandidateGenerationHistory position history) :
    ∀ {candidate}, candidate ∈ history →
      ∃ earlier, earlier < position ∧
        CandidateGeneratedAt earlier candidate := by
  induction generated with
  | nil => simp
  | @snoc position history candidate _ candidateGenerated
      inductionHypothesis =>
      intro selected member
      rw [List.mem_append] at member
      rcases member with earlierMember | currentMember
      · obtain ⟨earlier, bound, earlierGenerated⟩ :=
          inductionHypothesis earlierMember
        exact ⟨earlier, by omega, earlierGenerated⟩
      · simp only [List.mem_singleton] at currentMember
        subst selected
        exact ⟨position, by omega, candidateGenerated⟩

/-- A current-position candidate is disjoint from every candidate selected
at an earlier position. -/
theorem CandidateGenerationHistory.member_varsDisjoint_current
    {position : Nat} {history : List Atom} {current : Atom}
    (historyGenerated : CandidateGenerationHistory position history)
    (currentGenerated : CandidateGeneratedAt position current) :
    ∀ {earlier}, earlier ∈ history → VarsDisjoint earlier current := by
  intro earlier member
  obtain ⟨earlierPosition, bound, earlierGenerated⟩ :=
    historyGenerated.member_generated_lt member
  exact CandidateGeneratedAt.varsDisjoint_of_position_ne
    (Nat.ne_of_lt bound) earlierGenerated currentGenerated

/-- A complete current family avoids every private variable selected into an
earlier generated history. -/
theorem CandidateGenerationHistory.currentFamily_avoids
    {position : Nat} {history currentFamily : List Atom}
    (historyGenerated : CandidateGenerationHistory position history)
    (currentGenerated : CandidateFamilyGeneratedAt position currentFamily) :
    AtomsAvoid currentFamily (TypeSubst.typeVarsList history) := by
  intro name currentOccurrence historyOccurrence
  obtain ⟨current, currentMember, currentAtomOccurrence⟩ :=
    exists_mem_of_mem_typeVarsList currentOccurrence
  obtain ⟨earlier, earlierMember, earlierAtomOccurrence⟩ :=
    exists_mem_of_mem_typeVarsList historyOccurrence
  have disjoint := historyGenerated.member_varsDisjoint_current
    (currentGenerated current currentMember) earlierMember
  apply disjoint name
  · rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
    exact earlierAtomOccurrence
  · rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
    exact currentAtomOccurrence

/-- Pointwise alpha variants make the complete target family avoid their
declared public scope. -/
theorem candidateFamilyAlphaVariants_avoids
    {avoid : List String} {sources targets : List Atom}
    (variants : List.Forall₂
      (TypeCandidateAlphaVariantRel avoid) sources targets) :
    AtomsAvoid targets avoid := by
  induction variants with
  | nil => simp [AtomsAvoid, TypeSubst.typeVarsList]
  | @cons source target sources targets headVariant tailVariants
      inductionHypothesis =>
      intro name occurrence avoidMember
      rw [TypeSubst.typeVarsList, List.mem_append] at occurrence
      rcases occurrence with headOccurrence | tailOccurrence
      · exact
          LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
            headVariant name headOccurrence avoidMember
      · exact inductionHypothesis name tailOccurrence avoidMember

/-- A current generated family avoids every variable in a presentation
supported by the public boundary and an earlier generated history. -/
theorem CandidateGenerationHistory.currentFamily_avoids_supported
    {position : Nat} {history currentFamily : List Atom}
    {publicScope : List String} {presentation : TypeSubst}
    (historyGenerated : CandidateGenerationHistory position history)
    (currentGenerated : CandidateFamilyGeneratedAt position currentFamily)
    (currentAvoidsPublic : AtomsAvoid currentFamily publicScope)
    (supported : TypePresentationSupportedByCandidateHistory publicScope
      history presentation) :
    AtomsAvoid currentFamily
      (specBindingVars (⟨presentation, []⟩ : Bindings)) := by
  have currentAvoidsHistory :=
    historyGenerated.currentFamily_avoids currentGenerated
  intro name currentOccurrence presentationOccurrence
  have support := supported name presentationOccurrence
  simp only [argumentPresentationSupport, List.mem_append] at support
  rcases support with publicMember | historyMember
  · exact currentAvoidsPublic name currentOccurrence publicMember
  · exact currentAvoidsHistory name currentOccurrence historyMember

/-- A generated current family avoids the exact two-history node scope once
its public, theory, and current-formal boundaries are protected. -/
theorem TwoHistoryScopedTypePresentationSimulationState.currentFamily_avoids_nodeScope
    {theoryScope publicScope : List String} {position : Nat}
    {staticHistory runtimeHistory currentFamily : List Atom}
    {specPresentation branchPresentation : TypeSubst}
    {runtimeBindings : Metta.Bindings} {formal : Atom}
    (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope position staticHistory runtimeHistory specPresentation
        branchPresentation runtimeBindings)
    (staticGenerated : CandidateGenerationHistory position staticHistory)
    (runtimeGenerated : CandidateGenerationHistory position runtimeHistory)
    (currentGenerated : CandidateFamilyGeneratedAt position currentFamily)
    (currentAvoidsPublic : AtomsAvoid currentFamily publicScope)
    (currentAvoidsTheory : AtomsAvoid currentFamily theoryScope)
    (currentAvoidsFormal : AtomsAvoid currentFamily
      (TypeSubst.typeVars formal)) :
    AtomsAvoid currentFamily
      (twoHistoryCandidateNodeScope specPresentation branchPresentation
        theoryScope formal) := by
  rcases state with ⟨_, _, _, _, _, _, _, staticSupported,
    runtimeSupported⟩
  have avoidsSpecPresentation :=
    staticGenerated.currentFamily_avoids_supported currentGenerated
      currentAvoidsPublic staticSupported
  have avoidsRuntimePresentation :=
    runtimeGenerated.currentFamily_avoids_supported currentGenerated
      currentAvoidsPublic runtimeSupported
  intro name currentOccurrence scopeMember
  simp only [twoHistoryCandidateNodeScope, List.mem_append] at scopeMember
  rcases scopeMember with scopeMember | formalMember
  · rcases scopeMember with scopeMember | theoryMember
    · rcases scopeMember with specMember | runtimeMember
      · exact avoidsSpecPresentation name currentOccurrence specMember
      · exact avoidsRuntimePresentation name currentOccurrence runtimeMember
    · exact currentAvoidsTheory name currentOccurrence theoryMember
  · exact currentAvoidsFormal name currentOccurrence formalMember

/-- Pointwise monotonicity for one ordered candidate family. -/
theorem candidateFamilyAlphaVariants_mono
    {small large : List String} {sources targets : List Atom}
    (variants : List.Forall₂
      (TypeCandidateAlphaVariantRel large) sources targets)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    List.Forall₂ (TypeCandidateAlphaVariantRel small) sources targets := by
  induction variants with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (TypeCandidateAlphaVariantRel.mono head subset)
        inductionHypothesis

/-- The complete generated family list retains exact pointwise alpha
provenance at the initial scope.  Later positions are weakened only after
being generated against their strictly larger scopes. -/
theorem freshenArgumentCandidateFamilies_alphaVariants
    (avoid : List String) (position : Nat)
    (sources : List (List Atom)) :
    List.Forall₂
      (fun sourceFamily targetFamily =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          sourceFamily targetFamily)
      sources (freshenArgumentCandidateFamilies avoid position sources) := by
  induction sources generalizing avoid position with
  | nil => exact .nil
  | cons sourceFamily remaining inductionHypothesis =>
      let targetFamily := freshenCandidateFamily avoid position sourceFamily
      apply List.Forall₂.cons
      · exact freshenCandidateFamily_alphaVariants avoid position sourceFamily
      · have tail := inductionHypothesis
          (avoid ++ TypeSubst.typeVarsList targetFamily) (position + 1)
        exact tail.imp fun _ _ variants =>
          candidateFamilyAlphaVariants_mono variants
            (fun name member => List.mem_append_left _ member)

/-- Every variable emitted at one position avoids the complete finite scope
supplied to that position. -/
theorem freshenCandidateFamily_avoids
    (avoid : List String) (position : Nat) (sources : List Atom) :
    AtomsAvoid (freshenCandidateFamily avoid position sources) avoid := by
  intro name occurrence
  rw [freshenCandidateFamily,
    Spec.Type.Presentation.ScopeObservation.typeVarsList_renameTypeVars]
    at occurrence
  obtain ⟨sourceName, _sourceOccurrence, rfl⟩ := List.mem_map.mp occurrence
  exact Metta.Minimal.captureAvoidingName_not_mem avoid position sourceName

/-- Every variable emitted by the complete positional family fold avoids its
initial scope, even though later positions receive a strictly larger scope. -/
theorem freshenArgumentCandidateFamilies_avoids
    (avoid : List String) (position : Nat)
    (sources : List (List Atom)) :
    AtomsAvoid
      (freshenArgumentCandidateFamilies avoid position sources).flatten
      avoid := by
  induction sources generalizing avoid position with
  | nil => simp [freshenArgumentCandidateFamilies, AtomsAvoid,
      TypeSubst.typeVarsList]
  | cons sourceFamily remaining inductionHypothesis =>
      let targetFamily := freshenCandidateFamily avoid position sourceFamily
      intro name occurrence avoidMember
      obtain ⟨atom, atomMember, atomOccurrence⟩ :=
        exists_mem_of_mem_typeVarsList occurrence
      simp only [freshenArgumentCandidateFamilies, List.flatten_cons,
        List.mem_append] at atomMember
      rcases atomMember with headMember | tailMember
      · exact freshenCandidateFamily_avoids avoid position sourceFamily
          name (typeVars_mem_typeVarsList_of_mem headMember name atomOccurrence)
            avoidMember
      · exact inductionHypothesis
          (avoid ++ TypeSubst.typeVarsList targetFamily) (position + 1)
          name (typeVars_mem_typeVarsList_of_mem tailMember name atomOccurrence)
            (List.mem_append_left _ avoidMember)

/-- Distinct argument positions generated by the realization fold have
disjoint private-variable families.  Alternatives at one position are not
required to be mutually disjoint. -/
theorem freshenArgumentCandidateFamilies_pairwise
    (avoid : List String) (position : Nat)
    (sources : List (List Atom)) :
    (freshenArgumentCandidateFamilies avoid position sources).Pairwise
      FreshFamiliesSeparated := by
  induction sources generalizing avoid position with
  | nil => simp [freshenArgumentCandidateFamilies]
  | cons sourceFamily remaining inductionHypothesis =>
      let targetFamily := freshenCandidateFamily avoid position sourceFamily
      let tailFamilies := freshenArgumentCandidateFamilies
        (avoid ++ TypeSubst.typeVarsList targetFamily) (position + 1)
          remaining
      have tailAvoids : AtomsAvoid tailFamilies.flatten
          (avoid ++ TypeSubst.typeVarsList targetFamily) := by
        exact freshenArgumentCandidateFamilies_avoids
          (avoid ++ TypeSubst.typeVarsList targetFamily) (position + 1)
            remaining
      simp only [freshenArgumentCandidateFamilies, List.pairwise_cons]
      constructor
      · intro family familyMember
        apply FreshFamiliesSeparated.symm
        intro name occurrence headOccurrence
        obtain ⟨atom, atomMember, atomOccurrence⟩ :=
          exists_mem_of_mem_typeVarsList occurrence
        exact tailAvoids name
          (typeVars_mem_typeVarsList_of_mem
            (List.mem_flatten.mpr ⟨family, familyMember, atomMember⟩)
            name atomOccurrence)
          (List.mem_append_right avoid headOccurrence)
      · exact inductionHypothesis
          (avoid ++ TypeSubst.typeVarsList targetFamily) (position + 1)

/-- Generator-produced static candidate families satisfy the complete scan
preparation contract when the initial avoid set contains the public boundary
and every function-formal variable.  The initial presentation is empty at
the function-candidate boundary. -/
theorem freshenArgumentCandidateFamilies_prepared
    (forbidden : List String) (formals : List Atom)
    (sources : List (List Atom)) :
    let avoid := forbidden ++ TypeSubst.typeVarsList formals
    let targets := freshenArgumentCandidateFamilies avoid 0 sources
    PreparedArgumentCandidateLists formals [] targets
      (targets.map toLeaTTaAtoms) := by
  dsimp only
  let avoid := forbidden ++ TypeSubst.typeVarsList formals
  let targets := freshenArgumentCandidateFamilies avoid 0 sources
  have targetsAvoid := freshenArgumentCandidateFamilies_avoids
    avoid 0 sources
  exact
    { link := rfl
      avoidFormals := by
        intro name occurrence formalOccurrence
        exact targetsAvoid name occurrence
          (List.mem_append_right forbidden formalOccurrence)
      avoidInitial := TypeSubst.avoids_empty _
      families := freshenArgumentCandidateFamilies_pairwise avoid 0 sources }

/-! ## One branch-local candidate -/

/-- A private candidate fresh from a scope containing the formal's variables
is structurally disjoint from that formal at the runtime matcher boundary. -/
theorem PrivateCandidateAlphaRel.formal_runtime_disjoint
    {fixedScope : List String} {formal specCandidate runtimeCandidate : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope
      specCandidate runtimeCandidate)
    (formalCovered : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ fixedScope) :
    VarsDisjoint formal runtimeCandidate := by
  intro name formalMember candidateMember
  rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
    at formalMember candidateMember
  exact alpha.vars_avoid_fixedScope.2 name candidateMember
    (formalCovered name formalMember)

/-- Forgetting the protected-scope side conditions of a private candidate
pair yields the ordinary alpha observation used by diagnostics. -/
theorem PrivateCandidateAlphaRel.toObservedTypeAlphaRel
    {fixedScope : List String} {left right : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope left right) :
    ObservedTypeAlphaRel left right := by
  rcases alpha with
    ⟨source,
      ⟨leftRename, leftInjective, leftEquation, _⟩,
      ⟨rightRename, rightInjective, rightEquation, _⟩⟩
  exact ⟨source,
    ⟨leftRename, leftInjective, leftEquation⟩,
    ⟨rightRename, rightInjective, rightEquation⟩⟩

/-- One successful runtime match against a branch-local fresh candidate has
an independent static-candidate derivation.  The exact runtime output keeps
its branch spelling; only its finite theory is compared with the static
output on `theoryScope`. -/
theorem matchType_privateCandidate_scoped
    {fixedScope theoryScope : List String}
    {presentationIncoming branchIncoming : TypeSubst}
    {bindingIncoming : Bindings}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    {formal specCandidate runtimeCandidate : Atom}
    (specNormal : presentationIncoming.Normal)
    (state : TypePresentationSimulationState
      branchIncoming bindingIncoming runtimeIncoming)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope presentationIncoming branchIncoming)
    (alpha : PrivateCandidateAlphaRel fixedScope
      specCandidate runtimeCandidate)
    (presentationIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨presentationIncoming, []⟩ → name ∈ fixedScope)
    (branchIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨branchIncoming, []⟩ → name ∈ fixedScope)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (runtimeEquation : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) =
        some runtimeOutput) :
    ∃ specOutput branchOutput, ∃ bindingOutput : Bindings,
      CorePlusR2TypePresentationMatchRel
          presentationIncoming formal specCandidate specOutput ∧
        CorePlusR2TypePresentationMatchRel
          branchIncoming formal runtimeCandidate branchOutput ∧
        TypePresentationSimulationState
          branchOutput bindingOutput runtimeOutput ∧
        TypePresentationTheoryEquivAt
          theoryScope specOutput branchOutput := by
  obtain ⟨branchOutput, specBindingOutput, branchDerivation, outputState⟩ :=
    state.matchType formal runtimeCandidate runtimeEquation
  have constraints :=
    TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha
      incomingEquiv alpha presentationIncomingCovered branchIncomingCovered
      theoryCovered formalObserved (fun _ member => member)
  have branchOutputNormal := branchDerivation.output_normal state.normal
  have branchOutputSatisfied : TypeSubstSatisfied
      (presentedValuation branchOutput) branchOutput :=
    normal_presentedValuation_satisfied branchOutputNormal
  obtain ⟨branchIncomingSatisfied, branchConsistent⟩ :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      branchDerivation state.normal (presentedValuation branchOutput)).mp
        branchOutputSatisfied
  obtain ⟨specModel, specIncomingSatisfied, specConsistent, _⟩ :=
    constraints.rightToLeft (presentedValuation branchOutput)
      branchIncomingSatisfied branchConsistent
  obtain ⟨specOutput, specDerivation, specOutputNormal,
      _specOutputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      specNormal specIncomingSatisfied formal specCandidate specConsistent
  have outputEquiv :=
    CorePlusR2TypePresentationMatchRel.outputTheoryEquivAt
      specNormal state.normal specDerivation branchDerivation constraints
  exact ⟨specOutput, branchOutput, specBindingOutput,
    specDerivation, branchDerivation, outputState,
    outputEquiv⟩

/-- One successful candidate match extends the independent static and
runtime histories in lockstep without identifying their private spellings.
The current alpha siblings need only avoid the two incoming supports; they
are not required to be mutually disjoint. -/
theorem matchType_privateCandidate_twoHistory
    {theoryScope publicScope : List String} {position : Nat}
    {staticHistory runtimeHistory : List Atom}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    {formal specCandidate runtimeCandidate : Atom}
    (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope position staticHistory runtimeHistory specIncoming
        branchIncoming runtimeIncoming)
    (alpha : PrivateCandidateAlphaRel
      (twoHistoryCandidateNodeScope specIncoming branchIncoming
        theoryScope formal)
      specCandidate runtimeCandidate)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (formalPublic : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ publicScope)
    (runtimeEquation : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) =
        some runtimeOutput) :
    ∃ specOutput branchOutput,
      CorePlusR2TypePresentationMatchRel
          specIncoming formal specCandidate specOutput ∧
        TwoHistoryScopedTypePresentationSimulationState theoryScope
          publicScope (position + 1)
          (staticHistory ++ [specCandidate])
          (runtimeHistory ++ [runtimeCandidate]) specOutput branchOutput
            runtimeOutput := by
  rcases state with ⟨staticLength, runtimeLength, historyAlpha,
    specNormal, bindingIncoming, branchState, incomingEquiv,
    staticSupported, runtimeSupported⟩
  have specIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨specIncoming, []⟩ →
        name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  have branchIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨branchIncoming, []⟩ →
        name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  have theoryCovered : ∀ name, name ∈ theoryScope →
      name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
        theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  obtain ⟨specOutput, branchOutput, specBindingOutput,
      specDerivation, branchDerivation, outputState, outputEquiv⟩ :=
    matchType_privateCandidate_scoped specNormal branchState incomingEquiv
      alpha specIncomingCovered branchIncomingCovered theoryCovered
      formalObserved runtimeEquation
  refine ⟨specOutput, branchOutput, specDerivation, ?_⟩
  refine ⟨?_, ?_, ?_, specDerivation.output_normal specNormal,
      specBindingOutput, outputState, outputEquiv, ?_, ?_⟩
  · simp [staticLength]
  · simp [runtimeLength]
  · exact List.rel_append historyAlpha
      (.cons ⟨_, alpha⟩ .nil)
  · exact TypePresentationSupportedByCandidateHistory.step
      staticSupported formalPublic specDerivation
  · exact TypePresentationSupportedByCandidateHistory.step
      runtimeSupported formalPublic branchDerivation

/-- Runtime failure on one branch-local private candidate is exactly static
presentation failure for its alpha sibling. -/
theorem matchType_privateCandidate_none
    {fixedScope theoryScope : List String}
    {presentationIncoming branchIncoming : TypeSubst}
    {bindingIncoming : Bindings} {runtimeIncoming : Metta.Bindings}
    {formal specCandidate runtimeCandidate : Atom}
    (specNormal : presentationIncoming.Normal)
    (state : TypePresentationSimulationState
      branchIncoming bindingIncoming runtimeIncoming)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope presentationIncoming branchIncoming)
    (alpha : PrivateCandidateAlphaRel fixedScope
      specCandidate runtimeCandidate)
    (presentationIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨presentationIncoming, []⟩ → name ∈ fixedScope)
    (branchIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨branchIncoming, []⟩ → name ∈ fixedScope)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (runtimeFailure : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) = none) :
    ∀ specOutput,
      ¬CorePlusR2TypePresentationMatchRel
        presentationIncoming formal specCandidate specOutput := by
  have constraints :=
    TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha
      incomingEquiv alpha presentationIncomingCovered branchIncomingCovered
      theoryCovered formalObserved (fun _ member => member)
  have noRuntimePresentation :=
    (matchType_eq_none_iff_no_presentation state formal runtimeCandidate
      (PrivateCandidateAlphaRel.formal_runtime_disjoint alpha
        (fun name member => theoryCovered name
          (formalObserved name member)))).mp runtimeFailure
  intro specOutput specDerivation
  have specOutputNormal := specDerivation.output_normal specNormal
  have specOutputSatisfied : TypeSubstSatisfied
      (presentedValuation specOutput) specOutput :=
    normal_presentedValuation_satisfied specOutputNormal
  obtain ⟨specIncomingSatisfied, specConsistent⟩ :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      specDerivation specNormal (presentedValuation specOutput)).mp
        specOutputSatisfied
  obtain ⟨branchModel, branchIncomingSatisfied, branchConsistent, _⟩ :=
    constraints.leftToRight (presentedValuation specOutput)
      specIncomingSatisfied specConsistent
  obtain ⟨branchOutput, branchDerivation, _, _⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal branchIncomingSatisfied formal runtimeCandidate
        branchConsistent
  exact noRuntimePresentation branchOutput branchDerivation

/-- Runtime failure transports across the same two-history boundary. -/
theorem matchType_privateCandidate_none_twoHistory
    {theoryScope publicScope : List String} {position : Nat}
    {staticHistory runtimeHistory : List Atom}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings}
    {formal specCandidate runtimeCandidate : Atom}
    (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope position staticHistory runtimeHistory specIncoming
        branchIncoming runtimeIncoming)
    (alpha : PrivateCandidateAlphaRel
      (twoHistoryCandidateNodeScope specIncoming branchIncoming
        theoryScope formal)
      specCandidate runtimeCandidate)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (runtimeFailure : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) = none) :
    ∀ specOutput,
      ¬CorePlusR2TypePresentationMatchRel
        specIncoming formal specCandidate specOutput := by
  rcases state with ⟨_, _, _, specNormal, bindingIncoming,
    branchState, incomingEquiv, staticSupported, runtimeSupported⟩
  have specIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨specIncoming, []⟩ →
        name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  have branchIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨branchIncoming, []⟩ →
        name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  have theoryCovered : ∀ name, name ∈ theoryScope →
      name ∈ twoHistoryCandidateNodeScope specIncoming branchIncoming
        theoryScope formal := by
    intro name member
    simp [twoHistoryCandidateNodeScope, member]
  exact matchType_privateCandidate_none specNormal branchState incomingEquiv
    alpha specIncomingCovered branchIncomingCovered theoryCovered
    formalObserved runtimeFailure

/-- The branch-valued executable scan over one branch-local candidate family
has exactly the static presentation branches and failure positions.  Output
presentations are compared semantically at `theoryScope`; failed candidate
atoms retain their pointwise alpha relation for the diagnostic layer. -/
def ScopedTypePresentationCandidateBranchStates
    (scope : List String) (incoming : TypeSubst) (formal : Atom)
    (candidates : List Atom) (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation runtimeBindings =>
      ∃ candidate ∈ candidates,
        CorePlusR2TypePresentationMatchRel incoming formal candidate
            presentation ∧
          ScopedTypePresentationSimulationState scope presentation
            runtimeBindings)
    presentations runtimeBindings

/-- Forgetting the candidate provenance of every successful branch retains
the ordered scoped simulation states. -/
theorem ScopedTypePresentationCandidateBranchStates.states
    {scope : List String} {incoming : TypeSubst} {formal : Atom}
    {candidates : List Atom} {presentations : List TypeSubst}
    {runtimeBindings : List Metta.Bindings}
    (states : ScopedTypePresentationCandidateBranchStates scope incoming
      formal candidates presentations runtimeBindings) :
    ScopedTypePresentationSimulationStates scope presentations
      runtimeBindings := by
  induction states with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      obtain ⟨candidate, member, matched, scopedState⟩ := head
      exact .cons scopedState inductionHypothesis

theorem scanActualTypeBranches_privateCandidates_scoped
    {fixedScope theoryScope : List String}
    {presentationIncoming branchIncoming : TypeSubst}
    {bindingIncoming : Bindings} {runtimeIncoming : Metta.Bindings}
    {formal : Atom}
    (specNormal : presentationIncoming.Normal)
    (state : TypePresentationSimulationState
      branchIncoming bindingIncoming runtimeIncoming)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope presentationIncoming branchIncoming)
    (presentationIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨presentationIncoming, []⟩ → name ∈ fixedScope)
    (branchIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨branchIncoming, []⟩ → name ∈ fixedScope)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope) :
    ∀ {specCandidates runtimeCandidates : List Atom},
      PrivateCandidateFamilyAlphaRel fixedScope
          specCandidates runtimeCandidates →
      ∃ specOutputs failedSpecCandidates,
        ActualTypeCandidateBranchesRel presentationIncoming formal specCandidates
            specOutputs failedSpecCandidates ∧
          ScopedTypePresentationCandidateBranchStates theoryScope
            presentationIncoming formal specCandidates specOutputs
            (Metta.Minimal.scanActualTypeBranches runtimeIncoming
              (toLeaTTaAtom formal)
              (toLeaTTaAtoms runtimeCandidates)).successes ∧
          List.Forall₂
            (fun specCandidate runtimeCandidate =>
              ObservedTypeAlphaRel specCandidate
                (fromLeaTTaAtom runtimeCandidate))
            failedSpecCandidates
            (Metta.Minimal.scanActualTypeBranches runtimeIncoming
              (toLeaTTaAtom formal)
              (toLeaTTaAtoms runtimeCandidates)).failures := by
  intro specCandidates runtimeCandidates candidatesAlpha
  induction candidatesAlpha with
  | nil =>
      exact ⟨[], [], .nil, .nil, .nil⟩
  | @cons specCandidate runtimeCandidate specCandidates runtimeCandidates
      candidateAlpha _ inductionHypothesis =>
      cases runtimeEquation : Metta.Minimal.matchType runtimeIncoming
          (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) with
      | some runtimeOutput =>
          obtain ⟨specOutput, branchOutput, specBindingOutput,
              specDerivation, _branchDerivation, outputState,
              outputEquiv⟩ :=
            matchType_privateCandidate_scoped specNormal state incomingEquiv
              candidateAlpha presentationIncomingCovered branchIncomingCovered
              theoryCovered formalObserved runtimeEquation
          have scopedOutput : ScopedTypePresentationSimulationState
              theoryScope specOutput runtimeOutput :=
            ⟨specDerivation.output_normal specNormal, branchOutput,
              specBindingOutput, outputState, outputEquiv⟩
          obtain ⟨specOutputs, failedSpecCandidates, tailScan,
              tailStates, tailFailures⟩ := inductionHypothesis
          have tailStates' :
              ScopedTypePresentationCandidateBranchStates theoryScope
                presentationIncoming formal (specCandidate :: specCandidates)
                specOutputs
                (Metta.Minimal.scanActualTypeBranches runtimeIncoming
                  (toLeaTTaAtom formal)
                  (toLeaTTaAtoms runtimeCandidates)).successes := by
            apply tailStates.imp
            intro presentation runtimeBindings witness
            obtain ⟨candidate, member, matched, scopedState⟩ := witness
            exact ⟨candidate, by simp [member], matched, scopedState⟩
          refine ⟨specOutput :: specOutputs, failedSpecCandidates,
            .matched specDerivation tailScan, ?_, ?_⟩
          · simpa [ScopedTypePresentationCandidateBranchStates,
                Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using List.Forall₂.cons
                ⟨specCandidate, by simp, specDerivation, scopedOutput⟩
                tailStates'
          · simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using tailFailures
      | none =>
          have noSpecPresentation :=
            matchType_privateCandidate_none specNormal state incomingEquiv
              candidateAlpha presentationIncomingCovered branchIncomingCovered
              theoryCovered formalObserved runtimeEquation
          obtain ⟨specOutputs, failedSpecCandidates, tailScan,
              tailStates, tailFailures⟩ := inductionHypothesis
          have tailStates' :
              ScopedTypePresentationCandidateBranchStates theoryScope
                presentationIncoming formal (specCandidate :: specCandidates)
                specOutputs
                (Metta.Minimal.scanActualTypeBranches runtimeIncoming
                  (toLeaTTaAtom formal)
                  (toLeaTTaAtoms runtimeCandidates)).successes := by
            apply tailStates.imp
            intro presentation runtimeBindings witness
            obtain ⟨candidate, member, matched, scopedState⟩ := witness
            exact ⟨candidate, by simp [member], matched, scopedState⟩
          refine ⟨specOutputs, specCandidate :: failedSpecCandidates,
            .failed noSpecPresentation tailScan, ?_, ?_⟩
          · simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using tailStates'
          · have headAlpha : ObservedTypeAlphaRel specCandidate
                (fromLeaTTaAtom (toLeaTTaAtom runtimeCandidate)) := by
              simpa using PrivateCandidateAlphaRel.toObservedTypeAlphaRel
                candidateAlpha
            simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using List.Forall₂.cons
                (R := fun specCandidate runtimeCandidate =>
                  ObservedTypeAlphaRel specCandidate
                    (fromLeaTTaAtom runtimeCandidate))
                headAlpha tailFailures

/-! ## Two-history candidate scan -/

/-- Successful branches retain the exact selected candidate on each side,
its existing private-alpha witness, and the extended two-history state.
Unselected alternatives never enter either presentation support. -/
def TwoHistoryScopedTypePresentationCandidateBranchStates
    (theoryScope publicScope : List String) (position : Nat)
    (staticHistory runtimeHistory : List Atom)
    (incoming branchIncoming : TypeSubst) (formal : Atom)
    (specCandidates runtimeCandidates : List Atom)
    (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation runtimeBinding =>
      ∃ specCandidate ∈ specCandidates,
        ∃ runtimeCandidate ∈ runtimeCandidates,
          PrivateCandidateAlphaRel
              (twoHistoryCandidateNodeScope incoming branchIncoming
                theoryScope formal)
              specCandidate runtimeCandidate ∧
            CorePlusR2TypePresentationMatchRel incoming formal
              specCandidate presentation ∧
            ∃ nextBranchPresentation,
              TwoHistoryScopedTypePresentationSimulationState theoryScope
                publicScope (position + 1)
                (staticHistory ++ [specCandidate])
                (runtimeHistory ++ [runtimeCandidate]) presentation
                  nextBranchPresentation runtimeBinding)
    presentations runtimeBindings

/-- The theorem-local strengthening of branch correspondence by an opaque
recursive invariant.  This wrapper is proof evidence only; the semantic
branch carrier and executable recursion remain invariant-free. -/
def TwoHistoryInvariantCandidateBranchStates
    (invariant : TwoHistoryScanStateInvariant)
    (theoryScope publicScope : List String) (position : Nat)
    (staticHistory runtimeHistory : List Atom)
    (incoming branchIncoming : TypeSubst) (formal : Atom)
    (specCandidates runtimeCandidates : List Atom)
    (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation runtimeBinding =>
      ∃ specCandidate ∈ specCandidates,
        ∃ runtimeCandidate ∈ runtimeCandidates,
          PrivateCandidateAlphaRel
              (twoHistoryCandidateNodeScope incoming branchIncoming
                theoryScope formal)
              specCandidate runtimeCandidate ∧
            CorePlusR2TypePresentationMatchRel incoming formal
              specCandidate presentation ∧
            ∃ nextBranchPresentation,
              TwoHistoryScopedTypePresentationSimulationState theoryScope
                  publicScope (position + 1)
                  (staticHistory ++ [specCandidate])
                  (runtimeHistory ++ [runtimeCandidate]) presentation
                    nextBranchPresentation runtimeBinding ∧
                invariant (position + 1)
                  (staticHistory ++ [specCandidate])
                  (runtimeHistory ++ [runtimeCandidate]) presentation
                    runtimeBinding)
    presentations runtimeBindings

/-- The repaired one-position branch scan preserves two independent private
histories.  Success order and multiplicity are literal; failed candidates
retain the fieldwise alpha observation used by diagnostics. -/
theorem scanActualTypeBranches_privateCandidates_twoHistory
    {theoryScope publicScope : List String} {position : Nat}
    {staticHistory runtimeHistory : List Atom}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings}
    {formal : Atom}
    (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope position staticHistory runtimeHistory specIncoming
        branchIncoming runtimeIncoming)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (formalPublic : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ publicScope) :
    ∀ {specCandidates runtimeCandidates : List Atom},
      PrivateCandidateFamilyAlphaRel
          (twoHistoryCandidateNodeScope specIncoming branchIncoming
            theoryScope formal)
          specCandidates runtimeCandidates →
      ∃ specOutputs failedSpecCandidates,
        ActualTypeCandidateBranchesRel specIncoming formal specCandidates
            specOutputs failedSpecCandidates ∧
          TwoHistoryScopedTypePresentationCandidateBranchStates
            theoryScope publicScope position staticHistory runtimeHistory
            specIncoming branchIncoming formal specCandidates
            runtimeCandidates specOutputs
            (Metta.Minimal.scanActualTypeBranches runtimeIncoming
              (toLeaTTaAtom formal)
              (toLeaTTaAtoms runtimeCandidates)).successes ∧
          List.Forall₂
            (fun specCandidate runtimeCandidate =>
              ObservedTypeAlphaRel specCandidate
                (fromLeaTTaAtom runtimeCandidate))
            failedSpecCandidates
            (Metta.Minimal.scanActualTypeBranches runtimeIncoming
              (toLeaTTaAtom formal)
              (toLeaTTaAtoms runtimeCandidates)).failures := by
  intro specCandidates runtimeCandidates candidatesAlpha
  induction candidatesAlpha with
  | nil =>
      exact ⟨[], [], .nil, .nil, .nil⟩
  | @cons specCandidate runtimeCandidate specCandidates runtimeCandidates
      candidateAlpha _ inductionHypothesis =>
      cases runtimeEquation : Metta.Minimal.matchType runtimeIncoming
          (toLeaTTaAtom formal) (toLeaTTaAtom runtimeCandidate) with
      | some runtimeOutput =>
          obtain ⟨specOutput, branchOutput, specDerivation, nextState⟩ :=
            matchType_privateCandidate_twoHistory state candidateAlpha
              formalObserved formalPublic runtimeEquation
          obtain ⟨specOutputs, failedSpecCandidates, tailScan,
              tailStates, tailFailures⟩ := inductionHypothesis
          have tailStates' :
              TwoHistoryScopedTypePresentationCandidateBranchStates
                theoryScope publicScope position staticHistory runtimeHistory
                specIncoming branchIncoming formal
                (specCandidate :: specCandidates)
                (runtimeCandidate :: runtimeCandidates) specOutputs
                (Metta.Minimal.scanActualTypeBranches runtimeIncoming
                  (toLeaTTaAtom formal)
                  (toLeaTTaAtoms runtimeCandidates)).successes := by
            apply tailStates.imp
            intro presentation runtimeBinding witness
            obtain ⟨selectedSpec, selectedSpecMember, selectedRuntime,
              selectedRuntimeMember, selectedAlpha, selectedDerivation,
              selectedBranch, selectedState⟩ := witness
            exact ⟨selectedSpec, by simp [selectedSpecMember],
              selectedRuntime, by simp [selectedRuntimeMember],
              selectedAlpha, selectedDerivation, selectedBranch,
              selectedState⟩
          refine ⟨specOutput :: specOutputs, failedSpecCandidates,
            .matched specDerivation tailScan, ?_, ?_⟩
          · simpa [TwoHistoryScopedTypePresentationCandidateBranchStates,
                Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using List.Forall₂.cons
                ⟨specCandidate, by simp, runtimeCandidate, by simp,
                  candidateAlpha, specDerivation, branchOutput, nextState⟩
                tailStates'
          · simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using tailFailures
      | none =>
          have noSpecPresentation :=
            matchType_privateCandidate_none_twoHistory state candidateAlpha
              formalObserved runtimeEquation
          obtain ⟨specOutputs, failedSpecCandidates, tailScan,
              tailStates, tailFailures⟩ := inductionHypothesis
          have tailStates' :
              TwoHistoryScopedTypePresentationCandidateBranchStates
                theoryScope publicScope position staticHistory runtimeHistory
                specIncoming branchIncoming formal
                (specCandidate :: specCandidates)
                (runtimeCandidate :: runtimeCandidates) specOutputs
                (Metta.Minimal.scanActualTypeBranches runtimeIncoming
                  (toLeaTTaAtom formal)
                  (toLeaTTaAtoms runtimeCandidates)).successes := by
            apply tailStates.imp
            intro presentation runtimeBinding witness
            obtain ⟨selectedSpec, selectedSpecMember, selectedRuntime,
              selectedRuntimeMember, selectedAlpha, selectedDerivation,
              selectedBranch, selectedState⟩ := witness
            exact ⟨selectedSpec, by simp [selectedSpecMember],
              selectedRuntime, by simp [selectedRuntimeMember],
              selectedAlpha, selectedDerivation, selectedBranch,
              selectedState⟩
          refine ⟨specOutputs, specCandidate :: failedSpecCandidates,
            .failed noSpecPresentation tailScan, ?_, ?_⟩
          · simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using tailStates'
          · have headAlpha : ObservedTypeAlphaRel specCandidate
                (fromLeaTTaAtom (toLeaTTaAtom runtimeCandidate)) := by
              simpa using PrivateCandidateAlphaRel.toObservedTypeAlphaRel
                candidateAlpha
            simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using List.Forall₂.cons
                (R := fun specCandidate runtimeCandidate =>
                  ObservedTypeAlphaRel specCandidate
                    (fromLeaTTaAtom runtimeCandidate))
                headAlpha tailFailures

/-! ## Evidence-free runtime recursion seam -/

/-- The exact candidate family prepared by the repaired runtime at one
branch node.  The avoid set depends on the branch-local binding state, so
this equation must be re-established at every recursive call. -/
def RuntimeArgumentCandidatesAt
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) (boundaryScope : List String)
    (position : Nat)
    (bindings : Metta.Bindings) (argument : Atom)
    (remaining : List Atom) (candidates : List Metta.Atom) : Prop :=
  let prepared := Metta.Minimal.typePrep world (toLeaTTaAtom argument)
  let rawActuals := Metta.Minimal.getTypes env prepared
  let avoid := boundaryScope ++ Metta.Minimal.typeInferenceAvoid env
    (.expr (toLeaTTaAtom argument :: toLeaTTaAtoms remaining))
    (runtimeFormals ++ rawActuals) ++ bindings.vars
  rawActuals.map
      (Metta.Minimal.freshenTypeCandidate avoid position) = candidates

/-- The finite scope protected at one branch node.  It grows with both the
static and runtime-side presentations produced by earlier positions; this is
why replacing it by one global scope is inconsistent with recursive
freshening. -/
def argumentCandidateNodeScope
    (specIncoming branchIncoming : TypeSubst)
    (theoryScope : List String) (formal : Atom) : List String :=
  specBindingVars (⟨specIncoming, []⟩ : Bindings) ++
    specBindingVars (⟨branchIncoming, []⟩ : Bindings) ++
      theoryScope ++ TypeSubst.typeVars formal

/-- Node-local preparation coverage used by the recursive conformance
theorem.  The runtime skeleton remains evidence-free: this forall-shaped
hypothesis alone relates the exact executable candidate equation to the
static family at the current node.  It is intentionally relational and
asserts neither global totality nor functionality. -/
def NodeLocalArgumentCandidateCoverage
    (candidateFamily : Atom → List Atom → Prop)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) (boundaryScope theoryScope : List String) : Prop :=
  ∀ {formal argument : Atom} {remaining : List Atom} {position : Nat}
      {presentationIncoming branchIncoming : TypeSubst}
      {bindingIncoming : Bindings} {runtimeIncoming : Metta.Bindings}
      {specCandidates : List Atom} {runtimeCandidates : List Metta.Atom},
    candidateFamily argument specCandidates →
      TypePresentationSimulationState branchIncoming bindingIncoming
        runtimeIncoming →
      TypePresentationTheoryEquivAt theoryScope
        presentationIncoming branchIncoming →
      RuntimeArgumentCandidatesAt env world runtimeFormals boundaryScope position
        runtimeIncoming argument remaining runtimeCandidates →
      ∃ decodedRuntimeCandidates,
        toLeaTTaAtoms decodedRuntimeCandidates = runtimeCandidates ∧
          PrivateCandidateFamilyAlphaRel
            (argumentCandidateNodeScope presentationIncoming branchIncoming
              theoryScope formal)
            specCandidates decodedRuntimeCandidates

/-- The node-local realization oracle is restricted to states satisfying an
opaque invariant.  The generic recursion never inspects that invariant;
generator provenance is supplied only by the concrete realization instance. -/
def TwoHistoryNodeLocalArgumentCandidateCoverage
    (candidateFamily : Nat → Atom → List Atom → Prop)
    (invariant : TwoHistoryScanStateInvariant)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) (boundaryScope : List String)
    (theoryScope publicScope : List String) : Prop :=
  ∀ {formal argument : Atom} {remaining : List Atom} {position : Nat}
      {staticHistory runtimeHistory : List Atom}
      {specIncoming branchIncoming : TypeSubst}
      {runtimeIncoming : Metta.Bindings}
      {specCandidates : List Atom} {runtimeCandidates : List Metta.Atom}
      (_state : TwoHistoryScopedTypePresentationSimulationState theoryScope
        publicScope position staticHistory runtimeHistory specIncoming
          branchIncoming runtimeIncoming),
    candidateFamily position argument specCandidates →
      invariant position staticHistory runtimeHistory specIncoming
        runtimeIncoming →
      position < runtimeFormals.length →
      toLeaTTaAtom formal ∈ runtimeFormals →
      AtomsAvoid specCandidates (TypeSubst.typeVars formal) →
      RuntimeArgumentCandidatesAt env world runtimeFormals boundaryScope position
        runtimeIncoming argument remaining runtimeCandidates →
      ∃ decodedRuntimeCandidates,
        toLeaTTaAtoms decodedRuntimeCandidates = runtimeCandidates ∧
          PrivateCandidateFamilyAlphaRel
            (twoHistoryCandidateNodeScope specIncoming branchIncoming
              theoryScope formal)
            specCandidates decodedRuntimeCandidates ∧
          ∀ {specCandidate runtimeCandidate formal : Atom}
              {specOutput branchOutput : TypeSubst}
              {runtimeOutput : Metta.Bindings},
            specCandidate ∈ specCandidates →
              runtimeCandidate ∈ decodedRuntimeCandidates →
              PrivateCandidateAlphaRel
                (twoHistoryCandidateNodeScope specIncoming branchIncoming
                  theoryScope formal)
                specCandidate runtimeCandidate →
              CorePlusR2TypePresentationMatchRel specIncoming formal
                specCandidate specOutput →
              TwoHistoryScopedTypePresentationSimulationState theoryScope
                publicScope (position + 1)
                (staticHistory ++ [specCandidate])
                (runtimeHistory ++ [runtimeCandidate]) specOutput
                  branchOutput runtimeOutput →
              invariant (position + 1)
                (staticHistory ++ [specCandidate])
                (runtimeHistory ++ [runtimeCandidate]) specOutput
                  runtimeOutput

mutual

  /-- Evidence-free runtime skeleton for the branch-valued argument scan.

  Candidate preparation is recorded only by the executable equation in
  `RuntimeArgumentCandidatesAt`; no specification candidate or alpha witness
  occurs in this relation.  Correspondence is supplied separately to the
  recursive theorem, so realizing this skeleton cannot validate itself. -/
  inductive RuntimeBranchLocalArgumentScanRel
      (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
      (runtimeFormals : List Metta.Atom) (boundaryScope : List String) :
      List Atom → List Atom → Nat → Metta.Bindings →
        Metta.Minimal.TypeCheckArgsBranchResult → Prop where
    | noArguments (formals : List Atom) (position : Nat)
        (bindings : Metta.Bindings) :
        RuntimeBranchLocalArgumentScanRel env world runtimeFormals boundaryScope
          formals [] position bindings ⟨[bindings], []⟩
    | noFormal (argument : Atom) (remaining : List Atom)
        (position : Nat) (bindings : Metta.Bindings) :
        RuntimeBranchLocalArgumentScanRel env world runtimeFormals boundaryScope []
          (argument :: remaining) position bindings ⟨[bindings], []⟩
    | step {formal : Atom} {formals : List Atom}
        {argument : Atom} {remaining : List Atom}
        {runtimeCandidates : List Metta.Atom}
        {position : Nat} {bindings : Metta.Bindings}
        {head : Metta.Minimal.ActualTypeBranchScanResult}
        {tailOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult} :
        RuntimeArgumentCandidatesAt env world runtimeFormals boundaryScope position
          bindings argument remaining runtimeCandidates →
        Metta.Minimal.scanActualTypeBranches bindings
            (toLeaTTaAtom formal) runtimeCandidates = head →
        RuntimeBranchLocalArgumentTailsRel env world runtimeFormals boundaryScope
          formals remaining (position + 1) head.successes tailOutcomes →
        RuntimeBranchLocalArgumentScanRel env world runtimeFormals boundaryScope
          (formal :: formals) (argument :: remaining) position bindings
          ⟨tailOutcomes.flatMap (·.successes),
            tailOutcomes.flatMap (·.errors) ++
              runtimeArgumentTypeDiagnosticBlock (position + 1)
                bindings formal head.failures⟩

  /-- Every successful runtime binding branch recursively prepares and scans
  its tail at that branch's own binding state. -/
  inductive RuntimeBranchLocalArgumentTailsRel
      (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
      (runtimeFormals : List Metta.Atom) (boundaryScope : List String) :
      List Atom → List Atom → Nat → List Metta.Bindings →
        List Metta.Minimal.TypeCheckArgsBranchResult → Prop where
    | nil {formals remaining : List Atom}
        {position : Nat} :
        RuntimeBranchLocalArgumentTailsRel env world runtimeFormals boundaryScope
          formals remaining position [] []
    | cons {formals remaining : List Atom}
        {position : Nat} {next : Metta.Bindings}
        {nexts : List Metta.Bindings}
        {outcome : Metta.Minimal.TypeCheckArgsBranchResult}
        {outcomes : List Metta.Minimal.TypeCheckArgsBranchResult} :
        RuntimeBranchLocalArgumentScanRel env world runtimeFormals boundaryScope
          formals remaining position next outcome →
        RuntimeBranchLocalArgumentTailsRel env world runtimeFormals boundaryScope
          formals remaining position nexts outcomes →
        RuntimeBranchLocalArgumentTailsRel env world runtimeFormals boundaryScope
          formals remaining position (next :: nexts) (outcome :: outcomes)

end

/-- The concrete repaired runtime realizes the evidence-free branch-local
skeleton on translated inputs.  The only alignment premise states that the
remaining native formal list is the suffix selected by the runtime position;
candidate preparation and branch chronology are then definitional. -/
theorem typeCheckArgsBranchesScoped_runtimeBranchLocal
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) (boundaryScope : List String) :
    ∀ (arguments formals : List Atom) (position : Nat)
        (bindings : Metta.Bindings),
      runtimeFormals.drop position = toLeaTTaAtoms formals →
      RuntimeBranchLocalArgumentScanRel env world runtimeFormals boundaryScope
        formals arguments position bindings
        (Metta.Minimal.typeCheckArgsBranchesScoped env world runtimeFormals
          boundaryScope position bindings (toLeaTTaAtoms arguments)) := by
  intro arguments
  induction arguments with
  | nil =>
      intro formals position bindings alignment
      simpa [Metta.Minimal.typeCheckArgsBranchesScoped] using
        (RuntimeBranchLocalArgumentScanRel.noArguments
          (env := env) (world := world) (runtimeFormals := runtimeFormals)
          formals position bindings)
  | cons argument remaining inductionHypothesis =>
      intro formals position bindings alignment
      cases formals with
      | nil =>
          have lookup : runtimeFormals[position]? = none := by
            have atHead := congrArg (fun types => types[0]?) alignment
            simpa [List.getElem?_drop] using atHead
          simpa [Metta.Minimal.typeCheckArgsBranchesScoped, lookup] using
            (RuntimeBranchLocalArgumentScanRel.noFormal
              (env := env) (world := world)
              (runtimeFormals := runtimeFormals)
              argument remaining position bindings)
      | cons formal formals =>
          have lookup : runtimeFormals[position]? =
              some (toLeaTTaAtom formal) := by
            have atHead := congrArg (fun types => types[0]?) alignment
            simpa [List.getElem?_drop, toLeaTTaAtoms] using atHead
          have tailAlignment : runtimeFormals.drop (position + 1) =
              toLeaTTaAtoms formals := by
            rw [← List.drop_drop]
            · rw [alignment]
              rfl
          let prepared := Metta.Minimal.typePrep world
            (toLeaTTaAtom argument)
          let rawActuals := Metta.Minimal.getTypes env prepared
          let avoid := boundaryScope ++ Metta.Minimal.typeInferenceAvoid env
              (.expr (toLeaTTaAtom argument :: toLeaTTaAtoms remaining))
              (runtimeFormals ++ rawActuals) ++ bindings.vars
          let candidates := rawActuals.map
            (Metta.Minimal.freshenTypeCandidate avoid position)
          let checked := Metta.Minimal.scanActualTypeBranches bindings
            (toLeaTTaAtom formal) candidates
          have preparationEquation : RuntimeArgumentCandidatesAt env world
              runtimeFormals boundaryScope position bindings argument remaining
                candidates := by
            rfl
          have runtimeTails : RuntimeBranchLocalArgumentTailsRel env world
              runtimeFormals boundaryScope formals remaining (position + 1)
              checked.successes
              (checked.successes.map fun next =>
                Metta.Minimal.typeCheckArgsBranchesScoped env world runtimeFormals
                  boundaryScope (position + 1) next (toLeaTTaAtoms remaining)) := by
            induction checked.successes with
            | nil => exact .nil
            | cons next nexts tailInduction =>
                exact .cons
                  (inductionHypothesis formals (position + 1) next
                    tailAlignment)
                  tailInduction
          have runtimeRel := RuntimeBranchLocalArgumentScanRel.step
            (env := env) (world := world)
            (runtimeFormals := runtimeFormals)
            preparationEquation (show
              Metta.Minimal.scanActualTypeBranches bindings
                (toLeaTTaAtom formal) candidates = checked by rfl)
            runtimeTails
          simpa [Metta.Minimal.typeCheckArgsBranchesScoped, lookup, prepared,
              rawActuals, avoid, candidates, checked,
              runtimeArgumentTypeDiagnosticBlock] using runtimeRel

/-- Ordinary argument checking is the complete-source-scope specialization
of the scope-explicit branch-local runtime skeleton. -/
theorem typeCheckArgsBranches_runtimeBranchLocal
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) (arguments formals : List Atom)
    (position : Nat) (bindings : Metta.Bindings)
    (alignment : runtimeFormals.drop position = toLeaTTaAtoms formals) :
    RuntimeBranchLocalArgumentScanRel env world runtimeFormals
      (Metta.Minimal.applicationTypeInferenceScope (.sym "%Undefined%")
        (toLeaTTaAtoms arguments))
      formals arguments position bindings
      (Metta.Minimal.typeCheckArgsBranches env world runtimeFormals
        position bindings (toLeaTTaAtoms arguments)) := by
  exact typeCheckArgsBranchesScoped_runtimeBranchLocal env world runtimeFormals
    (Metta.Minimal.applicationTypeInferenceScope (.sym "%Undefined%")
      (toLeaTTaAtoms arguments)) arguments formals position bindings alignment

/-! ## Scoped outcome observation -/

/-- Branch outcomes preserve structural data exactly.  Only the finite
presentation paired with each runtime binding is compared at the declared
public scope. -/
structure ScopedArgumentBranchOutcomeRuntimeRel
    (scope : List String)
    (specOutcome : ArgumentCandidateListsBranchOutcome)
    (runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult) : Prop where
  successes : ScopedTypePresentationSimulationStates scope
    specOutcome.successes runtimeOutcome.successes
  errors : List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
    specOutcome.errors runtimeOutcome.errors

/-- One successful runtime type match can be reconstructed from a
scope-equivalent static presentation when the matched constraint is wholly
observable at that scope.  The two output presentations remain related by
their scoped solution theories; no private spelling is selected globally. -/
theorem matchType_scoped
    {theoryScope : List String}
    {specIncoming : TypeSubst} {runtimeIncoming runtimeOutput : Metta.Bindings}
    {expected actual : Atom}
    (state : ScopedTypePresentationSimulationState
      theoryScope specIncoming runtimeIncoming)
    (constraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars actual →
        name ∈ theoryScope)
    (runtimeEquation : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = some runtimeOutput) :
    ∃ specOutput,
      CorePlusR2TypePresentationMatchRel
          specIncoming expected actual specOutput ∧
        ScopedTypePresentationSimulationState
          theoryScope specOutput runtimeOutput := by
  rcases state with
    ⟨specNormal, branchIncoming, bindingIncoming, branchState, incomingEquiv⟩
  obtain ⟨branchOutput, bindingOutput, branchDerivation, outputState⟩ :=
    branchState.matchType expected actual runtimeEquation
  have constraints :=
    TypeConstraintTheoryEquivAt.of_scopedIncoming_sameConstraint
      incomingEquiv constraintObserved (fun _ member => member)
  have branchOutputNormal := branchDerivation.output_normal branchState.normal
  have branchOutputSatisfied : TypeSubstSatisfied
      (presentedValuation branchOutput) branchOutput :=
    normal_presentedValuation_satisfied branchOutputNormal
  obtain ⟨branchIncomingSatisfied, branchConsistent⟩ :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      branchDerivation branchState.normal
        (presentedValuation branchOutput)).mp branchOutputSatisfied
  obtain ⟨specModel, specIncomingSatisfied, specConsistent, _⟩ :=
    constraints.rightToLeft (presentedValuation branchOutput)
      branchIncomingSatisfied branchConsistent
  obtain ⟨specOutput, specDerivation, specOutputNormal, _⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      specNormal specIncomingSatisfied expected actual specConsistent
  have outputEquiv :=
    CorePlusR2TypePresentationMatchRel.outputTheoryEquivAt
      specNormal branchState.normal specDerivation branchDerivation constraints
  exact ⟨specOutput, specDerivation,
    ⟨specOutputNormal, branchOutput, bindingOutput, outputState, outputEquiv⟩⟩

/-- Runtime failure is exact across the same scoped boundary.  Disjointness
is the matcher-completeness side condition already exposed by the exact
runtime boundary; scoped presentation equivalence contributes no additional
negative assumption. -/
theorem matchType_scoped_none
    {theoryScope : List String}
    {specIncoming : TypeSubst} {runtimeIncoming : Metta.Bindings}
    {expected actual : Atom}
    (state : ScopedTypePresentationSimulationState
      theoryScope specIncoming runtimeIncoming)
    (constraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars actual →
        name ∈ theoryScope)
    (disjoint : VarsDisjoint expected actual)
    (runtimeFailure : Metta.Minimal.matchType runtimeIncoming
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = none) :
    ∀ specOutput,
      ¬CorePlusR2TypePresentationMatchRel
        specIncoming expected actual specOutput := by
  rcases state with
    ⟨specNormal, branchIncoming, bindingIncoming, branchState, incomingEquiv⟩
  have constraints :=
    TypeConstraintTheoryEquivAt.of_scopedIncoming_sameConstraint
      incomingEquiv constraintObserved (fun _ member => member)
  have noBranchPresentation :=
    (matchType_eq_none_iff_no_presentation branchState expected actual
      disjoint).mp runtimeFailure
  intro specOutput specDerivation
  have specOutputNormal := specDerivation.output_normal specNormal
  have specOutputSatisfied : TypeSubstSatisfied
      (presentedValuation specOutput) specOutput :=
    normal_presentedValuation_satisfied specOutputNormal
  obtain ⟨specIncomingSatisfied, specConsistent⟩ :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      specDerivation specNormal (presentedValuation specOutput)).mp
        specOutputSatisfied
  obtain ⟨branchModel, branchIncomingSatisfied, branchConsistent, _⟩ :=
    constraints.leftToRight (presentedValuation specOutput)
      specIncomingSatisfied specConsistent
  obtain ⟨branchOutput, branchDerivation, _, _⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      branchState.normal branchIncomingSatisfied expected actual
        branchConsistent
  exact noBranchPresentation branchOutput branchDerivation

/-- Expected-return branch outcomes retain exact branch and diagnostic order;
only the selected private presentation is compared at the declared public
scope. -/
structure ScopedExpectedReturnBranchOutcomeRuntimeRel
    (scope : List String)
    (specOutcome : ExpectedReturnBranchOutcome)
    (runtimeOutcome : Metta.Minimal.ExpectedReturnBranchScanResult) : Prop where
  selected : Option.Rel
    (ScopedTypePresentationSimulationState scope)
    specOutcome.selected runtimeOutcome.selected
  errors : List.Forall₂ ExpectedReturnDiagnosticRuntimeRel
    specOutcome.errors runtimeOutcome.errors

/-- The repaired expected-return worker is exact for branch lists whose
private finite presentations agree only at a declared scope.  The first
successful branch still commits and every preceding mismatch remains in
order. -/
theorem scanExpectedReturnBranches_presentation_scoped
    (theoryScope : List String) (expected returnType : Atom)
    (constraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars returnType →
        name ∈ theoryScope)
    (returnObserved : ∀ name,
      name ∈ TypeSubst.typeVars returnType → name ∈ theoryScope)
    (disjoint : VarsDisjoint expected returnType) :
    ∀ {presentations : List TypeSubst}
      {runtimeBindings : List Metta.Bindings},
      ScopedTypePresentationSimulationStates
          theoryScope presentations runtimeBindings →
      ∃ specOutcome,
        ExpectedReturnBranchScanRel expected returnType presentations
            specOutcome ∧
          ScopedExpectedReturnBranchOutcomeRuntimeRel theoryScope specOutcome
            (Metta.Minimal.scanExpectedReturnBranches
              (toLeaTTaAtom expected) (toLeaTTaAtom returnType)
              runtimeBindings) := by
  intro presentations runtimeBindings states
  induction states with
  | nil =>
      exact ⟨⟨none, []⟩, .nil,
        { selected := .none
          errors := .nil }⟩
  | @cons presentation runtimeBinding presentations runtimeBindings
      head tail inductionHypothesis =>
      cases runtimeEquation : Metta.Minimal.matchType runtimeBinding
          (toLeaTTaAtom expected) (toLeaTTaAtom returnType) with
      | some runtimeOutput =>
          obtain ⟨presentationOutput, matched, outputState⟩ :=
            matchType_scoped head constraintObserved runtimeEquation
          refine ⟨⟨some presentationOutput, []⟩,
            .matched matched, ?_⟩
          simp only [Metta.Minimal.scanExpectedReturnBranches,
            runtimeEquation]
          exact
            { selected := .some outputState
              errors := .nil }
      | none =>
          have noPresentation :=
            matchType_scoped_none head constraintObserved disjoint
              runtimeEquation
          obtain ⟨tailOutcome, tailScan, tailCorrespondence⟩ :=
            inductionHypothesis
          let specOutcome : ExpectedReturnBranchOutcome :=
            ⟨tailOutcome.selected,
              { expected := expected
                actual := presentation.apply returnType } ::
                tailOutcome.errors⟩
          refine ⟨specOutcome,
            ExpectedReturnBranchScanRel.failed noPresentation tailScan, ?_⟩
          simp only [Metta.Minimal.scanExpectedReturnBranches,
            runtimeEquation]
          exact
            { selected := tailCorrespondence.selected
              errors := .cons
                (.badReturn (head.returnAlpha returnType returnObserved))
                tailCorrespondence.errors }

/-- A branch-local failed-candidate block preserves its observable order and
one-based position.  The displayed formal is derived from scoped incoming
theory equivalence; each displayed actual retains the alpha evidence carried
by the candidate scan. -/
theorem argumentTypeDiagnosticBlock_runtime_scoped
    {theoryScope : List String} {specIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings} {formal : Atom}
    {specFailed : List Atom} {runtimeFailed : List Metta.Atom}
    (state : ScopedTypePresentationSimulationState
      theoryScope specIncoming runtimeIncoming)
    (formalObserved : ∀ name,
      name ∈ TypeSubst.typeVars formal → name ∈ theoryScope)
    (failedAlpha : List.Forall₂
      (fun specCandidate runtimeCandidate =>
        ObservedTypeAlphaRel specCandidate
          (fromLeaTTaAtom runtimeCandidate))
      specFailed runtimeFailed)
    (position : Nat) :
    List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      (argumentTypeDiagnosticBlock position
        (specIncoming.apply formal) specFailed)
      (runtimeArgumentTypeDiagnosticBlock position runtimeIncoming formal
        runtimeFailed) := by
  rcases state with
    ⟨specNormal, branchIncoming, bindingIncoming, branchState, incomingEquiv⟩
  have specBranchAlpha := incomingEquiv.observedTypeAlpha
    specNormal branchState.normal formal formalObserved
  have expectedAlpha : ObservedTypeAlphaRel
      (specIncoming.apply formal)
      (fromLeaTTaAtom
        (Metta.instantiate runtimeIncoming (toLeaTTaAtom formal))) :=
    ObservedTypeAlphaRel.trans specBranchAlpha
      (branchState.returnAlpha formal)
  induction failedAlpha with
  | nil => exact .nil
  | cons actualAlpha _ inductionHypothesis =>
      exact .cons
        { position := rfl
          expected := expectedAlpha
          actual := actualAlpha }
        inductionHypothesis

/-- Same-spelling exact simulation embeds into the scoped branch boundary. -/
theorem TypePresentationSimulationStates.toScoped
    {scope : List String} {presentations : List TypeSubst}
    {runtimeBindings : List Metta.Bindings}
    (states : TypePresentationSimulationStates
      presentations runtimeBindings) :
    ScopedTypePresentationSimulationStates scope
      presentations runtimeBindings := by
  induction states with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      obtain ⟨spec, state⟩ := head
      exact .cons
        (ScopedTypePresentationSimulationState.ofExact state)
        inductionHypothesis

/-- The old shared-spelling outcome is the reflexive specialization of the
branch-local scoped outcome. -/
theorem ArgumentCandidateListsBranchOutcomeRuntimeRel.toScoped
    {scope : List String}
    {specOutcome : ArgumentCandidateListsBranchOutcome}
    {runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
    (outcome : ArgumentCandidateListsBranchOutcomeRuntimeRel
      specOutcome runtimeOutcome) :
    ScopedArgumentBranchOutcomeRuntimeRel scope
      specOutcome runtimeOutcome :=
  ⟨TypePresentationSimulationStates.toScoped outcome.successes,
    outcome.errors⟩

/-- Flattening aligned scoped branch outcomes preserves success order. -/
theorem scopedBranchOutcomes_flatMap_successes
    {scope : List String}
    {specOutcomes : List ArgumentCandidateListsBranchOutcome}
    {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
    (outcomes : List.Forall₂ (ScopedArgumentBranchOutcomeRuntimeRel scope)
      specOutcomes runtimeOutcomes) :
    ScopedTypePresentationSimulationStates scope
      (specOutcomes.flatMap (·.successes))
      (runtimeOutcomes.flatMap (·.successes)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.successes inductionHypothesis

/-- Flattening aligned scoped branch outcomes preserves diagnostic order. -/
theorem scopedBranchOutcomes_flatMap_errors
    {scope : List String}
    {specOutcomes : List ArgumentCandidateListsBranchOutcome}
    {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
    (outcomes : List.Forall₂ (ScopedArgumentBranchOutcomeRuntimeRel scope)
      specOutcomes runtimeOutcomes) :
    List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      (specOutcomes.flatMap (·.errors))
      (runtimeOutcomes.flatMap (·.errors)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.errors inductionHypothesis

/-! ## Recursive node-local conformance -/

set_option maxHeartbeats 800000 in
mutual

  /-- A complete evidence-free runtime branch scan is simulated by the
  static presentation scan when candidate preparation is covered at every
  recursive node.  The node coverage is consumed after exposing the exact
  branch-local presentation; it is never stored in the runtime relation. -/
  theorem runtimeBranchLocalArgumentScan_scoped
      {candidateFamily : Atom → List Atom → Prop}
      {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
      {runtimeFormals : List Metta.Atom}
      {boundaryScope theoryScope : List String}
      {formals arguments : List Atom}
      {candidateLists : List (List Atom)} {position : Nat}
      {specIncoming : TypeSubst}
      {runtimeIncoming : Metta.Bindings}
      {runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
      (coverage : NodeLocalArgumentCandidateCoverage candidateFamily env
        world runtimeFormals boundaryScope theoryScope)
      (formalsObserved : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
      (state : ScopedTypePresentationSimulationState theoryScope
        specIncoming runtimeIncoming)
      (prepared : PreparedArgumentCandidateLists formals specIncoming
        candidateLists (candidateLists.map toLeaTTaAtoms))
      (families : List.Forall₂ candidateFamily arguments candidateLists)
      (runtimeScan : RuntimeBranchLocalArgumentScanRel env world
        runtimeFormals boundaryScope formals arguments position runtimeIncoming
          runtimeOutcome) :
      ∃ specOutcome,
        ArgumentCandidateListsBranchScanRel formals candidateLists position
            specIncoming specOutcome ∧
          ScopedArgumentBranchOutcomeRuntimeRel theoryScope specOutcome
            runtimeOutcome := by
    cases runtimeScan with
    | noArguments formals position bindings =>
        cases families
        exact ⟨⟨[specIncoming], []⟩,
          .noArguments formals position specIncoming,
          ⟨.cons state .nil, .nil⟩⟩
    | noFormal argument remaining position bindings =>
        cases families with
        | cons headFamily tailFamilies =>
            exact ⟨⟨[specIncoming], []⟩,
              .noFormal _ _ position specIncoming,
              ⟨.cons state .nil, .nil⟩⟩
    | @step formal formals argument remaining runtimeCandidates position
        bindings head tailOutcomes preparationEquation scanEquation
        runtimeTails =>
        cases families with
        | cons headFamily tailFamilies =>
            rcases state with
              ⟨specNormal, branchIncoming, bindingIncoming, branchState,
                incomingEquiv⟩
            obtain ⟨decodedRuntimeCandidates, decodedEquation,
                candidatesAlpha⟩ :=
              coverage headFamily branchState incomingEquiv
                (formal := formal) preparationEquation
            have formalObserved : ∀ name,
                name ∈ TypeSubst.typeVars formal →
                  name ∈ theoryScope := by
              intro name member
              exact formalsObserved name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inl member)
            have tailFormalsObserved : ∀ name,
                name ∈ TypeSubst.typeVarsList formals →
                  name ∈ theoryScope := by
              intro name member
              exact formalsObserved name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inr member)
            have decodedScan :
                Metta.Minimal.scanActualTypeBranches runtimeIncoming
                    (toLeaTTaAtom formal)
                    (toLeaTTaAtoms decodedRuntimeCandidates) = head := by
              rw [decodedEquation]
              exact scanEquation
            obtain ⟨headPresentations, failedCandidates, headRel,
                branchStates, failedAlpha⟩ :=
              scanActualTypeBranches_privateCandidates_scoped
                specNormal branchState incomingEquiv
                (by
                  intro name member
                  simp [argumentCandidateNodeScope, member])
                (by
                  intro name member
                  simp [argumentCandidateNodeScope, member])
                (by
                  intro name member
                  simp [argumentCandidateNodeScope, member])
                formalObserved candidatesAlpha
            rw [decodedScan] at branchStates failedAlpha
            obtain ⟨specTailOutcomes, specTails, tailCorrespondence⟩ :=
              runtimeBranchLocalArgumentTails_scoped coverage
                tailFormalsObserved prepared branchStates tailFamilies
                runtimeTails
            let specOutcome : ArgumentCandidateListsBranchOutcome :=
              ⟨specTailOutcomes.flatMap (·.successes),
                specTailOutcomes.flatMap (·.errors) ++
                  argumentTypeDiagnosticBlock (position + 1)
                    (specIncoming.apply formal) failedCandidates⟩
            refine ⟨specOutcome,
              .step headRel specTails, ?_⟩
            have currentDiagnostics : List.Forall₂
                ArgumentTypeDiagnosticRuntimeRel
                (argumentTypeDiagnosticBlock (position + 1)
                  (specIncoming.apply formal) failedCandidates)
                (runtimeArgumentTypeDiagnosticBlock (position + 1)
                  runtimeIncoming formal head.failures) := by
              exact argumentTypeDiagnosticBlock_runtime_scoped
                ⟨specNormal, branchIncoming, bindingIncoming, branchState,
                  incomingEquiv⟩ formalObserved failedAlpha (position + 1)
            exact
              { successes :=
                  scopedBranchOutcomes_flatMap_successes tailCorrespondence
                errors := List.rel_append
                  (scopedBranchOutcomes_flatMap_errors tailCorrespondence)
                  currentDiagnostics }

  /-- Pointwise recursive conformance for every successful presentation at
  one argument position.  Static tail freshness is derived from the selected
  candidate; runtime candidate coverage is requested anew at the next node,
  after the scoped state has grown. -/
  theorem runtimeBranchLocalArgumentTails_scoped
      {candidateFamily : Atom → List Atom → Prop}
      {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
      {runtimeFormals : List Metta.Atom}
      {boundaryScope theoryScope : List String}
      {parentIncoming : TypeSubst} {parentFormal : Atom}
      {parentCandidates formals arguments : List Atom}
      {candidateLists : List (List Atom)} {position : Nat}
      {presentations : List TypeSubst}
      {runtimeBindings : List Metta.Bindings}
      {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
      (coverage : NodeLocalArgumentCandidateCoverage candidateFamily env
        world runtimeFormals boundaryScope theoryScope)
      (formalsObserved : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
      (prepared : PreparedArgumentCandidateLists
        (parentFormal :: formals) parentIncoming
        (parentCandidates :: candidateLists)
        ((parentCandidates :: candidateLists).map toLeaTTaAtoms))
      (states : ScopedTypePresentationCandidateBranchStates theoryScope
        parentIncoming parentFormal parentCandidates presentations
          runtimeBindings)
      (families : List.Forall₂ candidateFamily arguments candidateLists)
      (runtimeTails : RuntimeBranchLocalArgumentTailsRel env world
        runtimeFormals boundaryScope formals arguments position runtimeBindings
          runtimeOutcomes) :
      ∃ specOutcomes,
        ArgumentCandidateListsBranchTailsRel formals candidateLists position
            presentations specOutcomes ∧
          List.Forall₂ (ScopedArgumentBranchOutcomeRuntimeRel theoryScope)
            specOutcomes runtimeOutcomes := by
    cases runtimeTails with
    | nil =>
        cases states
        exact ⟨[], .nil, .nil⟩
    | cons headScan tailScans =>
        cases states with
        | cons headState tailStates =>
            obtain ⟨candidate, candidateMember, matched, scopedState⟩ :=
              headState
            have nextAvoids := prepared.selected_output_avoids_tail
              candidateMember matched
            have tailPrepared := prepared.tail nextAvoids
            obtain ⟨specOutcome, specScan, outcomeCorrespondence⟩ :=
              runtimeBranchLocalArgumentScan_scoped coverage
                formalsObserved scopedState tailPrepared families headScan
            obtain ⟨specOutcomes, specScans,
                outcomeCorrespondences⟩ :=
              runtimeBranchLocalArgumentTails_scoped coverage
                formalsObserved prepared tailStates families tailScans
            exact ⟨specOutcome :: specOutcomes,
              .cons specScan specScans,
              .cons outcomeCorrespondence outcomeCorrespondences⟩

end

/-! ## Recursive conformance with two private histories -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
mutual

  /-- Recursive branch-scan conformance under the realizable two-history
  support invariant.  The executable recursion remains evidence-free;
  position-indexed coverage is consumed only by this theorem. -/
  theorem runtimeBranchLocalArgumentScan_twoHistory
      {candidateFamily : Nat → Atom → List Atom → Prop}
      {invariant : TwoHistoryScanStateInvariant}
      {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
      {runtimeFormals : List Metta.Atom}
      {boundaryScope theoryScope publicScope : List String}
      {formals arguments : List Atom}
      {candidateLists : List (List Atom)} {position : Nat}
      {staticHistory runtimeHistory : List Atom}
      {specIncoming branchIncoming : TypeSubst}
      {runtimeIncoming : Metta.Bindings}
      {runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
      (coverage : TwoHistoryNodeLocalArgumentCandidateCoverage
        candidateFamily invariant env world runtimeFormals boundaryScope theoryScope
          publicScope)
      (formalsObserved : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
      (formalsPublic : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ publicScope)
      (state : TwoHistoryScopedTypePresentationSimulationState theoryScope
        publicScope position staticHistory runtimeHistory specIncoming
          branchIncoming runtimeIncoming)
      (stateInvariant : invariant position staticHistory runtimeHistory
        specIncoming runtimeIncoming)
      (alignment : runtimeFormals.drop position = toLeaTTaAtoms formals)
      (prepared : PreparedArgumentCandidateLists formals specIncoming
        candidateLists (candidateLists.map toLeaTTaAtoms))
      (families : PositionedArgumentCandidateFamiliesRel candidateFamily
        position arguments candidateLists)
      (runtimeScan : RuntimeBranchLocalArgumentScanRel env world
        runtimeFormals boundaryScope formals arguments position runtimeIncoming
          runtimeOutcome) :
      ∃ specOutcome,
        ArgumentCandidateListsBranchScanRel formals candidateLists position
            specIncoming specOutcome ∧
          ScopedArgumentBranchOutcomeRuntimeRel theoryScope specOutcome
            runtimeOutcome := by
    cases runtimeScan with
    | noArguments formals position bindings =>
        cases families
        exact ⟨⟨[specIncoming], []⟩,
          .noArguments formals position specIncoming,
          ⟨.cons state.toScoped .nil, .nil⟩⟩
    | noFormal argument remaining position bindings =>
        cases families with
        | cons headFamily tailFamilies =>
            exact ⟨⟨[specIncoming], []⟩,
              .noFormal _ _ position specIncoming,
              ⟨.cons state.toScoped .nil, .nil⟩⟩
    | @step formal formals argument remaining runtimeCandidates position
        bindings head tailOutcomes preparationEquation scanEquation
        runtimeTails =>
        cases families with
        | @cons _ _ _ specCandidates _ headFamily tailFamilies =>
            have formalRuntimeMember :
                toLeaTTaAtom formal ∈ runtimeFormals := by
              apply List.mem_of_mem_drop
              rw [alignment]
              simp [toLeaTTaAtoms]
            have positionBound : position < runtimeFormals.length := by
              have dropLengthPositive :
                  0 < (runtimeFormals.drop position).length := by
                rw [alignment]
                simp [toLeaTTaAtoms_eq_map]
              simpa [List.length_drop] using dropLengthPositive
            have specCandidatesAvoidFormal :
                AtomsAvoid specCandidates (TypeSubst.typeVars formal) := by
              intro name candidateOccurrence formalOccurrence
              exact prepared.avoidFormals name
                (by
                  simp only [List.flatten_cons, typeVarsList_append,
                    List.mem_append]
                  exact Or.inl candidateOccurrence)
                (by
                  simp only [TypeSubst.typeVarsList, List.mem_append]
                  exact Or.inl formalOccurrence)
            obtain ⟨decodedRuntimeCandidates, decodedEquation,
                candidatesAlpha, invariantExtension⟩ :=
              coverage state headFamily stateInvariant positionBound
                formalRuntimeMember specCandidatesAvoidFormal preparationEquation
            have formalObserved : ∀ name,
                name ∈ TypeSubst.typeVars formal →
                  name ∈ theoryScope := by
              intro name member
              exact formalsObserved name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inl member)
            have formalPublic : ∀ name,
                name ∈ TypeSubst.typeVars formal →
                  name ∈ publicScope := by
              intro name member
              exact formalsPublic name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inl member)
            have tailFormalsObserved : ∀ name,
                name ∈ TypeSubst.typeVarsList formals →
                  name ∈ theoryScope := by
              intro name member
              exact formalsObserved name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inr member)
            have tailFormalsPublic : ∀ name,
                name ∈ TypeSubst.typeVarsList formals →
                  name ∈ publicScope := by
              intro name member
              exact formalsPublic name (by
                simp only [TypeSubst.typeVarsList, List.mem_append]
                exact Or.inr member)
            have decodedScan :
                Metta.Minimal.scanActualTypeBranches runtimeIncoming
                    (toLeaTTaAtom formal)
                    (toLeaTTaAtoms decodedRuntimeCandidates) = head := by
              rw [decodedEquation]
              exact scanEquation
            obtain ⟨headPresentations, failedCandidates, headRel,
                branchStates, failedAlpha⟩ :=
              scanActualTypeBranches_privateCandidates_twoHistory state
                formalObserved formalPublic candidatesAlpha
            rw [decodedScan] at branchStates failedAlpha
            have invariantBranchStates :
                TwoHistoryInvariantCandidateBranchStates invariant
                  theoryScope publicScope position staticHistory runtimeHistory
                  specIncoming branchIncoming formal
                  specCandidates decodedRuntimeCandidates
                  headPresentations head.successes := by
              apply branchStates.imp
              intro presentation runtimeBinding witness
              obtain ⟨specCandidate, specMember, runtimeCandidate,
                runtimeMember, alpha, matched, nextBranch, nextState⟩ := witness
              refine ⟨specCandidate, specMember, runtimeCandidate,
                runtimeMember, alpha, matched, nextBranch, nextState, ?_⟩
              exact invariantExtension specMember runtimeMember alpha matched
                nextState
            obtain ⟨specTailOutcomes, specTails, tailCorrespondence⟩ :=
              runtimeBranchLocalArgumentTails_twoHistory coverage
                tailFormalsObserved tailFormalsPublic alignment prepared
                invariantBranchStates tailFamilies runtimeTails
            let specOutcome : ArgumentCandidateListsBranchOutcome :=
              ⟨specTailOutcomes.flatMap (·.successes),
                specTailOutcomes.flatMap (·.errors) ++
                  argumentTypeDiagnosticBlock (position + 1)
                    (specIncoming.apply formal) failedCandidates⟩
            refine ⟨specOutcome, .step headRel specTails, ?_⟩
            have currentDiagnostics : List.Forall₂
                ArgumentTypeDiagnosticRuntimeRel
                (argumentTypeDiagnosticBlock (position + 1)
                  (specIncoming.apply formal) failedCandidates)
                (runtimeArgumentTypeDiagnosticBlock (position + 1)
                  runtimeIncoming formal head.failures) := by
              exact argumentTypeDiagnosticBlock_runtime_scoped
                state.toScoped formalObserved failedAlpha (position + 1)
            exact
              { successes :=
                  scopedBranchOutcomes_flatMap_successes tailCorrespondence
                errors := List.rel_append
                  (scopedBranchOutcomes_flatMap_errors tailCorrespondence)
                  currentDiagnostics }

  /-- Pointwise recursion over every successful branch, carrying the exact
  selected static/runtime candidate pair into the next node. -/
  theorem runtimeBranchLocalArgumentTails_twoHistory
      {candidateFamily : Nat → Atom → List Atom → Prop}
      {invariant : TwoHistoryScanStateInvariant}
      {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
      {runtimeFormals : List Metta.Atom}
      {boundaryScope theoryScope publicScope : List String}
      {parentPosition : Nat}
      {staticHistory runtimeHistory : List Atom}
      {parentIncoming branchIncoming : TypeSubst} {parentFormal : Atom}
      {parentCandidates runtimeParentCandidates formals arguments : List Atom}
      {candidateLists : List (List Atom)}
      {presentations : List TypeSubst}
      {runtimeBindings : List Metta.Bindings}
      {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
      (coverage : TwoHistoryNodeLocalArgumentCandidateCoverage
        candidateFamily invariant env world runtimeFormals boundaryScope theoryScope
          publicScope)
      (formalsObserved : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
      (formalsPublic : ∀ name,
        name ∈ TypeSubst.typeVarsList formals → name ∈ publicScope)
      (parentAlignment : runtimeFormals.drop parentPosition =
        toLeaTTaAtoms (parentFormal :: formals))
      (prepared : PreparedArgumentCandidateLists
        (parentFormal :: formals) parentIncoming
        (parentCandidates :: candidateLists)
        ((parentCandidates :: candidateLists).map toLeaTTaAtoms))
      (states : TwoHistoryInvariantCandidateBranchStates invariant
        theoryScope publicScope parentPosition staticHistory runtimeHistory
        parentIncoming branchIncoming parentFormal parentCandidates
        runtimeParentCandidates presentations runtimeBindings)
      (families : PositionedArgumentCandidateFamiliesRel candidateFamily
        (parentPosition + 1) arguments candidateLists)
      (runtimeTails : RuntimeBranchLocalArgumentTailsRel env world
        runtimeFormals boundaryScope formals arguments (parentPosition + 1)
          runtimeBindings runtimeOutcomes) :
      ∃ specOutcomes,
        ArgumentCandidateListsBranchTailsRel formals candidateLists
            (parentPosition + 1) presentations specOutcomes ∧
          List.Forall₂ (ScopedArgumentBranchOutcomeRuntimeRel theoryScope)
            specOutcomes runtimeOutcomes := by
    cases runtimeTails with
    | nil =>
        cases states
        exact ⟨[], .nil, .nil⟩
    | cons headScan tailScans =>
        cases states with
        | cons headState tailStates =>
            obtain ⟨specCandidate, specCandidateMember, runtimeCandidate,
              _runtimeCandidateMember, _candidateAlpha, matched,
              nextBranch, nextState, headInvariant⟩ := headState
            have nextAvoids := prepared.selected_output_avoids_tail
              specCandidateMember matched
            have tailPrepared := prepared.tail nextAvoids
            have tailAlignment : runtimeFormals.drop (parentPosition + 1) =
                toLeaTTaAtoms formals := by
              simpa [List.tail_drop, toLeaTTaAtoms] using
                congrArg List.tail parentAlignment
            obtain ⟨specOutcome, specScan, outcomeCorrespondence⟩ :=
              runtimeBranchLocalArgumentScan_twoHistory coverage
                formalsObserved formalsPublic nextState headInvariant
                tailAlignment
                tailPrepared families headScan
            obtain ⟨specOutcomes, specScans,
                outcomeCorrespondences⟩ :=
              runtimeBranchLocalArgumentTails_twoHistory coverage
                formalsObserved formalsPublic parentAlignment prepared
                tailStates families
                tailScans
            exact ⟨specOutcome :: specOutcomes,
              .cons specScan specScans,
              .cons outcomeCorrespondence outcomeCorrespondences⟩

end

/-! ## Boundary canaries -/

/-- A closed candidate is its own private alpha sibling for every scope. -/
theorem closed_candidate_family_alpha (fixedScope : List String) :
    PrivateCandidateFamilyAlphaRel fixedScope
      [.symbol "B"] [.symbol "B"] := by
  apply List.Forall₂.cons
  · refine ⟨.symbol "B", ?_, ?_⟩ <;>
      exact ⟨id, Function.injective_id, by simp [renameTypeVars], by
        simp [TypeSubst.typeVars]⟩
  · exact .nil

/-- Alpha-renaming cannot change one closed type constructor into another. -/
theorem distinct_closed_candidates_not_alpha :
    ¬PrivateCandidateFamilyAlphaRel []
      [.symbol "A"] [.symbol "B"] := by
  intro alpha
  cases alpha with
  | cons head tail =>
      rcases head with
        ⟨source,
          ⟨leftRename, _, leftEquation, _⟩,
          ⟨rightRename, _, rightEquation, _⟩⟩
      cases source with
      | symbol name =>
          simp [renameTypeVars] at leftEquation rightEquation
          have namesEqual : "A" = "B" :=
            leftEquation.trans rightEquation.symm
          simp at namesEqual
      | var name => simp [renameTypeVars] at leftEquation
      | grounded value => simp [renameTypeVars] at leftEquation
      | expression atoms => simp [renameTypeVars] at leftEquation

/-- With no arguments, the branch-local relation returns the incoming runtime
binding exactly once and emits no diagnostics. -/
theorem branch_local_no_arguments_canary
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeFormals : List Metta.Atom) :
    RuntimeBranchLocalArgumentScanRel env world runtimeFormals []
      [.symbol "A"] [] 0 Metta.Bindings.empty
      ⟨[Metta.Bindings.empty], []⟩ :=
  .noArguments [.symbol "A"] 0 Metta.Bindings.empty

end Mettapedia.Languages.MeTTa.HE.LeaTTaBranchLocalTypeScanConformance
