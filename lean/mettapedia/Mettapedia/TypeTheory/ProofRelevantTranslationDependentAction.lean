import Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

/-!
# Proof-relevant translations act on dependent history families

A proof-relevant GSLT translation maps one authored occurrence at a time.
This module proves that the local operation extends coherently to complete
finite histories, hence to a functor between the free evidence-path contexts
and a natural map between their representable dependent families.

The preservation levels are deliberately separated:

* every translation maps paths, preserves their length, and locally lifts
  target paths beginning at an image state;
* an exact translation is bijective on each fixed-endpoint one-step evidence
  fibre;
* exactness on complete histories is a stronger property, because a term map
  may identify distinct intermediate states.

The final canaries witness both sides.  The Boolean/optional representation
change is exact on complete histories.  A state-collapsing translation is
exact on every one-step evidence fibre but identifies two paths through
different intermediate states.
-/

set_option autoImplicit false

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

universe u

/-! ## Functorial action on complete evidence paths -/

namespace Mettapedia.GSLT.ProofRelevant.Translation

/-- Map every authored occurrence in a finite evidence path. -/
def mapEvidencePath {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    {first last : EvidenceObject source} →
      EvidencePath source first last →
      EvidencePath target (translation.mapTerm first)
        (translation.mapTerm last)
  | _, _, .refl object => .refl (translation.mapTerm object)
  | _, _, .cons evidence rest =>
      .cons (translation.mapEvidence evidence)
        (translation.mapEvidencePath rest)

@[simp] theorem mapEvidencePath_refl
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    (object : EvidenceObject source) :
    translation.mapEvidencePath (.refl object) =
      .refl (translation.mapTerm object) :=
  rfl

@[simp] theorem mapEvidencePath_append
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {first middle last : EvidenceObject source}
    (earlier : EvidencePath source first middle)
    (later : EvidencePath source middle last) :
    translation.mapEvidencePath (earlier.append later) =
      (translation.mapEvidencePath earlier).append
        (translation.mapEvidencePath later) := by
  induction earlier with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp [Route.append, mapEvidencePath, inductionHypothesis]

@[simp] theorem mapEvidencePath_length
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {first last : EvidenceObject source}
    (path : EvidencePath source first last) :
    (translation.mapEvidencePath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp [mapEvidencePath, Route.length, inductionHypothesis]

@[simp] theorem mapEvidencePath_id
    {system : ProofRelevantGSLT.{u}}
    {first last : EvidenceObject system}
    (path : EvidencePath system first last) :
    (Translation.id system).mapEvidencePath path = path := by
  induction path with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp only [mapEvidencePath]
      congr

@[simp] theorem mapEvidencePath_comp
    {first middle last : ProofRelevantGSLT.{u}}
    (earlier : Translation first middle)
    (later : Translation middle last)
    {source target : EvidenceObject first}
    (path : EvidencePath first source target) :
    (earlier.comp later).mapEvidencePath path =
      later.mapEvidencePath (earlier.mapEvidencePath path) := by
  induction path with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp only [mapEvidencePath]
      congr

/-- A proof-relevant translation induces a substitution between the free
evidence-path contexts. -/
def evidenceFunctor {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    ContextHom (evidenceContext source) (evidenceContext target) where
  obj := translation.mapTerm
  map := translation.mapEvidencePath
  map_id _ := rfl
  map_comp earlier later :=
    translation.mapEvidencePath_append earlier later

@[simp] theorem evidenceFunctor_obj
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    (term : EvidenceObject source) :
    translation.evidenceFunctor.obj term = translation.mapTerm term :=
  rfl

@[simp] theorem evidenceFunctor_map
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {first last : EvidenceObject source}
    (path : first ⟶ last) :
    translation.evidenceFunctor.map path =
      translation.mapEvidencePath path :=
  rfl

/-- Mapping histories is natural in their endpoint: extending a history and
then translating it is the same as translating both pieces and extending in
the target.  This is the dependent-family action of a GSLT translation. -/
def historyMap {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    (start : EvidenceObject source) :
    evidencePathFamily source start ⟶
      reindexFamily
        (evidencePathFamily target (translation.mapTerm start))
        translation.evidenceFunctor where
  app finish := TypeCat.ofHom translation.mapEvidencePath
  naturality first last path := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext history
    exact translation.mapEvidencePath_append history path

@[simp] theorem historyMap_app
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    (start finish : EvidenceObject source)
    (history : (evidencePathFamily source start).obj finish) :
    (translation.historyMap start).app finish history =
      translation.mapEvidencePath history :=
  rfl

/-! ## Local coverage extends from steps to paths -/

/-- Lift a target path whose initial state is propositionally identified with
a translated source state.  The explicit initial equality is what makes
coverage stable under dependent path indices. -/
def liftEvidencePathFrom {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {sourceTerm : EvidenceObject source}
    {targetStart : EvidenceObject target}
    {targetTerm : EvidenceObject target}
    (startEq : EqWitness (translation.mapTerm sourceTerm) targetStart)
    (path : EvidencePath target targetStart targetTerm) :
    Sigma fun sourceTarget =>
      EvidencePath source sourceTerm sourceTarget ×
        EqWitness (translation.mapTerm sourceTarget) targetTerm :=
  match path with
  | .refl _ => ⟨sourceTerm, .refl sourceTerm, startEq⟩
  | .cons evidence rest => by
      cases startEq.down.down
      obtain ⟨sourceMiddle, sourceEvidence, middleEq⟩ :=
        translation.liftEvidence evidence
      obtain ⟨sourceTarget, sourceRest, targetEq⟩ :=
        translation.liftEvidencePathFrom middleEq rest
      exact ⟨sourceTarget, .cons sourceEvidence sourceRest, targetEq⟩

/-- Every target path starting at a translated state can be lifted to a
source path whose translated endpoint is equal to the target endpoint.

This is a simulation/coverage theorem.  It intentionally does not claim that
mapping the selected source path recovers the same target occurrence history;
that stronger statement needs evidence exactness. -/
def liftEvidencePath {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {sourceTerm : EvidenceObject source}
    {targetTerm : EvidenceObject target}
    (path : EvidencePath target
      (translation.mapTerm sourceTerm) targetTerm) :
    Sigma fun sourceTarget =>
      EvidencePath source sourceTerm sourceTarget ×
        EqWitness (translation.mapTerm sourceTarget) targetTerm :=
  translation.liftEvidencePathFrom ⟨⟨rfl⟩⟩ path

end Mettapedia.GSLT.ProofRelevant.Translation

namespace Mettapedia.TypeTheory.ProofRelevantTranslationDependentAction

/-! ## Explicit preservation properties -/

/-- No two fixed-endpoint source histories are identified. -/
def HistoryFaithful {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop :=
  ∀ (first last : EvidenceObject source),
    Function.Injective
      (@Translation.mapEvidencePath source target translation first last)

/-- Every fixed-endpoint target history between translated states is the
image of a source history with those same source endpoints. -/
def HistoryFull {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop :=
  ∀ (first last : EvidenceObject source),
    Function.Surjective
      (@Translation.mapEvidencePath source target translation first last)

/-- Exactness on whole histories is componentwise bijectivity of the natural
history map. -/
structure HistoryExact {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop where
  faithful : HistoryFaithful translation
  full : HistoryFull translation

namespace HistoryExact

/-- Identity is exact on histories. -/
theorem id (system : ProofRelevantGSLT.{u}) :
    HistoryExact (Translation.id system) where
  faithful := by
    intro first last left right equality
    exact (Translation.mapEvidencePath_id left).symm.trans
      (equality.trans (Translation.mapEvidencePath_id right))
  full := by
    intro first last path
    exact ⟨path, Translation.mapEvidencePath_id path⟩

/-- History exactness is compositional. -/
theorem comp {first middle last : ProofRelevantGSLT.{u}}
    {earlier : Translation first middle}
    {later : Translation middle last}
    (earlierExact : HistoryExact earlier)
    (laterExact : HistoryExact later) :
    HistoryExact (earlier.comp later) where
  faithful := by
    intro source target left right equality
    apply earlierExact.faithful source target
    apply laterExact.faithful
      (earlier.mapTerm source) (earlier.mapTerm target)
    simpa using equality
  full := by
    intro source target targetPath
    obtain ⟨middlePath, middlePath_eq⟩ :=
      laterExact.full (earlier.mapTerm source)
        (earlier.mapTerm target) targetPath
    obtain ⟨sourcePath, sourcePath_eq⟩ :=
      earlierExact.full source target middlePath
    refine ⟨sourcePath, ?_⟩
    rw [Translation.mapEvidencePath_comp, sourcePath_eq, middlePath_eq]

end HistoryExact

/-- Injectivity on every fixed-endpoint one-step evidence fibre. -/
def StepFaithful {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop :=
  ∀ (first last : EvidenceObject source),
    Function.Injective
      (@Translation.mapEvidence source target translation first last)

/-- Surjectivity onto every one-step evidence fibre between image states. -/
def StepFullOnImage {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop :=
  ∀ (first last : EvidenceObject source),
    Function.Surjective
      (@Translation.mapEvidence source target translation first last)

/-- Exactness at one step, kept distinct from exactness of whole histories. -/
structure StepExactOnImage {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) : Prop where
  faithful : StepFaithful translation
  full : StepFullOnImage translation

/-- The existing exact-translation structure supplies exactly the one-step
property its name promises. -/
theorem stepExactOnImage_of_exactTranslation
    {source target : ProofRelevantGSLT.{u}}
    (translation : ExactTranslation source target) :
    StepExactOnImage translation.toTranslation where
  faithful := by
    intro first last left right equality
    apply (translation.evidenceEquiv first last).injective
    rw [translation.evidenceEquiv_agrees,
      translation.evidenceEquiv_agrees]
    exact equality
  full := by
    intro first last targetEvidence
    refine ⟨(translation.evidenceEquiv first last).symm targetEvidence, ?_⟩
    rw [← translation.evidenceEquiv_agrees]
    exact (translation.evidenceEquiv first last).apply_symm_apply
      targetEvidence

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.ProofRelevant.Canary

/-- Invert the nontrivial Boolean-to-optional evidence representation on
complete histories. -/
def optionToBoolPath :
    {first last : EvidenceObject optionSystem} →
      EvidencePath optionSystem first last →
      EvidencePath boolSystem first last
  | _, _, .refl object => .refl object
  | _, _, .cons evidence rest =>
      .cons (boolOptionEquiv.symm evidence) (optionToBoolPath rest)

theorem optionToBoolPath_map
    {first last : EvidenceObject boolSystem}
    (path : EvidencePath boolSystem first last) :
    optionToBoolPath
        (boolToOption.toTranslation.mapEvidencePath path) = path := by
  induction path with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp only [Translation.mapEvidencePath, optionToBoolPath]
      rw [show boolOptionEquiv.symm
          (boolToOption.toTranslation.mapEvidence evidence) = evidence by
        rw [← boolToOption.evidenceEquiv_agrees]
        exact boolOptionEquiv.symm_apply_apply evidence]
      rw [inductionHypothesis]
      rfl

theorem map_optionToBoolPath
    {first last : EvidenceObject optionSystem}
    (path : EvidencePath optionSystem first last) :
    boolToOption.toTranslation.mapEvidencePath
        (optionToBoolPath path) = path := by
  induction path with
  | refl => rfl
  | cons evidence rest inductionHypothesis =>
      simp only [optionToBoolPath, Translation.mapEvidencePath]
      rw [show boolToOption.toTranslation.mapEvidence
          (boolOptionEquiv.symm evidence) = evidence by
        rw [← boolToOption.evidenceEquiv_agrees]
        exact boolOptionEquiv.apply_symm_apply evidence]
      rw [inductionHypothesis]
      rfl

/-- A non-identity change of evidence representation is exact on complete
histories, not merely on isolated steps. -/
theorem boolToOption_historyExact :
    HistoryExact boolToOption.toTranslation where
  faithful := by
    intro first last left right equality
    rw [← optionToBoolPath_map left, ← optionToBoolPath_map right,
      equality]
  full := by
    intro first last path
    exact ⟨optionToBoolPath path, map_optionToBoolPath path⟩

/-! ### Exact steps do not suffice when states collapse -/

/-- The indiscrete Boolean-state dynamics: every state can step to every
state, with one retained occurrence per ordered pair. -/
def boolStateTheory : GSLT where
  Term := Bool
  equations :=
    { r := Eq
      iseqv :=
        { refl := fun _ => rfl
          symm := fun equality => equality.symm
          trans := fun first second => first.trans second } }
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target source_eq _
    subst source_eq
    exact ⟨target, trivial, rfl⟩
  rewrites_resp_right := by
    intros
    trivial

def boolStateSteps : StepEvidence boolStateTheory where
  Evidence := fun _ _ => Unit
  erases_iff := by
    intros
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨()⟩

def boolStateSystem : ProofRelevantGSLT :=
  ⟨boolStateTheory, boolStateSteps⟩

/-- Collapse both source states to the target's one state.  Each source
one-step fibre is still exactly equivalent to the corresponding target
one-step fibre. -/
def collapseStatesUnderlying : Translation boolStateSystem unitSystem where
  mapTerm := fun _ => ()
  mapEquiv := fun _ => rfl
  mapEvidence := fun _ => ()
  liftEvidence := by
    intro sourceTerm targetTerm evidence
    exact ⟨sourceTerm, (), ⟨⟨rfl⟩⟩⟩

def collapseStates : ExactTranslation boolStateSystem unitSystem where
  toTranslation := collapseStatesUnderlying
  evidenceEquiv := fun _ _ => Equiv.refl Unit
  evidenceEquiv_agrees := by
    intros
    rfl

/-- A two-step loop whose first intermediate state is `false`. -/
def pathViaFalse : EvidencePath boolStateSystem false false :=
  .cons (middle := false) ()
    (.cons (middle := false) () (.refl false))

/-- A two-step loop whose first intermediate state is `true`. -/
def pathViaTrue : EvidencePath boolStateSystem false false :=
  .cons (middle := true) ()
    (.cons (middle := false) () (.refl false))

/-- Observe the first intermediate state of a nonempty Boolean-state path. -/
def firstIntermediate {first last : EvidenceObject boolStateSystem} :
    EvidencePath boolStateSystem first last → Option Bool
  | .refl _ => none
  | .cons (middle := middle) _ _ => some middle

@[simp] theorem firstIntermediate_pathViaFalse :
    firstIntermediate pathViaFalse = some false :=
  rfl

@[simp] theorem firstIntermediate_pathViaTrue :
    firstIntermediate pathViaTrue = some true :=
  rfl

theorem pathViaFalse_ne_pathViaTrue :
    pathViaFalse ≠ pathViaTrue := by
  intro equality
  have observed := congrArg firstIntermediate equality
  simp at observed

/-- State collapse identifies the two histories even though their one-step
evidence fibres are exact. -/
theorem collapseStates_maps_paths_same :
    collapseStates.toTranslation.mapEvidencePath pathViaFalse =
      collapseStates.toTranslation.mapEvidencePath pathViaTrue :=
  rfl

theorem collapseStates_not_historyFaithful :
    ¬ HistoryFaithful collapseStates.toTranslation := by
  intro faithful
  exact pathViaFalse_ne_pathViaTrue
    (faithful false false collapseStates_maps_paths_same)

/-- The complete discriminator: fibrewise exact occurrences coexist with
loss of whole-history identity when intermediate states are collapsed. -/
theorem exactSteps_do_not_imply_exactHistories :
    StepExactOnImage collapseStates.toTranslation ∧
      ¬ HistoryExact collapseStates.toTranslation := by
  constructor
  · exact stepExactOnImage_of_exactTranslation collapseStates
  · intro exactHistories
    exact collapseStates_not_historyFaithful exactHistories.faithful

end Canary

#print axioms Translation.mapEvidencePath_append
#print axioms Translation.mapEvidencePath_length
#print axioms Translation.evidenceFunctor
#print axioms Translation.historyMap
#print axioms Translation.liftEvidencePath
#print axioms HistoryExact.comp
#print axioms stepExactOnImage_of_exactTranslation
#print axioms Canary.boolToOption_historyExact
#print axioms Canary.pathViaFalse_ne_pathViaTrue
#print axioms Canary.exactSteps_do_not_imply_exactHistories

end Mettapedia.TypeTheory.ProofRelevantTranslationDependentAction
