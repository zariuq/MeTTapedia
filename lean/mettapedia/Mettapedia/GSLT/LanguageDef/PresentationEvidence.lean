import Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization

/-!
# Scoped evidence for an authored presentation

The constructors record different kinds of supplied evidence, not authority
levels or a ranking of languages:

* `authoredProbe` carries a status notice, not an adequacy theorem;
* `reportedModel` carries a candidate value and a description, not a checked
  semantic structure or a typed interpretation of the presentation;
* `exactFragment` carries an observed operational realization and its proved
  equation on supported inputs.  Its actual scope is given by the realization's
  support predicate and observations; the scope string is a label;
* `exactFragmentWithArtifact` additionally binds an exporter result to an
  artifact by exact equality.  This does not relate artifact execution to the
  realization's machine or establish correctness of a C implementation.

Only the realization constructors carry operational adequacy.  Adding a
description or an artifact equality does not strengthen that theorem's scope.
-/

namespace Mettapedia.GSLT.LanguageDef.PresentationEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization

/-- The kind of witness supplied, with no ordering between kinds. -/
inductive Kind where
  | authoredProbe
  | reportedModel
  | exactFragment
  | exactFragmentWithArtifact
  deriving DecidableEq, Repr

/-- Evidence attached to one presentation.  Descriptions remain reports;
operational claims require the corresponding `BagExact` witness. -/
inductive Evidence (language : LanguageDef) : Type 1
  | authoredProbe (notice : String)
  | reportedModel (Carrier : Type) (candidate : Carrier) (description : String)
  | exactFragment (scope : String)
      {Surface Machine Answer Observation : Type}
      (realization : BagExact Surface Machine Answer Observation)
      (samePresentation : realization.language = language)
  | exactFragmentWithArtifact (scope : String)
      {Surface Machine Answer Observation : Type}
      (realization : BagExact Surface Machine Answer Observation)
      (samePresentation : realization.language = language)
      (exporter : LanguageDef → String) (artifact : String)
      (artifactIdentity : exporter language = artifact)

/-- A nominal discriminator for the supplied evidence, not a measure of
semantic authority, implementation correctness, or language quality. -/
def Evidence.kind {language : LanguageDef} : Evidence language → Kind
  | .authoredProbe _ => .authoredProbe
  | .reportedModel _ _ _ => .reportedModel
  | .exactFragment _ _ _ => .exactFragment
  | .exactFragmentWithArtifact _ _ _ _ _ _ => .exactFragmentWithArtifact

end Mettapedia.GSLT.LanguageDef.PresentationEvidence
