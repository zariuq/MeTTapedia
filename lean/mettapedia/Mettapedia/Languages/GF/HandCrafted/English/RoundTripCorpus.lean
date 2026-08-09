import Mettapedia.Languages.GF.HandCrafted.English.Examples

/-!
# English Linearization Roundtrip Corpus

Restricted roundtrip over the full proven English example corpus currently in
`English/Examples.lean` (18 theorem-backed linearizations).

This is intentionally corpus-restricted: parse succeeds exactly on the known
validated linearizations and is proved complete/sound for this corpus.
-/

namespace Mettapedia.Languages.GF.HandCrafted.English.RoundTripCorpus

open Mettapedia.Languages.GF.HandCrafted.English
open Nouns Verbs Adjectives Syntax Pronouns Relatives

inductive ExampleTree where
  | theCat
  | aDog
  | anApple
  | heWalks
  | theyWalk
  | catDoesntWalk
  | catWalked
  | catWillWalk
  | doesCatWalk
  | heAte
  | heHasEaten
  | heLovesHer
  | heLooksAtCat
  | catThatWalks
  | manSheLoves
  | telescopeNPAttachment
  | telescopeVPAttachment
  | annaNPAttachment
  | annaVPAttachment
  | heWalksWhenSheSleeps
  deriving DecidableEq, Repr

private def catNP := linDetCN theDefArt (linUseN cat_N)
private def catWalkVP := linPredVP catNP (predV walk_V)
private def heEatVP := linPredVP he_Pron (predV eat_V)

private def catThatWalksNP :=
  linDetCN theDefArt (relCN (linUseN cat_N)
    (useRCl .Pres .Simul .CPos (relVP idRP (predV walk_V))))

private def manSheLovesNP :=
  let slash := slashVP she_Pron (slashV2a love_V2)
  linDetCN theDefArt (relCN (linUseN man_N)
    (useRCl .Pres .Simul .CPos (relSlash idRP slash)))

private def heWalksWhenSheSleeps :=
  let sheSleeps := linUseCl .Pres .Simul .CPos (linPredVP she_Pron (predV sleep_V))
  let whenSheSleeps := linSubjS when_Subj sheSleeps
  linUseCl .Pres .Simul .CPos (linPredVP he_Pron (advVP (predV walk_V) whenSheSleeps))

/-- Grammar-level linearization for each validated corpus example. -/
def linearizeExample : ExampleTree → String
  | .theCat => catNP.s (.NCase .Nom)
  | .aDog => (linDetCN aIndefArt (linUseN dog_N)).s (.NCase .Nom)
  | .anApple => (linDetCN aIndefArt (linUseN (regN "apple"))).s (.NCase .Nom)
  | .heWalks => linUseCl .Pres .Simul .CPos (linPredVP he_Pron (predV walk_V))
  | .theyWalk => linUseCl .Pres .Simul .CPos (linPredVP they_Pron (predV walk_V))
  | .catDoesntWalk => linUseCl .Pres .Simul (.CNeg true) catWalkVP
  | .catWalked => linUseCl .Past .Simul .CPos catWalkVP
  | .catWillWalk => linUseCl .Fut .Simul .CPos catWalkVP
  | .doesCatWalk => linQuestCl .Pres .Simul .CPos catWalkVP
  | .heAte => linUseCl .Past .Simul .CPos heEatVP
  | .heHasEaten => linUseCl .Pres .Anter .CPos heEatVP
  | .heLovesHer => linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 love_V2 she_Pron))
  | .heLooksAtCat => linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 lookAt_V2 catNP))
  | .catThatWalks => catThatWalksNP.s (.NCase .Nom)
  | .manSheLoves => manSheLovesNP.s (.NCase .Nom)
  | .telescopeNPAttachment => Examples.telescopeNPAttachmentText
  | .telescopeVPAttachment => Examples.telescopeVPAttachmentText
  | .annaNPAttachment => Examples.annaNPAttachmentText
  | .annaVPAttachment => Examples.annaVPAttachmentText
  | .heWalksWhenSheSleeps => heWalksWhenSheSleeps

/-- Full curated English corpus used by the roundtrip parser. -/
def allExamples : List ExampleTree :=
  [ .theCat
  , .aDog
  , .anApple
  , .heWalks
  , .theyWalk
  , .catDoesntWalk
  , .catWalked
  , .catWillWalk
  , .doesCatWalk
  , .heAte
  , .heHasEaten
  , .heLovesHer
  , .heLooksAtCat
  , .catThatWalks
  , .manSheLoves
  , .telescopeNPAttachment
  , .telescopeVPAttachment
  , .annaNPAttachment
  , .annaVPAttachment
  , .heWalksWhenSheSleeps
  ]

/-- Every example constructor appears in the curated corpus list. -/
theorem mem_allExamples (e : ExampleTree) : e ∈ allExamples := by
  cases e <;> simp [allExamples]

/-- Canonical parser for the validated corpus (returns all matching analyses). -/
def parseLinearization : String → List ExampleTree
  | s => allExamples.filter (fun e => linearizeExample e = s)

/-- Corpus completeness: parsing linearization recovers the source analysis. -/
theorem parse_linearize_complete (e : ExampleTree) :
    e ∈ parseLinearization (linearizeExample e) := by
  refine List.mem_filter.mpr ?_
  exact ⟨mem_allExamples e, by simp⟩

/-- Corpus soundness: any parsed analysis linearizes back to the input text. -/
theorem parse_sound (s : String) (e : ExampleTree) :
    e ∈ parseLinearization s → linearizeExample e = s := by
  intro h
  simpa using (List.mem_filter.mp h).2

/-- Negative example: unknown text has no analysis in this corpus parser. -/
theorem parse_unknown_empty : parseLinearization "nonsense input" = [] := by
  decide

/-- Selected parse cardinalities in the curated corpus parser. -/
theorem selected_linearization_cardinalities :
    (parseLinearization "he walks").length = 1 ∧
    (parseLinearization "John sees the man with the telescope").length = 2 ∧
    (parseLinearization "Anna dresses the baby in the crib").length = 2 := by
  decide

/-- The curated corpus parser recovers both telescope-attachment analyses. -/
theorem telescope_text_ambiguous_in_corpus :
    parseLinearization "John sees the man with the telescope" =
      [.telescopeNPAttachment, .telescopeVPAttachment] := by
  decide

/-- The curated corpus parser recovers both Anna attachment analyses. -/
theorem anna_text_ambiguous_in_corpus :
    parseLinearization "Anna dresses the baby in the crib" =
      [.annaNPAttachment, .annaVPAttachment] := by
  decide

end Mettapedia.Languages.GF.HandCrafted.English.RoundTripCorpus
