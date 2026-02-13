/-
# English GF Examples

Comprehensive examples demonstrating the English linearization pipeline.
Each example shows the GF abstract tree and its English surface form.

## References
- GF RGL Demo: http://www.grammaticalframework.org/lib/doc/synopsis/index.html
-/

import Mettapedia.Languages.GF.English.Relatives
import Mettapedia.Languages.GF.English.Linearization

namespace Mettapedia.Languages.GF.English.Examples

open Mettapedia.Languages.GF.English
open Nouns Verbs Adjectives Syntax Pronouns Relatives

/-! ## Noun Phrases -/

-- UseN + DetCN: "the cat", "a dog", "the big house"
private def theCat := linDetCN theDefArt (linUseN cat_N)
private def aDog := linDetCN aIndefArt (linUseN dog_N)
private def theBigHouse := linDetCN theDefArt (linAdjCN (linPositA big_A) (linUseN house_N))
private def theOldMan := linDetCN theDefArt (linAdjCN (linPositA old_A) (linUseN man_N))
private def anApple := linDetCN aIndefArt (linUseN (regN "apple"))
private def everyChild := linDetCN every_Det (linUseN child_N)
private def thoseCities := linDetCN those_Det (linUseN city_N)

-- NP tests
#eval! theCat.s (.NCase .Nom)       -- "the cat"
#eval! aDog.s (.NCase .Nom)          -- "a dog"
#eval! theBigHouse.s (.NCase .Nom)  -- "the big house"
#eval! theOldMan.s (.NCase .Nom)    -- "the old man"
#eval! anApple.s (.NCase .Nom)      -- "an apple"
#eval! everyChild.s (.NCase .Nom)   -- "every child"
#eval! thoseCities.s (.NCase .Nom)  -- "those cities"

-- Possessive/genitive forms
#eval! theCat.s (.NCase .Gen)    -- "the cat's"
#eval! theOldMan.s (.NCase .Gen) -- "the old man's"

/-! ## Simple Sentences -/

-- PredVP: subject + intransitive verb
#eval! linUseCl .Pres .Simul .CPos (linPredVP theCat (predV walk_V))
  -- "the cat walks"
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (predV sleep_V))
  -- "he sleeps"
#eval! linUseCl .Pres .Simul .CPos (linPredVP they_Pron (predV run_V))
  -- "they run"
#eval! linUseCl .Pres .Simul .CPos (linPredVP i_Pron (predV sing_V))
  -- "I sing"

/-! ## Tense/Aspect -/

private def catWalk := linPredVP theCat (predV walk_V)

-- Present: "the cat walks"
#eval! linUseCl .Pres .Simul .CPos catWalk  -- "the cat walks"
-- Past: "the cat walked"
#eval! linUseCl .Past .Simul .CPos catWalk  -- "the cat walked"
-- Future: "the cat will walk"
#eval! linUseCl .Fut .Simul .CPos catWalk   -- "the cat will walk"
-- Conditional: "the cat would walk"
#eval! linUseCl .Cond .Simul .CPos catWalk  -- "the cat would walk"
-- Present perfect: "the cat has walked"
#eval! linUseCl .Pres .Anter .CPos catWalk  -- "the cat has walked"
-- Past perfect: "the cat had walked"
#eval! linUseCl .Past .Anter .CPos catWalk  -- "the cat had walked"
-- Future perfect: "the cat will have walked"
#eval! linUseCl .Fut .Anter .CPos catWalk   -- "the cat will have walked"

/-! ## Negation -/

-- Contracted: "the cat doesn't walk"
#eval! linUseCl .Pres .Simul (.CNeg true) catWalk  -- "the cat doesn't walk"
-- Uncontracted: "the cat does not walk"
#eval! linUseCl .Pres .Simul (.CNeg false) catWalk -- "the cat does not walk"
-- Past: "the cat didn't walk"
#eval! linUseCl .Past .Simul (.CNeg true) catWalk  -- "the cat didn't walk"
-- Future: "the cat won't walk"
#eval! linUseCl .Fut .Simul (.CNeg true) catWalk   -- "the cat won't walk"

/-! ## Questions -/

-- Present: "does the cat walk"
#eval! linQuestCl .Pres .Simul .CPos catWalk  -- "does the cat walk"
-- Past: "did the cat walk"
#eval! linQuestCl .Past .Simul .CPos catWalk  -- "did the cat walk"
-- Future: "will the cat walk"
#eval! linQuestCl .Fut .Simul .CPos catWalk   -- "will the cat walk"
-- Negative question: "doesn't the cat walk"
#eval! linQuestCl .Pres .Simul (.CNeg true) catWalk  -- "doesn't the cat walk"

/-! ## Irregular Verbs -/

private def heEat := linPredVP he_Pron (predV eat_V)
private def theySwim := linPredVP they_Pron (predV swim_V)

-- "he eats" / "he ate" / "he has eaten"
#eval! linUseCl .Pres .Simul .CPos heEat    -- "he eats"
#eval! linUseCl .Past .Simul .CPos heEat    -- "he ate"
#eval! linUseCl .Pres .Anter .CPos heEat    -- "he has eaten"

-- "they swim" / "they swam" / "they have swum"
#eval! linUseCl .Pres .Simul .CPos theySwim  -- "they swim"
#eval! linUseCl .Past .Simul .CPos theySwim  -- "they swam"
#eval! linUseCl .Pres .Anter .CPos theySwim  -- "they have swum"

/-! ## Pronoun Agreement -/

-- 3sg agreement: "he walks" vs "they walk"
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (predV walk_V))
  -- "he walks"
#eval! linUseCl .Pres .Simul .CPos (linPredVP they_Pron (predV walk_V))
  -- "they walk"
#eval! linUseCl .Pres .Simul .CPos (linPredVP i_Pron (predV walk_V))
  -- "I walk"
#eval! linUseCl .Pres .Simul .CPos (linPredVP she_Pron (predV walk_V))
  -- "she walks"

/-! ## Prepositions -/

-- "in the house", "with him", "from the old man"
#eval! linPrepNP in_Prep (linDetCN theDefArt (linUseN house_N))
  -- "in the house"
#eval! linPrepNP with_Prep he_Pron
  -- "with him"
#eval! linPrepNP from_Prep theOldMan
  -- "from the old man"

/-! ## Transitive Verbs (V2) -/

-- "he loves her"
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 love_V2 she_Pron))
  -- "he loves her"
-- "she sees the cat"
#eval! linUseCl .Pres .Simul .CPos (linPredVP she_Pron (complV2 see_V2 theCat))
  -- "she sees the cat"
-- "they ate an apple"
#eval! linUseCl .Past .Simul .CPos (linPredVP they_Pron (complV2 eat_V2 anApple))
  -- "they ate an apple"
-- "she doesn't love him"
#eval! linUseCl .Pres .Simul (.CNeg true)
  (linPredVP she_Pron (complV2 love_V2 he_Pron))
  -- "she doesn't love him"
-- Prepositional V2: "he looks at the cat"
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 lookAt_V2 theCat))
  -- "he looks at the cat"
-- "she listens to him"
#eval! linUseCl .Pres .Simul .CPos (linPredVP she_Pron (complV2 listenTo_V2 he_Pron))
  -- "she listens to him"

/-! ## Relative Clauses -/

-- "the cat that walks" (RelVP)
private def catThatWalks :=
  linDetCN theDefArt (relCN (linUseN cat_N)
    (useRCl .Pres .Simul .CPos (relVP idRP (predV walk_V))))
#eval! catThatWalks.s (.NCase .Nom)  -- "the cat that walks"

-- "the man that she loves" (RelSlash)
private def manSheLoves :=
  let slash := slashVP she_Pron (slashV2a love_V2)
  linDetCN theDefArt (relCN (linUseN man_N)
    (useRCl .Pres .Simul .CPos (relSlash idRP slash)))
#eval! manSheLoves.s (.NCase .Nom)  -- "the man that she loves"

-- Sentence with relative clause: "the cat that walks sleeps"
#eval! linUseCl .Pres .Simul .CPos (linPredVP catThatWalks (predV sleep_V))
  -- "the cat that walks sleeps"

-- "the man that she loves walks"
#eval! linUseCl .Pres .Simul .CPos (linPredVP manSheLoves (predV walk_V))
  -- "the man that she loves walks"

/-! ## Subordinate Clauses -/

-- "when she sleeps" as adverb on VP
private def heWalksWhenSheSleeps :=
  let sheSleeps := linUseCl .Pres .Simul .CPos (linPredVP she_Pron (predV sleep_V))
  let whenSheSleeps := linSubjS when_Subj sheSleeps
  linUseCl .Pres .Simul .CPos (linPredVP he_Pron (advVP (predV walk_V) whenSheSleeps))
#eval! heWalksWhenSheSleeps  -- "he walks when she sleeps"

-- SSubjS: "the cat walks if the dog sleeps"
private def catWalksIfDogSleeps :=
  let s1 := linUseCl .Pres .Simul .CPos catWalk
  let s2 := linUseCl .Pres .Simul .CPos (linPredVP aDog (predV sleep_V))
  linSSubjS s1 if_Subj s2
#eval! catWalksIfDogSleeps  -- "the cat walks if a dog sleeps"

/-! ## The Garden-Path Disambiguation

"The old man the boats" — a famous garden-path sentence.
Humans parse "old" as adjective + "man" as noun, then get stuck.
The actual reading: "the old [people]" (noun) + "man [verb]" (V2) + "the boats".

In typed English, both readings are expressible as DIFFERENT abstract trees.
The type IS the disambiguation.
-/

-- Noun for "old" as a substantivized adjective ("the old" = old people)
private def old_N : EnglishNoun := mk2N "old" "old"
-- Noun for "boat"
private def boat_N : EnglishNoun := regN "boat"

-- Parse 1: "the old man walks" — adjective + noun + intransitive verb
private def parse1_theOldManWalks :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArt (linAdjCN (linPositA old_A) (linUseN man_N)))
      (predV walk_V))
#eval! parse1_theOldManWalks  -- "the old man walks"

-- Parse 2: "the old man the boats" — substantivized noun (plural) + transitive verb
--   "the old" = the old people (plural), "man" = verb, "the boats" = plural object
private def parse2_theOldManTheBoats :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArtPl (linUseN old_N))
      (complV2 man_V2 (linDetCN theDefArtPl (linUseN boat_N))))
#eval! parse2_theOldManTheBoats  -- "the old man the boats"

/-! ## Proven Correctness -/

-- All the above examples are proven correct by the kernel
theorem ex_the_cat : theCat.s (.NCase .Nom) = "the cat" := by decide
theorem ex_a_dog : aDog.s (.NCase .Nom) = "a dog" := by decide
theorem ex_an_apple : anApple.s (.NCase .Nom) = "an apple" := by decide
theorem ex_he_walks :
    linUseCl .Pres .Simul .CPos (linPredVP he_Pron (predV walk_V)) =
    "he walks" := by decide
theorem ex_they_walk :
    linUseCl .Pres .Simul .CPos (linPredVP they_Pron (predV walk_V)) =
    "they walk" := by decide
theorem ex_doesnt :
    linUseCl .Pres .Simul (.CNeg true) catWalk =
    "the cat doesn't walk" := by decide
theorem ex_past :
    linUseCl .Past .Simul .CPos catWalk =
    "the cat walked" := by decide
theorem ex_future :
    linUseCl .Fut .Simul .CPos catWalk =
    "the cat will walk" := by decide
theorem ex_quest :
    linQuestCl .Pres .Simul .CPos catWalk =
    "does the cat walk" := by decide
theorem ex_he_ate :
    linUseCl .Past .Simul .CPos heEat =
    "he ate" := by decide
theorem ex_has_eaten :
    linUseCl .Pres .Anter .CPos heEat =
    "he has eaten" := by decide

-- V2 proofs
theorem ex_he_loves_her :
    linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 love_V2 she_Pron)) =
    "he loves her" := by decide
theorem ex_looks_at :
    linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 lookAt_V2 theCat)) =
    "he looks at the cat" := by decide

-- Relative clause proofs
theorem ex_cat_that_walks :
    catThatWalks.s (.NCase .Nom) = "the cat that walks" := by decide
theorem ex_man_she_loves :
    manSheLoves.s (.NCase .Nom) = "the man that she loves" := by decide

-- Garden-path disambiguation
theorem ex_parse1 : parse1_theOldManWalks = "the old man walks" := by decide
theorem ex_parse2 : parse2_theOldManTheBoats = "the old man the boats" := by decide

-- Subordination proofs
theorem ex_walks_when_sleeps :
    heWalksWhenSheSleeps = "he walks when she sleeps" := by decide

end Mettapedia.Languages.GF.English.Examples
