import Mettapedia.Languages.GF.English.Relatives
import Mettapedia.Languages.GF.English.Linearization

namespace Mettapedia.Demos.GF.English.Examples

open Mettapedia.Languages.GF.English
open Nouns Verbs Adjectives Syntax Pronouns Relatives

private def theCat := linDetCN theDefArt (linUseN cat_N)
private def aDog := linDetCN aIndefArt (linUseN dog_N)
private def theBigHouse := linDetCN theDefArt (linAdjCN (linPositA big_A) (linUseN house_N))
private def theOldMan := linDetCN theDefArt (linAdjCN (linPositA old_A) (linUseN man_N))
private def anApple := linDetCN aIndefArt (linUseN (regN "apple"))
private def catWalk := linPredVP theCat (predV walk_V)
private def heEat := linPredVP he_Pron (predV eat_V)
private def theySwim := linPredVP they_Pron (predV swim_V)

private def catThatWalks :=
  linDetCN theDefArt (relCN (linUseN cat_N)
    (useRCl .Pres .Simul .CPos (relVP idRP (predV walk_V))))

private def manSheLoves :=
  let slash := slashVP she_Pron (slashV2a love_V2)
  linDetCN theDefArt (relCN (linUseN man_N)
    (useRCl .Pres .Simul .CPos (relSlash idRP slash)))

private def old_N : EnglishNoun := mk2N "old" "old"
private def boat_N : EnglishNoun := regN "boat"

private def parse1_theOldManWalks :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArt (linAdjCN (linPositA old_A) (linUseN man_N)))
      (predV walk_V))

private def parse2_theOldManTheBoats :=
  linUseCl .Pres .Simul .CPos
    (linPredVP
      (linDetCN theDefArtPl (linUseN old_N))
      (complV2 man_V2 (linDetCN theDefArtPl (linUseN boat_N))))

#eval! theCat.s (.NCase .Nom)
#eval! aDog.s (.NCase .Nom)
#eval! theBigHouse.s (.NCase .Nom)
#eval! theOldMan.s (.NCase .Nom)
#eval! anApple.s (.NCase .Nom)
#eval! linUseCl .Pres .Simul .CPos catWalk
#eval! linUseCl .Past .Simul .CPos catWalk
#eval! linUseCl .Fut .Simul .CPos catWalk
#eval! linUseCl .Pres .Simul (.CNeg true) catWalk
#eval! linQuestCl .Pres .Simul .CPos catWalk
#eval! linUseCl .Pres .Anter .CPos heEat
#eval! linUseCl .Past .Simul .CPos theySwim
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (complV2 love_V2 she_Pron))
#eval! catThatWalks.s (.NCase .Nom)
#eval! manSheLoves.s (.NCase .Nom)
#eval! linUseCl .Pres .Simul .CPos (linPredVP catThatWalks (predV sleep_V))
#eval! parse1_theOldManWalks
#eval! parse2_theOldManTheBoats

end Mettapedia.Demos.GF.English.Examples
