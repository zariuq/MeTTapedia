import Mettapedia.Languages.GF.English.Syntax
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.Languages.GF.English.Relatives
import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF.English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives
open Mettapedia.Languages.GF.English.Linearization

#eval! cat_N.s .Pl .Nom
#eval! go_V.s .VPast
#eval! good_A.s (.AAdj .Comp .Nom)
#eval! i_Pron.s (.NCase .Nom)
#eval! linUseCl .Pres .Simul .CPos (linPredVP (linDetCN theDefArt (linUseN cat_N)) (predV walk_V))
#eval! linUseCl .Past .Simul .CPos (linPredVP (linDetCN theDefArt (linUseN man_N)) (predV eat_V))
#eval! linQuestCl .Pres .Simul .CPos (linPredVP (linDetCN theDefArt (linUseN cat_N)) (predV walk_V))
#eval! linPrepNP in_Prep (linDetCN theDefArt (linUseN house_N))
#eval! idRP.s (.RPrep .Masc)
#eval! linearizeTree {} (.apply { name := "PredVP", type := .arrow (.base "NP") (.arrow (.base "VP") (.base "Cl")) }
  [ .apply { name := "DetCN", type := .arrow (.base "Det") (.arrow (.base "CN") (.base "NP")) }
      [ .leaf "the_Det" (.base "Det"), .apply { name := "UseN", type := .arrow (.base "N") (.base "CN") } [ .leaf "cat_N" (.base "N") ] ],
    .apply { name := "UseV", type := .arrow (.base "V") (.base "VP") } [ .leaf "walk_V" (.base "V") ] ]) .Nom .Sg
