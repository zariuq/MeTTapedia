concrete PaperAmbiguityCze of PaperAmbiguity =
  GrammarCze [
    S, Cl, NP, VP, CN, Det, N, V2, Adv, Prep, PN, Temp, Tense, Ant, Pol, VPSlash,
    UseCl, PredVP, DetCN, UsePN, UseN, PrepNP, AdvCN, AdvVP, SlashV2a, ComplSlash,
    TTAnt, PPos, TPres, TPast, ASimul,
    with_Prep, in_Prep
  ]
  **
  open Prelude, ResCze, ParadigmsCze in {

  flags startcat = S ;

  oper
    mkSimplePN : Str -> Gender -> PN = \name,g -> lin PN {
      s = table {
        Nom => name ;
        Gen => name ;
        Dat => name ;
        Acc => name ;
        Voc => name ;
        Loc => name ;
        Ins => name
      } ;
      g = g
    } ;

    seeVerbForms : VerbForms = {
      inf = "vidět" ;
      pressg1 = "vidím" ;
      pressg2 = "vidíš" ;
      pressg3 = "vidí" ;
      prespl1 = "vidíme" ;
      prespl2 = "vidíte" ;
      prespl3 = "vidí" ;
      pastpartsg = "viděl" ;
      pastpartpl = "viděli" ;
      negpressg3 = "vidí"
    } ;

    dressVerbForms : VerbForms = {
      inf = "oblékat" ;
      pressg1 = "oblékám" ;
      pressg2 = "oblékáš" ;
      pressg3 = "obléká" ;
      prespl1 = "oblékáme" ;
      prespl2 = "oblékáte" ;
      prespl3 = "oblékají" ;
      pastpartsg = "oblékal" ;
      pastpartpl = "oblékali" ;
      negpressg3 = "obléká"
    } ;

  lin
    the_Det = {s = \\_,_ => [] ; size = Num1} ;

    john_PN = mkSimplePN "Jan" mascAnimate ;
    anna_PN = mkSimplePN "Anna" feminine ;

    man_N = mkN "muž" "muže" mascAnimate ;
    baby_N = mkN "dítě" "dítěte" neuter ;
    telescope_N = mkN "teleskop" "teleskopu" mascInanimate ;
    crib_N = mkN "kolébka" "kolébky" feminine ;

    see_V2 = mkV2 seeVerbForms ;
    dress_V2 = mkV2 dressVerbForms ;
}
