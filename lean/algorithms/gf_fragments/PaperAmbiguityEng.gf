concrete PaperAmbiguityEng of PaperAmbiguity =
  GrammarEng [
    S, Cl, NP, VP, CN, Det, N, V2, Adv, Prep, PN, Temp, Tense, Ant, Pol, VPSlash,
    UseCl, PredVP, DetCN, UsePN, UseN, PrepNP, AdvCN, AdvVP, SlashV2a, ComplSlash,
    TTAnt, PPos, TPres, TPast, ASimul,
    with_Prep, in_Prep
  ]
  **
  open SyntaxEng, ParadigmsEng, DictEng in {

  flags startcat = S ;

  lin
    the_Det = mkDet the_Quant ;

    john_PN = DictEng.john_PN ;
    anna_PN = mkPN "Anna" ;

    man_N = DictEng.man_N ;
    baby_N = DictEng.baby_N ;
    telescope_N = DictEng.telescope_N ;
    crib_N = DictEng.crib_N ;

    see_V2 = DictEng.see_V2 ;
    dress_V2 = DictEng.dress_V2 ;
}
