abstract PaperAmbiguity = Grammar [
  S, Cl, NP, VP, CN, Det, N, V2, Adv, Prep, PN, Temp, Tense, Ant, Pol, VPSlash,
  UseCl, PredVP, DetCN, UsePN, UseN, PrepNP, AdvCN, AdvVP, SlashV2a, ComplSlash,
  TTAnt, PPos, TPres, TPast, ASimul,
  with_Prep, in_Prep
] ** {
  flags startcat = S ;

  fun
    the_Det : Det ;

    john_PN : PN ;
    anna_PN : PN ;

    man_N : N ;
    baby_N : N ;
    telescope_N : N ;
    crib_N : N ;

    see_V2 : V2 ;
    dress_V2 : V2 ;
}
