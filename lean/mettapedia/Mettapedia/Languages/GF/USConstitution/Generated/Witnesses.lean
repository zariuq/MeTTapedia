-- AUTO-GENERATED from ParseEng PGF witnesses. Do not edit.

import Mettapedia.Languages.GF.PGFWitnessIR

namespace Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

open Mettapedia.Languages.GF.PGFWitnessIR

inductive ClauseId where
  | preambleEstablishJustice
  | articleISection1Vesting
  | articleISection2HouseComposition
  | articleISection2RepresentativeAge
  | articleISection3SenateImpeachments
  | articleISection5Rules
  | articleISection7EveryBillPresented
  | articleISection7PresidentSigns
  | articleISection7BecomesLaw
  | articleISection8DeclareWar
  | articleISection9Habeas
  | articleISection9NoTitleOfNobility
  | articleIISection1ExecutiveVesting
  | articleIISection1PresidentAge
  | articleIISection2CommanderInChief
  | articleIIISection3Treason
  | articleIVSection1FullFaithCredit
  | articleVProposeAmendments
  | articleVISupremacy
  | articleVINoReligiousTest
  | articleVIIRatification
  deriving Repr, DecidableEq

def sourceHash : String := "11d54d0644a29fc587e839c6710ddd362cd2c0ad45f693487d0ce1840bed4d34"
def grammarName : String := "Parse"
def archivesSourceUrl : String := "https://www.archives.gov/founding-docs/constitution-transcript"
def congressSourceUrl : String := "https://constitution.congress.gov/constitution/"

def allClauseIds : List ClauseId := [.preambleEstablishJustice, .articleISection1Vesting, .articleISection2HouseComposition, .articleISection2RepresentativeAge, .articleISection3SenateImpeachments, .articleISection5Rules, .articleISection7EveryBillPresented, .articleISection7PresidentSigns, .articleISection7BecomesLaw, .articleISection8DeclareWar, .articleISection9Habeas, .articleISection9NoTitleOfNobility, .articleIISection1ExecutiveVesting, .articleIISection1PresidentAge, .articleIISection2CommanderInChief, .articleIIISection3Treason, .articleIVSection1FullFaithCredit, .articleVProposeAmendments, .articleVISupremacy, .articleVINoReligiousTest, .articleVIIRatification]

def clauseText : ClauseId → String
  | .preambleEstablishJustice => "establish Justice"
  | .articleISection1Vesting => "All legislative Powers herein granted shall be vested in a Congress of the United States"
  | .articleISection2HouseComposition => "The House of Representatives shall be composed of Members chosen every second Year by the People of the several States"
  | .articleISection2RepresentativeAge => "No Person shall be a Representative who shall not have attained to the Age of twenty five Years"
  | .articleISection3SenateImpeachments => "The Senate shall have the sole Power to try all Impeachments"
  | .articleISection5Rules => "Each House may determine the Rules of its Proceedings"
  | .articleISection7EveryBillPresented => "Every Bill shall be presented to the President of the United States"
  | .articleISection7PresidentSigns => "he shall sign it"
  | .articleISection7BecomesLaw => "it shall be a Law"
  | .articleISection8DeclareWar => "To declare War"
  | .articleISection9Habeas => "The Privilege of the Writ of Habeas Corpus shall not be suspended"
  | .articleISection9NoTitleOfNobility => "No Title of Nobility shall be granted by the United States"
  | .articleIISection1ExecutiveVesting => "The executive Power shall be vested in a President of the United States of America"
  | .articleIISection1PresidentAge => "the Age of thirty five Years"
  | .articleIISection2CommanderInChief => "The President shall be Commander in Chief of the Army and Navy of the United States"
  | .articleIIISection3Treason => "Treason against the United States shall consist only in levying War against them"
  | .articleIVSection1FullFaithCredit => "Full Faith and Credit shall be given in each State to the public Acts Records and judicial Proceedings of every other State"
  | .articleVProposeAmendments => "shall propose Amendments to this Constitution"
  | .articleVISupremacy => "This Constitution shall be the supreme Law of the Land"
  | .articleVINoReligiousTest => "no religious Test shall ever be required as a Qualification to any Office or public Trust under the United States"
  | .articleVIIRatification => "The Ratification of the Conventions of nine States shall be sufficient for the Establishment of this Constitution"

def parserInput : ClauseId → String
  | .preambleEstablishJustice => "establish Justice"
  | .articleISection1Vesting => "All legislative Powers herein granted shall be vested in a Congress of the United States"
  | .articleISection2HouseComposition => "The House of Representatives shall be composed of Members chosen every second Year by the People of the several States"
  | .articleISection2RepresentativeAge => "No Person shall be a Representative who shall not have attained to the Age of twenty five Years"
  | .articleISection3SenateImpeachments => "The Senate shall have the sole Power to try all Impeachments"
  | .articleISection5Rules => "Each House may determine the Rules of its Proceedings"
  | .articleISection7EveryBillPresented => "Every Bill shall be presented to the President of the United States"
  | .articleISection7PresidentSigns => "he shall sign it"
  | .articleISection7BecomesLaw => "it shall be a Law"
  | .articleISection8DeclareWar => "To declare War"
  | .articleISection9Habeas => "The Privilege of the Writ of Habeas Corpus shall not be suspended"
  | .articleISection9NoTitleOfNobility => "No Title of Nobility shall be granted by the United States"
  | .articleIISection1ExecutiveVesting => "The executive Power shall be vested in a President of the United States of America"
  | .articleIISection1PresidentAge => "the Age of thirty five Years"
  | .articleIISection2CommanderInChief => "The President shall be Commander in Chief of the Army and Navy of the United States"
  | .articleIIISection3Treason => "Treason against the United States shall consist only in levying War against them"
  | .articleIVSection1FullFaithCredit => "Full Faith and Credit shall be given in each State to the public Acts Records and judicial Proceedings of every other State"
  | .articleVProposeAmendments => "shall propose Amendments to this Constitution"
  | .articleVISupremacy => "This Constitution shall be the supreme Law of the Land"
  | .articleVINoReligiousTest => "no religious Test shall ever be required as a Qualification to any Office or public Trust under the United States"
  | .articleVIIRatification => "The Ratification of the Conventions of nine States shall be sufficient for the Establishment of this Constitution"

def clauseAnchor : ClauseId → String
  | .preambleEstablishJustice => "Preamble"
  | .articleISection1Vesting => "Article I, Section 1"
  | .articleISection2HouseComposition => "Article I, Section 2"
  | .articleISection2RepresentativeAge => "Article I, Section 2"
  | .articleISection3SenateImpeachments => "Article I, Section 3"
  | .articleISection5Rules => "Article I, Section 5"
  | .articleISection7EveryBillPresented => "Article I, Section 7"
  | .articleISection7PresidentSigns => "Article I, Section 7"
  | .articleISection7BecomesLaw => "Article I, Section 7"
  | .articleISection8DeclareWar => "Article I, Section 8"
  | .articleISection9Habeas => "Article I, Section 9"
  | .articleISection9NoTitleOfNobility => "Article I, Section 9"
  | .articleIISection1ExecutiveVesting => "Article II, Section 1"
  | .articleIISection1PresidentAge => "Article II, Section 1"
  | .articleIISection2CommanderInChief => "Article II, Section 2"
  | .articleIIISection3Treason => "Article III, Section 3"
  | .articleIVSection1FullFaithCredit => "Article IV, Section 1"
  | .articleVProposeAmendments => "Article V"
  | .articleVISupremacy => "Article VI"
  | .articleVINoReligiousTest => "Article VI"
  | .articleVIIRatification => "Article VII"

def clauseNote : ClauseId → String
  | .preambleEstablishJustice => "Preamble purpose fragment."
  | .articleISection1Vesting => "Legislative vesting fragment."
  | .articleISection2HouseComposition => "House composition and election fragment."
  | .articleISection2RepresentativeAge => "Representative age qualification fragment."
  | .articleISection3SenateImpeachments => "Senate impeachment-trial power fragment."
  | .articleISection5Rules => "Internal chamber rules fragment."
  | .articleISection7EveryBillPresented => "Presentment fragment."
  | .articleISection7PresidentSigns => "Presidential signature fragment."
  | .articleISection7BecomesLaw => "Bill-becomes-law fragment."
  | .articleISection8DeclareWar => "Enumerated war power fragment."
  | .articleISection9Habeas => "Habeas suspension fragment."
  | .articleISection9NoTitleOfNobility => "Federal title-of-nobility prohibition fragment."
  | .articleIISection1ExecutiveVesting => "Executive vesting fragment."
  | .articleIISection1PresidentAge => "Presidential age-qualification fragment."
  | .articleIISection2CommanderInChief => "Commander-in-chief fragment."
  | .articleIIISection3Treason => "Treason definition fragment."
  | .articleIVSection1FullFaithCredit => "Full faith and credit fragment."
  | .articleVProposeAmendments => "Article V proposal fragment."
  | .articleVISupremacy => "Supremacy clause fragment."
  | .articleVINoReligiousTest => "No religious test fragment."
  | .articleVIIRatification => "Ratification threshold fragment."

def preambleEstablishJusticeParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttVPShort" [
      .node "ComplSlashPartLast" [
        .node "SlashV2a" [
          .node "establish_4_V2" []
        ],
        .node "MassNP" [
          .node "UseN" [
            .node "justiceFem_3_N" []
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection1VestingParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "PredetNP" [
          .node "all_1_Predet" [],
          .node "GenModNP" [
            .node "NumPl" [],
            .node "AdjAsNP" [
              .node "PositA" [
                .node "legislative_1_A" []
              ]
            ],
            .node "ApposCN" [
              .node "AdvCN" [
                .node "UseN" [
                  .node "power_10_N" []
                ],
                .node "herein_Adv" []
              ],
              .node "AdjAsNP" [
                .node "PastPartAP" [
                  .node "SlashV2a" [
                    .node "grant_1_V2" []
                  ]
                ]
              ]
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "PassVPSlash" [
                  .node "SlashV2a" [
                    .node "vest_4_V2" []
                  ]
                ],
                .node "in_5_Prep" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "IndefArt" [],
              .node "NumSg" []
            ],
            .node "PossNP" [
              .node "UseN" [
                .node "congress_2_N" []
              ],
              .node "UseLN" [
                .node "united_states_LN" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection2HouseCompositionParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "DefArt" [],
            .node "NumSg" []
          ],
          .node "PossNP" [
            .node "UseN" [
              .node "house_4_N" []
            ],
            .node "DetCN" [
              .node "DetQuant" [
                .node "IndefArt" [],
                .node "NumPl" []
              ],
              .node "UseN" [
                .node "representativeMasc_2_N" []
              ]
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "PassVPSlash" [
                  .node "SlashV2a" [
                    .node "compose_4_V2" []
                  ]
                ],
                .node "of_2_Prep" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "gen_Quant" [],
              .node "NumPl" []
            ],
            .node "AdjCN" [
              .node "PastPartAgentAP" [
                .node "AdvVPSlash" [
                  .node "SlashV2a" [
                    .node "choose_2_V2" []
                  ],
                  .node "TimeNP" [
                    .node "DetCN" [
                      .node "every_Det" [],
                      .node "ApposCN" [
                        .node "UseN" [
                          .node "second_10_N" []
                        ],
                        .node "MassNP" [
                          .node "UseN" [
                            .node "year_1_N" []
                          ]
                        ]
                      ]
                    ]
                  ]
                ],
                .node "DetCN" [
                  .node "DetQuant" [
                    .node "DefArt" [],
                    .node "NumPl" []
                  ],
                  .node "PossNP" [
                    .node "UseN" [
                      .node "people_4_N" []
                    ],
                    .node "DetCN" [
                      .node "DetQuant" [
                        .node "DefArt" [],
                        .node "NumCard" [
                          .node "several_Card" []
                        ]
                      ],
                      .node "UseN" [
                        .node "state_8_N" []
                      ]
                    ]
                  ]
                ]
              ],
              .node "UseN" [
                .node "memberMasc_1_N" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection2RepresentativeAgeParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "no_Quant" [],
            .node "NumSg" []
          ],
          .node "UseN" [
            .node "person_2_N" []
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "UseComp_ser" [
                  .node "CompCN" [
                    .node "RelCN" [
                      .node "UseN" [
                        .node "representativeFem_1_N" []
                      ],
                      .node "RelVPS" [
                        .node "IdRP" [],
                        .node "ComplVPS2" [
                          .node "MkVPS2" [
                            .node "TTAnt" [
                              .node "TPres" [],
                              .node "ASimul" []
                            ],
                            .node "PNeg" [],
                            .node "SlashVV" [
                              .node "shall_VV" [],
                              .node "ASimul" [],
                              .node "PPos" [],
                              .node "SlashV2a" [
                                .node "have_8_V2" []
                              ]
                            ]
                          ],
                          .node "AdjAsNP" [
                            .node "PastPartAP" [
                              .node "SlashV2a" [
                                .node "attain_3_V2" []
                              ]
                            ]
                          ]
                        ]
                      ]
                    ]
                  ]
                ],
                .node "to_4_Prep" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "DefArt" [],
              .node "NumSg" []
            ],
            .node "AdvCN" [
              .node "PossNP" [
                .node "UseN" [
                  .node "age_2_N" []
                ],
                .node "UseDAPMasc" [
                  .node "DetDAP" [
                    .node "DetQuant" [
                      .node "gen_Quant" [],
                      .node "NumCard" [
                        .node "NumNumeral" [
                          .node "num" [
                            .node "pot4as5" [
                              .node "pot3as4" [
                                .node "pot2as3" [
                                  .node "pot1as2" [
                                    .node "pot1" [
                                      .node "n2" []
                                    ]
                                  ]
                                ]
                              ]
                            ]
                          ]
                        ]
                      ]
                    ]
                  ]
                ]
              ],
              .node "timeunitAdv" [
                .node "NumNumeral" [
                  .node "num" [
                    .node "pot4as5" [
                      .node "pot3as4" [
                        .node "pot2as3" [
                          .node "pot1as2" [
                            .node "pot0as1" [
                              .node "pot0" [
                                .node "n5" []
                              ]
                            ]
                          ]
                        ]
                      ]
                    ]
                  ]
                ],
                .node "year_Timeunit" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection5RulesParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "each_Det" [],
          .node "UseN" [
            .node "house_6_N" []
          ]
        ],
        .node "ReflVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "may_1_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "SlashV2a" [
                .node "determine_7_V2" []
              ]
            ]
          ],
          .node "AdvRNP" [
            .node "DetCN" [
              .node "DetQuant" [
                .node "DefArt" [],
                .node "NumPl" []
              ],
              .node "UseN" [
                .node "rule_3_N" []
              ]
            ],
            .node "of_2_Prep" [],
            .node "ReflPoss" [
              .node "NumSg" [],
              .node "UseN" [
                .node "proceedings_2_N" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection7EveryBillPresentedParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "every_Det" [],
          .node "UseN" [
            .node "bill_9_N" []
          ]
        ],
        .node "MkVPS" [
          .node "TTAnt" [
            .node "TPres" [],
            .node "ASimul" []
          ],
          .node "PPos" [],
          .node "ComplVPIVV" [
            .node "shall_VV" [],
            .node "MkVPI" [
              .node "PassVPSlash" [
                .node "Slash3V3" [
                  .node "present_to_V3" [],
                  .node "DetCN" [
                    .node "DetQuant" [
                      .node "DefArt" [],
                      .node "NumSg" []
                    ],
                    .node "PossNP" [
                      .node "UseN" [
                        .node "presidentMasc_2_N" []
                      ],
                      .node "UseLN" [
                        .node "united_states_LN" []
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection7PresidentSignsParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "UsePron" [
          .node "he_Pron" []
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "SlashV2a" [
                .node "sign_2_V2" []
              ]
            ]
          ],
          .node "UsePron" [
            .node "it_Pron" []
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection7BecomesLawParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "UseCl" [
        .node "TTAnt" [
          .node "TPres" [],
          .node "ASimul" []
        ],
        .node "PPos" [],
        .node "ImpersCl" [
          .node "ComplVPIVV" [
            .node "shall_VV" [],
            .node "MkVPI" [
              .node "UseComp_estar" [
                .node "CompCN" [
                  .node "UseN" [
                    .node "law_3_N" []
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection9HabeasParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "DefArt" [],
            .node "NumSg" []
          ],
          .node "PartNP" [
            .node "PartNP" [
              .node "UseN" [
                .node "privilege_2_N" []
              ],
              .node "DetCN" [
                .node "DetQuant" [
                  .node "DefArt" [],
                  .node "NumSg" []
                ],
                .node "UseN" [
                  .node "writ_N" []
                ]
              ]
            ],
            .node "MassNP" [
              .node "UseN" [
                .node "habeas_corpus_2_N" []
              ]
            ]
          ]
        ],
        .node "MkVPS" [
          .node "TTAnt" [
            .node "TPres" [],
            .node "ASimul" []
          ],
          .node "PNeg" [],
          .node "ComplVPIVV" [
            .node "shall_VV" [],
            .node "MkVPI" [
              .node "PassVPSlash" [
                .node "SlashV2a" [
                  .node "suspend_5_V2" []
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection9NoTitleOfNobilityParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "no_Quant" [],
            .node "NumSg" []
          ],
          .node "PartNP" [
            .node "UseN" [
              .node "title_2_N" []
            ],
            .node "MassNP" [
              .node "UseN" [
                .node "nobility_2_N" []
              ]
            ]
          ]
        ],
        .node "MkVPS" [
          .node "TTAnt" [
            .node "TPres" [],
            .node "ASimul" []
          ],
          .node "PPos" [],
          .node "ComplVPIVV" [
            .node "shall_VV" [],
            .node "MkVPI" [
              .node "PassAgentVPSlash" [
                .node "SlashV2a" [
                  .node "grant_7_V2" []
                ],
                .node "UseLN" [
                  .node "united_states_LN" []
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleIISection1ExecutiveVestingParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "DefArt" [],
            .node "NumSg" []
          ],
          .node "AdjCN" [
            .node "PositA" [
              .node "executive_A" []
            ],
            .node "UseN" [
              .node "power_2_N" []
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "PassVPSlash" [
                  .node "SlashV2a" [
                    .node "vest_2_V2" []
                  ]
                ],
                .node "in_1_Prep" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "IndefArt" [],
              .node "NumSg" []
            ],
            .node "PossNP" [
              .node "PartNP" [
                .node "UseN" [
                  .node "presidentMasc_6_N" []
                ],
                .node "UseLN" [
                  .node "united_states_LN" []
                ]
              ],
              .node "UseLN" [
                .node "america_1_LN" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleIISection1PresidentAgeParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttNP" [
      .node "DetCN" [
        .node "DetQuant" [
          .node "DefArt" [],
          .node "NumSg" []
        ],
        .node "AdvCN" [
          .node "PartNP" [
            .node "UseN" [
              .node "age_3_N" []
            ],
            .node "UseDAPFem" [
              .node "DetDAP" [
                .node "DetQuant" [
                  .node "IndefArt" [],
                  .node "NumCard" [
                    .node "NumNumeral" [
                      .node "num" [
                        .node "pot4as5" [
                          .node "pot3as4" [
                            .node "pot2as3" [
                              .node "pot1as2" [
                                .node "pot1" [
                                  .node "n3" []
                                ]
                              ]
                            ]
                          ]
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ],
          .node "timeunitAdv" [
            .node "NumNumeral" [
              .node "num" [
                .node "pot4as5" [
                  .node "pot3as4" [
                    .node "pot2as3" [
                      .node "pot1as2" [
                        .node "pot0as1" [
                          .node "pot0" [
                            .node "n5" []
                          ]
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ],
            .node "year_Timeunit" []
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleIISection2CommanderInChiefParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "DefArt" [],
            .node "NumSg" []
          ],
          .node "UseN" [
            .node "presidentFem_1_N" []
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "UseComp_ser" [
                  .node "CompNP" [
                    .node "MassNP" [
                      .node "UseN" [
                        .node "commanderFem_2_N" []
                      ]
                    ]
                  ]
                ],
                .node "in_2_Prep" []
              ]
            ]
          ],
          .node "MassNP" [
            .node "PartNP" [
              .node "UseN" [
                .node "chiefMasc_3_N" []
              ],
              .node "DetCNN" [
                .node "DefArt" [],
                .node "and_Conj" [],
                .node "BaseCNN" [
                  .node "NumSg" [],
                  .node "UseN" [
                    .node "army_3_N" []
                  ],
                  .node "NumSg" [],
                  .node "PartNP" [
                    .node "UseN" [
                      .node "navy_3_N" []
                    ],
                    .node "UseLN" [
                      .node "united_states_LN" []
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleIIISection3TreasonParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "MassNP" [
          .node "AdvCN" [
            .node "UseN" [
              .node "treason_2_N" []
            ],
            .node "PrepNP" [
              .node "against_Prep" [],
              .node "UseLN" [
                .node "united_states_LN" []
              ]
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "VPSlashPrep" [
              .node "ComplVPIVV" [
                .node "shall_VV" [],
                .node "ComplVPI2" [
                  .node "MkVPI2" [
                    .node "AdvVPSlash" [
                      .node "VPSlashPrep" [
                        .node "UseV" [
                          .node "consist_4_V" []
                        ],
                        .node "in_1_Prep" []
                      ],
                      .node "only_7_Adv" []
                    ]
                  ],
                  .node "GerundNP" [
                    .node "ComplSlashPartLast" [
                      .node "SlashV2a" [
                        .node "levy_1_V2" []
                      ],
                      .node "MassNP" [
                        .node "UseN" [
                          .node "war_4_N" []
                        ]
                      ]
                    ]
                  ]
                ]
              ],
              .node "against_Prep" []
            ]
          ],
          .node "UsePron" [
            .node "theyFem_Pron" []
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleIVSection1FullFaithCreditParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "MassNP" [
          .node "AdjCN" [
            .node "PositA" [
              .node "full_2_A" []
            ],
            .node "ConjCN" [
              .node "and_Conj" [],
              .node "BaseCN" [
                .node "UseN" [
                  .node "faith_1_N" []
                ],
                .node "UseN" [
                  .node "credit_9_N" []
                ]
              ]
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "VPSlashPrep" [
              .node "ComplVPIVV" [
                .node "shall_VV" [],
                .node "ComplVPI2" [
                  .node "MkVPI2" [
                    .node "VPSlashPrep" [
                      .node "PassVPSlash" [
                        .node "SlashV2a" [
                          .node "give_22_V2" []
                        ]
                      ],
                      .node "in_4_Prep" []
                    ]
                  ],
                  .node "DetCN" [
                    .node "each_Det" [],
                    .node "UseN" [
                      .node "state_4_N" []
                    ]
                  ]
                ]
              ],
              .node "to_5_Prep" []
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "DefArt" [],
              .node "NumPl" []
            ],
            .node "AdjCN" [
              .node "PositA" [
                .node "public_1_A" []
              ],
              .node "ApposCN" [
                .node "UseN" [
                  .node "act_3_N" []
                ],
                .node "DetCNN" [
                  .node "gen_Quant" [],
                  .node "and_Conj" [],
                  .node "BaseCNN" [
                    .node "NumPl" [],
                    .node "UseN" [
                      .node "record_2_N" []
                    ],
                    .node "NumSg" [],
                    .node "PartNP" [
                      .node "AdjCN" [
                        .node "PositA" [
                          .node "judicial_1_A" []
                        ],
                        .node "UseN" [
                          .node "proceedings_1_N" []
                        ]
                      ],
                      .node "DetCN" [
                        .node "every_Det" [],
                        .node "AdjCN" [
                          .node "PositA" [
                            .node "other_4_A" []
                          ],
                          .node "UseN" [
                            .node "state_8_N" []
                          ]
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleVISupremacyParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "this_Quant" [],
            .node "NumSg" []
          ],
          .node "UseN" [
            .node "constitution_1_N" []
          ]
        ],
        .node "MkVPS" [
          .node "TTAnt" [
            .node "TPres" [],
            .node "ASimul" []
          ],
          .node "PPos" [],
          .node "ComplVPIVV" [
            .node "shall_VV" [],
            .node "MkVPI" [
              .node "UseComp" [
                .node "CompNP" [
                  .node "DetCN" [
                    .node "DetQuant" [
                      .node "DefArt" [],
                      .node "NumSg" []
                    ],
                    .node "PossNP" [
                      .node "AdjCN" [
                        .node "PositA" [
                          .node "supreme_2_A" []
                        ],
                        .node "UseN" [
                          .node "law_1_N" []
                        ]
                      ],
                      .node "DetCN" [
                        .node "DetQuant" [
                          .node "DefArt" [],
                          .node "NumSg" []
                        ],
                        .node "UseN" [
                          .node "land_9_N" []
                        ]
                      ]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleVINoReligiousTestParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "no_Quant" [],
            .node "NumSg" []
          ],
          .node "AdjCN" [
            .node "PositA" [
              .node "religious_4_A" []
            ],
            .node "UseN" [
              .node "test_4_N" []
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "VPSlashPrep" [
              .node "ComplVPIVV" [
                .node "shall_VV" [],
                .node "ComplVPI2" [
                  .node "MkVPI2" [
                    .node "AdVVPSlash" [
                      .node "ever_1_AdV" [],
                      .node "VPSlashPrep" [
                        .node "PassVPSlash" [
                          .node "SlashV2a" [
                            .node "require_1_V2" []
                          ]
                        ],
                        .node "as_Prep" []
                      ]
                    ]
                  ],
                  .node "DetCNN" [
                    .node "IndefArt" [],
                    .node "or_Conj" [],
                    .node "BaseCNN" [
                      .node "NumSg" [],
                      .node "AdvCN" [
                        .node "UseN" [
                          .node "qualification_3_N" []
                        ],
                        .node "PrepNP" [
                          .node "to_4_Prep" [],
                          .node "DetCN" [
                            .node "anySg_2_Det" [],
                            .node "UseN" [
                              .node "office_3_N" []
                            ]
                          ]
                        ]
                      ],
                      .node "NumSg" [],
                      .node "AdjCN" [
                        .node "PositA" [
                          .node "public_1_A" []
                        ],
                        .node "UseN" [
                          .node "trust_3_N" []
                        ]
                      ]
                    ]
                  ]
                ]
              ],
              .node "under_Prep" []
            ]
          ],
          .node "UseLN" [
            .node "united_states_LN" []
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleVIIRatificationParse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "DetCN" [
          .node "DetQuant" [
            .node "DefArt" [],
            .node "NumSg" []
          ],
          .node "PossNP" [
            .node "UseN" [
              .node "ratification_N" []
            ],
            .node "DetCN" [
              .node "DetQuant" [
                .node "DefArt" [],
                .node "NumPl" []
              ],
              .node "PartNP" [
                .node "UseN" [
                  .node "convention_2_N" []
                ],
                .node "DetCN" [
                  .node "DetQuant" [
                    .node "IndefArt" [],
                    .node "NumCard" [
                      .node "NumNumeral" [
                        .node "num" [
                          .node "pot4as5" [
                            .node "pot3as4" [
                              .node "pot2as3" [
                                .node "pot1as2" [
                                  .node "pot0as1" [
                                    .node "pot0" [
                                      .node "n9" []
                                    ]
                                  ]
                                ]
                              ]
                            ]
                          ]
                        ]
                      ]
                    ]
                  ],
                  .node "UseN" [
                    .node "state_1_N" []
                  ]
                ]
              ]
            ]
          ]
        ],
        .node "ComplVPS2" [
          .node "MkVPS2" [
            .node "TTAnt" [
              .node "TPres" [],
              .node "ASimul" []
            ],
            .node "PPos" [],
            .node "SlashVV" [
              .node "shall_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "VPSlashPrep" [
                .node "UseComp_estar" [
                  .node "CompAP" [
                    .node "PositA" [
                      .node "sufficient_A" []
                    ]
                  ]
                ],
                .node "for_Prep" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "DefArt" [],
              .node "NumSg" []
            ],
            .node "ApposCN" [
              .node "PartNP" [
                .node "UseN" [
                  .node "establishment_4_N" []
                ],
                .node "UseDAPMasc" [
                  .node "DetDAP" [
                    .node "DetQuant" [
                      .node "this_Quant" [],
                      .node "NumSg" []
                    ]
                  ]
                ]
              ],
              .node "UsePN" [
                .node "constitution_PN" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]

def clauseParses : ClauseId → List ExportedTree
  | .preambleEstablishJustice => [preambleEstablishJusticeParse1]
  | .articleISection1Vesting => [articleISection1VestingParse1]
  | .articleISection2HouseComposition => [articleISection2HouseCompositionParse1]
  | .articleISection2RepresentativeAge => [articleISection2RepresentativeAgeParse1]
  | .articleISection3SenateImpeachments => []
  | .articleISection5Rules => [articleISection5RulesParse1]
  | .articleISection7EveryBillPresented => [articleISection7EveryBillPresentedParse1]
  | .articleISection7PresidentSigns => [articleISection7PresidentSignsParse1]
  | .articleISection7BecomesLaw => [articleISection7BecomesLawParse1]
  | .articleISection8DeclareWar => []
  | .articleISection9Habeas => [articleISection9HabeasParse1]
  | .articleISection9NoTitleOfNobility => [articleISection9NoTitleOfNobilityParse1]
  | .articleIISection1ExecutiveVesting => [articleIISection1ExecutiveVestingParse1]
  | .articleIISection1PresidentAge => [articleIISection1PresidentAgeParse1]
  | .articleIISection2CommanderInChief => [articleIISection2CommanderInChiefParse1]
  | .articleIIISection3Treason => [articleIIISection3TreasonParse1]
  | .articleIVSection1FullFaithCredit => [articleIVSection1FullFaithCreditParse1]
  | .articleVProposeAmendments => []
  | .articleVISupremacy => [articleVISupremacyParse1]
  | .articleVINoReligiousTest => [articleVINoReligiousTestParse1]
  | .articleVIIRatification => [articleVIIRatificationParse1]

def rawParseCount : ClauseId → Nat
  | .preambleEstablishJustice => 1
  | .articleISection1Vesting => 1
  | .articleISection2HouseComposition => 1
  | .articleISection2RepresentativeAge => 1
  | .articleISection3SenateImpeachments => 3
  | .articleISection5Rules => 1
  | .articleISection7EveryBillPresented => 1
  | .articleISection7PresidentSigns => 1
  | .articleISection7BecomesLaw => 1
  | .articleISection8DeclareWar => 3
  | .articleISection9Habeas => 1
  | .articleISection9NoTitleOfNobility => 1
  | .articleIISection1ExecutiveVesting => 1
  | .articleIISection1PresidentAge => 1
  | .articleIISection2CommanderInChief => 1
  | .articleIIISection3Treason => 1
  | .articleIVSection1FullFaithCredit => 1
  | .articleVProposeAmendments => 3
  | .articleVISupremacy => 1
  | .articleVINoReligiousTest => 1
  | .articleVIIRatification => 1

def acceptedParseCount : ClauseId → Nat
  | .preambleEstablishJustice => 1
  | .articleISection1Vesting => 1
  | .articleISection2HouseComposition => 1
  | .articleISection2RepresentativeAge => 1
  | .articleISection3SenateImpeachments => 0
  | .articleISection5Rules => 1
  | .articleISection7EveryBillPresented => 1
  | .articleISection7PresidentSigns => 1
  | .articleISection7BecomesLaw => 1
  | .articleISection8DeclareWar => 0
  | .articleISection9Habeas => 1
  | .articleISection9NoTitleOfNobility => 1
  | .articleIISection1ExecutiveVesting => 1
  | .articleIISection1PresidentAge => 1
  | .articleIISection2CommanderInChief => 1
  | .articleIIISection3Treason => 1
  | .articleIVSection1FullFaithCredit => 1
  | .articleVProposeAmendments => 0
  | .articleVISupremacy => 1
  | .articleVINoReligiousTest => 1
  | .articleVIIRatification => 1

def parseError : ClauseId → Option String
  | .preambleEstablishJustice => none
  | .articleISection1Vesting => none
  | .articleISection2HouseComposition => none
  | .articleISection2RepresentativeAge => none
  | .articleISection3SenateImpeachments => some "no accepted parse without PGF meta holes"
  | .articleISection5Rules => none
  | .articleISection7EveryBillPresented => none
  | .articleISection7PresidentSigns => none
  | .articleISection7BecomesLaw => none
  | .articleISection8DeclareWar => some "no accepted parse without PGF meta holes"
  | .articleISection9Habeas => none
  | .articleISection9NoTitleOfNobility => none
  | .articleIISection1ExecutiveVesting => none
  | .articleIISection1PresidentAge => none
  | .articleIISection2CommanderInChief => none
  | .articleIIISection3Treason => none
  | .articleIVSection1FullFaithCredit => none
  | .articleVProposeAmendments => some "no accepted parse without PGF meta holes"
  | .articleVISupremacy => none
  | .articleVINoReligiousTest => none
  | .articleVIIRatification => none

def clauseGFLinearizations : ClauseId → List String
  | .preambleEstablishJustice => ["establish justice"]
  | .articleISection1Vesting => ["all legislative powers herein granted shall be vested in a congress of the United States"]
  | .articleISection2HouseComposition => ["the house of representatives shall be composed of members chosen every second year by the people of the several states"]
  | .articleISection2RepresentativeAge => ["no person shall be a representative who shall not have attained to the age of twenty for five years"]
  | .articleISection3SenateImpeachments => []
  | .articleISection5Rules => ["each house may determine the rules of its proceedings"]
  | .articleISection7EveryBillPresented => ["every bill shall be presented to the president of the United States"]
  | .articleISection7PresidentSigns => ["he shall sign it"]
  | .articleISection7BecomesLaw => ["it shall be a law"]
  | .articleISection8DeclareWar => []
  | .articleISection9Habeas => ["the privilege of the writ of habeas corpus shall not be suspended"]
  | .articleISection9NoTitleOfNobility => ["no title of nobility shall be granted by the United States"]
  | .articleIISection1ExecutiveVesting => ["the executive power shall be vested in a president of the United States of America"]
  | .articleIISection1PresidentAge => ["the age of thirty for five years"]
  | .articleIISection2CommanderInChief => ["the president shall be commander in chief of the army and navy of the United States"]
  | .articleIIISection3Treason => ["treason against the United States shall consist only in levying war against them"]
  | .articleIVSection1FullFaithCredit => ["full faith and credit shall be given in each state to the public acts records and judicial proceedings of every other state"]
  | .articleVProposeAmendments => []
  | .articleVISupremacy => ["this constitution shall be the supreme law of the land"]
  | .articleVINoReligiousTest => ["no religious test shall ever be required as a qualification to any office or public trust under the United States"]
  | .articleVIIRatification => ["the ratification of the conventions of nine states shall be sufficient for the establishment of this Constitution"]

def clauseGFBracketedLinearizations : ClauseId → List String
  | .preambleEstablishJustice => ["(Phr:9 (Utt:7 (VP:6 (VPSlash:2 (V2:1 establish))) (VP:6 (NP:5 (CN:4 (N:3 justice))))))"]
  | .articleISection1Vesting => ["(Phr:44 (Utt:42 (S:41 (NP:16 (Predet:1 all) (NP:15 (NP:5 (AP:4 (A:3 legislative))) (CN:14 (CN:9 (CN:7 (N:6 powers)) (Adv:8 herein)) (NP:13 (AP:12 (VPSlash:11 (V2:10 granted))))))) (VPS:40 (VPS2:30 (VPSlash:29 (VV:21 shall)))) (VPS:40 (VPS2:30 (VPSlash:29 (VPSlash:28 (VP:26 be)) (VPSlash:28 (VP:26 (VPSlash:25 (V2:24 vested)))))) (VPS2:30 (VPSlash:29 (VPSlash:28 (Prep:27 in)))) (NP:39 (Det:33 (Quant:31 a)) (CN:38 (CN:35 (N:34 congress)) of (NP:37 the (LN:36 United States))))))))"]
  | .articleISection2HouseComposition => ["(Phr:66 (Utt:64 (S:63 (NP:13 (Det:3 (Quant:1 the)) (CN:12 (CN:5 (N:4 house)) of (NP:11 (CN:10 (N:9 representatives))))) (VPS:62 (VPS2:27 (VPSlash:26 (VV:18 shall)))) (VPS:62 (VPS2:27 (VPSlash:26 (VPSlash:25 (VP:23 be)) (VPSlash:25 (VP:23 (VPSlash:22 (V2:21 composed)))))) (VPS2:27 (VPSlash:26 (VPSlash:25 (Prep:24 of)))) (NP:61 (CN:60 (CN:59 (N:58 members)) (AP:57 (VPSlash:42 (VPSlash:32 (V2:31 chosen))) (VPSlash:42 (Adv:41 (NP:40 (Det:33 every) (CN:39 (CN:35 (N:34 second)) (NP:38 (CN:37 (N:36 year))))))) by (NP:56 (Det:45 (Quant:43 the)) (CN:55 (CN:47 (N:46 people)) of (NP:54 (Det:51 (Quant:48 the) (Num:50 (Card:49 several))) (CN:53 (N:52 states))))))))))))"]
  | .articleISection2RepresentativeAge => ["(Phr:77 (Utt:75 (S:74 (NP:6 (Det:3 (Quant:1 no)) (CN:5 (N:4 person))) (VPS:73 (VPS2:40 (VPSlash:39 (VV:11 shall)))) (VPS:73 (VPS2:40 (VPSlash:39 (VPSlash:38 (VP:36 be)) (VPSlash:38 (VP:36 (Comp:35 a (CN:34 (CN:15 (N:14 representative)) (RS:33 (RP:16 who) (VPS:32 (VPS2:27 (VPSlash:26 (VV:21 shall)))) (VPS:32 (VPS2:27 not (VPSlash:26 (VPSlash:25 (V2:24 have)))) (NP:31 (AP:30 (VPSlash:29 (V2:28 attained)))))))))))) (VPS2:40 (VPSlash:39 (VPSlash:38 (Prep:37 to)))) (NP:72 (Det:43 (Quant:41 the)) (CN:71 (CN:59 (CN:45 (N:44 age)) of (NP:58 (DAP:57 (Det:56 (Num:55 (Card:54 (Numeral:53 (Sub1000000000000:52 (Sub1000000000:51 (Sub1000000:50 (Sub1000:49 (Sub100:48 (Digit:47 twenty))))))))))))) (Adv:70 for (Card:68 (Numeral:67 (Sub1000000000000:66 (Sub1000000000:65 (Sub1000000:64 (Sub1000:63 (Sub100:62 (Sub10:61 (Digit:60 five))))))))) (Timeunit:69 years))))))))"]
  | .articleISection3SenateImpeachments => []
  | .articleISection5Rules => ["(Phr:32 (Utt:30 (S:29 (NP:4 (Det:1 each) (CN:3 (N:2 house))) (VPS:28 (VPS2:15 (VPSlash:14 (VV:9 may)))) (VPS:28 (VPS2:15 (VPSlash:14 (VPSlash:13 (V2:12 determine)))) (RNP:27 (NP:21 (Det:18 (Quant:16 the)) (CN:20 (N:19 rules))) (Prep:22 of) (RNP:26 its (CN:25 (N:24 proceedings))))))))"]
  | .articleISection7EveryBillPresented => ["(Phr:28 (Utt:26 (S:25 (NP:4 (Det:1 every) (CN:3 (N:2 bill))) (VPS:24 (VP:23 (VV:9 shall))) (VPS:24 (VP:23 (VPI:22 (VP:21 be) (VP:21 (VPSlash:20 (V3:10 presented)) (VPSlash:20 (V3:10 to) (NP:19 (Det:13 (Quant:11 the)) (CN:18 (CN:15 (N:14 president)) of (NP:17 the (LN:16 United States))))))))))))"]
  | .articleISection7PresidentSigns => ["(Phr:20 (Utt:18 (S:17 (NP:2 (Pron:1 he)) (VPS:16 (VPS2:13 (VPSlash:12 (VV:7 shall)))) (VPS:16 (VPS2:13 (VPSlash:12 (VPSlash:11 (V2:10 sign)))) (NP:15 (Pron:14 it))))))"]
  | .articleISection7BecomesLaw => ["(Phr:16 (Utt:14 (S:13 (Cl:12 it (VP:11 (VV:5 shall)) (VP:11 (VPI:10 (VP:9 be) (VP:9 (Comp:8 a (CN:7 (N:6 law))))))))))"]
  | .articleISection8DeclareWar => []
  | .articleISection9Habeas => ["(Phr:32 (Utt:30 (S:29 (NP:17 (Det:3 (Quant:1 the)) (CN:16 (CN:12 (CN:5 (N:4 privilege)) of (NP:11 (Det:8 (Quant:6 the)) (CN:10 (N:9 writ)))) of (NP:15 (CN:14 (N:13 habeas corpus))))) (VPS:28 (VP:27 (VV:22 shall))) (VPS:28 not (VP:27 (VPI:26 (VP:25 be) (VP:25 (VPSlash:24 (V2:23 suspended)))))))))"]
  | .articleISection9NoTitleOfNobility => ["(Phr:27 (Utt:25 (S:24 (NP:10 (Det:3 (Quant:1 no)) (CN:9 (CN:5 (N:4 title)) of (NP:8 (CN:7 (N:6 nobility))))) (VPS:23 (VP:22 (VV:15 shall))) (VPS:23 (VP:22 (VPI:21 (VP:20 be) (VP:20 (VPSlash:17 (V2:16 granted)) by (NP:19 the (LN:18 United States)))))))))"]
  | .articleIISection1ExecutiveVesting => ["(Phr:40 (Utt:38 (S:37 (NP:9 (Det:3 (Quant:1 the)) (CN:8 (AP:5 (A:4 executive)) (CN:7 (N:6 power)))) (VPS:36 (VPS2:23 (VPSlash:22 (VV:14 shall)))) (VPS:36 (VPS2:23 (VPSlash:22 (VPSlash:21 (VP:19 be)) (VPSlash:21 (VP:19 (VPSlash:18 (V2:17 vested)))))) (VPS2:23 (VPSlash:22 (VPSlash:21 (Prep:20 in)))) (NP:35 (Det:26 (Quant:24 a)) (CN:34 (CN:31 (CN:28 (N:27 president)) of (NP:30 the (LN:29 United States))) of (NP:33 (LN:32 America))))))))"]
  | .articleIISection1PresidentAge => ["(Phr:35 (Utt:33 (NP:32 (Det:3 (Quant:1 the)) (CN:31 (CN:19 (CN:5 (N:4 age)) of (NP:18 (DAP:17 (Det:16 (Num:15 (Card:14 (Numeral:13 (Sub1000000000000:12 (Sub1000000000:11 (Sub1000000:10 (Sub1000:9 (Sub100:8 (Digit:7 thirty))))))))))))) (Adv:30 for (Card:28 (Numeral:27 (Sub1000000000000:26 (Sub1000000000:25 (Sub1000000:24 (Sub1000:23 (Sub100:22 (Sub10:21 (Digit:20 five))))))))) (Timeunit:29 years))))))"]
  | .articleIISection2CommanderInChief => ["(Phr:44 (Utt:42 (S:41 (NP:6 (Det:3 (Quant:1 the)) (CN:5 (N:4 president))) (VPS:40 (VPS2:22 (VPSlash:21 (VV:11 shall)))) (VPS:40 (VPS2:22 (VPSlash:21 (VPSlash:20 (VP:18 be)) (VPSlash:20 (VP:18 (Comp:17 (NP:16 (CN:15 (N:14 commander)))))))) (VPS2:22 (VPSlash:21 (VPSlash:20 (Prep:19 in)))) (NP:39 (CN:38 (CN:24 (N:23 chief)) of (NP:37 (Quant:25 the) (CNN:36 (CN:29 (N:28 army))) (Conj:26 and) (CNN:36 (CN:35 (CN:32 (N:31 navy)) of (NP:34 the (LN:33 United States)))))))))))"]
  | .articleIIISection3Treason => ["(Phr:39 (Utt:37 (S:36 (NP:8 (CN:7 (CN:2 (N:1 treason)) (Adv:6 (Prep:3 against) (NP:5 the (LN:4 United States))))) (VPS:35 (VPS2:32 (VPSlash:31 (VP:29 (VV:13 shall))))) (VPS:35 (VPS2:32 (VPSlash:31 (VP:29 (VPI:28 (VPI2:20 (VPSlash:19 (VPSlash:17 (VP:15 (V:14 consist)))) (VPSlash:19 (Adv:18 only))) (VPI2:20 (VPSlash:19 (VPSlash:17 (Prep:16 in)))) (NP:27 (VP:26 (VPSlash:22 (V2:21 levying))) (VP:26 (NP:25 (CN:24 (N:23 war))))))))) (VPS2:32 (VPSlash:31 (Prep:30 against))) (NP:34 (Pron:33 them))))))"]
  | .articleIVSection1FullFaithCredit => ["(Phr:67 (Utt:65 (S:64 (NP:11 (CN:10 (AP:2 (A:1 full)) (CN:9 (ListCN:8 (CN:5 (N:4 faith))) (Conj:3 and) (ListCN:8 (CN:7 (N:6 credit)))))) (VPS:63 (VPS2:31 (VPSlash:30 (VP:28 (VV:16 shall))))) (VPS:63 (VPS2:31 (VPSlash:30 (VP:28 (VPI:27 (VPI2:22 (VPSlash:21 (VP:19 be)) (VPSlash:21 (VP:19 (VPSlash:18 (V2:17 given))))) (VPI2:22 (VPSlash:21 (Prep:20 in))) (NP:26 (Det:23 each) (CN:25 (N:24 state))))))) (VPS2:31 (VPSlash:30 (Prep:29 to))) (NP:62 (Det:34 (Quant:32 the)) (CN:61 (AP:36 (A:35 public)) (CN:60 (CN:38 (N:37 acts)) (NP:59 (CNN:58 (CN:43 (N:42 records))) (Conj:40 and) (CNN:58 (CN:57 (CN:49 (AP:46 (A:45 judicial)) (CN:48 (N:47 proceedings))) of (NP:56 (Det:50 every) (CN:55 (AP:52 (A:51 other)) (CN:54 (N:53 state))))))))))))))"]
  | .articleVProposeAmendments => []
  | .articleVISupremacy => ["(Phr:36 (Utt:34 (S:33 (NP:6 (Det:3 (Quant:1 this)) (CN:5 (N:4 constitution))) (VPS:32 (VP:31 (VV:11 shall))) (VPS:32 (VP:31 (VPI:30 (VP:29 be) (VP:29 (Comp:28 (NP:27 (Det:14 (Quant:12 the)) (CN:26 (CN:19 (AP:16 (A:15 supreme)) (CN:18 (N:17 law))) of (NP:25 (Det:22 (Quant:20 the)) (CN:24 (N:23 land)))))))))))))"]
  | .articleVINoReligiousTest => ["(Phr:54 (Utt:52 (S:51 (NP:9 (Det:3 (Quant:1 no)) (CN:8 (AP:5 (A:4 religious)) (CN:7 (N:6 test)))) (VPS:50 (VPS2:47 (VPSlash:46 (VP:44 (VV:14 shall))))) (VPS:50 (VPS2:47 (VPSlash:46 (VP:44 (VPI:43 (VPI2:22 (VPSlash:21 (AdV:15 ever)) (VPSlash:21 (VPSlash:20 (VP:18 be))) (VPSlash:21 (VPSlash:20 (VP:18 (VPSlash:17 (V2:16 required)))))) (VPI2:22 (VPSlash:21 (VPSlash:20 (Prep:19 as)))) (NP:42 (Quant:23 a) (CNN:41 (CN:34 (CN:27 (N:26 qualification)) (Adv:33 (Prep:28 to) (NP:32 (Det:29 any) (CN:31 (N:30 office)))))) (Conj:24 or) (CNN:41 (CN:40 (AP:37 (A:36 public)) (CN:39 (N:38 trust))))))))) (VPS2:47 (VPSlash:46 (Prep:45 under))) (NP:49 the (LN:48 United States))))))"]
  | .articleVIIRatification => ["(Phr:64 (Utt:62 (S:61 (NP:29 (Det:3 (Quant:1 the)) (CN:28 (CN:5 (N:4 ratification)) of (NP:27 (Det:8 (Quant:6 the)) (CN:26 (CN:10 (N:9 conventions)) of (NP:25 (Det:22 (Num:21 (Card:20 (Numeral:19 (Sub1000000000000:18 (Sub1000000000:17 (Sub1000000:16 (Sub1000:15 (Sub100:14 (Sub10:13 (Digit:12 nine))))))))))) (CN:24 (N:23 states))))))) (VPS:60 (VPS2:44 (VPSlash:43 (VV:34 shall)))) (VPS:60 (VPS2:44 (VPSlash:43 (VPSlash:42 (VP:40 be)) (VPSlash:42 (VP:40 (Comp:39 (AP:38 (A:37 sufficient))))))) (VPS2:44 (VPSlash:43 (VPSlash:42 (Prep:41 for)))) (NP:59 (Det:47 (Quant:45 the)) (CN:58 (CN:55 (CN:49 (N:48 establishment)) of (NP:54 (DAP:53 (Det:52 (Quant:50 this))))) (NP:57 (PN:56 Constitution))))))))"]

def usedFunctions : List String := ["ASimul", "AdVVPSlash", "AdjAsNP", "AdjCN", "AdvCN", "AdvRNP", "AdvVPSlash", "ApposCN", "BaseCN", "BaseCNN", "CompAP", "CompCN", "CompNP", "ComplSlashPartLast", "ComplVPI2", "ComplVPIVV", "ComplVPS2", "ConjCN", "DefArt", "DetCN", "DetCNN", "DetDAP", "DetQuant", "GenModNP", "GerundNP", "IdRP", "ImpersCl", "IndefArt", "MassNP", "MkVPI", "MkVPI2", "MkVPS", "MkVPS2", "NoPConj", "NoVoc", "NumCard", "NumNumeral", "NumPl", "NumSg", "PNeg", "PPos", "PartNP", "PassAgentVPSlash", "PassVPSlash", "PastPartAP", "PastPartAgentAP", "PhrUtt", "PositA", "PossNP", "PredVPS", "PredetNP", "PrepNP", "ReflPoss", "ReflVPS2", "RelCN", "RelVPS", "Slash3V3", "SlashV2a", "SlashVV", "TPres", "TTAnt", "TimeNP", "UseCl", "UseComp", "UseComp_estar", "UseComp_ser", "UseDAP", "UseDAPFem", "UseDAPMasc", "UseLN", "UseN", "UsePN", "UsePron", "UseV", "UttNP", "UttS", "UttVPShort", "VPSlashPrep", "act_3_N", "against_Prep", "age_2_N", "age_3_N", "all_1_Predet", "all_2_Predet", "amendment_2_N", "america_1_LN", "and_Conj", "anySg_2_Det", "army_3_N", "as_Prep", "attain_3_V2", "bill_9_N", "chiefMasc_3_N", "choose_2_V2", "commanderFem_2_N", "compose_4_V2", "congress_2_N", "congress_3_N", "consist_4_V", "constitution_1_N", "constitution_PN", "convention_2_N", "credit_9_N", "declare_6_V2", "determine_7_V2", "each_Det", "establish_4_V2", "establishment_4_N", "ever_1_AdV", "every_Det", "executive_A", "faith_1_N", "for_Prep", "full_2_A", "gen_Quant", "give_22_V2", "grant_1_V2", "grant_7_V2", "habeas_corpus_2_N", "have_15_V2", "have_8_V2", "he_Pron", "herein_Adv", "house_4_N", "house_6_N", "impeachment_N", "in_1_Prep", "in_2_Prep", "in_4_Prep", "in_5_Prep", "it_Pron", "judicial_1_A", "justiceFem_3_N", "land_9_N", "law_1_N", "law_3_N", "legislative_1_A", "levy_1_V2", "may_1_VV", "memberMasc_1_N", "n2", "n3", "n5", "n9", "navy_3_N", "no_Quant", "nobility_2_N", "num", "of_2_Prep", "office_3_N", "only_7_Adv", "or_Conj", "other_4_A", "people_4_N", "person_2_N", "pot0", "pot0as1", "pot1", "pot1as2", "pot2as3", "pot3as4", "pot4as5", "power_10_N", "power_2_N", "power_7_N", "present_to_V3", "presidentFem_1_N", "presidentMasc_2_N", "presidentMasc_6_N", "privilege_2_N", "proceedings_1_N", "proceedings_2_N", "propose_4_V2", "public_1_A", "qualification_3_N", "ratification_N", "record_2_N", "religious_4_A", "representativeFem_1_N", "representativeMasc_2_N", "require_1_V2", "rule_3_N", "second_10_N", "senate_2_N", "several_Card", "shall_VV", "sign_2_V2", "sole_1_A", "state_1_N", "state_4_N", "state_8_N", "sufficient_A", "supreme_2_A", "suspend_5_V2", "test_4_N", "theyFem_Pron", "this_Quant", "timeunitAdv", "title_2_N", "to_1_Prep", "to_4_Prep", "to_5_Prep", "treason_2_N", "trust_3_N", "try_3_V2", "under_Prep", "united_states_LN", "vest_2_V2", "vest_4_V2", "war_4_N", "writ_N", "year_1_N", "year_Timeunit"]

end Mettapedia.Languages.GF.USConstitution.Generated.Witnesses
