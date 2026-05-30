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

def usedFunctions : List String := ["ASimul", "AdVVPSlash", "AdjAsNP", "AdjCN", "AdvCN", "AdvRNP", "AdvVPSlash", "ApposCN", "BaseCN", "BaseCNN", "CompAP", "CompCN", "CompNP", "ComplSlashPartLast", "ComplVPI2", "ComplVPIVV", "ComplVPS2", "ConjCN", "DefArt", "DetCN", "DetCNN", "DetDAP", "DetQuant", "GenModNP", "GerundNP", "IdRP", "ImpersCl", "IndefArt", "MassNP", "MkVPI", "MkVPI2", "MkVPS", "MkVPS2", "NoPConj", "NoVoc", "NumCard", "NumNumeral", "NumPl", "NumSg", "PNeg", "PPos", "PartNP", "PassAgentVPSlash", "PassVPSlash", "PastPartAP", "PastPartAgentAP", "PhrUtt", "PositA", "PossNP", "PredVPS", "PredetNP", "PrepNP", "ReflPoss", "ReflVPS2", "RelCN", "RelVPS", "Slash3V3", "SlashV2a", "SlashVV", "TPres", "TTAnt", "TimeNP", "UseCl", "UseComp", "UseComp_estar", "UseComp_ser", "UseDAP", "UseDAPFem", "UseDAPMasc", "UseLN", "UseN", "UsePN", "UsePron", "UseV", "UttNP", "UttS", "UttVPShort", "VPSlashPrep", "act_3_N", "against_Prep", "age_2_N", "age_3_N", "all_1_Predet", "all_2_Predet", "amendment_2_N", "america_1_LN", "and_Conj", "anySg_2_Det", "army_3_N", "as_Prep", "attain_3_V2", "bill_9_N", "chiefMasc_3_N", "choose_2_V2", "commanderFem_2_N", "compose_4_V2", "congress_2_N", "congress_3_N", "consist_4_V", "constitution_1_N", "constitution_PN", "convention_2_N", "credit_9_N", "declare_6_V2", "determine_7_V2", "each_Det", "establish_4_V2", "establishment_4_N", "ever_1_AdV", "every_Det", "executive_A", "faith_1_N", "for_Prep", "full_2_A", "gen_Quant", "give_22_V2", "grant_1_V2", "grant_7_V2", "habeas_corpus_2_N", "have_15_V2", "have_8_V2", "he_Pron", "herein_Adv", "house_4_N", "house_6_N", "impeachment_N", "in_1_Prep", "in_2_Prep", "in_4_Prep", "in_5_Prep", "it_Pron", "judicial_1_A", "justiceFem_3_N", "land_9_N", "law_1_N", "law_3_N", "legislative_1_A", "levy_1_V2", "may_1_VV", "memberMasc_1_N", "n2", "n3", "n5", "n9", "navy_3_N", "no_Quant", "nobility_2_N", "num", "of_2_Prep", "office_3_N", "only_7_Adv", "or_Conj", "other_4_A", "people_4_N", "person_2_N", "pot0", "pot0as1", "pot1", "pot1as2", "pot2as3", "pot3as4", "pot4as5", "power_10_N", "power_2_N", "power_7_N", "present_to_V3", "presidentFem_1_N", "presidentMasc_2_N", "presidentMasc_6_N", "privilege_2_N", "proceedings_1_N", "proceedings_2_N", "propose_4_V2", "public_1_A", "qualification_3_N", "ratification_N", "record_2_N", "religious_4_A", "representativeFem_1_N", "representativeMasc_2_N", "require_1_V2", "rule_3_N", "second_10_N", "senate_2_N", "several_Card", "shall_VV", "sign_2_V2", "sole_1_A", "state_1_N", "state_4_N", "state_8_N", "sufficient_A", "supreme_2_A", "suspend_5_V2", "test_4_N", "theyFem_Pron", "this_Quant", "timeunitAdv", "title_2_N", "to_1_Prep", "to_4_Prep", "to_5_Prep", "treason_2_N", "trust_3_N", "try_3_V2", "under_Prep", "united_states_LN", "vest_2_V2", "vest_4_V2", "war_4_N", "writ_N", "year_1_N", "year_Timeunit"]

end Mettapedia.Languages.GF.USConstitution.Generated.Witnesses
