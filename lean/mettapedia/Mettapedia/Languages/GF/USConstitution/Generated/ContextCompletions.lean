-- AUTO-GENERATED from ParseEng PGF context-completion witnesses. Do not edit.

import Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

namespace Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions

open Mettapedia.Languages.GF.PGFWitnessIR
open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

inductive CorrectionKind where
  | exactSubfragment
  | contextCompletion
  deriving Repr, DecidableEq

inductive CorrectionId where
  | articleISection3SenateImpeachmentsExactSubfragment1
  | articleISection3SenateImpeachmentsContextCompletion1
  | articleISection8DeclareWarContextCompletion1
  | articleVProposeAmendmentsContextCompletion1
  deriving Repr, DecidableEq

def sourceHash : String := "11d54d0644a29fc587e839c6710ddd362cd2c0ad45f693487d0ce1840bed4d34"
def correctionLogHash : String := "88b0a071ffad46e34de1d59de6cb432f38098d24b459aa7683cd97566bc65810"
def allCorrectionIds : List CorrectionId := [.articleISection3SenateImpeachmentsExactSubfragment1, .articleISection3SenateImpeachmentsContextCompletion1, .articleISection8DeclareWarContextCompletion1, .articleVProposeAmendmentsContextCompletion1]

def sourceClause : CorrectionId → ClauseId
  | .articleISection3SenateImpeachmentsExactSubfragment1 => .articleISection3SenateImpeachments
  | .articleISection3SenateImpeachmentsContextCompletion1 => .articleISection3SenateImpeachments
  | .articleISection8DeclareWarContextCompletion1 => .articleISection8DeclareWar
  | .articleVProposeAmendmentsContextCompletion1 => .articleVProposeAmendments

def correctionKind : CorrectionId → CorrectionKind
  | .articleISection3SenateImpeachmentsExactSubfragment1 => .exactSubfragment
  | .articleISection3SenateImpeachmentsContextCompletion1 => .contextCompletion
  | .articleISection8DeclareWarContextCompletion1 => .contextCompletion
  | .articleVProposeAmendmentsContextCompletion1 => .contextCompletion

def correctionParserInput : CorrectionId → String
  | .articleISection3SenateImpeachmentsExactSubfragment1 => "The Senate shall have the sole Power"
  | .articleISection3SenateImpeachmentsContextCompletion1 => "The Senate shall try all Impeachments"
  | .articleISection8DeclareWarContextCompletion1 => "Congress may declare War"
  | .articleVProposeAmendmentsContextCompletion1 => "The Congress shall propose Amendments to this Constitution"

def confidencePermille : CorrectionId → Nat
  | .articleISection3SenateImpeachmentsExactSubfragment1 => 990
  | .articleISection3SenateImpeachmentsContextCompletion1 => 930
  | .articleISection8DeclareWarContextCompletion1 => 760
  | .articleVProposeAmendmentsContextCompletion1 => 910

def correctionJustification : CorrectionId → String
  | .articleISection3SenateImpeachmentsExactSubfragment1 => "Exact contiguous subfragment of the original clause; ParseEng parses it without meta holes."
  | .articleISection3SenateImpeachmentsContextCompletion1 => "The controlled infinitive 'to try all Impeachments' is governed by the subject 'The Senate' in the same clause. This preserves the actor/action relation but drops the explicit 'sole Power' modality."
  | .articleISection8DeclareWarContextCompletion1 => "Article I, Section 8 introduces Congress's powers, and 'To declare War' is one item in that list. 'May' captures power better than duty, but it is not the literal modal text."
  | .articleVProposeAmendmentsContextCompletion1 => "The subject 'The Congress' is explicit in the same Article V sentence. This completion parses without meta holes, but omits the condition 'whenever two thirds of both Houses shall deem it necessary'."

def correctionSource : CorrectionId → String
  | .articleISection3SenateImpeachmentsExactSubfragment1 => "Original Article I, Section 3 wording."
  | .articleISection3SenateImpeachmentsContextCompletion1 => "Original Article I, Section 3 wording; tested with ParseEng and no meta hole."
  | .articleISection8DeclareWarContextCompletion1 => "Article I, Section 8 power-list context; tested with ParseEng and no meta hole."
  | .articleVProposeAmendmentsContextCompletion1 => "Original Article V wording; tested with ParseEng and no meta hole."

def articleISection3SenateImpeachmentsExactSubfragment1Parse1 : ExportedTree :=
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
            .node "senate_2_N" []
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
              .node "SlashV2a" [
                .node "have_15_V2" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "DefArt" [],
              .node "NumSg" []
            ],
            .node "AdjCN" [
              .node "PositA" [
                .node "sole_1_A" []
              ],
              .node "UseN" [
                .node "power_7_N" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection3SenateImpeachmentsContextCompletion1Parse1 : ExportedTree :=
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
            .node "senate_2_N" []
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
              .node "SlashV2a" [
                .node "try_3_V2" []
              ]
            ]
          ],
          .node "PredetNP" [
            .node "all_2_Predet" [],
            .node "DetCN" [
              .node "DetQuant" [
                .node "gen_Quant" [],
                .node "NumPl" []
              ],
              .node "UseN" [
                .node "impeachment_N" []
              ]
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleISection8DeclareWarContextCompletion1Parse1 : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "MassNP" [
          .node "UseN" [
            .node "congress_3_N" []
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
              .node "may_1_VV" [],
              .node "ASimul" [],
              .node "PPos" [],
              .node "SlashV2a" [
                .node "declare_6_V2" []
              ]
            ]
          ],
          .node "MassNP" [
            .node "UseN" [
              .node "war_4_N" []
            ]
          ]
        ]
      ]
    ],
    .node "NoVoc" []
  ]
def articleVProposeAmendmentsContextCompletion1Parse1 : ExportedTree :=
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
            .node "congress_3_N" []
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
              .node "SlashV2a" [
                .node "propose_4_V2" []
              ]
            ]
          ],
          .node "DetCN" [
            .node "DetQuant" [
              .node "IndefArt" [],
              .node "NumPl" []
            ],
            .node "ApposCN" [
              .node "AdvCN" [
                .node "UseN" [
                  .node "amendment_2_N" []
                ],
                .node "PrepNP" [
                  .node "to_1_Prep" [],
                  .node "UseDAP" [
                    .node "DetDAP" [
                      .node "DetQuant" [
                        .node "this_Quant" [],
                        .node "NumSg" []
                      ]
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

def correctionParses : CorrectionId → List ExportedTree
  | .articleISection3SenateImpeachmentsExactSubfragment1 => [articleISection3SenateImpeachmentsExactSubfragment1Parse1]
  | .articleISection3SenateImpeachmentsContextCompletion1 => [articleISection3SenateImpeachmentsContextCompletion1Parse1]
  | .articleISection8DeclareWarContextCompletion1 => [articleISection8DeclareWarContextCompletion1Parse1]
  | .articleVProposeAmendmentsContextCompletion1 => [articleVProposeAmendmentsContextCompletion1Parse1]

def rawParseCount : CorrectionId → Nat
  | .articleISection3SenateImpeachmentsExactSubfragment1 => 1
  | .articleISection3SenateImpeachmentsContextCompletion1 => 1
  | .articleISection8DeclareWarContextCompletion1 => 1
  | .articleVProposeAmendmentsContextCompletion1 => 1

def acceptedParseCount : CorrectionId → Nat
  | .articleISection3SenateImpeachmentsExactSubfragment1 => 1
  | .articleISection3SenateImpeachmentsContextCompletion1 => 1
  | .articleISection8DeclareWarContextCompletion1 => 1
  | .articleVProposeAmendmentsContextCompletion1 => 1

def correctionsForClause : ClauseId → List CorrectionId
  | .preambleEstablishJustice => []
  | .articleISection1Vesting => []
  | .articleISection2HouseComposition => []
  | .articleISection2RepresentativeAge => []
  | .articleISection3SenateImpeachments => [.articleISection3SenateImpeachmentsExactSubfragment1, .articleISection3SenateImpeachmentsContextCompletion1]
  | .articleISection5Rules => []
  | .articleISection7EveryBillPresented => []
  | .articleISection7PresidentSigns => []
  | .articleISection7BecomesLaw => []
  | .articleISection8DeclareWar => [.articleISection8DeclareWarContextCompletion1]
  | .articleISection9Habeas => []
  | .articleISection9NoTitleOfNobility => []
  | .articleIISection1ExecutiveVesting => []
  | .articleIISection1PresidentAge => []
  | .articleIISection2CommanderInChief => []
  | .articleIIISection3Treason => []
  | .articleIVSection1FullFaithCredit => []
  | .articleVProposeAmendments => [.articleVProposeAmendmentsContextCompletion1]
  | .articleVISupremacy => []
  | .articleVINoReligiousTest => []
  | .articleVIIRatification => []

end Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions
