import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.PGFWitnessIR

namespace Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses

open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.PGFWitnessIR

def englishTelescopeSurface : String := "John sees the man with the telescope"
def englishTelescopeLanguage : String := "PaperAmbiguityEng"
def englishTelescopeParse1 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "see_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "man_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "with_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "telescope_N" []
            ]
          ]
        ]
      ]
    ]
  ]
def englishTelescopeAbstractNode1 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "john_PN" (FunctionSig.resultCategory FunctionSig.john_PN.type)
      ],
      .apply FunctionSig.AdvVP [
        .apply FunctionSig.ComplSlash [
          .apply FunctionSig.SlashV2a [
            .leaf "see_V2" (FunctionSig.resultCategory FunctionSig.see_V2.type)
          ],
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "man_N" (FunctionSig.resultCategory FunctionSig.man_N.type)
            ]
          ]
        ],
        .apply FunctionSig.PrepNP [
          .leaf "with_Prep" (FunctionSig.resultCategory FunctionSig.with_Prep.type),
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "telescope_N" (FunctionSig.resultCategory FunctionSig.telescope_N.type)
            ]
          ]
        ]
      ]
    ]
  ]
def englishTelescopeProb1 : Float := 10.397207260131836
def englishTelescopeParse2 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "see_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "man_N" []
            ],
            .node "PrepNP" [
              .node "with_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "telescope_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def englishTelescopeAbstractNode2 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "john_PN" (FunctionSig.resultCategory FunctionSig.john_PN.type)
      ],
      .apply FunctionSig.ComplSlash [
        .apply FunctionSig.SlashV2a [
          .leaf "see_V2" (FunctionSig.resultCategory FunctionSig.see_V2.type)
        ],
        .apply FunctionSig.DetCN [
          .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
          .apply FunctionSig.AdvCN [
            .apply FunctionSig.UseN [
              .leaf "man_N" (FunctionSig.resultCategory FunctionSig.man_N.type)
            ],
            .apply FunctionSig.PrepNP [
              .leaf "with_Prep" (FunctionSig.resultCategory FunctionSig.with_Prep.type),
              .apply FunctionSig.DetCN [
                .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
                .apply FunctionSig.UseN [
                  .leaf "telescope_N" (FunctionSig.resultCategory FunctionSig.telescope_N.type)
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def englishTelescopeProb2 : Float := 10.397207260131836
def englishTelescopeParses : List ExportedTree := [englishTelescopeParse1, englishTelescopeParse2]
def englishTelescopeRecovered : List AbstractNode := [englishTelescopeAbstractNode1, englishTelescopeAbstractNode2]

def englishAnnaSurface : String := "Anna dresses the baby in the crib"
def englishAnnaLanguage : String := "PaperAmbiguityEng"
def englishAnnaParse1 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "dress_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "baby_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "in_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "crib_N" []
            ]
          ]
        ]
      ]
    ]
  ]
def englishAnnaAbstractNode1 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "anna_PN" (FunctionSig.resultCategory FunctionSig.anna_PN.type)
      ],
      .apply FunctionSig.AdvVP [
        .apply FunctionSig.ComplSlash [
          .apply FunctionSig.SlashV2a [
            .leaf "dress_V2" (FunctionSig.resultCategory FunctionSig.dress_V2.type)
          ],
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "baby_N" (FunctionSig.resultCategory FunctionSig.baby_N.type)
            ]
          ]
        ],
        .apply FunctionSig.PrepNP [
          .leaf "in_Prep" (FunctionSig.resultCategory FunctionSig.in_Prep.type),
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "crib_N" (FunctionSig.resultCategory FunctionSig.crib_N.type)
            ]
          ]
        ]
      ]
    ]
  ]
def englishAnnaProb1 : Float := 10.397207260131836
def englishAnnaParse2 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "dress_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "baby_N" []
            ],
            .node "PrepNP" [
              .node "in_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "crib_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def englishAnnaAbstractNode2 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "anna_PN" (FunctionSig.resultCategory FunctionSig.anna_PN.type)
      ],
      .apply FunctionSig.ComplSlash [
        .apply FunctionSig.SlashV2a [
          .leaf "dress_V2" (FunctionSig.resultCategory FunctionSig.dress_V2.type)
        ],
        .apply FunctionSig.DetCN [
          .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
          .apply FunctionSig.AdvCN [
            .apply FunctionSig.UseN [
              .leaf "baby_N" (FunctionSig.resultCategory FunctionSig.baby_N.type)
            ],
            .apply FunctionSig.PrepNP [
              .leaf "in_Prep" (FunctionSig.resultCategory FunctionSig.in_Prep.type),
              .apply FunctionSig.DetCN [
                .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
                .apply FunctionSig.UseN [
                  .leaf "crib_N" (FunctionSig.resultCategory FunctionSig.crib_N.type)
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def englishAnnaProb2 : Float := 10.397207260131836
def englishAnnaParses : List ExportedTree := [englishAnnaParse1, englishAnnaParse2]
def englishAnnaRecovered : List AbstractNode := [englishAnnaAbstractNode1, englishAnnaAbstractNode2]

def czechTelescopeSurface : String := "Jan vidí muže s teleskopem"
def czechTelescopeLanguage : String := "PaperAmbiguityCze"
def czechTelescopeParse1 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "see_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "man_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "with_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "telescope_N" []
            ]
          ]
        ]
      ]
    ]
  ]
def czechTelescopeAbstractNode1 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "john_PN" (FunctionSig.resultCategory FunctionSig.john_PN.type)
      ],
      .apply FunctionSig.AdvVP [
        .apply FunctionSig.ComplSlash [
          .apply FunctionSig.SlashV2a [
            .leaf "see_V2" (FunctionSig.resultCategory FunctionSig.see_V2.type)
          ],
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "man_N" (FunctionSig.resultCategory FunctionSig.man_N.type)
            ]
          ]
        ],
        .apply FunctionSig.PrepNP [
          .leaf "with_Prep" (FunctionSig.resultCategory FunctionSig.with_Prep.type),
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "telescope_N" (FunctionSig.resultCategory FunctionSig.telescope_N.type)
            ]
          ]
        ]
      ]
    ]
  ]
def czechTelescopeProb1 : Float := 10.397207260131836
def czechTelescopeParse2 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "john_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "see_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "man_N" []
            ],
            .node "PrepNP" [
              .node "with_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "telescope_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def czechTelescopeAbstractNode2 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "john_PN" (FunctionSig.resultCategory FunctionSig.john_PN.type)
      ],
      .apply FunctionSig.ComplSlash [
        .apply FunctionSig.SlashV2a [
          .leaf "see_V2" (FunctionSig.resultCategory FunctionSig.see_V2.type)
        ],
        .apply FunctionSig.DetCN [
          .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
          .apply FunctionSig.AdvCN [
            .apply FunctionSig.UseN [
              .leaf "man_N" (FunctionSig.resultCategory FunctionSig.man_N.type)
            ],
            .apply FunctionSig.PrepNP [
              .leaf "with_Prep" (FunctionSig.resultCategory FunctionSig.with_Prep.type),
              .apply FunctionSig.DetCN [
                .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
                .apply FunctionSig.UseN [
                  .leaf "telescope_N" (FunctionSig.resultCategory FunctionSig.telescope_N.type)
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def czechTelescopeProb2 : Float := 10.397207260131836
def czechTelescopeParses : List ExportedTree := [czechTelescopeParse1, czechTelescopeParse2]
def czechTelescopeRecovered : List AbstractNode := [czechTelescopeAbstractNode1, czechTelescopeAbstractNode2]

def czechAnnaSurface : String := "Anna obléká dítě v kolébkě"
def czechAnnaLanguage : String := "PaperAmbiguityCze"
def czechAnnaParse1 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "AdvVP" [
        .node "ComplSlash" [
          .node "SlashV2a" [
            .node "dress_V2" []
          ],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "baby_N" []
            ]
          ]
        ],
        .node "PrepNP" [
          .node "in_Prep" [],
          .node "DetCN" [
            .node "the_Det" [],
            .node "UseN" [
              .node "crib_N" []
            ]
          ]
        ]
      ]
    ]
  ]
def czechAnnaAbstractNode1 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "anna_PN" (FunctionSig.resultCategory FunctionSig.anna_PN.type)
      ],
      .apply FunctionSig.AdvVP [
        .apply FunctionSig.ComplSlash [
          .apply FunctionSig.SlashV2a [
            .leaf "dress_V2" (FunctionSig.resultCategory FunctionSig.dress_V2.type)
          ],
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "baby_N" (FunctionSig.resultCategory FunctionSig.baby_N.type)
            ]
          ]
        ],
        .apply FunctionSig.PrepNP [
          .leaf "in_Prep" (FunctionSig.resultCategory FunctionSig.in_Prep.type),
          .apply FunctionSig.DetCN [
            .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
            .apply FunctionSig.UseN [
              .leaf "crib_N" (FunctionSig.resultCategory FunctionSig.crib_N.type)
            ]
          ]
        ]
      ]
    ]
  ]
def czechAnnaProb1 : Float := 10.397207260131836
def czechAnnaParse2 : ExportedTree :=
  .node "UseCl" [
    .node "TTAnt" [
      .node "TPres" [],
      .node "ASimul" []
    ],
    .node "PPos" [],
    .node "PredVP" [
      .node "UsePN" [
        .node "anna_PN" []
      ],
      .node "ComplSlash" [
        .node "SlashV2a" [
          .node "dress_V2" []
        ],
        .node "DetCN" [
          .node "the_Det" [],
          .node "AdvCN" [
            .node "UseN" [
              .node "baby_N" []
            ],
            .node "PrepNP" [
              .node "in_Prep" [],
              .node "DetCN" [
                .node "the_Det" [],
                .node "UseN" [
                  .node "crib_N" []
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def czechAnnaAbstractNode2 : AbstractNode :=
  .apply FunctionSig.UseCl [
    .apply FunctionSig.TTAnt [
      .leaf "TPres" (FunctionSig.resultCategory FunctionSig.TPres.type),
      .leaf "ASimul" (FunctionSig.resultCategory FunctionSig.ASimul.type)
    ],
    .leaf "PPos" (FunctionSig.resultCategory FunctionSig.PPos.type),
    .apply FunctionSig.PredVP [
      .apply FunctionSig.UsePN [
        .leaf "anna_PN" (FunctionSig.resultCategory FunctionSig.anna_PN.type)
      ],
      .apply FunctionSig.ComplSlash [
        .apply FunctionSig.SlashV2a [
          .leaf "dress_V2" (FunctionSig.resultCategory FunctionSig.dress_V2.type)
        ],
        .apply FunctionSig.DetCN [
          .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
          .apply FunctionSig.AdvCN [
            .apply FunctionSig.UseN [
              .leaf "baby_N" (FunctionSig.resultCategory FunctionSig.baby_N.type)
            ],
            .apply FunctionSig.PrepNP [
              .leaf "in_Prep" (FunctionSig.resultCategory FunctionSig.in_Prep.type),
              .apply FunctionSig.DetCN [
                .leaf "the_Det" (FunctionSig.resultCategory FunctionSig.the_Det.type),
                .apply FunctionSig.UseN [
                  .leaf "crib_N" (FunctionSig.resultCategory FunctionSig.crib_N.type)
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
def czechAnnaProb2 : Float := 10.397207260131836
def czechAnnaParses : List ExportedTree := [czechAnnaParse1, czechAnnaParse2]
def czechAnnaRecovered : List AbstractNode := [czechAnnaAbstractNode1, czechAnnaAbstractNode2]

def allWitnessParses : List (String × String × String × List ExportedTree) := [
  ("englishTelescope", englishTelescopeLanguage, englishTelescopeSurface, englishTelescopeParses),
  ("englishAnna", englishAnnaLanguage, englishAnnaSurface, englishAnnaParses),
  ("czechTelescope", czechTelescopeLanguage, czechTelescopeSurface, czechTelescopeParses),
  ("czechAnna", czechAnnaLanguage, czechAnnaSurface, czechAnnaParses)
]

def usedFunctions : List String := ["ASimul", "AdvCN", "AdvVP", "ComplSlash", "DetCN", "PPos", "PredVP", "PrepNP", "SlashV2a", "TPres", "TTAnt", "UseCl", "UseN", "UsePN", "anna_PN", "baby_N", "crib_N", "dress_V2", "in_Prep", "john_PN", "man_N", "see_V2", "telescope_N", "the_Det", "with_Prep"]

def grammarName : String := "PaperAmbiguity"

end Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
