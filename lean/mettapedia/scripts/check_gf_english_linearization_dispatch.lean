import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Abstract.FunctionSig
open Mettapedia.Languages.GF.Abstract.AbstractNode
open Mettapedia.Languages.GF.English.Linearization

private def lin (node : AbstractNode) : String :=
  linearizeTree {} node .Nom .Sg

private def assertEq (label actual expected : String) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"{label} failed\nexpected: {expected}\nactual:   {actual}"

private def assertContains (label actual needle : String) : IO Unit := do
  if !(actual.contains needle) then
    throw <| IO.userError s!"{label} failed\nexpected substring: {needle}\nactual: {actual}"

private def tDetQuant : AbstractNode :=
  apply DetQuant [
    leaf "this_Quant" Category.Quant,
    apply NumPl []
  ]

private def tDetQuantOrd : AbstractNode :=
  apply DetQuantOrd [
    apply DefArt [],
    apply NumSg [],
    apply OrdSuperl [leaf "important_A" Category.A]
  ]

private def tSlash2V3 : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply Slash2V3 [leaf "give_V3" Category.V3, leaf "she_Pron" Category.Pron],
        leaf "it_Pron" Category.Pron
      ]
    ]
  ]

private def tSlash3V3 : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply Slash3V3 [leaf "give_V3" Category.V3, leaf "she_Pron" Category.Pron],
        leaf "it_Pron" Category.Pron
      ]
    ]
  ]

private def tSlashV2V : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply SlashV2V [leaf "beg_V2V" Category.V2V, apply UseV [leaf "run_V" Category.V]],
        leaf "she_Pron" Category.Pron
      ]
    ]
  ]

private def tSlashV2S : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply SlashV2S [
          leaf "answer_V2S" Category.V2S,
          apply UseCl [
            apply TTAnt [apply TPres [], apply ASimul []],
            apply PPos [],
            apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
          ]
        ],
        leaf "it_Pron" Category.Pron
      ]
    ]
  ]

private def tSlashV2Q : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply SlashV2Q [
          leaf "ask_V2Q" Category.V2Q,
          apply UseQCl [
            apply TTAnt [apply TPres [], apply ASimul []],
            apply PPos [],
            apply QuestCl [apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]]
          ]
        ],
        leaf "it_Pron" Category.Pron
      ]
    ]
  ]

private def tSlashV2A : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplSlash [
        apply SlashV2A [leaf "paint_V2A" Category.V2A, apply PositA [leaf "beautiful_A" Category.A]],
        leaf "she_Pron" Category.Pron
      ]
    ]
  ]

private def tComplVV : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplVV [leaf "can_VV" Category.VV, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tComplVS : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplVS [
        leaf "know_VS" Category.VS,
        apply UseCl [
          apply TTAnt [apply TPres [], apply ASimul []],
          apply PPos [],
          apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
        ]
      ]
    ]
  ]

private def tComplVQ : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplVQ [
        leaf "know_VQ" Category.VQ,
        apply UseQCl [
          apply TTAnt [apply TPres [], apply ASimul []],
          apply PPos [],
          apply QuestCl [apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]]
        ]
      ]
    ]
  ]

private def tComplVA : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "he_Pron" Category.Pron,
      apply ComplVA [leaf "become_VA" Category.VA, apply PositA [leaf "beautiful_A" Category.A]]
    ]
  ]

private def tPassV2 : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "she_Pron" Category.Pron,
      apply PassV2 [leaf "lookAt_V2" Category.V2]
    ]
  ]

private def tNumeralCard : AbstractNode :=
  apply NumCard [
    apply NumNumeral [
      apply num_f [
        apply pot3plus [
          apply pot2 [apply pot0 [apply n2_f []]],
          apply pot1as2 [apply pot1plus [apply n3_f [], apply pot0 [apply n4_f []]]]
        ]
      ]
    ]
  ]

private def tDecimalCard : AbstractNode :=
  apply NumCard [
    apply NumDecimal [
      apply IFrac [
        apply PosDecimal [apply IIDig [apply D_1 [], apply IDig_f [apply D_2 []]]],
        apply D_5 []
      ]
    ]
  ]

private def tOrdinalFromNumeral : AbstractNode :=
  apply OrdNumeral [
    apply NumNumeral [
      apply num_f [apply pot1plus [apply n2_f [], apply pot0 [apply n3_f []]]]
    ]
  ]

private def tAdvNP : AbstractNode :=
  apply AdvNP [leaf "he_Pron" Category.Pron, leaf "here_Adv" Category.Adv]

private def tQuestIAdv : AbstractNode :=
  apply UseQCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply QuestIAdv [
      leaf "why_IAdv" Category.IAdv,
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tRelCl : AbstractNode :=
  apply UseRCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply RelCl_f [apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]]
  ]

private def tRelSlash : AbstractNode :=
  apply UseRCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply RelSlash [
      apply IdRP [],
      apply SlashVP [leaf "he_Pron" Category.Pron, apply SlashV2a [leaf "lookAt_V2" Category.V2]]
    ]
  ]

private def tQuestQVP : AbstractNode :=
  apply UseQCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply QuestQVP [
      leaf "who_IP" Category.IP,
      apply AdvQVP [apply UseV [leaf "run_V" Category.V], leaf "where_IAdv" Category.IAdv]
    ]
  ]

private def tIdetCN : AbstractNode :=
  apply IdetCN [leaf "how8many_IDet" Category.IDet, leaf "cat_N" Category.CN]

private def tIdetIP : AbstractNode :=
  apply IdetIP [leaf "how8many_IDet" Category.IDet]

private def tPrepIP : AbstractNode :=
  apply PrepIP [leaf "in_Prep" Category.Prep, leaf "whatSg_IP" Category.IP]

private def tAdvS : AbstractNode :=
  apply AdvS [
    leaf "here_Adv" Category.Adv,
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tEmbedS : AbstractNode :=
  apply EmbedS [
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tUttS : AbstractNode :=
  apply UttS [
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tUttImpNeg : AbstractNode :=
  apply UttImpSg [
    apply PNeg [],
    apply ImpVP [apply UseV [leaf "run_V" Category.V]]
  ]

private def tPhrUttSimple : AbstractNode :=
  apply PhrUtt [
    apply NoPConj [],
    apply UttNP [leaf "he_Pron" Category.Pron],
    apply NoVoc []
  ]

private def tConjAdv : AbstractNode :=
  apply ConjAdv [
    leaf "and_Conj" Category.Conj,
    apply BaseAdv [leaf "here_Adv" Category.Adv, leaf "there_Adv" Category.Adv]
  ]

private def tConjIAdv : AbstractNode :=
  apply ConjIAdv [
    leaf "and_Conj" Category.Conj,
    apply BaseIAdv [leaf "why_IAdv" Category.IAdv, leaf "where_IAdv" Category.IAdv]
  ]

private def tConjDet : AbstractNode :=
  apply ConjDet [
    leaf "and_Conj" Category.Conj,
    apply BaseDAP [leaf "this_DAP" Category.DAP, leaf "that_DAP" Category.DAP]
  ]

private def tConjRS : AbstractNode :=
  apply ConjRS [
    leaf "and_Conj" Category.Conj,
    apply BaseRS [
      apply UseRCl [
        apply TTAnt [apply TPres [], apply ASimul []],
        apply PPos [],
        apply RelCl_f [apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]]
      ],
      apply UseRCl [
        apply TTAnt [apply TPres [], apply ASimul []],
        apply PPos [],
        apply RelCl_f [apply PredVP [leaf "he_Pron" Category.Pron, apply UseV [leaf "walk_V" Category.V]]]
      ]
    ]
  ]

private def tComplN2 : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply ComplN2 [leaf "owner_N2" Category.N2, leaf "he_Pron" Category.Pron]
  ]

private def tUseN2 : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply UseN2 [leaf "owner_N2" Category.N2]
  ]

private def tUse2N3 : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply ComplN2 [
      apply Use2N3 [leaf "distance_N3" Category.N3],
      leaf "it_Pron" Category.Pron
    ]
  ]

private def tSentCN : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply SentCN [
      apply UseN [leaf "cat_N" Category.N],
      apply EmbedS [
        apply UseCl [
          apply TTAnt [apply TPres [], apply ASimul []],
          apply PPos [],
          apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
        ]
      ]
    ]
  ]

private def tApposCN : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply ApposCN [apply UseN [leaf "cat_N" Category.N], leaf "he_Pron" Category.Pron]
  ]

private def tPossNP : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply PossNP [apply UseN [leaf "cat_N" Category.N], leaf "he_Pron" Category.Pron]
  ]

private def tPartNP : AbstractNode :=
  apply DetCN [
    apply DefArt [],
    apply PartNP [apply UseN [leaf "cat_N" Category.N], leaf "he_Pron" Category.Pron]
  ]

private def tAdjDAP : AbstractNode :=
  apply AdjDAP [leaf "this_DAP" Category.DAP, apply PositA [leaf "beautiful_A" Category.A]]

private def tDetDAP : AbstractNode :=
  apply DetDAP [apply DefArt []]

private def tComplA2 : AbstractNode :=
  apply ComplA2 [leaf "close_A2" Category.A2, leaf "he_Pron" Category.Pron]

private def tReflA2 : AbstractNode :=
  apply ReflA2 [leaf "close_A2" Category.A2]

private def tUseA2 : AbstractNode :=
  apply UseA2 [leaf "close_A2" Category.A2]

private def tUseComparA : AbstractNode :=
  apply UseComparA [leaf "beautiful_A" Category.A]

private def tCAdvAP : AbstractNode :=
  apply CAdvAP [
    leaf "as_CAdv" Category.CAdv,
    apply PositA [leaf "beautiful_A" Category.A],
    leaf "he_Pron" Category.Pron
  ]

private def tAdjOrd : AbstractNode :=
  apply AdjOrd [apply OrdNumeral [apply NumNumeral [apply num_f [apply pot0 [apply n3_f []]]]]]

private def tSentAP : AbstractNode :=
  apply SentAP [
    apply PositA [leaf "beautiful_A" Category.A],
    apply EmbedS [
      apply UseCl [
        apply TTAnt [apply TPres [], apply ASimul []],
        apply PPos [],
        apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
      ]
    ]
  ]

private def tAdAP : AbstractNode :=
  apply AdAP [leaf "very_AdA" Category.AdA, apply PositA [leaf "beautiful_A" Category.A]]

private def tAdvAP : AbstractNode :=
  apply AdvAP [apply PositA [leaf "beautiful_A" Category.A], leaf "quite_Adv" Category.Adv]

private def tFunRP : AbstractNode :=
  apply UseRCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply RelVP [
      apply FunRP [leaf "with_Prep" Category.Prep, leaf "he_Pron" Category.Pron, apply IdRP []],
      apply UseV [leaf "run_V" Category.V]
    ]
  ]

private def tPositAdvAdj : AbstractNode :=
  apply PositAdvAdj [leaf "beautiful_A" Category.A]

private def tComparAdvAdj : AbstractNode :=
  apply ComparAdvAdj [leaf "more_CAdv" Category.CAdv, leaf "beautiful_A" Category.A, leaf "he_Pron" Category.Pron]

private def tComparAdvAdjS : AbstractNode :=
  apply ComparAdvAdjS [
    leaf "more_CAdv" Category.CAdv,
    leaf "beautiful_A" Category.A,
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tAdAdv : AbstractNode :=
  apply AdAdv [leaf "very_AdA" Category.AdA, leaf "here_Adv" Category.Adv]

private def tPositAdAAdj : AbstractNode :=
  apply PositAdAAdj [leaf "beautiful_A" Category.A]

private def tSubjS : AbstractNode :=
  apply SubjS [
    leaf "if_Subj" Category.Subj,
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tAdnCAdv : AbstractNode :=
  apply AdnCAdv [leaf "as_CAdv" Category.CAdv]

private def tTextFullStop : AbstractNode :=
  apply TFullStop [apply PhrUtt [apply NoPConj [], apply UttNP [leaf "he_Pron" Category.Pron], apply NoVoc []], apply TEmpty []]

private def tTextQuestMark : AbstractNode :=
  apply TQuestMark [apply PhrUtt [apply NoPConj [], apply UttNP [leaf "he_Pron" Category.Pron], apply NoVoc []], apply TEmpty []]

private def tTextExclMark : AbstractNode :=
  apply TExclMark [apply PhrUtt [apply NoPConj [], apply UttNP [leaf "he_Pron" Category.Pron], apply NoVoc []], apply TEmpty []]

private def tPredetAll : AbstractNode :=
  apply PredetNP [leaf "all_Predet" Category.Predet, leaf "they_Pron" Category.Pron]

private def tNoUtt : AbstractNode := apply no_Utt []
private def tYesUtt : AbstractNode := apply yes_Utt []
private def tLanguageTitleUtt : AbstractNode := apply language_title_Utt []

private def tImpersCl : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply ImpersCl [apply UseV [leaf "run_V" Category.V]]
  ]

private def tGenericCl : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply GenericCl [apply UseV [leaf "run_V" Category.V]]
  ]

private def tExistNP : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply ExistNP [leaf "he_Pron" Category.Pron]
  ]

private def tExistIP : AbstractNode :=
  apply UseQCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply ExistIP [leaf "whatSg_IP" Category.IP]
  ]

private def tProgrVP : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [leaf "she_Pron" Category.Pron, apply ProgrVP [apply UseV [leaf "run_V" Category.V]]]
  ]

private def tImpPl1 : AbstractNode :=
  apply ImpPl1 [apply UseV [leaf "run_V" Category.V]]

private def tImpP3 : AbstractNode :=
  apply ImpP3 [leaf "he_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]

private def tSelfNP : AbstractNode :=
  apply UttNP [apply SelfNP [leaf "he_Pron" Category.Pron]]

private def tICompAP : AbstractNode :=
  apply ICompAP [apply PositA [leaf "beautiful_A" Category.A]]

private def tExistS : AbstractNode :=
  apply ExistS [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    leaf "he_Pron" Category.Pron
  ]

private def tPiedPipingQuestSlash : AbstractNode :=
  apply UseQCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PiedPipingQuestSlash [
      leaf "whatSg_IP" Category.IP,
      apply SlashPrep [
        apply PredVP [leaf "he_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]],
        leaf "in_Prep" Category.Prep
      ]
    ]
  ]

private def tPiedPipingRelSlash : AbstractNode :=
  apply UseRCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PiedPipingRelSlash [
      apply IdRP [],
      apply SlashPrep [
        apply PredVP [leaf "he_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]],
        leaf "in_Prep" Category.Prep
      ]
    ]
  ]

private def tEmptyRelSlash : AbstractNode :=
  apply UseRCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply EmptyRelSlash [
      apply SlashPrep [
        apply PredVP [leaf "he_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]],
        leaf "in_Prep" Category.Prep
      ]
    ]
  ]

private def tFocusAdv : AbstractNode :=
  apply FocusAdv [
    leaf "here_Adv" Category.Adv,
    apply UseCl [
      apply TTAnt [apply TPres [], apply ASimul []],
      apply PPos [],
      apply PredVP [leaf "she_Pron" Category.Pron, apply UseV [leaf "run_V" Category.V]]
    ]
  ]

private def tPassVPSlash : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [leaf "she_Pron" Category.Pron, apply PassVPSlash [apply SlashV2a [leaf "lookAt_V2" Category.V2]]]
  ]

private def tNominalizeVPSlashNP : AbstractNode :=
  apply UttNP [
    apply NominalizeVPSlashNP [
      apply SlashV2a [leaf "lookAt_V2" Category.V2],
      leaf "he_Pron" Category.Pron
    ]
  ]

private def tMkVPS : AbstractNode :=
  apply MkVPS [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply UseV [leaf "run_V" Category.V]
  ]

private def tConjVPS2 : AbstractNode :=
  apply ConjVPS [
    leaf "and_Conj" Category.Conj,
    apply BaseVPS [
      tMkVPS,
      apply MkVPS [
        apply TTAnt [apply TPres [], apply ASimul []],
        apply PPos [],
        apply UseV [leaf "walk_V" Category.V]
      ]
    ]
  ]

private def tPredVPS2 : AbstractNode :=
  apply PredVPS [leaf "she_Pron" Category.Pron, tMkVPS]

private def tQuestVPS2 : AbstractNode :=
  apply QuestVPS [leaf "whatSg_IP" Category.IP, tMkVPS]

private def tMkVPI : AbstractNode :=
  apply MkVPI [apply UseV [leaf "run_V" Category.V]]

private def tConjVPI2 : AbstractNode :=
  apply ConjVPI [
    leaf "and_Conj" Category.Conj,
    apply BaseVPI [
      tMkVPI,
      apply MkVPI [apply UseV [leaf "walk_V" Category.V]]
    ]
  ]

private def tComplVPIVV2 : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [leaf "he_Pron" Category.Pron, apply ComplVPIVV [leaf "can_VV" Category.VV, tMkVPI]]
  ]

private def tMkVPS2 : AbstractNode :=
  apply MkVPS2 [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply SlashV2a [leaf "lookAt_V2" Category.V2]
  ]

private def tConjComp2 : AbstractNode :=
  apply UseCl [
    apply TTAnt [apply TPres [], apply ASimul []],
    apply PPos [],
    apply PredVP [
      leaf "she_Pron" Category.Pron,
      apply UseComp [
        apply ConjComp [
          leaf "and_Conj" Category.Conj,
          apply BaseComp [
            apply CompNP [leaf "he_Pron" Category.Pron],
            apply CompAP [apply PositA [leaf "beautiful_A" Category.A]]
          ]
        ]
      ]
    ]
  ]

private def tConjImp2 : AbstractNode :=
  apply UttImpSg [
    apply PPos [],
    apply ConjImp [
      leaf "and_Conj" Category.Conj,
      apply BaseImp [
        apply ImpVP [apply UseV [leaf "run_V" Category.V]],
        apply AdvImp [leaf "here_Adv" Category.Adv, apply ImpVP [apply UseV [leaf "walk_V" Category.V]]]
      ]
    ]
  ]

private def tSymbNum2 : AbstractNode :=
  apply SymbNum [apply MkSymb [leaf "alpha" (Category.base "String")]]

private def tSymbOrd2 : AbstractNode :=
  apply SymbOrd [apply MkSymb [leaf "alpha" (Category.base "String")]]

private def tSymbPN2 : AbstractNode :=
  apply UsePN [apply SymbPN [apply MkSymb [leaf "alpha" (Category.base "String")]]]

private def tIntPN2 : AbstractNode :=
  apply UsePN [apply IntPN [leaf "42" (Category.base "Int")]]

private def tFloatPN2 : AbstractNode :=
  apply UsePN [apply FloatPN [leaf "3.14" (Category.base "Float")]]

private def tCNNumNP2 : AbstractNode :=
  apply UttNP [
    apply CNNumNP [
      apply UseN [leaf "cat_N" Category.N],
      apply NumCard [apply NumNumeral [apply num_f [apply pot0 [apply n2_f []]]]]
    ]
  ]

private def tCNSymbNP2 : AbstractNode :=
  apply UttNP [
    apply CNSymbNP [
      apply DefArt [],
      apply UseN [leaf "cat_N" Category.N],
      apply BaseSymb [
        apply MkSymb [leaf "alpha" (Category.base "String")],
        apply MkSymb [leaf "beta" (Category.base "String")]
      ]
    ]
  ]

private def tSymbS2 : AbstractNode :=
  apply SymbS [apply MkSymb [leaf "alpha" (Category.base "String")]]

private def tNegNPBucketFallback : AbstractNode :=
  apply RelNP [leaf "cat_N" Category.N, leaf "here_Adv" Category.Adv]

private def tNegVPBucketFallback : AbstractNode :=
  apply SlashVV [leaf "he_Pron" Category.Pron, leaf "here_Adv" Category.Adv]

private def tNegQClBucketFallback : AbstractNode :=
  apply QuestVP [leaf "cat_N" Category.N, leaf "dog_N" Category.N]


def main : IO Unit := do
  assertEq "DetQuant" (lin tDetQuant) "these"
  assertEq "DetQuantOrd" (lin tDetQuantOrd) "the most important"
  assertEq "Slash2V3" (lin tSlash2V3) "he gives her to it"
  assertEq "Slash3V3" (lin tSlash3V3) "he gives it to her"
  assertEq "SlashV2V" (lin tSlashV2V) "he begs her to run"
  assertEq "SlashV2S" (lin tSlashV2S) "he answers it that she runs"
  assertEq "SlashV2Q" (lin tSlashV2Q) "he asks it does she run"
  assertEq "SlashV2A" (lin tSlashV2A) "he paints her beautiful"
  assertEq "ComplVV" (lin tComplVV) "he can run"
  assertEq "ComplVS" (lin tComplVS) "he knows that she runs"
  assertEq "ComplVQ" (lin tComplVQ) "he knows does she run"
  assertEq "ComplVA" (lin tComplVA) "he becomes beautiful"
  assertEq "PassV2" (lin tPassV2) "she is looked at"
  assertEq "NumeralCard" (lin tNumeralCard) "two hundred thousand thirty-four"
  assertEq "DecimalCard" (lin tDecimalCard) "twelve point five"
  assertEq "OrdinalFromNumeral" (lin tOrdinalFromNumeral) "twenty-third"
  assertEq "AdvNP" (lin tAdvNP) "he here"
  assertEq "QuestIAdv" (lin tQuestIAdv) "why she runs"
  assertEq "RelCl" (lin tRelCl) "that she runs"
  assertEq "RelSlash" (lin tRelSlash) "that he looks at"
  assertEq "QuestQVP" (lin tQuestQVP) "who where run"
  assertEq "IdetCN" (lin tIdetCN) "how many cat"
  assertEq "IdetIP" (lin tIdetIP) "how many"
  assertEq "PrepIP" (lin tPrepIP) "in what"
  assertEq "AdvS" (lin tAdvS) "here she runs"
  assertEq "EmbedS" (lin tEmbedS) "she runs"
  assertEq "UttS" (lin tUttS) "she runs"
  assertEq "UttImpNeg" (lin tUttImpNeg) "do not run"
  assertEq "PhrUttSimple" (lin tPhrUttSimple) "he"
  assertEq "ConjAdv" (lin tConjAdv) "here and there"
  assertEq "ConjIAdv" (lin tConjIAdv) "why and where"
  assertEq "ConjDet" (lin tConjDet) "this and that"
  assertEq "ConjRS" (lin tConjRS) "that she runs and that he walks"
  assertEq "ComplN2" (lin tComplN2) "DetCN(the, owner of he)"
  assertEq "UseN2" (lin tUseN2) "DetCN(the, owner)"
  assertEq "Use2N3" (lin tUse2N3) "DetCN(the, distance of of it)"
  assertEq "SentCN" (lin tSentCN) "DetCN(the, cat that she runs)"
  assertEq "ApposCN" (lin tApposCN) "DetCN(the, cat he)"
  assertEq "PossNP" (lin tPossNP) "DetCN(the, his cat)"
  assertEq "PartNP" (lin tPartNP) "DetCN(the, cat of he)"
  assertEq "AdjDAP" (lin tAdjDAP) "beautiful this"
  assertEq "DetDAP" (lin tDetDAP) "DetDAP(the)"
  assertEq "ComplA2" (lin tComplA2) "close him"
  assertEq "ReflA2" (lin tReflA2) "close itself"
  assertEq "UseA2" (lin tUseA2) "close"
  assertEq "UseComparA" (lin tUseComparA) "more beautiful"
  assertEq "CAdvAP" (lin tCAdvAP) "as beautiful him"
  assertEq "AdjOrd" (lin tAdjOrd) "third"
  assertEq "SentAP" (lin tSentAP) "beautiful that she runs"
  assertEq "AdAP" (lin tAdAP) "very beautiful"
  assertEq "AdvAP" (lin tAdvAP) "quite beautiful"
  assertEq "FunRP" (lin tFunRP) "that runs"
  assertEq "PositAdvAdj" (lin tPositAdvAdj) "beautifully"
  assertEq "ComparAdvAdj" (lin tComparAdvAdj) "more more beautiful him"
  assertEq "ComparAdvAdjS" (lin tComparAdvAdjS) "more more beautiful she runs"
  assertEq "AdAdv" (lin tAdAdv) "very here"
  assertEq "PositAdAAdj" (lin tPositAdAAdj) "beautifully"
  assertEq "SubjS" (lin tSubjS) "if she runs"
  assertEq "AdnCAdv" (lin tAdnCAdv) "as"
  assertEq "TextFullStop" (lin tTextFullStop) "he."
  assertEq "TextQuestMark" (lin tTextQuestMark) "he?"
  assertEq "TextExclMark" (lin tTextExclMark) "he!"
  assertEq "PredetAll" (lin tPredetAll) "all they"
  assertEq "NoUtt" (lin tNoUtt) "no"
  assertEq "YesUtt" (lin tYesUtt) "yes"
  assertEq "LanguageTitleUtt" (lin tLanguageTitleUtt) "language title"
  assertEq "ImpersCl" (lin tImpersCl) "it runs"
  assertEq "GenericCl" (lin tGenericCl) "one runs"
  assertEq "ExistNP" (lin tExistNP) "there is he"
  assertEq "ExistIP" (lin tExistIP) "is there what"
  assertEq "ProgrVP" (lin tProgrVP) "she is running"
  assertEq "ImpPl1" (lin tImpPl1) "let us run"
  assertEq "ImpP3" (lin tImpP3) "let he run"
  assertEq "SelfNP" (lin tSelfNP) "he self"
  assertEq "ICompAP" (lin tICompAP) "beautiful"
  assertEq "ExistS" (lin tExistS) "there is he"
  assertEq "PiedPipingQuestSlash" (lin tPiedPipingQuestSlash) "what in he runs"
  assertEq "PiedPipingRelSlash" (lin tPiedPipingRelSlash) "that in he runs"
  assertEq "EmptyRelSlash" (lin tEmptyRelSlash) "that he runs in"
  assertEq "FocusAdv" (lin tFocusAdv) "here she runs"
  assertEq "PassVPSlash" (lin tPassVPSlash) "she is looked"
  assertEq "NominalizeVPSlashNP" (lin tNominalizeVPSlashNP) "the looked at him"
  assertEq "MkVPS" (lin tMkVPS) "it runs"
  assertEq "ConjVPS" (lin tConjVPS2) "it runs and it walks"
  assertEq "PredVPS" (lin tPredVPS2) "she it runs"
  assertEq "QuestVPS" (lin tQuestVPS2) "what it runs"
  assertEq "MkVPI" (lin tMkVPI) "run"
  assertEq "ConjVPI" (lin tConjVPI2) "run and walk"
  assertEq "ComplVPIVV" (lin tComplVPIVV2) "he can run"
  assertEq "MkVPS2" (lin tMkVPS2) "it looks at"
  assertEq "ConjComp" (lin tConjComp2) "she is he and beautiful"
  assertEq "ConjImp" (lin tConjImp2) "run and here walk"
  assertEq "SymbNum" (lin tSymbNum2) "alpha"
  assertEq "SymbOrd" (lin tSymbOrd2) "alpha"
  assertEq "SymbPN" (lin tSymbPN2) "alpha"
  assertEq "IntPN" (lin tIntPN2) "42"
  assertEq "FloatPN" (lin tFloatPN2) "3.14"
  assertEq "CNNumNP" (lin tCNNumNP2) "two cat"
  assertEq "CNSymbNP" (lin tCNSymbNP2) "the cat alpha and beta"
  assertEq "SymbS" (lin tSymbS2) "alpha"
  assertContains "NegNPBucketFallback" (lin tNegNPBucketFallback) "RelNP("
  assertContains "NegVPBucketFallback" (lin tNegVPBucketFallback) "SlashVV("
  assertContains "NegQClBucketFallback" (lin tNegQClBucketFallback) "QuestVP("
  IO.println "gf_en_linearization_dispatch_regression=PASS"
