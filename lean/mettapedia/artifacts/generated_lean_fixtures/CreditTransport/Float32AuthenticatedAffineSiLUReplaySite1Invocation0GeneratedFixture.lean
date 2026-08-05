import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplayChunkedGeneratedFixture

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedAffineSiLUReplaySite1Invocation0Fixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open Float32AffineSiLUReplayCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: beb12bfe26f0d944d8a2c55afb8bbb3b1937978f40a171bdae2875ae190c117b
-- Affine sidecar SHA-256: dee3acd8a3271178ab567b7ab0a7b8684938a61e22a2f077e19d986ab973fd00
-- The imported affine theorem checks arithmetic; endpoint hashes bind it to the trace.
-- Source invocation indices: 0
-- Hidden affine-SiLU site: 1 (error_dependent_hidden_transition)

def activation0_0 : Float32ActivationReplay where
  input := {
    word := 3187697994
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3178282396
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4207781 : ℚ) / 33554432)
    runtimeValue := ((-3944295 : ℚ) / 67108864)
    localError := ((146820089385303841939914874998016658724341174265311239262684794815 : ℚ) / 74216980290004790080225655623901506587902079349406779404307373679624323072)
    outputLower := ((-12999985728791464743604878725495103135944186512118172931426615296 : ℚ) / 221183837324041374869920269229460725702961363566820374984192286827)
    outputUpper := ((-64999928643957323718024393627475515679720932560590864657133076480 : ℚ) / 1105919186621975750926519269107304611621828069529038360779097284073)
    expCertificate := {
      argument := ((4207781 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((4207781 : ℚ) / 33554432)
        terms := 8
        lower := ((117517050212805394214157210728347643889049004031904843593229918315 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
        upper := ((587585251065795847647703976601739202552266271854460703824285441513 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((117517050212805394214157210728347643889049004031904843593229918315 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      upper := ((587585251065795847647703976601739202552266271854460703824285441513 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
    }
  }

theorem activation0_0_is_accepted : activation0_0.check = true := by
  norm_num [activation0_0, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_1 : Float32ActivationReplay where
  input := {
    word := 1057299651
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1051129306
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((8723651 : ℚ) / 16777216)
    runtimeValue := ((5470957 : ℚ) / 16777216)
    localError := ((3958534811352349232593291400638581884015397013742125317256175221 : ℚ) / 54165712209468830110814627202340709241100329868444586413627224916754432)
    outputLower := ((210561061056731472230429775327512444294760555301123627073667072 : ℚ) / 645705727800737134869915852775122243433227292043288909464529749)
    outputUpper := ((1052805305283657361152148876637562221473802776505618135368335360 : ℚ) / 3228528035251428491521753502031606986588259331491266871310903127)
    expCertificate := {
      argument := ((-8723651 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-8723651 : ℚ) / 16777216)
        terms := 8
        lower := ((1203786099485100744338881265681742107410283559324947898831169367 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((240757340647471585433341405505149267597632137610025114968582997 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      }
      lower := ((1203786099485100744338881265681742107410283559324947898831169367 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((240757340647471585433341405505149267597632137610025114968582997 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
    }
  }

theorem activation0_1_is_accepted : activation0_1.check = true := by
  norm_num [activation0_1, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_2 : Float32ActivationReplay where
  input := {
    word := 3198713755
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188524301
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11042715 : ℚ) / 33554432)
    runtimeValue := ((-9241869 : ℚ) / 67108864)
    localError := ((13957491624397937574855514608275688171851039278425094430918356809 : ℚ) / 1847239010690247175750694450415856874348585674760269537712544929697234944)
    outputLower := ((-3790732175227841510133957076589660330754906671979708016660316160 : ℚ) / 27526006173415347494139775445993947704585000685423902940453077971)
    outputUpper := ((-3790732175227841510133957076589660330754906671979708016660316160 : ℚ) / 27526006261859047051529503619907153760620738189820491339453234221)
    expCertificate := {
      argument := ((11042715 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((11042715 : ℚ) / 33554432)
        terms := 8
        lower := ((16007474272166905199054991168092494169705849625988843897012814803 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((16007474360610604756444719342005700225741587130385432296012971053 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((16007474272166905199054991168092494169705849625988843897012814803 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((16007474360610604756444719342005700225741587130385432296012971053 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
    }
  }

theorem activation0_2_is_accepted : activation0_2.check = true := by
  norm_num [activation0_2, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_3 : Float32ActivationReplay where
  input := {
    word := 3203919175
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3191671741
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-16248135 : ℚ) / 33554432)
    runtimeValue := ((-12389309 : ℚ) / 67108864)
    localError := ((3094406778926110069969933219358307351587595350725803304673086943 : ℚ) / 289644563425368841877206566363907788190346939886076083914338179221553152)
    outputLower := ((-796806221916383330099273627967580445029665977184661214142136320 : ℚ) / 4316040328523052362758019065319117727731867728919924555932554293)
    outputUpper := ((-5577643553414683310694915395773063115207661840292628498994954240 : ℚ) / 30212284242730003161833578742762004096233856478310796892603036301)
    expCertificate := {
      argument := ((16248135 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((16248135 : ℚ) / 33554432)
        terms := 8
        lower := ((2670535771201846320603049882761767222749131863286344692583945269 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
        upper := ((18693752341481560866748794464860550561354705418875737849162773133 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((2670535771201846320603049882761767222749131863286344692583945269 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
      upper := ((18693752341481560866748794464860550561354705418875737849162773133 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
    }
  }

theorem activation0_3_is_accepted : activation0_3.check = true := by
  norm_num [activation0_3, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_4 : Float32ActivationReplay where
  input := {
    word := 3185422195
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3176248043
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14528371 : ℚ) / 134217728)
    runtimeValue := ((-13742827 : ℚ) / 268435456)
    localError := ((1928615542924955189445271499117319170577401829974517554248345693223383 : ℚ) / 918080953582365751378383832853646429838251634937548473699381509319028990017536)
    outputLower := ((-175096440607567731063493885091015016455760756232403307955502155038720 : ℚ) / 3420118069583049980470477912029796949916525315260695195568284054543931)
    outputUpper := ((-1225675084252974117444457195637105115190325293626823155688515085271040 : ℚ) / 23940826487093259173918807083315834560285905527785469992733460763536483)
    expCertificate := {
      argument := ((14528371 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((14528371 : ℚ) / 134217728)
        terms := 8
        lower := ((1802521269554011592790457006808619109498296649908260846702067439590971 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
        upper := ((12617648886889990460158660746767589677358304870318429550669944458865763 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((1802521269554011592790457006808619109498296649908260846702067439590971 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
      upper := ((12617648886889990460158660746767589677358304870318429550669944458865763 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
    }
  }

theorem activation0_4_is_accepted : activation0_4.check = true := by
  norm_num [activation0_4, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_5 : Float32ActivationReplay where
  input := {
    word := 3193378658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3183515013
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7048113 : ℚ) / 33554432)
    runtimeValue := ((-12621189 : ℚ) / 134217728)
    localError := ((18648722902887986006376247281933840469466447221363508188614136065 : ℚ) / 3453342207691884070538302945475365365342433004073459406206883523725361152)
    outputLower := ((-12097345953301170821448699261437780764412536920751335069513154560 : ℚ) / 128647022223657205746451174086360945222854608970593842992452363903)
    outputUpper := ((-2419469190660234164289739852287556152882507384150267013902630912 : ℚ) / 25729404447167248059349529038931171337831266254733945475569989709)
    expCertificate := {
      argument := ((7048113 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((7048113 : ℚ) / 33554432)
        terms := 8
        lower := ((71054362717414994271027252696853677548458853673418547775251048063 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((14210872545918805764264744761029717802952115195298886432129726541 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((71054362717414994271027252696853677548458853673418547775251048063 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((14210872545918805764264744761029717802952115195298886432129726541 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
    }
  }

theorem activation0_5_is_accepted : activation0_5.check = true := by
  norm_num [activation0_5, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_6 : Float32ActivationReplay where
  input := {
    word := 1041540886
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1033858162
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4871051 : ℚ) / 33554432)
    runtimeValue := ((5223993 : ℚ) / 67108864)
    localError := ((96603791208133316831742887079589006778542079225263777761067599819 : ℚ) / 21623118922596540543005003949034568286874412405479854182470885626513195008)
    outputLower := ((25081942827749904732368156407023736749228815874701233411703439360 : ℚ) / 322209580581250171724788648882303075051223276576729656280458464803)
    outputUpper := ((25081942827749904732368156407023736749228815874701233411703439360 : ℚ) / 322209580579348512634709536269822244150555318675635072327716434397)
    expCertificate := {
      argument := ((-4871051 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-4871051 : ℚ) / 33554432)
        terms := 8
        lower := ((149431602060621878208437772101300441127368052784109186676112486877 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
        upper := ((149431602062523537298516884713781272028036010685203770628854517283 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
      }
      lower := ((149431602060621878208437772101300441127368052784109186676112486877 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
      upper := ((149431602062523537298516884713781272028036010685203770628854517283 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
    }
  }

theorem activation0_6_is_accepted : activation0_6.check = true := by
  norm_num [activation0_6, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_7 : Float32ActivationReplay where
  input := {
    word := 3205024247
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192532365
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8964599 : ℚ) / 16777216)
    runtimeValue := ((-13249933 : ℚ) / 67108864)
    localError := ((614151746772085246674608369034806275805304571829802057124022689 : ℚ) / 17510855736407892064678291440270117557118286336871385861209289673146368)
    outputLower := ((-51518279974315523976563922754667379589347619184954992062627840 : ℚ) / 260932083970425904760931304697247111158345436109176067429919387)
    outputUpper := ((-10303655994863104795312784550933475917869523836990998412525568 : ℚ) / 52186423944482056241887247340084982888919804830026694023257569)
    expCertificate := {
      argument := ((8964599 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((8964599 : ℚ) / 16777216)
        terms := 8
        lower := ((164515801314886488228413579156777355007013256482208497311836827 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
        upper := ((32903167413374172935383702231991031658653368904633179999641057 : ℚ) / 19283256531107883306503545108093951230266435925393514023616512)
      }
      lower := ((164515801314886488228413579156777355007013256482208497311836827 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
      upper := ((32903167413374172935383702231991031658653368904633179999641057 : ℚ) / 19283256531107883306503545108093951230266435925393514023616512)
    }
  }

theorem activation0_7_is_accepted : activation0_7.check = true := by
  norm_num [activation0_7, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_8 : Float32ActivationReplay where
  input := {
    word := 1041075292
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1033326814
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2319127 : ℚ) / 16777216)
    runtimeValue := ((4958319 : ℚ) / 67108864)
    localError := ((41050959443502824352599349824052435995495738829984418124107497 : ℚ) / 16947605694607766203814204564742723290532679451525901943129749900492800)
    outputLower := ((93293859387794263548472979483392896009552109610572632545034240 : ℚ) / 1262695021530624501206508487620777103447928753410407010366153411)
    outputUpper := ((18658771877558852709694595896678579201910421922114526509006848 : ℚ) / 252539004305120799002263017963509608664105526380626886235620825)
    expCertificate := {
      argument := ((-2319127 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-2319127 : ℚ) / 16777216)
        terms := 8
        lower := ((117556208587365615856738202206851950052240474902872288070305241 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
        upper := ((587781042941848585478884408837488810388603496021634019539575491 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      }
      lower := ((117556208587365615856738202206851950052240474902872288070305241 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
      upper := ((587781042941848585478884408837488810388603496021634019539575491 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
    }
  }

theorem activation0_8_is_accepted : activation0_8.check = true := by
  norm_num [activation0_8, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_9 : Float32ActivationReplay where
  input := {
    word := 3214207419
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196963838
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9759163 : ℚ) / 8388608)
    runtimeValue := ((-4646399 : ℚ) / 16777216)
    localError := ((1805293732718368818597349201285466497707126265022124677224081803513325983495776646193630200203212208912593119563304372442732729 : ℚ) / 11556998697759518792292575730014450599884161616676315731303959288761059700643948958192781920975322321426218829999359844163653520588800)
    outputLower := ((-190775244419946075493506998739363178595597011080277043103043417652176992208414842325502521699396785917768626849486972957753344 : ℚ) / 688850802049608158605848296285536921017418004076261265951631026790205222406622705351876134930570263947619130015335073719242425)
    outputUpper := ((-4769381110498651887337674968484079464889925277006926077576085441304424805210371058137563042484919647944215671237174323943833600 : ℚ) / 17221280781198961365275879345100946685386584308891706386870426663767749795118627277859807069399829515350818535865040175651827729)
    expCertificate := {
      argument := ((9759163 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((9759163 : ℚ) / 16777216)
        terms := 8
        lower := ((724477470865434928417691988310776592621776220446165052693951339 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((3622388835388628635885676509793930405294378330150491835525168873 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((524867605791577115528338805186657654949984367408434255992832835012447935818065222128115136415868391100113534982377716899892921 : ℚ) / 163983196258031043077509491098879266067433636667827009958798191777757286588557483223760998514701872847505595032957356819349504)
      upper := ((13121700874748185288338142067628965033700743392196031137900471869323817630404690197265782106532282694163178660041106255168090129 : ℚ) / 4099579906450776076937737277471981651685840916695675248969954794443932164713937080594024962867546821187639875823933920483737600)
    }
  }

theorem activation0_9_is_accepted : activation0_9.check = true := by
  norm_num [activation0_9, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_10 : Float32ActivationReplay where
  input := {
    word := 1050603115
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1043818237
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10415723 : ℚ) / 33554432)
    runtimeValue := ((12019453 : ℚ) / 67108864)
    localError := ((78760939677778076035208026082595664313968485480192109050444189079 : ℚ) / 20095693532646637590913420675551781425578303911291776898567439221535014912)
    outputLower := ((53632484816044775751421171972174895398321185667916586168908513280 : ℚ) / 299449168632129394872686574988838753485356329549726499595752942883)
    outputUpper := ((53632484816044775751421171972174895398321185667916586168908513280 : ℚ) / 299449167801003864759429991521625048963425314671161654399729291997)
    expCertificate := {
      argument := ((-10415723 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-10415723 : ℚ) / 33554432)
        terms := 8
        lower := ((126671189282277230333158227353103245940238048779635768748125344477 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
        upper := ((126671190113402760446414810820316950462169063658200613944148995363 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
      }
      lower := ((126671189282277230333158227353103245940238048779635768748125344477 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
      upper := ((126671190113402760446414810820316950462169063658200613944148995363 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
    }
  }

theorem activation0_10_is_accepted : activation0_10.check = true := by
  norm_num [activation0_10, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_11 : Float32ActivationReplay where
  input := {
    word := 1055631968
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1049656177
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((482643 : ℚ) / 1048576)
    runtimeValue := ((9468785 : ℚ) / 33554432)
    localError := ((12180224697816583365382601636144776851670632187294375 : ℚ) / 409544263997539055980772722646825134031130823340611101261824)
    outputLower := ((3444255540753412974368071575765063405545889894236160 : ℚ) / 12205371028965061054649680335252942610209341377205143)
    outputUpper := ((3444255540753412974368071575765063405545889894236160 : ℚ) / 12205370187686057567023418028558049620125616292375657)
    expCertificate := {
      argument := ((-482643 : ℚ) / 1048576)
      halvings := 0
      reduced := {
        argument := ((-482643 : ℚ) / 1048576)
        terms := 8
        lower := ((4722481804551834625820551685050680559487241672338537 : ℚ) / 7482888383134222941202866343507369060638374620037120)
        upper := ((4722482645830838113446813991745573549570966757168023 : ℚ) / 7482888383134222941202866343507369060638374620037120)
      }
      lower := ((4722481804551834625820551685050680559487241672338537 : ℚ) / 7482888383134222941202866343507369060638374620037120)
      upper := ((4722482645830838113446813991745573549570966757168023 : ℚ) / 7482888383134222941202866343507369060638374620037120)
    }
  }

theorem activation0_11_is_accepted : activation0_11.check = true := by
  norm_num [activation0_11, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_12 : Float32ActivationReplay where
  input := {
    word := 1050557716
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1043758997
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2592581 : ℚ) / 8388608)
    runtimeValue := ((11960213 : ℚ) / 67108864)
    localError := ((30447109463953044573155147687310830444079685232252983122951 : ℚ) / 2922014909087581318594495906958627200710170024836859390191644704768)
    outputLower := ((271599919461283095859773357988033497412384570751066392494080 : ℚ) / 1523949535072052646305250898738826042988823338973492547626977)
    outputUpper := ((7759997698893802738850667371086671354639559164316182642688 : ℚ) / 43541415171140153983153341814259099970909506452632835361237)
    expCertificate := {
      argument := ((-2592581 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-2592581 : ℚ) / 8388608)
        terms := 8
        lower := ((18433008229593430927810184121428434306500084674776697309653 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
        upper := ((645155292117917339368240379489752744734493576748527715821537 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      }
      lower := ((18433008229593430927810184121428434306500084674776697309653 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
      upper := ((645155292117917339368240379489752744734493576748527715821537 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
    }
  }

theorem activation0_12_is_accepted : activation0_12.check = true := by
  norm_num [activation0_12, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_13 : Float32ActivationReplay where
  input := {
    word := 3146337008
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3137929551
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-562351 : ℚ) / 134217728)
    runtimeValue := ((-8978767 : ℚ) / 4294967296)
    localError := ((6006078954524579949937603093607590923177291928289250067690433277417581 : ℚ) / 97469545631800005987328920939062580974314191706352094983362720963422878903042048)
    outputLower := ((-47442318846672090623168141040982619361275577227229235020539614986240 : ℚ) / 22693897046102212273359453120630729827135176388025888448837075520044157)
    outputUpper := ((-47442318846672090623168141040982619361275577227229235020539614986240 : ℚ) / 22693897046102212273359513128889394219572234830435387553498782441816963)
    expCertificate := {
      argument := ((562351 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((562351 : ℚ) / 134217728)
        terms := 8
        lower := ((11370719445898943559599306784082484944207575730558848006773559215373437 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
        upper := ((11370719445898943559599366792341149336644634172968347111435266137146243 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((11370719445898943559599306784082484944207575730558848006773559215373437 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      upper := ((11370719445898943559599366792341149336644634172968347111435266137146243 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
    }
  }

theorem activation0_13_is_accepted : activation0_13.check = true := by
  norm_num [activation0_13, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_14 : Float32ActivationReplay where
  input := {
    word := 3193190560
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3183365878
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-434629 : ℚ) / 2097152)
    runtimeValue := ((-6236027 : ℚ) / 67108864)
    localError := ((3690727567467521134971839308347728990522506434205998107 : ℚ) / 2007002255113681748315828656410705902137576681172190871645323264)
    outputLower := ((-2779048103700281894407278341319073504906417585342382080 : ℚ) / 29906664117318017648679984439959011900539876664732341279)
    outputUpper := ((-2779048103700281894407278341319073504906417585342382080 : ℚ) / 29906664119864728276667425877015380593204150813403589601)
    expCertificate := {
      argument := ((434629 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((434629 : ℚ) / 2097152)
        terms := 8
        lower := ((16497328134741490138044447952393806543875909345625822239 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
        upper := ((16497328137288200766031889389450175236540183494297070561 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      }
      lower := ((16497328134741490138044447952393806543875909345625822239 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      upper := ((16497328137288200766031889389450175236540183494297070561 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
    }
  }

theorem activation0_14_is_accepted : activation0_14.check = true := by
  norm_num [activation0_14, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_15 : Float32ActivationReplay where
  input := {
    word := 1051162888
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1044553462
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1371937 : ℚ) / 4194304)
    runtimeValue := ((6377339 : ℚ) / 33554432)
    localError := ((576629158220554414542884949802344868531407669926412201671 : ℚ) / 84958143193310549690751107064794303565683784185785846181320982528)
    outputLower := ((481221161235563269653986102002147002513048270051087482880 : ℚ) / 2531949972907023122631046386504003511836641555600936597029)
    outputUpper := ((481221161235563269653986102002147002513048270051087482880 : ℚ) / 2531949962149146458325164511286418433986979306551121218011)
    expCertificate := {
      argument := ((-1371937 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((-1371937 : ℚ) / 4194304)
        terms := 8
        lower := ((1060754242917893154301151365222121617712989749254863129051 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
        upper := ((1060754253675769818607033240439706695562651998304678508069 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
      }
      lower := ((1060754242917893154301151365222121617712989749254863129051 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
      upper := ((1060754253675769818607033240439706695562651998304678508069 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
    }
  }

theorem activation0_15_is_accepted : activation0_15.check = true := by
  norm_num [activation0_15, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_16 : Float32ActivationReplay where
  input := {
    word := 1030782625
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1022856585
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((15761057 : ℚ) / 268435456)
    runtimeValue := ((16223625 : ℚ) / 536870912)
    localError := ((1725534633533427007482334446665473753291366304470445093118773883943307613 : ℚ) / 1814248745486205432106817084585954444956866691898506594785221846474867739805614080)
    outputLower := ((510593168958454884864493419853243076848355028635717868886952242178949120 : ℚ) / 16896508126391217035444056388818796712502594586009599667478059142112611593)
    outputUpper := ((102118633791690976972898683970648615369671005727143573777390448435789824 : ℚ) / 3379301625278229698737742536861364627176647431959410374584089678665376715)
    expCertificate := {
      argument := ((-15761057 : ℚ) / 268435456)
      halvings := 0
      reduced := {
        argument := ((-15761057 : ℚ) / 268435456)
        terms := 8
        lower := ((1640061545887007624304184059567554213158967970972472962683133574267954123 : ℚ) / 1739240079391222074433558477293810414017679460986937411900956104397422592)
        upper := ((8200307729435106663276264002349744642414197281074912607973278620125498633 : ℚ) / 8696200396956110372167792386469052070088397304934687059504780521987112960)
      }
      lower := ((1640061545887007624304184059567554213158967970972472962683133574267954123 : ℚ) / 1739240079391222074433558477293810414017679460986937411900956104397422592)
      upper := ((8200307729435106663276264002349744642414197281074912607973278620125498633 : ℚ) / 8696200396956110372167792386469052070088397304934687059504780521987112960)
    }
  }

theorem activation0_16_is_accepted : activation0_16.check = true := by
  norm_num [activation0_16, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_17 : Float32ActivationReplay where
  input := {
    word := 1034455075
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1026520658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((11044899 : ℚ) / 134217728)
    runtimeValue := ((5749545 : ℚ) / 134217728)
    localError := ((425392329799819441234310691167644204613062077132200699646275985352905 : ℚ) / 973162161421436788003408302411581032707296946290222075812120082611559236370432)
    outputLower := ((310598196966716355118504977505394253530110353167000059066978318417920 : ℚ) / 7250623117547454204714759533370475137893970246970878016668436827100321)
    outputUpper := ((310598196966716355118504977505394253530110353167000059066978318417920 : ℚ) / 7250623117547011286045672762480236833596951859371528594286144395258719)
    expCertificate := {
      argument := ((-11044899 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-11044899 : ℚ) / 134217728)
        terms := 8
        lower := ((3476230584145921714792290650297488539287751640215848446931638960368479 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
        upper := ((3476230584146364633461377421187726843584770027815197869313931392210081 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
      }
      lower := ((3476230584145921714792290650297488539287751640215848446931638960368479 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
      upper := ((3476230584146364633461377421187726843584770027815197869313931392210081 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
    }
  }

theorem activation0_17_is_accepted : activation0_17.check = true := by
  norm_num [activation0_17, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_18 : Float32ActivationReplay where
  input := {
    word := 1071096482
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1068885118
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((7065937 : ℚ) / 4194304)
    runtimeValue := ((5960255 : ℚ) / 4194304)
    localError := ((4096918092902627896055698659345188895041227320434697589101073042524877601557614109801611474107528660998470789435116125353745 : ℚ) / 311042851419724192542794587078854340503685647409598065568293341999262619981340333967783625425581777392424197640972971842641854464)
    outputLower := ((105382690327849840689847786143831550783827317752707638580181139224400884661526297107925722099205541537456623850665856204800 : ℚ) / 74159156696763636865657919267892641166476450619709786266984104898736397232961499661377050635804212123982465627073036606801)
    outputUpper := ((105382690327849840689847786143831550783827317752707638580181139224400884661526297107925722099205541537456623850665856204800 : ℚ) / 74158394675189064155291220445359788061067020275496975318978629588905005450568278781839281422038502071481751833194010697041)
    expCertificate := {
      argument := ((-7065937 : ℚ) / 4194304)
      halvings := 1
      reduced := {
        argument := ((-7065937 : ℚ) / 8388608)
        terms := 8
        lower := ((3406430630116102769112244703097954409457520138313359474001271 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((3406542478726452292269931041787584980392238633681420155648649 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((11603769637793188957877016382371786784122426209706032188943918980324497566139307215157992315783210000137149235782909615441 : ℚ) / 62554625037395875197414204062988001276944594065790943130034710608580507884428971566681289106255292071344602597411101081600)
      upper := ((11604531659367761668243715204904639889531856553918843136949394290155889348532528094695761529548920052637863029661935525201 : ℚ) / 62554625037395875197414204062988001276944594065790943130034710608580507884428971566681289106255292071344602597411101081600)
    }
  }

theorem activation0_18_is_accepted : activation0_18.check = true := by
  norm_num [activation0_18, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_19 : Float32ActivationReplay where
  input := {
    word := 3206251231
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3193658171
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-10191583 : ℚ) / 16777216)
    runtimeValue := ((-14375739 : ℚ) / 67108864)
    localError := ((5266095224821078398874297233427813822821757642713961157108941623 : ℚ) / 77063881601215149643554826783191920089251399723680102530576075158716416)
    outputLower := ((-245992249154367421157565815152588664948073766875530834347032576 : ℚ) / 1148341321963297570400756996619580985445550079996587373771907019)
    outputUpper := ((-175708749395976729398261296537563332105766976339664881676451840 : ℚ) / 820244100702985260588975714493439960596750241635594694034027119)
    expCertificate := {
      argument := ((10191583 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((10191583 : ℚ) / 16777216)
        terms := 8
        lower := ((743392934810032020964182549349608009609954925563323579275960267 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((530995252736367010991422537872030692142753702754691983679779439 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      }
      lower := ((743392934810032020964182549349608009609954925563323579275960267 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      upper := ((530995252736367010991422537872030692142753702754691983679779439 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
    }
  }

theorem activation0_19_is_accepted : activation0_19.check = true := by
  norm_num [activation0_19, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_20 : Float32ActivationReplay where
  input := {
    word := 1065489121
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1061093941
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((8524513 : ℚ) / 8388608)
    runtimeValue := ((12517941 : ℚ) / 16777216)
    localError := ((97918737107539251858181294340811611724671337553818488205575293844908091076975034215309026435040520518567660559568258485000139 : ℚ) / 1156487269287539330729688685548184450203959817131615888154253139740475042116903716487308750366968679341113372955117967547758580596736)
    outputLower := ((1049634106397641534916570115503736055463692823274041300536662220163459095110971879127308940860086802762373221217294771814400 : ℚ) / 1406776081014701025843229250978555131063697827252571239217948731124130182270270310186577510979738876596744681236009487419089)
    outputUpper := ((51432071213484435210911935659683066717720948340428023726296448788009495660437622077238138102144253335356287839647443818905600 : ℚ) / 68932012873145301981549780699502494943377960749364846238747426255969705707842333107430264375625174006290040788359520885214721)
    expCertificate := {
      argument := ((-8524513 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((-8524513 : ℚ) / 16777216)
        terms := 8
        lower := ((135351081497865740637946841471004244067659576488013253221546239 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((19335876752294879839767159994396960443010920120205724615667383 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      }
      lower := ((18319915262641893624293764928243462206515727209912065387266502867773012316312245692689215451334472510146338617693670015045121 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
      upper := ((373876129779937589980861582177350381331815510120881834085684988507871133463533832334719369667683744022383412446910490068689 : ℚ) / 1032899951234763435862367668801204749731882317131689405132263742616259048806736477851858141312055132574361268789098997350400)
    }
  }

theorem activation0_20_is_accepted : activation0_20.check = true := by
  norm_num [activation0_20, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_21 : Float32ActivationReplay where
  input := {
    word := 3209884231
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196101637
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-13824583 : ℚ) / 16777216)
    runtimeValue := ((-8430597 : ℚ) / 33554432)
    localError := ((40038970298835328470743326382403844156435664005194539000661094089 : ℚ) / 44562722788634770491523264019295738552830086665768529999214454776004608)
    outputLower := ((-333681260878828365160615842459372568857442114762096004957208576 : ℚ) / 1328072631020390107975103378870956258560123642258898317790462219)
    outputUpper := ((-238343757770591689400439887470980406326744367687211432112291840 : ℚ) / 948626738635256532885913142697629695913269153581967685800467119)
    expCertificate := {
      argument := ((13824583 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((13824583 : ℚ) / 16777216)
        terms := 8
        lower := ((923124243867124558538528931600983282724528487825634523294515467 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((659377890668638283288359966076220427459272614701064975446219439 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      }
      lower := ((923124243867124558538528931600983282724528487825634523294515467 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      upper := ((659377890668638283288359966076220427459272614701064975446219439 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
    }
  }

theorem activation0_21_is_accepted : activation0_21.check = true := by
  norm_num [activation0_21, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_22 : Float32ActivationReplay where
  input := {
    word := 3200535372
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189710524
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3216083 : ℚ) / 8388608)
    runtimeValue := ((-2607023 : ℚ) / 16777216)
    localError := ((2278588791263215809258387662652484593462995397270542655571207 : ℚ) / 327387436536855678267021523475153039545166529353823859316297578840064)
    outputLower := ((-3032264355106828101045979787826902461341275766154737966120960 : ℚ) / 19513811652693985675121594940123515488964495847843083441285591)
    outputUpper := ((-3032264355106828101045979787826902461341275766154737966120960 : ℚ) / 19513811858705024615944714753338875743458660206426612097996329)
    expCertificate := {
      argument := ((3216083 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((3216083 : ℚ) / 8388608)
        terms := 8
        lower := ((11604663466106767912688500266881855804675527987818399955036631 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((11604663672117806853511620080097216059169692346401928611747369 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((11604663466106767912688500266881855804675527987818399955036631 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((11604663672117806853511620080097216059169692346401928611747369 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
    }
  }

theorem activation0_22_is_accepted : activation0_22.check = true := by
  norm_num [activation0_22, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_23 : Float32ActivationReplay where
  input := {
    word := 1060505235
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1056187609
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((11929235 : ℚ) / 16777216)
    runtimeValue := ((16000217 : ℚ) / 33554432)
    localError := ((3007083985445275697257635730299034982530950583306362140737350091 : ℚ) / 2894458292016381145898300826544176541795072424490997234200597216886784)
    outputLower := ((287933616234200343885005365400231842541225907927494980188241920 : ℚ) / 603832530492207969325896232721807166635713833990043180586884309)
    outputUpper := ((41133373747742906269286480771461691791603701132499282884034560 : ℚ) / 86261579156410132226297283963685528689476025834411300247925437)
    expCertificate := {
      argument := ((-11929235 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-11929235 : ℚ) / 16777216)
        terms := 8
        lower := ((28411809563086482306786648639403674998676718058230758177075901 : ℚ) / 57849769593323649919510635324281853690799307776180542070849536)
        upper := ((198884143338942419889321785451834190800118679556779386090937557 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      }
      lower := ((28411809563086482306786648639403674998676718058230758177075901 : ℚ) / 57849769593323649919510635324281853690799307776180542070849536)
      upper := ((198884143338942419889321785451834190800118679556779386090937557 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
    }
  }

theorem activation0_23_is_accepted : activation0_23.check = true := by
  norm_num [activation0_23, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_24 : Float32ActivationReplay where
  input := {
    word := 3178084158
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3169243607
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7789471 : ℚ) / 134217728)
    runtimeValue := ((-15126999 : ℚ) / 536870912)
    localError := ((12322585544858890482557241544656050163038072094918360281534789225698437 : ℚ) / 12521414330480879274446941825911027931003586732564955482740507104396364476317696)
    outputLower := ((-93878979709140909304620922510431061489734203071381838171908834590720 : ℚ) / 3331850237740159996475278197664042638183662232049400399623678055610331)
    outputUpper := ((-657152857963986365132346457573017430428139421499672867203361842135040 : ℚ) / 23322951664181201298622306112034298351041202866593292882182648599886083)
    expCertificate := {
      argument := ((7789471 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((7789471 : ℚ) / 134217728)
        terms := 8
        lower := ((1714253437711121608795257292442864797765433566696966050757461440657371 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
        upper := ((11999774063977932584862159775486053468113602209126252440119132295215363 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((1714253437711121608795257292442864797765433566696966050757461440657371 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
      upper := ((11999774063977932584862159775486053468113602209126252440119132295215363 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
    }
  }

theorem activation0_24_is_accepted : activation0_24.check = true := by
  norm_num [activation0_24, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_25 : Float32ActivationReplay where
  input := {
    word := 1064707136
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1060245589
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((252049 : ℚ) / 262144)
    runtimeValue := ((11669589 : ℚ) / 16777216)
    localError := ((146777080664632914361618059061507765899391007022537 : ℚ) / 7943800758393751573986210482203238810568780696950669312)
    outputLower := ((65869693670442715221104721737141564873681928192 : ℚ) / 94700276780276658241282829382001527918920892193)
    outputUpper := ((329348468352213576105523608685707824368409640960 : ℚ) / 473487422370538209318292765748693872128056329307)
    expCertificate := {
      argument := ((-252049 : ℚ) / 262144)
      halvings := 0
      reduced := {
        argument := ((-252049 : ℚ) / 262144)
        terms := 8
        lower := ((130947976121107837864304133080815039396197139547 : ℚ) / 342539446249430371453988632667878832731859189760)
        upper := ((26192387530390583950485102848425761372549054241 : ℚ) / 68507889249886074290797726533575766546371837952)
      }
      lower := ((130947976121107837864304133080815039396197139547 : ℚ) / 342539446249430371453988632667878832731859189760)
      upper := ((26192387530390583950485102848425761372549054241 : ℚ) / 68507889249886074290797726533575766546371837952)
    }
  }

theorem activation0_25_is_accepted : activation0_25.check = true := by
  norm_num [activation0_25, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_26 : Float32ActivationReplay where
  input := {
    word := 3197889934
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3187957176
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5109447 : ℚ) / 16777216)
    runtimeValue := ((-1084343 : ℚ) / 8388608)
    localError := ((7877246278194091611488957398164517101655297246412270170224529 : ℚ) / 635179114923998244103136679360198767853495580465907539014265912426496)
    outputLower := ((-9787755929738241537090601428540082259141519689529549484195840 : ℚ) / 75719251027583866608516774101281019193350741918791239144118537)
    outputUpper := ((-9787755929738241537090601428540082259141519689529549484195840 : ℚ) / 75719251160299824031043952057095948938421234623364373285889783)
    expCertificate := {
      argument := ((5109447 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((5109447 : ℚ) / 16777216)
        terms := 8
        lower := ((43580490142404061097677532254457767142906682043135382438091017 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((43580490275120018520204710210272696887977174747708516579862263 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      }
      lower := ((43580490142404061097677532254457767142906682043135382438091017 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((43580490275120018520204710210272696887977174747708516579862263 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
    }
  }

theorem activation0_26_is_accepted : activation0_26.check = true := by
  norm_num [activation0_26, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_27 : Float32ActivationReplay where
  input := {
    word := 1067326647
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1064631696
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10362039 : ℚ) / 8388608)
    runtimeValue := ((1003481 : ℚ) / 1048576)
    localError := ((61844689667010845782615237967376439722442326534522985800329129668932949055838066774693221059628361134993462187988043837751719 : ℚ) / 68501474863106117674991418700511567337211924606016225088007184522833989836083469460812906782217140517810724423648414531577290162176)
    outputLower := ((62518659748058691862918468523788592376904869265904158811747853267730030607471112664336672288704907445955203950026536307916800 : ℚ) / 65328161706568582111138273773684203006049607999120747894115951169077879296373651710211244743206747709058957595756277407765121)
    outputUpper := ((62518659748058691862918468523788592376904869265904158811747853267730030607471112664336672288704907445955203950026536307916800 : ℚ) / 65328097212892644572249811840545241677486347776428437316901382944902410350879163227856547147957935827074741767548002749993601)
    expCertificate := {
      argument := ((-10362039 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((-10362039 : ℚ) / 16777216)
        terms := 8
        lower := ((121309519834138475642652575029326864893637074462936943932087999 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((121309785656661572364825464746229085165351708680229134379376961 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((14715999602389236214993796069286208940624114236975656465420459556705716959349075813115498223667234330931039596882151879824001 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
      upper := ((14716064096065173753882258002425170269187374459667967042635027780881185904843564295470195818916046212915255425090426537595521 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
    }
  }

theorem activation0_27_is_accepted : activation0_27.check = true := by
  norm_num [activation0_27, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_28 : Float32ActivationReplay where
  input := {
    word := 1051953451
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1045606881
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((11766059 : ℚ) / 33554432)
    runtimeValue := ((13808097 : ℚ) / 67108864)
    localError := ((102370812077496614676547693883352443441034428949598160108648604867 : ℚ) / 19760388323393123040544953426435104988047972048541149148408971233197031424)
    outputLower := ((60585614715578263566820166326788469468271724537860786038757130240 : ℚ) / 294452731659905955799593827522324099958657801874595122760667968291)
    outputUpper := ((12117122943115652713364033265357693893654344907572157207751426048 : ℚ) / 58890545891193538669615705779946488909705635500309683887131470073)
    expCertificate := {
      argument := ((-11766059 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-11766059 : ℚ) / 33554432)
        terms := 8
        lower := ((24334950187448211784361352946242128305068182322004506756810680569 : ℚ) / 34555595703745326885254352833704360604637453178305177130320789504)
        upper := ((121674753141179321373322063353802296935470535983069237109064020771 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
      }
      lower := ((24334950187448211784361352946242128305068182322004506756810680569 : ℚ) / 34555595703745326885254352833704360604637453178305177130320789504)
      upper := ((121674753141179321373322063353802296935470535983069237109064020771 : ℚ) / 172777978518726634426271764168521803023187265891525885651603947520)
    }
  }

theorem activation0_28_is_accepted : activation0_28.check = true := by
  norm_num [activation0_28, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_29 : Float32ActivationReplay where
  input := {
    word := 1055185338
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1049334931
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((7498973 : ℚ) / 16777216)
    runtimeValue := ((9147539 : ℚ) / 33554432)
    localError := ((1188156501974604079514499063231318613575557265970427960976844811 : ℚ) / 111390221709864557919902443406258075274078215995167429498651981603930112)
    outputLower := ((905006236331428652124117908646896796381706148989759533644513280 : ℚ) / 3319687478240175951209784682311031423303043844402248535328948649)
    outputUpper := ((905006236331428652124117908646896796381706148989759533644513280 : ℚ) / 3319687298234240946766806942411007740321106195305807277520059991)
    expCertificate := {
      argument := ((-7498973 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-7498973 : ℚ) / 16777216)
        terms := 8
        lower := ((1294945362467913199583934706061142861143130423139488305040326231 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((1294945542473848204026912445961166544125068072235929562849214889 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((1294945362467913199583934706061142861143130423139488305040326231 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((1294945542473848204026912445961166544125068072235929562849214889 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
    }
  }

theorem activation0_29_is_accepted : activation0_29.check = true := by
  norm_num [activation0_29, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_30 : Float32ActivationReplay where
  input := {
    word := 3146717168
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3138308084
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-586111 : ℚ) / 134217728)
    runtimeValue := ((-2339325 : ℚ) / 1073741824)
    localError := ((1595065102149443983154619953970158412830652174073560117695158741369335 : ℚ) / 24369547945620595349799438881323391328484892173364396597165288803194782181490688)
    outputLower := ((-49446813363080755092879184554968985591661773241673890803294551408640 : ℚ) / 22695910134930718084610476048033117622588660729457062293929316851491837)
    outputUpper := ((-49446813363080755092879184554968985591661773241673890803294551408640 : ℚ) / 22695910134930718084610559606454779495499639316176103035794903534033923)
    expCertificate := {
      argument := ((586111 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((586111 : ℚ) / 134217728)
        terms := 8
        lower := ((11372732534727449370850329711484872739661060071990021851865800546821117 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
        upper := ((11372732534727449370850413269906534612572038658709062593731387229363203 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((11372732534727449370850329711484872739661060071990021851865800546821117 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      upper := ((11372732534727449370850413269906534612572038658709062593731387229363203 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
    }
  }

theorem activation0_30_is_accepted : activation0_30.check = true := by
  norm_num [activation0_30, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_31 : Float32ActivationReplay where
  input := {
    word := 1062720496
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1058464601
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((884031 : ℚ) / 1048576)
    runtimeValue := ((9888601 : ℚ) / 16777216)
    localError := ((6697987843004633785418981640591045146363738643584141657 : ℚ) / 1257001802449000376251332081208550738424281453808701069590528)
    outputLower := ((8832118435213796937282863227008846444381031165329408 : ℚ) / 14984778394092729088321461366108619672033302241028813)
    outputUpper := ((44160592176068984686414316135044232221905155826647040 : ℚ) / 74923145916998408809383635592970296050565329421085183)
    expCertificate := {
      argument := ((-884031 : ℚ) / 1048576)
      halvings := 0
      reduced := {
        argument := ((-884031 : ℚ) / 1048576)
        terms := 8
        lower := ((22542927235058848220963571188418712626096707080825343 : ℚ) / 52380218681939560588420064404551583424468622340259840)
        upper := ((4508734657704816970637448485198302987139577772976845 : ℚ) / 10476043736387912117684012880910316684893724468051968)
      }
      lower := ((22542927235058848220963571188418712626096707080825343 : ℚ) / 52380218681939560588420064404551583424468622340259840)
      upper := ((4508734657704816970637448485198302987139577772976845 : ℚ) / 10476043736387912117684012880910316684893724468051968)
    }
  }

theorem activation0_31_is_accepted : activation0_31.check = true := by
  norm_num [activation0_31, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_32 : Float32ActivationReplay where
  input := {
    word := 1054772425
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1049040329
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((14585033 : ℚ) / 33554432)
    runtimeValue := ((8852937 : ℚ) / 33554432)
    localError := ((7702522019829049811216459051551177865142380584144851336374597231 : ℚ) / 454819478267669138500606013462613297789430378376489792031815177628286976)
    outputLower := ((3576239685741094011758210754630264864525179122470219167333089280 : ℚ) / 13554676719536457613128602905947366290969561886086755753511642743)
    outputUpper := ((25033677800187658082307475282411854051676253857291534171331624960 : ℚ) / 94882732941421227542455799158415146893914159208841034591251542719)
    expCertificate := {
      argument := ((-14585033 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-14585033 : ℚ) / 33554432)
        terms := 8
        lower := ((37290073435179016067031877768907879219518403911665739374050226879 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((5327153932930427402353756993160613766055882557918856436768597623 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
      }
      lower := ((37290073435179016067031877768907879219518403911665739374050226879 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((5327153932930427402353756993160613766055882557918856436768597623 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
    }
  }

theorem activation0_32_is_accepted : activation0_32.check = true := by
  norm_num [activation0_32, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_33 : Float32ActivationReplay where
  input := {
    word := 3205962183
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3193406634
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9902535 : ℚ) / 16777216)
    runtimeValue := ((-7062101 : ℚ) / 33554432)
    localError := ((247987431613092386528381652828504175945379379697070178228887249 : ℚ) / 4233985751763810217075413492827790656465928668888950220177341469949952)
    outputLower := ((-26557283778844690770506254462378302165310483923261694704353280 : ℚ) / 126182608358973569186789199496143777861175795462398237591306611)
    outputUpper := ((-26557283778844690770506254462378302165310483923261694704353280 : ℚ) / 126182645344438283867846233123282949841957559460073871466462861)
    expCertificate := {
      argument := ((9902535 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((9902535 : ℚ) / 16777216)
        terms := 8
        lower := ((81188343119721841471614260910591224990554111636480038202868083 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((81188380105186556152671294537730396971335875634155672078024333 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((81188343119721841471614260910591224990554111636480038202868083 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((81188380105186556152671294537730396971335875634155672078024333 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
    }
  }

theorem activation0_33_is_accepted : activation0_33.check = true := by
  norm_num [activation0_33, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_34 : Float32ActivationReplay where
  input := {
    word := 3204698187
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192207284
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8638539 : ℚ) / 16777216)
    runtimeValue := ((-3231213 : ℚ) / 16777216)
    localError := ((35416808858647012402539171131677444088173527008090631872835723 : ℚ) / 1441529982779397137418444777480632483738860014379948394809171508199424)
    outputLower := ((-16548153121370093340742570961965005930935798797261015697326080 : ℚ) / 85921882556640931214001463501491098626784087084528708148549289)
    outputUpper := ((-3309630624274018668148514192393001186187159759452203139465216 : ℚ) / 17184378283412321533016773619066419976226238526957784827686571)
    expCertificate := {
      argument := ((8638539 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((8638539 : ℚ) / 16777216)
        terms := 8
        lower := ((53783121671461125703162221654667846576340027208872851442521769 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((10756626106376360430848925249701769566137426551826613486481067 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      }
      lower := ((53783121671461125703162221654667846576340027208872851442521769 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((10756626106376360430848925249701769566137426551826613486481067 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
    }
  }

theorem activation0_34_is_accepted : activation0_34.check = true := by
  norm_num [activation0_34, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_35 : Float32ActivationReplay where
  input := {
    word := 3201925779
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190554022
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14254739 : ℚ) / 33554432)
    runtimeValue := ((-5635795 : ℚ) / 33554432)
    localError := ((274699088955178208829205746253059869998790212656347072851452469195 : ℚ) / 43990976372142633792111180997396660278716209730312844827907865135852552192)
    outputLower := ((-220200865453367363163374549862011997512425073093828899715017605120 : ℚ) / 1311033259992081933978533178490300782880670122215534592506523881431)
    outputUpper := ((-220200865453367363163374549862011997512425073093828899715017605120 : ℚ) / 1311033290678532993317534639732014543777981540300511376836301877289)
    expCertificate := {
      argument := ((14254739 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((14254739 : ℚ) / 33554432)
        terms := 8
        lower := ((792699324435902030699717885984735373811108324540956935551712038871 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
        upper := ((792699355122353090038719347226449134708419742625933719881490034729 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((792699324435902030699717885984735373811108324540956935551712038871 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      upper := ((792699355122353090038719347226449134708419742625933719881490034729 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
    }
  }

theorem activation0_35_is_accepted : activation0_35.check = true := by
  norm_num [activation0_35, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_36 : Float32ActivationReplay where
  input := {
    word := 1067738501
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1065402603
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10773893 : ℚ) / 8388608)
    runtimeValue := ((8437995 : ℚ) / 8388608)
    localError := ((51903161216978646308052023804926326282300668466675338940729462424355319840189978423244873499974318753525589170838071358362031205 : ℚ) / 43909868866893605289373265963406394145284327170505978184937143180799319301428121267716296780675818670455495312110501798495620272488448)
    outputLower := ((107454852807401810908529099370981821754091904239997860595038115175830879118701228596853726711234079633357001676025076541030400 : ℚ) / 106825943557360694621901459818564417249301756374272528280879907075339529574878884951068557053418508146687225196768094485772769)
    outputUpper := ((5265287787562688734517925869178109265950503307759895169156867643615713076816360201245832608850469902034493082125228750510489600 : ℚ) / 5234464271890354787036569829393195408020535370171782754056113145446696198156848104919945809921719869429528154386341786205246481)
    expCertificate := {
      argument := ((-10773893 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((-10773893 : ℚ) / 16777216)
        terms := 8
        lower := ((1065309516262564280909836794469934158455353069886738395916058391 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((152187540578540319340008970325781187786908258625292577210342287 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      }
      lower := ((1134884365439578710098832551921213756334694453476107505086158351002764033442911024325920847054173048241888278562407865721508881 : ℚ) / 4099579906450776076937737277471981651685840916695675248969954794443932164713937080594024962867546821187639875823933920483737600)
      upper := ((23161047507344856317049678645666832521019288686605686465166543923422546621533230245068047607142042408163962424851075700390369 : ℚ) / 83664896050015838304851781172897584728282467687666841815713363151916982953345654706000509446276465738523262771917018785382400)
    }
  }

theorem activation0_36_is_accepted : activation0_36.check = true := by
  norm_num [activation0_36, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_37 : Float32ActivationReplay where
  input := {
    word := 3189450710
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180293229
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5084139 : ℚ) / 33554432)
    runtimeValue := ((-9399405 : ℚ) / 134217728)
    localError := ((123674188425313040614252587163751716414228044057494158361647045965 : ℚ) / 16724537117837406720140443999271728874666037464881863897551200646057689088)
    outputLower := ((-8726390788239442432178565867821219276393495826149747021504839680 : ℚ) / 124607511741798914636452981079149092447582214949911824149044729759)
    outputUpper := ((-8726390788239442432178565867821219276393495826149747021504839680 : ℚ) / 124607511742691745759103029960928327401474397367848931979769473121)
    expCertificate := {
      argument := ((5084139 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((5084139 : ℚ) / 33554432)
        terms := 8
        lower := ((67014852235556703161029059689641824773186459652736528931843413919 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((67014852236449534283679108571421059727078642070673636762568157281 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((67014852235556703161029059689641824773186459652736528931843413919 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((67014852236449534283679108571421059727078642070673636762568157281 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
    }
  }

theorem activation0_37_is_accepted : activation0_37.check = true := by
  norm_num [activation0_37, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_38 : Float32ActivationReplay where
  input := {
    word := 3209812494
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196082837
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6876423 : ℚ) / 8388608)
    runtimeValue := ((-8411797 : ℚ) / 33554432)
    localError := ((83551077297812364827691201115655596850070858418755911513976917 : ℚ) / 96420501452533662080420642229471137006022003587896824190715694153728)
    outputLower := ((-720377080979037758080210529065879625892869594877753179504640 : ℚ) / 2873554869071652355206627912207577735365092861291671520194879)
    outputUpper := ((-720377080979037758080210529065879625892869594877753179504640 : ℚ) / 2873564867475392030222372625050424705556354527098697082818241)
    expCertificate := {
      argument := ((6876423 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((6876423 : ℚ) / 8388608)
        terms := 8
        lower := ((1994760626117517048269617392958504437110763099066706688389439 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
        upper := ((1994770624521256723285362105801351407302024764873732251012801 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      }
      lower := ((1994760626117517048269617392958504437110763099066706688389439 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      upper := ((1994770624521256723285362105801351407302024764873732251012801 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
    }
  }

theorem activation0_38_is_accepted : activation0_38.check = true := by
  norm_num [activation0_38, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_39 : Float32ActivationReplay where
  input := {
    word := 1021720924
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1013544315
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3771991 : ℚ) / 134217728)
    runtimeValue := ((15299963 : ℚ) / 1073741824)
    localError := ((32271051066259158907659257954688776855237475507510854206263891298122259 : ℚ) / 71938223981727811274966515890720885830709077123165927323174544779358966248374272)
    outputLower := ((954663544879145795678008678707695396934426501353675708415350428139520 : ℚ) / 66997691971927705476960647749454608029414971473781324292695657144634953)
    outputUpper := ((190932708975829159135601735741539079386885300270735141683070085627904 : ℚ) / 13399538394385540947866429738809415122313507089071857482799395259917195)
    expCertificate := {
      argument := ((-3771991 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-3771991 : ℚ) / 134217728)
        terms := 8
        lower := ((6605631834263579719610341936880468192556946694591633217561285477114763 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
        upper := ((33028159171317899335680208739809873380632169501380202966505108230622793 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      }
      lower := ((6605631834263579719610341936880468192556946694591633217561285477114763 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
      upper := ((33028159171317899335680208739809873380632169501380202966505108230622793 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
    }
  }

theorem activation0_39_is_accepted : activation0_39.check = true := by
  norm_num [activation0_39, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_40 : Float32ActivationReplay where
  input := {
    word := 1066637742
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1063280744
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4836567 : ℚ) / 4194304)
    runtimeValue := ((1838093 : ℚ) / 2097152)
    localError := ((1010604069052078009460670505358033819111069687930769249370789876782181846460477633236244783271677770269165653385628855667 : ℚ) / 2130805513251772130826980357592322111221304460717357665473661945598701151007732653610258259894651008650818451135086651519270912)
    outputLower := ((890536470628793315875477333723214492009092508972427887509200573509152734064964534981306754244032727958617241443683532800 : ℚ) / 1016047836974704674270611892396248852377984132793876132183602801070476318485100435996341294256978368097553003123531006081)
    outputUpper := ((890536470628793315875477333723214492009092508972427887509200573509152734064964534981306754244032727958617241443683532800 : ℚ) / 1016047245622526231206407717510376983271267156943014939057188961791372848037592245869759683558774475407990670745414090881)
    expCertificate := {
      argument := ((-4836567 : ℚ) / 4194304)
      halvings := 1
      reduced := {
        argument := ((-4836567 : ℚ) / 8388608)
        terms := 8
        lower := ((493728593635404550331562009581150218690856754436612692404159 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
        upper := ((493729192498653943740566742532628817917717746095076376549441 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      }
      lower := ((243767924173194438645738531547562152691704267241892184365402411068156701316246917886040064963030128848180762135400497281 : ℚ) / 772279321449331792560669185962814830579562889701122754691786550723216146721345327983719618595744346559809908610013593600)
      upper := ((243768515525372881709942706433434021798421243092753377491816250347260171763755108012621675661234021537743094513517412481 : ℚ) / 772279321449331792560669185962814830579562889701122754691786550723216146721345327983719618595744346559809908610013593600)
    }
  }

theorem activation0_40_is_accepted : activation0_40.check = true := by
  norm_num [activation0_40, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_41 : Float32ActivationReplay where
  input := {
    word := 3205379969
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192874492
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9320321 : ℚ) / 16777216)
    runtimeValue := ((-3398015 : ℚ) / 16777216)
    localError := ((1290384639609767516692132547241309879451834943827067530272266365 : ℚ) / 31058023088433190508657655583065533435794923621587136874156021201764352)
    outputLower := ((-374937947263390930393362342213960667065082993642746571936235520 : ℚ) / 1851202433611940771857360338155361022698576666211315207133055997)
    outputUpper := ((-53562563894770132913337477459137238152154713377535224562319360 : ℚ) / 264457539325020894533309013813429920551366408085491982463497509)
    expCertificate := {
      argument := ((9320321 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((9320321 : ℚ) / 16777216)
        terms := 8
        lower := ((1176288455023164856129736259372072729639251408822542216306478077 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((168041256669481478000791288272960164400034228458524412345414949 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
      }
      lower := ((1176288455023164856129736259372072729639251408822542216306478077 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((168041256669481478000791288272960164400034228458524412345414949 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
    }
  }

theorem activation0_41_is_accepted : activation0_41.check = true := by
  norm_num [activation0_41, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_42 : Float32ActivationReplay where
  input := {
    word := 1059889545
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1055177256
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((11313545 : ℚ) / 16777216)
    runtimeValue := ((1873733 : ℚ) / 4194304)
    localError := ((1668830257299672377842558105553771061072476124359104081564564873 : ℚ) / 2563834321660030992789850250750404079274697236068165660897934737145856)
    outputLower := ((273072826906197767883563617172179604226345919457833733314314240 : ℚ) / 611266702277927222311288425059583531854864311632786128622460789)
    outputUpper := ((273072826906197767883563617172179604226345919457833733314314240 : ℚ) / 611265736022002933690512240111924190348314579979936042046054539)
    expCertificate := {
      argument := ((-11313545 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-11313545 : ℚ) / 16777216)
        terms := 8
        lower := ((206317348868737384253937792841951214512719425546672247550107787 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((206318315124661672874713977789610556019269157199522334126514037 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      }
      lower := ((206317348868737384253937792841951214512719425546672247550107787 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      upper := ((206318315124661672874713977789610556019269157199522334126514037 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
    }
  }

theorem activation0_42_is_accepted : activation0_42.check = true := by
  norm_num [activation0_42, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_43 : Float32ActivationReplay where
  input := {
    word := 1028215378
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1020150948
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6596905 : ℚ) / 134217728)
    runtimeValue := ((3379497 : ℚ) / 134217728)
    localError := ((134303718966204775816130418989113569019887480832562160297573080385819 : ℚ) / 254284323090773447139200866358647804394634171752485060274975609919316454014976)
    outputLower := ((47703679284880594096533663465491447752762800933153037361237207285760 : ℚ) / 1894565843722026401305205124308525058587150065246858151815649940962467)
    outputUpper := ((47703679284880594096533663465491447752762800933153037361237207285760 : ℚ) / 1894565843722024556602856795925981033916933372412894641233307258618717)
    expCertificate := {
      argument := ((-6596905 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-6596905 : ℚ) / 134217728)
        terms := 8
        lower := ((924007763704601523994844252793274329665996173201434031913577289646941 : ℚ) / 970558080017423032608012543132706704250937199211460609319729968971776)
        upper := ((924007763704603368697192581175818354336212866035397542495919971990691 : ℚ) / 970558080017423032608012543132706704250937199211460609319729968971776)
      }
      lower := ((924007763704601523994844252793274329665996173201434031913577289646941 : ℚ) / 970558080017423032608012543132706704250937199211460609319729968971776)
      upper := ((924007763704603368697192581175818354336212866035397542495919971990691 : ℚ) / 970558080017423032608012543132706704250937199211460609319729968971776)
    }
  }

theorem activation0_43_is_accepted : activation0_43.check = true := by
  norm_num [activation0_43, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_44 : Float32ActivationReplay where
  input := {
    word := 1042452965
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1034908312
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10654181 : ℚ) / 67108864)
    runtimeValue := ((1437267 : ℚ) / 16777216)
    localError := ((7199915784113623553484575692049983372946052932136401431530286974603 : ℚ) / 4125647519812088944937692535678456245032635058359678440522770404861989093376)
    outputLower := ((21066374083930497581844297759713124754204379970971410582551857725440 : ℚ) / 245907754889859278443607376752763079430818492805475685683071718019049)
    outputUpper := ((21066374083930497581844297759713124754204379970971410582551857725440 : ℚ) / 245907754886870917376142295341399684252299967906455900700257444671511)
    expCertificate := {
      argument := ((-10654181 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-10654181 : ℚ) / 67108864)
        terms := 8
        lower := ((113214267384488862136765580459974939530492147701764020519825612976151 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
        upper := ((113214267387477223204230661871338334709010672600783805502639886323689 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
      }
      lower := ((113214267384488862136765580459974939530492147701764020519825612976151 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
      upper := ((113214267387477223204230661871338334709010672600783805502639886323689 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
    }
  }

theorem activation0_44_is_accepted : activation0_44.check = true := by
  norm_num [activation0_44, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_45 : Float32ActivationReplay where
  input := {
    word := 1051394123
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1044859760
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((11206731 : ℚ) / 33554432)
    runtimeValue := ((816311 : ℚ) / 4194304)
    localError := ((1798961832399325875936207117546583914898930200308808570616008791 : ℚ) / 414534193496435815437202252712861056330691858918956832804624040768569344)
    outputLower := ((19235177119405546332901388346473996978162193809666293661140254720 : ℚ) / 98832653402432397708225787332740081865952458123912056161075601761)
    outputUpper := ((19235177119405546332901388346473996978162193809666293661140254720 : ℚ) / 98832652904853933080412036442429202897172445540081650080188587679)
    expCertificate := {
      argument := ((-11206731 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-11206731 : ℚ) / 33554432)
        terms := 8
        lower := ((41239993398611721604988115052921935222776690242906354862987271839 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((41239993896190186232801865943232814191556702826736760943874285921 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((41239993398611721604988115052921935222776690242906354862987271839 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((41239993896190186232801865943232814191556702826736760943874285921 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
    }
  }

theorem activation0_45_is_accepted : activation0_45.check = true := by
  norm_num [activation0_45, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_46 : Float32ActivationReplay where
  input := {
    word := 3168257072
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3159682254
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-883779 : ℚ) / 33554432)
    runtimeValue := ((-6977127 : ℚ) / 536870912)
    localError := ((2340802421578274579134895536622117728604592822764941223706989121 : ℚ) / 8952121987431545690949173003414656713133381592245242166456457490442747904)
    outputLower := ((-216701980257746302296173052369259695998301702826288279600496640 : ℚ) / 16674626595213163068423369905752421753729473039964665037498730217)
    outputUpper := ((-1516913861804224116073211366584817871988111919784017957203476480 : ℚ) / 116722386166492142223317403713103832200407903263077662838405697441)
    expCertificate := {
      argument := ((883779 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((883779 : ℚ) / 33554432)
        terms := 8
        lower := ((8447103808607132857648523992965669228815793711796765720755685097 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
        upper := ((59129726660249930747893482323596564526012147965902367621204381601 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((8447103808607132857648523992965669228815793711796765720755685097 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
      upper := ((59129726660249930747893482323596564526012147965902367621204381601 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
    }
  }

theorem activation0_46_is_accepted : activation0_46.check = true := by
  norm_num [activation0_46, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_47 : Float32ActivationReplay where
  input := {
    word := 1015553592
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1007239095
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1115079 : ℚ) / 67108864)
    runtimeValue := ((8994743 : ℚ) / 1073741824)
    localError := ((183551765473877775831472373155431338608023515957381746103113727773 : ℚ) / 897172174819590629286101256464990887743124912037720751527511962535751319552)
    outputLower := ((6999464325993244599457248234240981459600998406657511140605558784 : ℚ) / 835556699726349328911026247278778709231992170249783202565751934923)
    outputUpper := ((34997321629966222997286241171204907298004992033287555703027793920 : ℚ) / 4177783498631746643872199883816607924841402120967766958848288764169)
    expCertificate := {
      argument := ((-1115079 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-1115079 : ℚ) / 67108864)
        terms := 8
        lower := ((2071537665260602909913839330143199278463500212956784733762069213449 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
        upper := ((414307533052120582119354136544096979956411788647586757548508024779 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
      }
      lower := ((2071537665260602909913839330143199278463500212956784733762069213449 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
      upper := ((414307533052120582119354136544096979956411788647586757548508024779 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
    }
  }

theorem activation0_47_is_accepted : activation0_47.check = true := by
  norm_num [activation0_47, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_48 : Float32ActivationReplay where
  input := {
    word := 3210663641
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196291993
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14603993 : ℚ) / 16777216)
    runtimeValue := ((-8620953 : ℚ) / 33554432)
    localError := ((7038165813613447223964466179924813576177592569599963117892633157 : ℚ) / 5115063908593078400459526083678081305136513949335834991622584054841344)
    outputLower := ((-39165969764839145945925760083129369214456616416092074062905344 : ℚ) / 152440783637555789961204710116329232011333523670906871307569267)
    outputUpper := ((-195829848824195729729628800415646846072283082080460370314526720 : ℚ) / 762208056306293258717890243733218529501113695626753180901823937)
    expCertificate := {
      argument := ((14603993 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((14603993 : ℚ) / 16777216)
        terms := 8
        lower := ((107446518398304062246029771530776679140711839844988671919130739 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((537236730110034620142015550805455765148005276497162183959631297 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((107446518398304062246029771530776679140711839844988671919130739 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((537236730110034620142015550805455765148005276497162183959631297 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
    }
  }

theorem activation0_48_is_accepted : activation0_48.check = true := by
  norm_num [activation0_48, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_49 : Float32ActivationReplay where
  input := {
    word := 3202734426
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3191020324
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7531693 : ℚ) / 16777216)
    runtimeValue := ((-2934473 : ℚ) / 16777216)
    localError := ((119006510452174577505173591363942627218204089582260063868623677 : ℚ) / 17437412606940572725234555639849191415160033566468255367146726204899328)
    outputLower := ((-181791003518315557589089972286350999611027310817178004274282496 : ℚ) / 1039350784238611026122245528688978637168409440902963600584669483)
    outputUpper := ((-908955017591577787945449861431754998055136554085890021371412480 : ℚ) / 5196754107579094662973800806334605073919336323795478061369467433)
    expCertificate := {
      argument := ((7531693 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((7531693 : ℚ) / 16777216)
        terms := 8
        lower := ((634402397085345476685671081419005661332814286469699806088722731 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((3172012171812766915790928569984740194741360551629159088889733673 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((634402397085345476685671081419005661332814286469699806088722731 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      upper := ((3172012171812766915790928569984740194741360551629159088889733673 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
    }
  }

theorem activation0_49_is_accepted : activation0_49.check = true := by
  norm_num [activation0_49, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_50 : Float32ActivationReplay where
  input := {
    word := 1023509354
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1015254925
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4243893 : ℚ) / 134217728)
    runtimeValue := ((8621965 : ℚ) / 536870912)
    localError := ((810042232475603907358638630476990673741705607185595472557587295215689 : ℚ) / 797930605431918788271540957349802549782665927971246970806292454100218031374336)
    outputLower := ((23868855911125466561042114454832047532470158704628433119649818738688 : ℚ) / 1486261571630684264510014946292718033832806959694711437088050794043053)
    outputUpper := ((17049182793661047543601510324880033951764399074734595085464156241920 : ℚ) / 1061615408307631587443112140624304111436703170415348882995340274378409)
    expCertificate := {
      argument := ((-4243893 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-4243893 : ℚ) / 134217728)
        terms := 8
        lower := ((522416474964618791549771838883911497963960281964537433373268069394089 : ℚ) / 539198933343012795893340301740392613472742888450811449622072204984320)
        upper := ((731383064950466350259338523856168374970966915863575407617149707065005 : ℚ) / 754878506680217914250676422436549658861840043831136029470901086978048)
      }
      lower := ((522416474964618791549771838883911497963960281964537433373268069394089 : ℚ) / 539198933343012795893340301740392613472742888450811449622072204984320)
      upper := ((731383064950466350259338523856168374970966915863575407617149707065005 : ℚ) / 754878506680217914250676422436549658861840043831136029470901086978048)
    }
  }

theorem activation0_50_is_accepted : activation0_50.check = true := by
  norm_num [activation0_50, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_51 : Float32ActivationReplay where
  input := {
    word := 3213808199
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196910900
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9359943 : ℚ) / 8388608)
    runtimeValue := ((-2309965 : ℚ) / 8388608)
    localError := ((7875814366048410810959663599333253368102842998113969824959853427000270332777531599814825257565946135595148942059353022732587 : ℚ) / 68813215563231459533592638312852880060169355635582368975170447407699476370831901621700887420997338351376299749199474157533916037120)
    outputLower := ((-2258903259013882177017402382021358416806051753911811256224407713417472471872321610388725174386845976991270886070292645412864 : ℚ) / 8203174538997585717867927350145921714326066450546070215126329351389345690111148550713168075203578275606191128396925229732265)
    outputUpper := ((-56472581475347054425435059550533960420151293847795281405610192835436811796808040259718129359671149424781772151757316135321600 : ℚ) / 205079456086226321569613363792420687303662011542755404346200695968986124335533167635820798367939705155422025560189870178023809)
    expCertificate := {
      argument := ((9359943 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((9359943 : ℚ) / 16777216)
        terms := 8
        lower := ((78604647665245910594990428211817822531008422679941673409779059 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((393023356145309655835367773845695601405541351940514107179439297 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((6178690634577449383577686719295560404851577108967958981067092415861477954449945054123526118231950215760443041570291194925481 : ℚ) / 2024483904420136334290240630850361309474489341578111234059236935527867735661203496589641956971628059845748086826634034806784)
      upper := ((154467358475722913212357348021161654566799778003302623494719772580789430944003080221079749443649003659278323389524019307854209 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
    }
  }

theorem activation0_51_is_accepted : activation0_51.check = true := by
  norm_num [activation0_51, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_52 : Float32ActivationReplay where
  input := {
    word := 3211875658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196539195
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7908005 : ℚ) / 8388608)
    runtimeValue := ((-8868155 : ℚ) / 33554432)
    localError := ((69370341346551076646220687613497648980721646164505015727713585 : ℚ) / 27045872505792257805492584683455632927513164922160519851591969275904)
    outputLower := ((-213028987493762462484529103011636771446144850873655922524160 : ℚ) / 806029811674125725194590827329624680504595187966839070665597)
    outputUpper := ((-213028987493762462484529103011636771446144850873655922524160 : ℚ) / 806037677420569830228530890783713767326590376753780928009347)
    expCertificate := {
      argument := ((7908005 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((7908005 : ℚ) / 8388608)
        terms := 8
        lower := ((580054149200205217696502408094148689524910391966133828201341 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
        upper := ((580062014946649322730442471548237776346905580753075685545091 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      }
      lower := ((580054149200205217696502408094148689524910391966133828201341 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      upper := ((580062014946649322730442471548237776346905580753075685545091 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
    }
  }

theorem activation0_52_is_accepted : activation0_52.check = true := by
  norm_num [activation0_52, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_53 : Float32ActivationReplay where
  input := {
    word := 3190465981
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3181147666
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11183549 : ℚ) / 67108864)
    runtimeValue := ((-5126921 : ℚ) / 67108864)
    localError := ((5283408966989028144900383725430098810293771891452629726515378976681 : ℚ) / 2158290960818658594653577996061182876070445553888648516845215783704053415936)
    outputLower := ((-2457009619248869239440024263884363608904727839500310804943224176640 : ℚ) / 32161041510383167783224254787879927099800788669119008136469360943199)
    outputUpper := ((-2457009619248869239440024263884363608904727839500310804943224176640 : ℚ) / 32161041510872571378024531016294221268172795592516524263755376746401)
    expCertificate := {
      argument := ((11183549 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((11183549 : ℚ) / 67108864)
        terms := 8
        lower := ((17417320676785161645515730912166066575155475313042132560865824088159 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
        upper := ((17417320677274565240316007140580360743527482236439648688151839891361 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      }
      lower := ((17417320676785161645515730912166066575155475313042132560865824088159 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      upper := ((17417320677274565240316007140580360743527482236439648688151839891361 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
    }
  }

theorem activation0_53_is_accepted : activation0_53.check = true := by
  norm_num [activation0_53, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_54 : Float32ActivationReplay where
  input := {
    word := 3218626255
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196504287
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14177999 : ℚ) / 8388608)
    runtimeValue := ((-8833247 : ℚ) / 33554432)
    localError := ((266906836085568910478214614989020603913962700777519251242142100930828341714640605120219168755483175965793052804589139568216470313 : ℚ) / 98128872521384470474114464073347016431313367131806212548727968770708342212315285200863936153206999442855648925349318298034179745513472)
    outputLower := ((-769877961133310487112034190790659565205311786215442644016223087650819298788998328509926866551387521468951132188795133440819200 : ℚ) / 2924468294423355772319867136280149711111586306446975843570469879231105512747624075438497547900885326947440174977461048902099721)
    outputUpper := ((-628471805006784071111864645543395563432907580584034811441814765429240243909386390620348462490928588954245822194934802808832 : ℚ) / 2387346188438733200959009165440827004381942099973021776536722041840055825420773138137840999668172219856973124314217025932353)
    expCertificate := {
      argument := ((14177999 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((14177999 : ℚ) / 16777216)
        terms := 8
        lower := ((1571292275780933474485103639540085691343558250835170077265899389 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((44894344922208391257262160901213583703462368057054172557067297 : ℚ) / 19283256531107883306503545108093951230266435925393514023616512)
      }
      lower := ((2468959415928825097104562994338818416479826204591900815907141568737335272223853288705828107582269013482146855441468391070573321 : ℚ) / 455508878494530675215304141941331294631760101855075027663328310493770240523770786732669440318616313465293319535992657831526400)
      upper := ((2015502205994218364048556804672393294478464465805613590689107094498202567850348006111172068795832372130203067550141386886209 : ℚ) / 371843982444514836910452360768433709903477634167408185847614947341853257570425132026668930872339847726770056764075639046144)
    }
  }

theorem activation0_54_is_accepted : activation0_54.check = true := by
  norm_num [activation0_54, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_55 : Float32ActivationReplay where
  input := {
    word := 3206539656
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3193900910
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1310001 : ℚ) / 2097152)
    runtimeValue := ((-7309239 : ℚ) / 33554432)
    localError := ((4192185512242669946221841137884246654383906084117457117 : ℚ) / 36864499338852300851264442723857926785559739541586109431545856)
    outputLower := ((-239321075800640019218718166817895434004036410903887872 : ℚ) / 1098647693957456971742643199081955158280126438784185333)
    outputUpper := ((-1196605379003200096093590834089477170020182054519439360 : ℚ) / 5493240947808231159252058556900117411570101922723920951)
    expCertificate := {
      argument := ((1310001 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((1310001 : ℚ) / 2097152)
        terms := 8
        lower := ((715523808740984757153056442294377862375441658238284789 : ℚ) / 383123885216472214589586756787577295904684780545900544)
        upper := ((3577621521725870086304124772962230932046678019994418231 : ℚ) / 1915619426082361072947933783937886479523423902729502720)
      }
      lower := ((715523808740984757153056442294377862375441658238284789 : ℚ) / 383123885216472214589586756787577295904684780545900544)
      upper := ((3577621521725870086304124772962230932046678019994418231 : ℚ) / 1915619426082361072947933783937886479523423902729502720)
    }
  }

theorem activation0_55_is_accepted : activation0_55.check = true := by
  norm_num [activation0_55, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_56 : Float32ActivationReplay where
  input := {
    word := 3189830092
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180614285
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-2636915 : ℚ) / 16777216)
    runtimeValue := ((-9720461 : ℚ) / 134217728)
    localError := ((217972338166774573677568659948348905986697594102948096022507547 : ℚ) / 39317647442157325059814090831106731637312769785529191317298900614774784)
    outputLower := ((-21215567515497470424424503418264802089840539229957059992616960 : ℚ) / 292939301149229146985814652078648892323022855710455710569760953)
    outputUpper := ((-21215567515497470424424503418264802089840539229957059992616960 : ℚ) / 292939301152034259538304884841619841052966034174474596120229703)
    expCertificate := {
      argument := ((2636915 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((2636915 : ℚ) / 16777216)
        terms := 8
        lower := ((157956505431473963840289836321991233711157804232701112404445369 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
        upper := ((157956505434279076392780069084962182441100982696719997954914119 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
      }
      lower := ((157956505431473963840289836321991233711157804232701112404445369 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
      upper := ((157956505434279076392780069084962182441100982696719997954914119 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
    }
  }

theorem activation0_56_is_accepted : activation0_56.check = true := by
  norm_num [activation0_56, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_57 : Float32ActivationReplay where
  input := {
    word := 3209565042
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3195972957
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6752697 : ℚ) / 8388608)
    runtimeValue := ((-16690525 : ℚ) / 67108864)
    localError := ((20557825395495953511323606062827552821652617905711433524715195 : ℚ) / 27268734676486312302319111004857021430287306688965797185838169194496)
    outputLower := ((-101059355872250635704783543898406361067331140763201600225280 : ℚ) / 406335810966585759853111371470347366188277403845873433140489)
    outputUpper := ((-20211871174450127140956708779681272213466228152640320045056 : ℚ) / 81267409240584771368841197035123222168606960257870617727947)
    expCertificate := {
      argument := ((6752697 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((6752697 : ℚ) / 8388608)
        terms := 8
        lower := ((280793776258852144576395583006194037866230294956592742882569 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
        upper := ((56159002299038048313498039342292556504197538480014479676363 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
      }
      lower := ((280793776258852144576395583006194037866230294956592742882569 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
      upper := ((56159002299038048313498039342292556504197538480014479676363 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
    }
  }

theorem activation0_57_is_accepted : activation0_57.check = true := by
  norm_num [activation0_57, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_58 : Float32ActivationReplay where
  input := {
    word := 3199908716
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189312911
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3059419 : ℚ) / 8388608)
    runtimeValue := ((-10030479 : ℚ) / 67108864)
    localError := ((77691194786723772880840597165592528579265036009885987655715 : ℚ) / 28780898752678498846875268507075379872800142026140104921802631806976)
    outputLower := ((-64101214503872339406345410008203520323561747236646167773184 : ℚ) / 428868811617471260530878134177258310806753367575110568431059)
    outputUpper := ((-320506072519361697031727050041017601617808736183230838865920 : ℚ) / 2144344073438533029496491870455782821769554601985118142986977)
    expCertificate := {
      argument := ((3059419 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((3059419 : ℚ) / 8388608)
        terms := 8
        lower := ((253109963026644199143476030327443651155887415130117602069971 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((1265549830484397722559481351206709523515224839760153311181537 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      }
      lower := ((253109963026644199143476030327443651155887415130117602069971 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      upper := ((1265549830484397722559481351206709523515224839760153311181537 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
    }
  }

theorem activation0_58_is_accepted : activation0_58.check = true := by
  norm_num [activation0_58, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_59 : Float32ActivationReplay where
  input := {
    word := 3199929984
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189326585
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-95773 : ℚ) / 262144)
    runtimeValue := ((-10044153 : ℚ) / 67108864)
    localError := ((5022765398582733740250208257882092666272557728097 : ℚ) / 1178364154446731859126696243063590077194863930631180517376)
    outputLower := ((-2628046562570879342157439879022659104888135352320 : ℚ) / 17558994083048721356760213514268880261926954507351)
    outputUpper := ((-2628046562570879342157439879022659104888135352320 : ℚ) / 17558994210462746905188206479900927501840351978409)
    expCertificate := {
      argument := ((95773 : ℚ) / 262144)
      halvings := 0
      reduced := {
        argument := ((95773 : ℚ) / 262144)
        terms := 8
        lower := ((10365665711810683556226452228243424774557911522391 : ℚ) / 7193328371238037800533761286025455487369042984960)
        upper := ((10365665839224709104654445193875472014471308993449 : ℚ) / 7193328371238037800533761286025455487369042984960)
      }
      lower := ((10365665711810683556226452228243424774557911522391 : ℚ) / 7193328371238037800533761286025455487369042984960)
      upper := ((10365665839224709104654445193875472014471308993449 : ℚ) / 7193328371238037800533761286025455487369042984960)
    }
  }

theorem activation0_59_is_accepted : activation0_59.check = true := by
  norm_num [activation0_59, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_60 : Float32ActivationReplay where
  input := {
    word := 1069754505
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1067468001
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((12789897 : ℚ) / 8388608)
    runtimeValue := ((10503393 : ℚ) / 8388608)
    localError := ((115802995482551005157415740925329216288106901039323056809694190480769450004252538570714324534659396456539592055209964516827511 : ℚ) / 20679484940378730732107394829180144460040997355093007501113745654799779863629393961549261753757924452082320735437416053687474716672)
    outputLower := ((77166976379428471450596290152642558696758278627341568881751693201056328322678862862054621864991053365877133364855367427686400 : ℚ) / 61629968337335622380482048058317758643685716965975132588701298815991935911235698940535969350524714411340289987984610585249409)
    outputUpper := ((3086679055177138858023851606105702347870331145093662755270067728042253132907154514482184874599642134635085334594214697107456 : ℚ) / 2465186708018628446114944795272367532258152646433473527564256865358326418832468266671807975024929577360429851464917189322409)
    expCertificate := {
      argument := ((-12789897 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((-12789897 : ℚ) / 16777216)
        terms := 8
        lower := ((20992922702627476492775361186413531407392848465990610392645875 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((104966045590144120772369526759180342281367881996739377451301697 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((440702803598492111824704164422006222783663304855362293505019929830458683171264770082166018053301517514681764638283154515625 : ℚ) / 2024483904420136334290240630850361309474489341578111234059236935527867735661203496589641956971628059845748086826634034806784)
      upper := ((11017870726832214023226032287058725906823483426522351737220375427795242519705611525794920426234012915196587817318759715079809 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
    }
  }

theorem activation0_60_is_accepted : activation0_60.check = true := by
  norm_num [activation0_60, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_61 : Float32ActivationReplay where
  input := {
    word := 3182916749
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3173990008
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-12022925 : ℚ) / 134217728)
    runtimeValue := ((-1435599 : ℚ) / 33554432)
    localError := ((1108977049335419918557559996362348722171226714554636667097671417610811 : ℚ) / 477294559656121914847108938077879202118732414718177338633721617787371177115648)
    outputLower := ((-608583010951834400744965854555417480062271609014318513305022575411200 : ℚ) / 14224486340763246287470330454915576221380441896188478615867790752272939)
    outputUpper := ((-608583010951834400744965854555417480062271609014318513305022575411200 : ℚ) / 14224486340764818037960199656423306528292072257941285927108574443679189)
    expCertificate := {
      argument := ((12022925 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((12022925 : ℚ) / 134217728)
        terms := 8
        lower := ((7430579780641285059214242652986629291623881501708254350629680969470507 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
        upper := ((7430579780642856809704111854494359598535511863461061661870464660876757 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
      }
      lower := ((7430579780641285059214242652986629291623881501708254350629680969470507 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
      upper := ((7430579780642856809704111854494359598535511863461061661870464660876757 : ℚ) / 6793906560121961228256087801928946929756560394480224265238109782802432)
    }
  }

theorem activation0_61_is_accepted : activation0_61.check = true := by
  norm_num [activation0_61, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_62 : Float32ActivationReplay where
  input := {
    word := 3198908151
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188655324
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11237111 : ℚ) / 33554432)
    runtimeValue := ((-2343223 : ℚ) / 16777216)
    localError := ((20330629733412964409543728850272946246643582222697978443456744227 : ℚ) / 4170331450652635700715791142346743460257701420836402962854066926794047488)
    outputLower := ((-34717178159425498897512623014345804568976596843175715263611928576 : ℚ) / 248571124711789828581559130093261209741693819811129746607188399243)
    outputUpper := ((-173585890797127494487563115071729022844882984215878576318059642880 : ℚ) / 1242855628135200511957123774544704622323961127654762999172208646473)
    expCertificate := {
      argument := ((11237111 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((11237111 : ℚ) / 33554432)
        terms := 8
        lower := ((144904337600553847925796071592148127927781460276214215216226030731 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
        upper := ((724521692579020608678308482039139213254399329980185342217396803913 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((144904337600553847925796071592148127927781460276214215216226030731 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      upper := ((724521692579020608678308482039139213254399329980185342217396803913 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
    }
  }

theorem activation0_62_is_accepted : activation0_62.check = true := by
  norm_num [activation0_62, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activation0_63 : Float32ActivationReplay where
  input := {
    word := 1046516826
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1039735731
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((7359021 : ℚ) / 33554432)
    runtimeValue := ((16325555 : ℚ) / 134217728)
    localError := ((81100499606518184231271193595619934595385858776135038783882322195 : ℚ) / 13937635953034575720860136789095536601320193062410787781852953058736078848)
    outputLower := ((12630986891755046407404113453857098891392336056911177581089259520 : ℚ) / 103843479998667357272357767739113692949117668438038138910032459041)
    outputUpper := ((12630986891755046407404113453857098891392336056911177581089259520 : ℚ) / 103843479981464906106521060592974943043322373841197126567559236319)
    expCertificate := {
      argument := ((-7359021 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-7359021 : ℚ) / 33554432)
        terms := 8
        lower := ((46250820475222694631097139203467675368926618544021831350357920479 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((46250820492425145796933846349606425274721913140862843692831143201 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((46250820475222694631097139203467675368926618544021831350357920479 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((46250820492425145796933846349606425274721913140862843692831143201 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
    }
  }

theorem activation0_63_is_accepted : activation0_63.check = true := by
  norm_num [activation0_63, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay0 : Float32AffineSiLUReplay 64 64 where
  affine := GeneratedAuthenticatedAffineReplayChunkedFixture.replay0
  activation := ![activation0_0, activation0_1, activation0_2, activation0_3, activation0_4, activation0_5, activation0_6, activation0_7, activation0_8, activation0_9, activation0_10, activation0_11, activation0_12, activation0_13, activation0_14, activation0_15, activation0_16, activation0_17, activation0_18, activation0_19, activation0_20, activation0_21, activation0_22, activation0_23, activation0_24, activation0_25, activation0_26, activation0_27, activation0_28, activation0_29, activation0_30, activation0_31, activation0_32, activation0_33, activation0_34, activation0_35, activation0_36, activation0_37, activation0_38, activation0_39, activation0_40, activation0_41, activation0_42, activation0_43, activation0_44, activation0_45, activation0_46, activation0_47, activation0_48, activation0_49, activation0_50, activation0_51, activation0_52, activation0_53, activation0_54, activation0_55, activation0_56, activation0_57, activation0_58, activation0_59, activation0_60, activation0_61, activation0_62, activation0_63]
  radius := ((62355640572109882891 : ℚ) / 36893488147419103232)

theorem replay0_is_accepted : replay0.check = true := by
  refine replay0.check_of_observed_radius_and_affine_budget
    ((14177999 : ℚ) / 8388608) GeneratedAuthenticatedAffineReplayChunkedFixture.replay0_is_accepted ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [replay0]
  · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
      Float32AffineReplay.ofRows]
  · intro row
    fin_cases row
    · exact activation0_0_is_accepted
    · exact activation0_1_is_accepted
    · exact activation0_2_is_accepted
    · exact activation0_3_is_accepted
    · exact activation0_4_is_accepted
    · exact activation0_5_is_accepted
    · exact activation0_6_is_accepted
    · exact activation0_7_is_accepted
    · exact activation0_8_is_accepted
    · exact activation0_9_is_accepted
    · exact activation0_10_is_accepted
    · exact activation0_11_is_accepted
    · exact activation0_12_is_accepted
    · exact activation0_13_is_accepted
    · exact activation0_14_is_accepted
    · exact activation0_15_is_accepted
    · exact activation0_16_is_accepted
    · exact activation0_17_is_accepted
    · exact activation0_18_is_accepted
    · exact activation0_19_is_accepted
    · exact activation0_20_is_accepted
    · exact activation0_21_is_accepted
    · exact activation0_22_is_accepted
    · exact activation0_23_is_accepted
    · exact activation0_24_is_accepted
    · exact activation0_25_is_accepted
    · exact activation0_26_is_accepted
    · exact activation0_27_is_accepted
    · exact activation0_28_is_accepted
    · exact activation0_29_is_accepted
    · exact activation0_30_is_accepted
    · exact activation0_31_is_accepted
    · exact activation0_32_is_accepted
    · exact activation0_33_is_accepted
    · exact activation0_34_is_accepted
    · exact activation0_35_is_accepted
    · exact activation0_36_is_accepted
    · exact activation0_37_is_accepted
    · exact activation0_38_is_accepted
    · exact activation0_39_is_accepted
    · exact activation0_40_is_accepted
    · exact activation0_41_is_accepted
    · exact activation0_42_is_accepted
    · exact activation0_43_is_accepted
    · exact activation0_44_is_accepted
    · exact activation0_45_is_accepted
    · exact activation0_46_is_accepted
    · exact activation0_47_is_accepted
    · exact activation0_48_is_accepted
    · exact activation0_49_is_accepted
    · exact activation0_50_is_accepted
    · exact activation0_51_is_accepted
    · exact activation0_52_is_accepted
    · exact activation0_53_is_accepted
    · exact activation0_54_is_accepted
    · exact activation0_55_is_accepted
    · exact activation0_56_is_accepted
    · exact activation0_57_is_accepted
    · exact activation0_58_is_accepted
    · exact activation0_59_is_accepted
    · exact activation0_60_is_accepted
    · exact activation0_61_is_accepted
    · exact activation0_62_is_accepted
    · exact activation0_63_is_accepted
  · intro row
    fin_cases row
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro row
    fin_cases row
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro row
    fin_cases row
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplayChunkedFixture.replay0,
        GeneratedAuthenticatedAffineReplayChunkedFixture.replay0Output,
        Float32AffineReplay.ofRows]

def certificateBatch : Float32AffineSiLUReplayBatch 64 64 where
  expectedCount := 1
  entries := [replay0]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32AffineSiLUReplayBatch.check,
    replay0_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end

end GeneratedAuthenticatedAffineSiLUReplaySite1Invocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
