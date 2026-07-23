import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixture

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedAffineSiLUReplaySite0Invocation0Fixture

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
-- Affine sidecar SHA-256: d0c360d853c9a00f1ce66ddd0f99fcb5fdcc569fa818ba195c7363bd1479f988
-- The imported affine theorem checks arithmetic; endpoint hashes bind it to the trace.
-- Source invocation indices: 0
-- Hidden affine-SiLU site: 0 (base_hidden_transition)

def activation0_0 : Float32ActivationReplay where
  input := {
    word := 1067559524
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1065094412
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2648729 : ℚ) / 2097152)
    runtimeValue := ((4129603 : ℚ) / 4194304)
    localError := ((107458585448216434360223194952270269576062378791816751870344482742270989786189163156345422727510256580216540280983517 : ℚ) / 104809846848903417082512702364363482881639184850420351604858881595003040345923599161048058036533561497967211990463486623744)
    outputLower := ((48222209274732897499276944236350870235555391320751624591029746514848328681026953688369878862612669330800568537448448 : ℚ) / 48977742250842711803243370776310607108538499088719498973293607000635664696531110873985065088959168165272410824164473)
    outputUpper := ((24603167997312702805753542977730035834467036388138583975015176793289963612768853922637693297251361903469677825228800 : ℚ) / 24988614761567930479648757544604178162011905872922027493681641005278358541947269239675535687573805212489893910995361)
    expCertificate := {
      argument := ((-2648729 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((-2648729 : ℚ) / 4194304)
        terms := 8
        lower := ((2347096751948808810383379786786977829070594662364287411281 : ℚ) / 4413587157693759912072039438192890448821968671888774266880)
        upper := ((3285944174459833766067379371484769895259596304674285525493 : ℚ) / 6179022020771263876900855213470046628350756140644283973632)
      }
      lower := ((5508863163008648154242249682594701122147044539256859158087086771001604004036660966210230715371179682061812446060961 : ℚ) / 19479751598559282325406507862009477039864861333665168335594554234276754537910608273465304972202625530428081464934400)
      upper := ((10797429117666518445446615366772032110403370874735769035528280701453225802226318657993067343442022125633371152893049 : ℚ) / 38180313133176193357796755409538574998135128213983729937765326299182438894304792215991997745517146039639039671271424)
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
    word := 1029691332
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1021703469
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3667441 : ℚ) / 67108864)
    runtimeValue := ((15070509 : ℚ) / 536870912)
    localError := ((5308699690546173684558552132291865164668668983117060236253148330669 : ℚ) / 15409983375535782164509060858710095024047296747094201379341407169324796346368)
    outputLower := ((805731509293489236052094198931335156505789349376021811930343669760 : ℚ) / 28703330784171479390501882648861623731818550180367685189204885982081)
    outputUpper := ((805731509293489236052094198931335156505789349376021811930343669760 : ℚ) / 28703330784171413936669120301883844703523994883697855061556039693439)
    expCertificate := {
      argument := ((-3667441 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-3667441 : ℚ) / 67108864)
        terms := 8
        lower := ((13959609950573407798960596426169984178878681527620979485952502838399 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
        upper := ((13959609950573473252793358773147763207173236824290809613601349127041 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      }
      lower := ((13959609950573407798960596426169984178878681527620979485952502838399 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      upper := ((13959609950573473252793358773147763207173236824290809613601349127041 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
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
    word := 3196233070
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3185844902
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4281015 : ℚ) / 16777216)
    runtimeValue := ((-7475539 : ℚ) / 67108864)
    localError := ((2359565333178790007256397057430996218331889438873057861970513 : ℚ) / 988105305965717296733539088005280525216219388137086387114550547709952)
    outputLower := ((-1640159099469995797741239749608970217427394115788708417372160 : ℚ) / 14723916440691311608754680872042186933997562350885367201485493)
    outputUpper := ((-11481113696289970584188678247262791521991758810520958921605120 : ℚ) / 103067415129965924048516033068791476743450429035497783185554701)
    expCertificate := {
      argument := ((4281015 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((4281015 : ℚ) / 16777216)
        terms := 8
        lower := ((8296164263655350506586832502677536523908750375754195860279989 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
        upper := ((58073149890714196333341094483238923872828745209579583797116173 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((8296164263655350506586832502677536523908750375754195860279989 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      upper := ((58073149890714196333341094483238923872828745209579583797116173 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
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
    word := 3185178446
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3176030409
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7142311 : ℚ) / 67108864)
    runtimeValue := ((-13525193 : ℚ) / 268435456)
    localError := ((76396719855560026825019720845091735039019670951402713645916282275677 : ℚ) / 15047862137115307829831415142660479839311988999599035676122946009058812887040)
    outputLower := ((-14122399023422984471005319712183827905338405581325189283838573936640 : ℚ) / 280288274159818211422285889712613594549742899013387556356511219699767)
    outputUpper := ((-2824479804684596894201063942436765581067681116265037856767714787328 : ℚ) / 56057654831988021097449269677178859112083870916064961538176782462965)
    expCertificate := {
      argument := ((7142311 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((7142311 : ℚ) / 67108864)
        terms := 8
        lower := ((147594786657436156182909174831188849827935078808695676176079388004407 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
        upper := ((29518957331511610049573926700893910167722306875126585502090416123893 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
      }
      lower := ((147594786657436156182909174831188849827935078808695676176079388004407 : ℚ) / 132693487502382055239376714881424744721807820204691880180431831695360)
      upper := ((29518957331511610049573926700893910167722306875126585502090416123893 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
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
    word := 1048899998
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1041636217
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4356303 : ℚ) / 16777216)
    runtimeValue := ((9837433 : ℚ) / 67108864)
    localError := ((4367511641492401292010726347330326032823449343931536204542719 : ℚ) / 3820368850451608868013273507927232645729713371220171592932528612179968)
    outputLower := ((8345018652700867789166302786769966684407330117732240887644160 : ℚ) / 56927932097591434409242052183848888021381502806032697253833783)
    outputUpper := ((8345018652700867789166302786769966684407330117732240887644160 : ℚ) / 56927932060533894121844671784747133340384265351596051349230537)
    expCertificate := {
      argument := ((-4356303 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-4356303 : ℚ) / 16777216)
        terms := 8
        lower := ((24789171175354088611005429937923881289940205475940194643203017 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((24789171212411628898402810337025635970937442930376840547806263 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      }
      lower := ((24789171175354088611005429937923881289940205475940194643203017 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((24789171212411628898402810337025635970937442930376840547806263 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
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
    word := 3196461385
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3186184765
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8790345 : ℚ) / 33554432)
    runtimeValue := ((-15290941 : ℚ) / 134217728)
    localError := ((24545124297504383357680196995770879588521620178280326717340898841 : ℚ) / 3554992901360912352440737541982238148609262877093740258643568484205723648)
    outputLower := ((-3017540851398698642444224895636130946071662638173987689233121280 : ℚ) / 26486761118821957612405103255688069835089557110076242893516251891)
    outputUpper := ((-3017540851398698642444224895636130946071662638173987689233121280 : ℚ) / 26486761133081557992404233977066264663705698230070920725491408141)
    expCertificate := {
      argument := ((8790345 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((8790345 : ℚ) / 33554432)
        terms := 8
        lower := ((14968229217573515317320318977786616300210406050641183850075988723 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((14968229231833115697319449699164811128826547170635861682051144973 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((14968229217573515317320318977786616300210406050641183850075988723 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((14968229231833115697319449699164811128826547170635861682051144973 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
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
    word := 1025015602
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1016813015
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4997017 : ℚ) / 134217728)
    runtimeValue := ((10180055 : ℚ) / 536870912)
    localError := ((1490427648686549332358670439801325025168108749367001605675783208977145 : ℚ) / 5115429558559555590022344608939223433952821549311920896632662040686854011879424)
    outputLower := ((180672676314950853218652047747648084802773052841128977373281459896320 : ℚ) / 9528230053483612071764365972837849397124390209674687863574665115562927)
    outputUpper := ((1264708734204655972530564334233536593619411369887902841612970219274240 : ℚ) / 66697610374385277504589321333993477857197903351486188451919331008042551)
    expCertificate := {
      argument := ((-4997017 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-4997017 : ℚ) / 134217728)
        terms := 8
        lower := ((32728077573775471363308882324348743208415101379085067125728782094030391 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
        upper := ((4675439653396496908724303257174315875869704213617384816976015270704047 : ℚ) / 4852790400087115163040062715663533521254685996057303046598649844858880)
      }
      lower := ((32728077573775471363308882324348743208415101379085067125728782094030391 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      upper := ((4675439653396496908724303257174315875869704213617384816976015270704047 : ℚ) / 4852790400087115163040062715663533521254685996057303046598649844858880)
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
    word := 3189746847
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180544020
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-10464415 : ℚ) / 67108864)
    runtimeValue := ((-2412549 : ℚ) / 33554432)
    localError := ((1593472765755698251878788916145032367052463745914259400136147923721 : ℚ) / 1931249200395947820862547843992949059133933194122607497289226468340266958848)
    outputLower := ((-4138230446047304018073565619754506111258436980448009912187795537920 : ℚ) / 57555711280661193497884448954047433348162259565230332220981604910539)
    outputUpper := ((-4138230446047304018073565619754506111258436980448009912187795537920 : ℚ) / 57555711281178826715426082730083139512954151455241665163315131316789)
    expCertificate := {
      argument := ((10464415 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((10464415 : ℚ) / 67108864)
        terms := 8
        lower := ((31017013780184782450009105977762484403800695524291956184895238571467 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
        upper := ((31017013780702415667550739753798190568592587414303289127228764977717 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
      }
      lower := ((31017013780184782450009105977762484403800695524291956184895238571467 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
      upper := ((31017013780702415667550739753798190568592587414303289127228764977717 : ℚ) / 26538697500476411047875342976284948944361564040938376036086366339072)
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
    word := 3189390733
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180242278
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-10108301 : ℚ) / 67108864)
    runtimeValue := ((-4674227 : ℚ) / 67108864)
    localError := ((217924012036972776514402248429932023669742536799159102309126321745 : ℚ) / 61134635920030285152464320232699189577622406129158954605704205765651202048)
    outputLower := ((-317254168744554602758810370311997388207769278208156222653705748480 : ℚ) / 4554885321826658690593331480254510805359706441225966588007493887849)
    outputUpper := ((-63450833748910920551762074062399477641553855641631244530741149696 : ℚ) / 910977064371560292727713588367390477323865981834515252794388022507)
    expCertificate := {
      argument := ((10108301 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((10108301 : ℚ) / 67108864)
        terms := 8
        lower := ((2448639488455514956634970926581102158981804533214984362921274337129 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
        upper := ((489727897697331545936041477632708748048285600232318807777144112363 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
      }
      lower := ((2448639488455514956634970926581102158981804533214984362921274337129 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
      upper := ((489727897697331545936041477632708748048285600232318807777144112363 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
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
    word := 3195662702
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3185284870
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8190135 : ℚ) / 33554432)
    runtimeValue := ((-7195523 : ℚ) / 67108864)
    localError := ((10914911169116878756710451428952825095239195790517732267798379687 : ℚ) / 1759688038560968317129918305194138459024811242396971702529670769817944064)
    outputLower := ((-2811501362116080848468965878542972241249306674664204040132362240 : ℚ) / 26221395113482599215655301588686383650076556837513621189142328051)
    outputUpper := ((-2811501362116080848468965878542972241249306674664204040132362240 : ℚ) / 26221395121580798773212552481441152658621738789928191446717484301)
    expCertificate := {
      argument := ((8190135 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((8190135 : ℚ) / 33554432)
        terms := 8
        lower := ((14702863212234156920570517310784930115197405778078562145702064883 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((14702863220332356478127768203539699123742587730493132403277221133 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((14702863212234156920570517310784930115197405778078562145702064883 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((14702863220332356478127768203539699123742587730493132403277221133 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
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
    word := 3191192717
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3181749974
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11910285 : ℚ) / 67108864)
    runtimeValue := ((-5428075 : ℚ) / 67108864)
    localError := ((2564578655267317770688940467233137096447885320051370509634124145295 : ℚ) / 434203507968008980086469774090171874971638422807778621573690991805626056704)
    outputLower := ((-74762070642449953101301945230388921200707642514868323298427535360 : ℚ) / 924305209000492290348057329594703750993021915231612075815117533973)
    outputUpper := ((-523334494497149671709113616612722448404953497604078263088992747520 : ℚ) / 6470136463165417016841020794066367670471048694964924776162072894061)
    expCertificate := {
      argument := ((11910285 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((11910285 : ℚ) / 67108864)
        terms := 8
        lower := ((503056042326263543556385218860022021717441533629415630797873623829 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
        upper := ((3521392296445815789299316018923595565541986023749549661041365523053 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
      }
      lower := ((503056042326263543556385218860022021717441533629415630797873623829 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
      upper := ((3521392296445815789299316018923595565541986023749549661041365523053 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
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
    word := 1032470698
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1024387795
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4530261 : ℚ) / 67108864)
    runtimeValue := ((9366227 : ℚ) / 268435456)
    localError := ((17358369443825492548041569654694396167843360489197816239672338718707 : ℚ) / 7657121558163229557089617032824227474776740716825676946018480135819206066176)
    outputLower := ((995291821469910992434942052985956512305739550736757850974936104960 : ℚ) / 28525000654769053895360294851750982831331866669750500269303024321121)
    outputUpper := ((995291821469910992434942052985956512305739550736757850974936104960 : ℚ) / 28525000654768699069075390835648935360581484269609261049811264339359)
    expCertificate := {
      argument := ((-4530261 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-4530261 : ℚ) / 67108864)
        terms := 8
        lower := ((13781279821170692931366866959935074835936170913532385474207727484319 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
        upper := ((13781279821171047757651770976037122306686553313673624693699487466081 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      }
      lower := ((13781279821170692931366866959935074835936170913532385474207727484319 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      upper := ((13781279821171047757651770976037122306686553313673624693699487466081 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
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
    word := 3198646424
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188478670
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1371923 : ℚ) / 4194304)
    runtimeValue := ((-4598119 : ℚ) / 33554432)
    localError := ((825695688604349357786258308540232048531579594013676806211 : ℚ) / 117831074838375777944266731356738650325306423823185291404600410112)
    outputLower := ((-481216250590061837820180937621109075802102226117743083520 : ℚ) / 3511639679621928272970519404314120123544526810144939762491)
    outputUpper := ((-481216250590061837820180937621109075802102226117743083520 : ℚ) / 3511639690378926734302213807550918153373319630777146350789)
    expCertificate := {
      argument := ((1371923 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((1371923 : ℚ) / 4194304)
        terms := 8
        lower := ((2040443960390674968946506258249823307270537252848681673531 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
        upper := ((2040443971147673430278200661486621337099330073480888261829 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
      }
      lower := ((2040443960390674968946506258249823307270537252848681673531 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
      upper := ((2040443971147673430278200661486621337099330073480888261829 : ℚ) / 1471195719231253304024013146064296816273989557296258088960)
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
    word := 1052649794
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1046549265
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6231201 : ℚ) / 16777216)
    runtimeValue := ((14750481 : ℚ) / 67108864)
    localError := ((115230438472457692879162569219786112673222464870255449859225617 : ℚ) / 25511301544902747218291205334358571900587660765834460307786440053358592)
    outputLower := ((2387321936684766880022847588481508433818567709222396015673344 : ℚ) / 10861372032319577646337998656836084334673063941354723718567563)
    outputUpper := ((83556267783966840800799665596852795183649869822783860548567040 : ℚ) / 380148016585450578008461078023293195673639487711108629521525503)
    expCertificate := {
      argument := ((-6231201 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-6231201 : ℚ) / 16777216)
        terms := 8
        lower := ((155176690389191939432586385095530431320531068581517632579332863 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((4433619855283616544170150287471433924584251966223552377362059 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      }
      lower := ((155176690389191939432586385095530431320531068581517632579332863 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((4433619855283616544170150287471433924584251966223552377362059 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
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
    word := 1067239452
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1064459206
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2568711 : ℚ) / 2097152)
    runtimeValue := ((7941603 : ℚ) / 8388608)
    localError := ((102555434968133713680094275104495695087497456117586051671552355975859978633791504637636074772683926244880332991064477 : ℚ) / 127894265477552612004445779446254347380280822811373815503013465357039791216089748667642128189069753050836804144769561264128)
    outputLower := ((14433771052277257827520291214341181667062188862234039205410908634765534017502313354564746297566256952966766185676800 : ℚ) / 15246198632843580481650957207950870614613928572331361502176755147729410060619918611179235210128142396954551106231681)
    outputUpper := ((14433771052277257827520291214341181667062188862234039205410908634765534017502313354564746297566256952966766185676800 : ℚ) / 15246184525198055744701120787412446424994566775724150598408396882657979871760576804595247291215628749231911199661441)
    expCertificate := {
      argument := ((-2568711 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((-2568711 : ℚ) / 4194304)
        terms := 8
        lower := ((1860681934633662782701402426466882707485154203653020457279 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((1860685725617734424767273244372888166844618791675344578241 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((3462137261872070140442862944962268956434342018321764815147493703897967867345517478671791196920213304898874264083841 : ℚ) / 11784047263325985604258257842450177468560224757402385783260903178760012004415059325923456094295415444333036935577600)
      upper := ((3462151369517594877392699365500693146053703814928975718915851968969398056204859285255779115832726952621514170654081 : ℚ) / 11784047263325985604258257842450177468560224757402385783260903178760012004415059325923456094295415444333036935577600)
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
    word := 1061043628
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1057025057
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3116907 : ℚ) / 4194304)
    runtimeValue := ((8449057 : ℚ) / 16777216)
    localError := ((137959470641030794644998790900809565092391951241868653687937 : ℚ) / 84984814243607704426755812322911898327132007832884591175038664704)
    outputLower := ((2551004222988565468358915901296838472450159691448629329920 : ℚ) / 5065507480725431154857023601439529876433225054985975757921)
    outputUpper := ((2551004222988565468358915901296838472450159691448629329920 : ℚ) / 5065489664292794729873884458715432782598257531695639561119)
    expCertificate := {
      argument := ((-3116907 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((-3116907 : ℚ) / 4194304)
        terms := 8
        lower := ((1632699652753203687151187117898740211292281898004370686879 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((1632717469185840112134326260622837305127249421294706883681 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((1632699652753203687151187117898740211292281898004370686879 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      upper := ((1632717469185840112134326260622837305127249421294706883681 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
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
    word := 1069677148
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1067387212
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3178135 : ℚ) / 2097152)
    runtimeValue := ((2605651 : ℚ) / 2097152)
    localError := ((56731019727134862194763788161123316801676976264632733123941580319689341046534133951554225599964966473365637592323293 : ℚ) / 10851284577216704674541295726976839882763026212224228239718785573569131967834926099454470929023161132579579733601192771584)
    outputLower := ((6428940533505912424573972026692172106197049125371995583945370001149293074891374418967126621402588681575362912583680 : ℚ) / 5174319816901858262753516862323593164439511852125584290041629188470931113713144120986431046178508765349549774060017)
    outputUpper := ((6428940533505912424573972026692172106197049125371995583945370001149293074891374418967126621402588681575362912583680 : ℚ) / 5174295700653412186880729545105380956059945207702745551928894793304983123700583505370364632140713278093137614060017)
    expCertificate := {
      argument := ((-3178135 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((-3178135 : ℚ) / 4194304)
        terms := 8
        lower := ((965421506833184947018136742173268790453669523723784514009 : ℚ) / 2059674006923754625633618404490015542783585380214761324544)
        upper := ((965433996762338717477369482893416106864600586819509982759 : ℚ) / 2059674006923754625633618404490015542783585380214761324544)
      }
      lower := ((932038685856057369347756721823317067378264295037886669954969648951378802111162148037920438194363718133244317252081 : ℚ) / 4242257014797354817532972823282063888681680912664858881973925144353604321589421357332444193946349559959893296807936)
      upper := ((932062802104503445220544039041529275757830939460725408067704044117326792123722763653986852232159205389656477252081 : ℚ) / 4242257014797354817532972823282063888681680912664858881973925144353604321589421357332444193946349559959893296807936)
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
    word := 1066989780
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1063967663
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2506293 : ℚ) / 2097152)
    runtimeValue := ((15391663 : ℚ) / 16777216)
    localError := ((135156198181769062517869837710587909869755411949312038821874413156255731371113837027708634600294125843505214907401 : ℚ) / 210239473753115927798083113882648363876980660692431552083249168746002967939174021218691863773168662072011271727256436736)
    outputLower := ((14083039840575730532671566878665915793519120878173970066016349225332244284907070294926965973348588781463518209638400 : ℚ) / 15350791970919806801369967778398813579556658804586994429514594899048770277210175179902372842843733528497045582081729)
    outputUpper := ((11496359053531208598099238268298706770219690512795077604911305490067138191760873710144462019060072474664096497664 : ℚ) / 12531249150819535720234102838197252981482783597256633763506959005952058311651588750999680982420960788250641329721)
    expCertificate := {
      argument := ((-2506293 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((-2506293 : ℚ) / 4194304)
        terms := 8
        lower := ((53959417452173395557053652601105944301232024263313982805 : ℚ) / 98079714615416886934934209737619787751599303819750539264)
        upper := ((1888582724583125375653832024627059279526060987020593153377 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((2911618731777914818798790313748128517351987876928155573089895186556130144782152566572369885036948180631835668025 : ℚ) / 9619630419041620901435312524449124464130795720328478190417063819395928166869436184427311097384012607618805661696)
      upper := ((3566744707593821197111709935948636110996434047184608646253691720288758272795115853978916748548318084164008646504129 : ℚ) / 11784047263325985604258257842450177468560224757402385783260903178760012004415059325923456094295415444333036935577600)
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
    word := 1064364774
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1059933159
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((7894387 : ℚ) / 8388608)
    runtimeValue := ((11357159 : ℚ) / 16777216)
    localError := ((2783325333816029702637670485261639997540664467294395986572499711 : ℚ) / 184466977084375681294543052902383776882014557113091620253521250615296)
    outputLower := ((7443174913557494434108842725540185698279730333995423435325440 : ℚ) / 10995360173146408925213949842405861944739030997814041276634409)
    outputUpper := ((7443174913557494434108842725540185698279730333995423435325440 : ℚ) / 10995088641904335099133435064696298651815328425949312463612631)
    expCertificate := {
      argument := ((-7894387 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-7894387 : ℚ) / 8388608)
        terms := 8
        lower := ((3085940455317117336700340391454638967526360565924628977363671 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((3086211986559191162780855169164202260450063137789357790385449 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((3085940455317117336700340391454638967526360565924628977363671 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((3086211986559191162780855169164202260450063137789357790385449 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
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
    word := 3185192552
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3176043014
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1787341 : ℚ) / 16777216)
    runtimeValue := ((-6768899 : ℚ) / 134217728)
    localError := ((953512231744748759328816587089271552393286884313368591668848251 : ℚ) / 574062155521265341998090700573819797158268367512927739232984726228697088)
    outputLower := ((-215703503859908819316481473790991535366466188108892483627253760 : ℚ) / 4277096357355008587226947401268927731799098607249019587285702871)
    outputUpper := ((-30814786265701259902354496255855933623780884015556069089607680 : ℚ) / 611013765336697612503022883585778627535627218837041384349430607)
    expCertificate := {
      argument := ((1787341 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((1787341 : ℚ) / 16777216)
        terms := 8
        lower := ((2252354421588680840044075164919062852621122835082700614805969111 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((321764917370079362905469706964369359081630679956138673995182927 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      }
      lower := ((2252354421588680840044075164919062852621122835082700614805969111 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((321764917370079362905469706964369359081630679956138673995182927 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
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
    word := 3180962320
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3172196239
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-629281 : ℚ) / 8388608)
    runtimeValue := ((-9691023 : ℚ) / 268435456)
    localError := ((111508312410033999000242847052019296311135948239301025956267 : ℚ) / 210075431036059033364940623232783914148732407243734158444221553442816)
    outputLower := ((-28253036907762521679978485613051964259085462115629473464320 : ℚ) / 782591965183835600930976209166586079257474866672359997198811)
    outputUpper := ((-197771258354337651759849399291363749813598234809406314250240 : ℚ) / 5478143756286996745981750616036968261425620113572892804760323)
    expCertificate := {
      argument := ((629281 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((629281 : ℚ) / 8388608)
        terms := 8
        lower := ((405965861060634755100828843774126094291333540004517926425051 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
        upper := ((2841761027424590825170719058289748366662630826897998309344003 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
      }
      lower := ((405965861060634755100828843774126094291333540004517926425051 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
      upper := ((2841761027424590825170719058289748366662630826897998309344003 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
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
    word := 1035889000
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1028080081
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1559853 : ℚ) / 16777216)
    runtimeValue := ((13058513 : ℚ) / 268435456)
    localError := ((176378138367571148144794551619458969459051085394165045991995633 : ℚ) / 115418915733007899329966745657574961859479536125576977422300985253953536)
    outputLower := ((20916592960429944167047373496738048271208359414610261044101120 : ℚ) / 429968967039167505986864662384893603099433839788947170310843681)
    outputUpper := ((20916592960429944167047373496738048271208359414610261044101120 : ℚ) / 429968967039097408995846988220770079572944493997758895221019359)
    expCertificate := {
      argument := ((-1559853 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-1559853 : ℚ) / 16777216)
        terms := 8
        lower := ((204997640842838770419972295293007315219836074868167898278826719 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((204997640842908867410989969457130838746325420659356173368651041 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((204997640842838770419972295293007315219836074868167898278826719 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((204997640842908867410989969457130838746325420659356173368651041 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
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
    word := 3199393108
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188977551
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-2930517 : ℚ) / 8388608)
    runtimeValue := ((-9695119 : ℚ) / 67108864)
    localError := ((198770259027369244360465678481118698161459596660690441201827 : ℚ) / 28521883066558574524924715957632337306739003950382483366810767851520)
    outputLower := ((-43857463231754707221970000536752369314949575352774641582080 : ℚ) / 303577982107920265317647454093998214523548408787304353601449)
    outputUpper := ((-61400448524456590110758000751453317040929405493884498214912 : ℚ) / 425009177126863219215344130361562033098027168965078642469805)
    expCertificate := {
      argument := ((2930517 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((2930517 : ℚ) / 8388608)
        terms := 8
        lower := ((178035947400186650040931665629844886201501299898023663343529 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
        upper := ((249250328536036157827942026511747373447161216520085676108717 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      }
      lower := ((178035947400186650040931665629844886201501299898023663343529 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
      upper := ((249250328536036157827942026511747373447161216520085676108717 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
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
    word := 1069768864
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1067483009
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((400133 : ℚ) / 262144)
    runtimeValue := ((10518401 : ℚ) / 8388608)
    localError := ((49325203841795651722026713071948844489737168314473203692985846870380030252917232112866198286713373679 : ℚ) / 8724713423779524996033033834983996743756272128811134216314530972571003660433420375134151428992630593159168)
    outputLower := ((2556107551975276744747887805016011255941398587863927770816879906217876222610685254816562289299161088 : ℚ) / 2038541130359639951876650320906826847776555878327784266680532943483919704257925611213077748772745705)
    outputUpper := ((1304136506109835073850963165824495538745611524420371311641265258274426644189125130008450147601612800 : ℚ) / 1040066888782921432975892285702704995126279846288100983657184955188155610613038584605950287460402321)
    expCertificate := {
      argument := ((-400133 : ℚ) / 262144)
      halvings := 1
      reduced := {
        argument := ((-400133 : ℚ) / 524288)
        terms := 8
        lower := ((13626154058081003511500040082183283802094557538089 : ℚ) / 29230032746618058364073696654325660393118650859520)
        upper := ((19076878523428471191711475252333432761070496041261 : ℚ) / 40922045845265281709703175316055924550366111203328)
      }
      lower := ((185672074414557400017883603234884149285198037345439875678368312059267720300782364596765452685771921 : ℚ) / 854394814368364032958008682467820845841081808942661107978816643128887890312256220009184834774630400)
      upper := ((363927294197646447278953303269897989928035532800168495042052322951299439245903419995075472614470121 : ℚ) / 1674613836161993504597697017636928857848520345527615771638480620532620265012022191218002276158275584)
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
    word := 3199883556
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189296718
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3053129 : ℚ) / 8388608)
    runtimeValue := ((-5007143 : ℚ) / 33554432)
    localError := ((288627001209401130621905448805205203616312167700087256766165 : ℚ) / 18493821666209103873524363008600954748566844997866450607325885497344)
    outputLower := ((-82246404694716745035306358019350716693856008235077523734528 : ℚ) / 551158835476908203170429557818202815907205492194487172583517)
    outputUpper := ((-2878624164315086076235722530677275084284960288227713330708480 : ℚ) / 19290559377596256773286715736424426099990085926301328349233993)
    expCertificate := {
      argument := ((3053129 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((3053129 : ℚ) / 8388608)
        terms := 8
        lower := ((325183173002987695672341138582726824927520696193781930119261 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
        upper := ((11381411191009039010853621063182766415701118066276644862985033 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((325183173002987695672341138582726824927520696193781930119261 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      upper := ((11381411191009039010853621063182766415701118066276644862985033 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
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
    word := 1074438617
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1073266839
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9085401 : ℚ) / 4194304)
    runtimeValue := ((16302231 : ℚ) / 8388608)
    localError := ((5985954844714887489518041185202240772711222682720539933592539449576642433455315593624213030005207246894018078295852281856531079436526138131806962684641675638501932278284525697624651570541832372260421487896510843876942983088261427193596795990284809 : ℚ) / 9975469230165890108042840965151603424373482898219098086178626201556184854796344750522756482406130368647080942073261448702294791476578837504731433442819508182276073804051775240604691973151915383430819475392243234923053157381853505358765831787767962533888)
    outputLower := ((8877953221227969190960207657091611685410139121068834572363888123006614284576283626025340138293012644008357230986194395983211967359226544093189480918843224126680102589974741938947967457427090820682363216018369546334476520049374906373155212402622464 : ℚ) / 4568311426115470736508133813539207678079402318401191687089364066915110528618090912077840006779460929280372872073240376239930711283037871137128223534944459819162300262007664076435238220929707010698863460072770652632909668321396882926848489497855377)
    outputUpper := ((2311004066333811222136663800783947231729003311398592922835247845430709674244138803109470048493599709498218771081370886084759466721997746796436245553634741807236594801638572974528313061595973245700323619330062876492731289059083430438659728343040000 : ℚ) / 1189168599863754523759226914066267421766934740331065426609352374262354952668707937064499435711637779312977903136403733337199067053387026489345006161072195551666745400911781220508181091922749922684528765129118351331121105835658729715200165723296161)
    expCertificate := {
      argument := ((-9085401 : ℚ) / 4194304)
      halvings := 2
      reduced := {
        argument := ((-9085401 : ℚ) / 16777216)
        terms := 8
        lower := ((18700122127715088919145681489120461285260716269640786374745609 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((26180189548839217362874330416767365063604901094562863430709133 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((122286290602977839906450627550866174223773408760520120945951124380108994617886805621070283572189092794109117441454414865856858788727928076486869192699262744291520188189538891154088566176859678727894362547376495014050586149662495908613945343136161 : ℚ) / 1066882309260776683852776286515401247543161331570545305663401249882245958050821131443429152139448686518868785694949318471342208264659098412858136968372932807375225212722242329354092525745890243956634402581741856317070519685996233806586220380160000)
      upper := ((469776346859271027819308431261642245517593747039784840852841825367474456170056453524762575920554855149486544947523074400422484013523478674292404557243001146349635084813897943988556374024295049515056739114751137405251559895673751135466865285432721 : ℚ) / 4098535079256199708688825382277565432561808571361406846236522241547636072448034458553077430858906074130886327125717301839508227269514392462835818977701458672812665177193766132446681846905411961183806720958019515227658108425723131791381624212422656)
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
    word := 3189116256
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180008433
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-307307 : ℚ) / 2097152)
    runtimeValue := ((-9114609 : ℚ) / 134217728)
    localError := ((5849119608172645378031398400578870809939602447934221343 : ℚ) / 4993166135240606862770441902845098460686090854257876034058715136)
    outputLower := ((-2526354470605768779849861233742428170807906848661831680 : ℚ) / 37201986724236275971243951600852631756219028880807440113)
    outputUpper := ((-2526354470605768779849861233742428170807906848661831680 : ℚ) / 37201986724440804591554715505578357433424076842202812687)
    expCertificate := {
      argument := ((307307 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((307307 : ℚ) / 2097152)
        terms := 8
        lower := ((19961411889495026314712547545411653440508213756241915633 : ℚ) / 17240574834741249656531404055440978315710815124565524480)
        upper := ((19961411889699554935023311450137379117713261717637288207 : ℚ) / 17240574834741249656531404055440978315710815124565524480)
      }
      lower := ((19961411889495026314712547545411653440508213756241915633 : ℚ) / 17240574834741249656531404055440978315710815124565524480)
      upper := ((19961411889699554935023311450137379117713261717637288207 : ℚ) / 17240574834741249656531404055440978315710815124565524480)
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
    word := 3164831552
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3156336022
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-167421 : ℚ) / 8388608)
    runtimeValue := ((-5304011 : ℚ) / 536870912)
    localError := ((48329253972926707225296939188926311236382270311918623963453 : ℚ) / 136158422561188825906523722529849383938749690139441525793807646326784)
    outputLower := ((-2505585311985429478078250172192694471002274634522469335040 : ℚ) / 253614825310537267302207131925689771657343376687618951860457)
    outputUpper := ((-17539097183898006346547751205348861297015922441657285345280 : ℚ) / 1775303777173760872350002097753202207616446877817286526716321)
    expCertificate := {
      argument := ((167421 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((167421 : ℚ) / 8388608)
        terms := 8
        lower := ((128072790602803652025491343461536443335296267798338261602537 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
        upper := ((896509534219625565412991578504128909362117115592321694910881 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
      }
      lower := ((128072790602803652025491343461536443335296267798338261602537 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
      upper := ((896509534219625565412991578504128909362117115592321694910881 : ℚ) / 878794242954135306937010519249073298254329762224964831805440)
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
    word := 1051868810
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1045493257
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((5840709 : ℚ) / 16777216)
    runtimeValue := ((13694473 : ℚ) / 67108864)
    localError := ((27626632468001223968770396144079486765556215540660199495688079 : ℚ) / 3679503632617263746648143429342075942429157204710137789524222031167488)
    outputLower := ((11188575622494081060016653383250069001930777699487331102228480 : ℚ) / 54828877129929330206748633332702734644845761981791149886852823)
    outputUpper := ((11188575622494081060016653383250069001930777699487331102228480 : ℚ) / 54828876742977853814484826167554794884162503551097777329746217)
    expCertificate := {
      argument := ((-5840709 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-5840709 : ℚ) / 16777216)
        terms := 8
        lower := ((22690115857798048303645584320731542833718443675441920623718697 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((22690116244749524695909391485879482594401702106135293180825303 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      }
      lower := ((22690115857798048303645584320731542833718443675441920623718697 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((22690116244749524695909391485879482594401702106135293180825303 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
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
    word := 1059346721
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1054301389
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10770721 : ℚ) / 16777216)
    runtimeValue := ((14113997 : ℚ) / 33554432)
    localError := ((1948666591725787508660206209557186339470694935684936877154809761 : ℚ) / 4937699073339863594505919477588002511106521984984447423733395519176704)
    outputLower := ((86656929998155583379527937715730877722599849648328571516616704 : ℚ) / 206017076831835246433188033898085795119140248220358595615216999)
    outputUpper := ((61897807141539702413948526939807769801857035463091836797583360 : ℚ) / 147154899637099015549001678156495169136122524290813428870838747)
    expCertificate := {
      argument := ((-10770721 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-10770721 : ℚ) / 16777216)
        terms := 8
        lower := ((50738616981559599016483952616025412984790344663845858752756187 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
        upper := ((71034281114080063287663218141428136507275196742603997449901415 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
      }
      lower := ((50738616981559599016483952616025412984790344663845858752756187 : ℚ) / 96416282655539416532517725540469756151332179626967570118082560)
      upper := ((71034281114080063287663218141428136507275196742603997449901415 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
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
    word := 3201982527
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190587324
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14311487 : ℚ) / 33554432)
    runtimeValue := ((-2826223 : ℚ) / 16777216)
    localError := ((30365374799837457662917232124626292412848318530200840224032541601 : ℚ) / 3145428464526226750387036821505605232684702405880417500404063135982419968)
    outputLower := ((-31582497615350597481370067741592427575369884981071729183193825280 : ℚ) / 187482146294488117121877480835056616823953533523107618117574640273)
    outputUpper := ((-221077483307454182369590474191146993027589194867502104282356776960 : ℚ) / 1312375055738894119613898462635901410076726541580432749761441082889)
    expCertificate := {
      argument := ((14311487 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((14311487 : ℚ) / 33554432)
        terms := 8
        lower := ((113434441215033845224903867619975844099730419569596524266887234193 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
        upper := ((794041120182714216335083170130336001007164743905855092806629240329 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((113434441215033845224903867619975844099730419569596524266887234193 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      upper := ((794041120182714216335083170130336001007164743905855092806629240329 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
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
    word := 1060523250
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1056217437
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((5973625 : ℚ) / 8388608)
    runtimeValue := ((16030045 : ℚ) / 33554432)
    localError := ((12289445779731524167764400075560838625024817738020633710353335 : ℚ) / 11302480777214270111870492122258109084667877809372412266540311773184)
    outputLower := ((160919888823720621061714700860443147017481278122629267456000 : ℚ) / 336841009792005200352597747436270874721119267027747996644387)
    outputUpper := ((160919888823720621061714700860443147017481278122629267456000 : ℚ) / 336840175903268757816269759007039936920043164770973094300637)
    expCertificate := {
      argument := ((-5973625 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-5973625 : ℚ) / 8388608)
        terms := 8
        lower := ((110864513429348250318181339771563945940358368770267851836381 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
        upper := ((110865347318084692854509328200794883741434471027042754180131 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      }
      lower := ((110864513429348250318181339771563945940358368770267851836381 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      upper := ((110865347318084692854509328200794883741434471027042754180131 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
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
    word := 3205234879
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192736517
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9175231 : ℚ) / 16777216)
    runtimeValue := ((-13454085 : ℚ) / 67108864)
    localError := ((12019150448052915859224359191293538160757500600262552209353954605 : ℚ) / 370657102280178680412772137160405946425382381759839471973843904688553984)
    outputLower := ((-1107303796770764535791424036741054480388463605763277232181084160 : ℚ) / 5523221228721420175027432101374953186890220370290271520224867831)
    outputUpper := ((-1107303796770764535791424036741054480388463605763277232181084160 : ℚ) / 5523222132804958537071081125133175703564403035771807357956098569)
    expCertificate := {
      argument := ((9175231 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((9175231 : ℚ) / 16777216)
        terms := 8
        lower := ((3498479292955092427844559865025088307712244598123952547745134071 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((3498480197038630789888208888783310824386427263605488385476364809 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((3498479292955092427844559865025088307712244598123952547745134071 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((3498480197038630789888208888783310824386427263605488385476364809 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
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
    word := 1024605848
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1016388321
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1198035 : ℚ) / 33554432)
    runtimeValue := ((9755361 : ℚ) / 536870912)
    localError := ((1526718904721537817689172152380572427173146612295134564946330507 : ℚ) / 1735861560260374025814676908947270439229685841933092339211889835493031936)
    outputLower := ((411260258147483395486828670870532628466455451830931930575011840 : ℚ) / 22633058804688265718620715874258648143439222490918115379125946221)
    outputUpper := ((58751465449640485069546952981504661209493635975847418653573120 : ℚ) / 3233294114955466288728037679469716621990661773706027007125112853)
    expCertificate := {
      argument := ((-1198035 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-1198035 : ℚ) / 33554432)
        terms := 8
        lower := ((1587789557634260246573068496912366117007925908072447143776503829 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
        upper := ((11114526903439823423535931596357194608560071431483056335685683053 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((1587789557634260246573068496912366117007925908072447143776503829 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
      upper := ((11114526903439823423535931596357194608560071431483056335685683053 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
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
    word := 3208602237
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3195404437
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-12542589 : ℚ) / 16777216)
    runtimeValue := ((-16122005 : ℚ) / 67108864)
    localError := ((18916562851281400179768180616597637820179970398190253987855916725 : ℚ) / 46982320056894566414969341186197197510391678985782785297736291919593472)
    outputLower := ((-168187789992368545613094662958033981489234553192984915539394560 : ℚ) / 700091124428727722391029315981227122402067169335227985646371423)
    outputUpper := ((-4805365428353387017516990370229542328263844376942426158268416 : ℚ) / 20002638554416502779787322433513692015603121771078762947642731)
    expCertificate := {
      argument := ((12542589 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((12542589 : ℚ) / 16777216)
        terms := 8
        lower := ((475119798232469083815154623053464358048958750205636988704178783 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((13574886377380541677619474064149041605514309795947591606437227 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      }
      lower := ((475119798232469083815154623053464358048958750205636988704178783 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((13574886377380541677619474064149041605514309795947591606437227 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
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
    word := 3166619260
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3158085078
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3125663 : ℚ) / 134217728)
    runtimeValue := ((-6178539 : ℚ) / 536870912)
    localError := ((11220192370909732065927392125760639734041456154875260014795559814850371 : ℚ) / 36904201285694677225080552540117612558096641029319206941280106823679340789628928)
    outputLower := ((-791082619146648410655357247860753463480758660744586632309740257935360 : ℚ) / 68739431511042038234026435244296919589804186205782910851144694545286391)
    outputUpper := ((-791082619146648410655357247860753463480758660744586632309740257935360 : ℚ) / 68739431511042038398013548068921291377575399408711505944431027069090569)
    expCertificate := {
      argument := ((3125663 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((3125663 : ℚ) / 134217728)
        terms := 8
        lower := ((34769898710432232092745996234652184941021384233381789524954145631274231 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
        upper := ((34769898710432232256733109059276556728792597436310384618240478155078409 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      }
      lower := ((34769898710432232092745996234652184941021384233381789524954145631274231 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      upper := ((34769898710432232256733109059276556728792597436310384618240478155078409 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
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
    word := 1055424691
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1049506757
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((15237299 : ℚ) / 33554432)
    runtimeValue := ((9319365 : ℚ) / 33554432)
    localError := ((10076394236889178565552802530033478514963965112772054823313290035 : ℚ) / 451378312410331139428326547604881792849687265756954919390527152531177472)
    outputLower := ((3736174843574442789691965247752060635719140801233452680442019840 : ℚ) / 13452121985266540629515843022015148188164450697808114272073720471)
    outputUpper := ((747234968714888557938393049550412127143828160246690536088403968 : ℚ) / 2690424231008282589850290137875181492243189660175028394698045717)
    expCertificate := {
      argument := ((-15237299 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-15237299 : ℚ) / 33554432)
        terms := 8
        lower := ((1044919673687076547695320955317830987260453794541448531349436693 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
        upper := ((5224599198660510418740997109228395663250771369640214955330675351 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
      }
      lower := ((1044919673687076547695320955317830987260453794541448531349436693 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
      upper := ((5224599198660510418740997109228395663250771369640214955330675351 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
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
    word := 1051773200
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1045365151
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((724113 : ℚ) / 2097152)
    runtimeValue := ((13566367 : ℚ) / 67108864)
    localError := ((1443986902343774671924836489460079550039784995175731487 : ℚ) / 1537021431266462412982154817086151970691105343866406761905782784)
    outputLower := ((4630028966117590458540358654318000577178008731527413760 : ℚ) / 22903404105699992373319787041636585752533455846703153281)
    outputUpper := ((4630028966117590458540358654318000577178008731527413760 : ℚ) / 22903403954524722984437140005190205156721632217380896639)
    expCertificate := {
      argument := ((-724113 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((-724113 : ℚ) / 2097152)
        terms := 8
        lower := ((9494067971948195473801603517624999800057664898274377599 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
        upper := ((9494068123123464862684250554071380395869488527596634241 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      }
      lower := ((9494067971948195473801603517624999800057664898274377599 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      upper := ((9494068123123464862684250554071380395869488527596634241 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
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
    word := 1062167294
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1057982966
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6795647 : ℚ) / 8388608)
    runtimeValue := ((4703483 : ℚ) / 8388608)
    localError := ((16552873753211076744128748760554244258763464628392189574264647 : ℚ) / 4564663232044737915901967142192004286159905740901832012509057384448)
    outputLower := ((2135744855671599174564090272463586525462439520004318565498880 : ℚ) / 3809079116150273429187130631987265903192348080946641197358083)
    outputUpper := ((305106407953085596366298610351940932208919931429188366499840 : ℚ) / 544150260930626143920656101964951072473514764416436196864731)
    expCertificate := {
      argument := ((-6795647 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-6795647 : ℚ) / 8388608)
        terms := 8
        lower := ((167524156807425298090508736572491087507373437748594126090971 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
        upper := ((1172696387287867508376099074240046008429358794271746701941763 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
      }
      lower := ((167524156807425298090508736572491087507373437748594126090971 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
      upper := ((1172696387287867508376099074240046008429358794271746701941763 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
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
    word := 3204550143
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192056027
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8490495 : ℚ) / 16777216)
    runtimeValue := ((-12773595 : ℚ) / 67108864)
    localError := ((196994358448723876776599771128845736461654405705892959548435295 : ℚ) / 8028175448270130601058756789099245750022255452921588113846258026676224)
    outputLower := ((-22770380022677218789282693873997987650945726240607460875304960 : ℚ) / 119629136447163382188361239270854678005311719371700109747741491)
    outputUpper := ((-22770380022677218789282693873997987650945726240607460875304960 : ℚ) / 119629147249658428403127673830349769593936164652061280872897741)
    expCertificate := {
      argument := ((8490495 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((8490495 : ℚ) / 16777216)
        terms := 8
        lower := ((74634871207911654473186300685302125134690035545781910359302963 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((74634882010406700687952735244797216723314480826143081484459213 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((74634871207911654473186300685302125134690035545781910359302963 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((74634882010406700687952735244797216723314480826143081484459213 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
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
    word := 3198432794
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188333046
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5380877 : ℚ) / 16777216)
    runtimeValue := ((-4525307 : ℚ) / 33554432)
    localError := ((224368693281668166624160044846429524069943546273349554316234001 : ℚ) / 53855906614061745962286661062092499589557390110567321058889189667373056)
    outputLower := ((-216461962721755312865538041005801198511849815428395786557194240 : ℚ) / 1605031087177150672699075269189767269069826285253119826150762397)
    outputUpper := ((-216461962721755312865538041005801198511849815428395786557194240 : ℚ) / 1605031091393880425759752424421682941602390709834317000475203683)
    expCertificate := {
      argument := ((5380877 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((5380877 : ℚ) / 16777216)
        terms := 8
        lower := ((930117108588374756971451190406478976010501027864346835324184477 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((930117112805104510032128345638394648543065452445544009648625763 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      }
      lower := ((930117108588374756971451190406478976010501027864346835324184477 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((930117112805104510032128345638394648543065452445544009648625763 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
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
    word := 3200925340
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189952464
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3313575 : ℚ) / 8388608)
    runtimeValue := ((-666877 : ℚ) / 4194304)
    localError := ((2394249219766385329555416950581830227510570123318461443673 : ℚ) / 1831463086877383310911770831414354292029290265713267235368210530304)
    outputLower := ((-69426313247603151790709605963724805218293446108450599731200 : ℚ) / 436654826850267245986883838513935635573694769314114388315251)
    outputUpper := ((-69426313247603151790709605963724805218293446108450599731200 : ℚ) / 436654832663723794583217655951510013730930407595425423471501)
    expCertificate := {
      argument := ((3313575 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((3313575 : ℚ) / 8388608)
        terms := 8
        lower := ((260895978259440184599481734664120975922828816869121421954163 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((260895984072896733195815552101695354080064455150432457110413 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      }
      lower := ((260895978259440184599481734664120975922828816869121421954163 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      upper := ((260895984072896733195815552101695354080064455150432457110413 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
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
    word := 3188144414
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3179060619
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4430991 : ℚ) / 33554432)
    runtimeValue := ((-16555403 : ℚ) / 268435456)
    localError := ((1112429624694072667307454829123268735827753073780554380774984911 : ℚ) / 6620459066754012442480711144258353864777705410333092242118312470706651136)
    outputLower := ((-1521066164602182405398488741288269743322363627910530916033757184 : ℚ) / 24663131932742940047683980853327936920440589675058023043417604531)
    outputUpper := ((-7605330823010912026992443706441348716611818139552654580168785920 : ℚ) / 123315659664011892118225239120626535758356133417492869973459892097)
    expCertificate := {
      argument := ((4430991 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((4430991 : ℚ) / 33554432)
        terms := 8
        lower := ((13144600031494497752599196575426483385561438615622963999977341363 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((65723000157769680642801317731119268083960378120317574756258576257 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((13144600031494497752599196575426483385561438615622963999977341363 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((65723000157769680642801317731119268083960378120317574756258576257 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
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
    word := 1062287559
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1058087120
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((13711559 : ℚ) / 16777216)
    runtimeValue := ((594445 : ℚ) / 1048576)
    localError := ((12130779309143476392892140832796308022674000607901936843365038645 : ℚ) / 3060706815198427653569414825683397961277368520191377436993488442884096)
    outputLower := ((1654766113283289260794820574413127716355126279630007767914250240 : ℚ) / 2918939968551791094099737860377105658870680291373573726924687049)
    outputUpper := ((1654766113283289260794820574413127716355126279630007767914250240 : ℚ) / 2918917479704311040467657876666448556210869331542375027650345271)
    expCertificate := {
      argument := ((-13711559 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-13711559 : ℚ) / 16777216)
        terms := 8
        lower := ((894175543937983293284785640316583677032893559376056055170611511 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((894198032785463346916865624027240779692704519207254754444953289 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((894175543937983293284785640316583677032893559376056055170611511 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((894198032785463346916865624027240779692704519207254754444953289 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
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
    word := 1057971371
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1052146841
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9395371 : ℚ) / 16777216)
    runtimeValue := ((11959449 : ℚ) / 33554432)
    localError := ((1397032053690952636667073077295193105731716056943951481521070073 : ℚ) / 11860682354773657708746161928435996421432752123055084806413170902040576)
    outputLower := ((25197137283991202370825462216942398203409059058976226979872768 : ℚ) / 70695200141867998399175542184018014974352874629930681775328173)
    outputUpper := ((125985686419956011854127311084711991017045295294881134899363840 : ℚ) / 353475879275013736151044426215767753762982848973723793220912543)
    expCertificate := {
      argument := ((-9395371 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-9395371 : ℚ) / 16777216)
        terms := 8
        lower := ((128504553078755097575169733288004989409874429844132796278719903 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((25700934902616270684000603598465462103731190804012482386889645 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((128504553078755097575169733288004989409874429844132796278719903 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((25700934902616270684000603598465462103731190804012482386889645 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
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
    word := 1057508824
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1051443671
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1116603 : ℚ) / 2097152)
    runtimeValue := ((11256279 : ℚ) / 33554432)
    localError := ((39649045250852095534384183707868886875191080711567017719 : ℚ) / 714136147249893039509061160079031787474771714055761546767761408)
    outputLower := ((7139637368275117086390577291786561487611320448120258560 : ℚ) / 21282920522087172160665750158572240991322277934196457441)
    outputUpper := ((7139637368275117086390577291786561487611320448120258560 : ℚ) / 21282915689047963604601060154409163817011467041246937119)
    expCertificate := {
      argument := ((-1116603 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((-1116603 : ℚ) / 2097152)
        terms := 8
        lower := ((7873579706471436093965523666843958460347499722140418079 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
        upper := ((7873584539510644650030213671007035634658310615089938401 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      }
      lower := ((7873579706471436093965523666843958460347499722140418079 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      upper := ((7873584539510644650030213671007035634658310615089938401 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
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
    word := 3201569206
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190342760
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6949083 : ℚ) / 16777216)
    runtimeValue := ((-1382541 : ℚ) / 8388608)
    localError := ((7712748079585176383830091911501172126965542028509256967047881 : ℚ) / 948563756705950813509950895926762246985173304579313726379147791433728)
    outputLower := ((-18636517743562168704637945160323815987100502401951737330008064 : ℚ) / 113077611530536510170692312231869965432306922027982917592423891)
    outputUpper := ((-93182588717810843523189725801619079935502512009758686650040320 : ℚ) / 565388068528201442377245478936275393930383494007287326178765537)
    expCertificate := {
      argument := ((6949083 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((6949083 : ℚ) / 16777216)
        terms := 8
        lower := ((68083346291284782455517373646317412561685238202064718203985363 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((340416742331942803801370786008512629577275074877696329236572897 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((68083346291284782455517373646317412561685238202064718203985363 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((340416742331942803801370786008512629577275074877696329236572897 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
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
    word := 1059327840
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1054271179
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((335995 : ℚ) / 524288)
    runtimeValue := ((14083787 : ℚ) / 33554432)
    localError := ((7431469976197793268567288027147168752381245161399847 : ℚ) / 18868730060777207638712370776040536060254197348452551098368)
    outputLower := ((236027574813879346756869250322082316062359531028480 : ℚ) / 562332561060661576364881082898640298883654133184149)
    outputUpper := ((236027574813879346756869250322082316062359531028480 : ℚ) / 562331976317680109700929247618929626353210131777899)
    expCertificate := {
      argument := ((-335995 : ℚ) / 524288)
      halvings := 0
      reduced := {
        argument := ((-335995 : ℚ) / 524288)
        terms := 8
        lower := ((194033563710292574313600669774426305399915130947947 : ℚ) / 368298412607387535387328577844503320953295000829952)
        upper := ((194034148453274040977552505054136977930359132354197 : ℚ) / 368298412607387535387328577844503320953295000829952)
      }
      lower := ((194033563710292574313600669774426305399915130947947 : ℚ) / 368298412607387535387328577844503320953295000829952)
      upper := ((194034148453274040977552505054136977930359132354197 : ℚ) / 368298412607387535387328577844503320953295000829952)
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
    word := 1062856876
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1058584326
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3570219 : ℚ) / 4194304)
    runtimeValue := ((5004163 : ℚ) / 8388608)
    localError := ((239530034077114410491078567738636589538385479911246768875171 : ℚ) / 41089068822529654301231945572860693550631633035251253404640477184)
    outputLower := ((584402662382548675201339043494855467569134188696937955328 : ℚ) / 979650299431506874645893812639141515400510895724403359661)
    outputUpper := ((2922013311912743376006695217474277337845670943484689776640 : ℚ) / 4898198702636915958074563213927828496769861344725042987423)
    expCertificate := {
      argument := ((-3570219 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((-3570219 : ℚ) / 4194304)
        terms := 8
        lower := ((1465408691097324915351865873111135925463885711033774113183 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((293092297123588666101354344475803001139315768986149584813 : ℚ) / 686558002307918208544539468163338514261195126738253774848)
      }
      lower := ((1465408691097324915351865873111135925463885711033774113183 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      upper := ((293092297123588666101354344475803001139315768986149584813 : ℚ) / 686558002307918208544539468163338514261195126738253774848)
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
    word := 1045112079
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1038039726
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((13313295 : ℚ) / 67108864)
    runtimeValue := ((7314775 : ℚ) / 67108864)
    localError := ((916579061235858523689844208499220591228592116402484312956586817835 : ℚ) / 360165040228392443653359273644729261966579834191556735585832369909728804864)
    outputLower := ((83568907148214820079771196149043509259163408227005808360365752320 : ℚ) / 766696760175238821617549876452727324766820202234600293776175621643)
    outputUpper := ((584982350037503740558398373043304564814143857589040658522560266240 : ℚ) / 5366877320831901485522974634837050169208345326655458444145804195251)
    expCertificate := {
      argument := ((-13313295 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-13313295 : ℚ) / 67108864)
        terms := 8
        lower := ((2418133154112300257981269859694278064279282655440083329025096824243 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
        upper := ((345447593501010074825877765718045595491239820632403848758931711499 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
      }
      lower := ((2418133154112300257981269859694278064279282655440083329025096824243 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
      upper := ((345447593501010074825877765718045595491239820632403848758931711499 : ℚ) / 421249166674228746791672110734681729275580381602196445017243910144)
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
    word := 1045791662
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1038856620
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6996439 : ℚ) / 33554432)
    runtimeValue := ((3861611 : ℚ) / 33554432)
    localError := ((24611499305648364125447750766477374148723643418277746146754220163 : ℚ) / 31511426719051531514102213908072646115599764739479262375904078493527310336)
    outputLower := ((108077876619957201669100856372187898906029339854732883800484741120 : ℚ) / 939113697977409705939954933764715376961224220379569005248072102473)
    outputUpper := ((21615575323991440333820171274437579781205867970946576760096948224 : ℚ) / 187822739574812967294724163025598793367279823159960371083887513483)
    expCertificate := {
      argument := ((-6996439 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-6996439 : ℚ) / 33554432)
        terms := 8
        lower := ((84155952463576986638961104524485711553367463625044839692925144971 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
        upper := ((420779762421229802661139641259149967891662422704991348293260259913 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((84155952463576986638961104524485711553367463625044839692925144971 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      upper := ((420779762421229802661139641259149967891662422704991348293260259913 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
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
    word := 1052638738
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1046534197
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6225673 : ℚ) / 16777216)
    runtimeValue := ((14735413 : ℚ) / 67108864)
    localError := ((226035697821835056614903782542594943036813827207977264308093279 : ℚ) / 76544200137970048645219194031010791900024122197478327190514471385694208)
    outputLower := ((250446422923965473270162617053448604185314694234331519133941760 : ℚ) / 1140597478250745823140849247282291145596512145048527561972985283)
    outputUpper := ((250446422923965473270162617053448604185314694234331519133941760 : ℚ) / 1140597464710027704316663653120559333265187177024458753921307197)
    expCertificate := {
      argument := ((-6225673 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-6225673 : ℚ) / 16777216)
        terms := 8
        lower := ((465683486121251788589039574337271040205861919635685763094729277 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((465683499661969907413225168499002852537186887659754571146407363 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      }
      lower := ((465683486121251788589039574337271040205861919635685763094729277 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((465683499661969907413225168499002852537186887659754571146407363 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
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
    word := 1058864293
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1053534955
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10288293 : ℚ) / 16777216)
    runtimeValue := ((13347563 : ℚ) / 33554432)
    localError := ((3270757097315788530818037578418730992979428481260428595261971083 : ℚ) / 11637189153868325904375795486459486086893652989736105876761152321486848)
    outputLower := ((137959177524190209951979015596261689314528398321392366093598720 : ℚ) / 346815513909633589578108532475945748982048066298981189702166241)
    outputUpper := ((137959177524190209951979015596261689314528398321392366093598720 : ℚ) / 346815262850175079833739861442431392875124603204015072487627039)
    expCertificate := {
      argument := ((-10288293 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-10288293 : ℚ) / 16777216)
        terms := 8
        lower := ((121843936653916441257865168514668628522016184074424075545434399 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((121844187713374951002233839548182984628939647169390192759973601 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((121843936653916441257865168514668628522016184074424075545434399 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((121844187713374951002233839548182984628939647169390192759973601 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
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
    word := 1060194878
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1055676088
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((5809439 : ℚ) / 8388608)
    runtimeValue := ((1936087 : ℚ) / 4194304)
    localError := ((14196516473175589762606509904639867526368186563177493361296261 : ℚ) / 16590019204418736444034995485206140655894171543202776169683424903168)
    outputLower := ((1825798111436329673551382823205882477547169413398660707778560 : ℚ) / 3955376590379300136777459800669986647367248711264620288595203)
    outputUpper := ((1825798111436329673551382823205882477547169413398660707778560 : ℚ) / 3955368805985149489411114569951567806218665014076894800587517)
    expCertificate := {
      argument := ((-5809439 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-5809439 : ℚ) / 8388608)
        terms := 8
        lower := ((1318986077122743568600083012204347911455675727402000305171197 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
        upper := ((1318993861516894215966428242922766752604259424589725793178883 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
      }
      lower := ((1318986077122743568600083012204347911455675727402000305171197 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
      upper := ((1318993861516894215966428242922766752604259424589725793178883 : ℚ) / 2636382728862405920811031557747219894762989286674894495416320)
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
    word := 3204950314
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192459622
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4445333 : ℚ) / 8388608)
    runtimeValue := ((-6588595 : ℚ) / 33554432)
    localError := ((15197215012497293755761846728018158862966883911866548001300075 : ℚ) / 716227572206440751615147109363439975915899922501268341090153305997312)
    outputLower := ((-4191255263772763788405656342874213071982780738366497315880960 : ℚ) / 21345245009852670181248995940787791488048431947865138682429591)
    outputUpper := ((-4191255263772763788405656342874213071982780738366497315880960 : ℚ) / 21345247754628630594729508200903228450343738085217634246164329)
    expCertificate := {
      argument := ((4445333 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((4445333 : ℚ) / 8388608)
        terms := 8
        lower := ((13436096823265452418815901267546131803759464087840455196180631 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((13436099568041412832296413527661568766054770225192950759915369 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((13436096823265452418815901267546131803759464087840455196180631 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((13436099568041412832296413527661568766054770225192950759915369 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
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
    word := 3193202130
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3183375066
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6959849 : ℚ) / 33554432)
    runtimeValue := ((-6240621 : ℚ) / 67108864)
    localError := ((10705633397445860711087246315124301198683993143189413908152997909 : ℚ) / 77587460256099448795885107461050954663614272905266974103136402914280472576)
    outputLower := ((-15358950082943878615137335805933675198671564919538206846285250560 : ℚ) / 165163321685469577044964522714583270223471935562805905003801890513)
    outputUpper := ((-107512650580607150305961350641535726390700954436767447923996753920 : ℚ) / 1156143251897386443553643039778634230250332845825954885827547355209)
    expCertificate := {
      argument := ((6959849 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((6959849 : ℚ) / 33554432)
        terms := 8
        lower := ((91115616606015305147990909499502497499248821609294811153114484433 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
        upper := ((637809316341206540274827747273068821180771048151377228872735512649 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((91115616606015305147990909499502497499248821609294811153114484433 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      upper := ((637809316341206540274827747273068821180771048151377228872735512649 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
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
    word := 1066183200
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1062405026
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((288081 : ℚ) / 262144)
    runtimeValue := ((6914513 : ℚ) / 8388608)
    localError := ((6842303086582442903582622482582879436048399261805337219948253203229545837903586605113421807757292679 : ℚ) / 18728689072106250220739009494107596759417978750383249511500466744433154245285173232882706642278128218537984)
    outputLower := ((46007578710115742759514728025232706289087256399149043951929582180372026306622349249675113078875750400 : ℚ) / 55815865374133741747496329369778600950226420572546864563302980108033204253657604612542755346932043009)
    outputUpper := ((1840303148404629710380589121009308251563490255965961758077183287214881052264893969987004523155030016 : ℚ) / 2232633718503266599266411005748223872115371078298479260385092108778137474690100339994753198895231273)
    expCertificate := {
      argument := ((-288081 : ℚ) / 262144)
      halvings := 1
      reduced := {
        argument := ((-288081 : ℚ) / 524288)
        terms := 8
        lower := ((23622444461597810996952196625660171872244000136883 : ℚ) / 40922045845265281709703175316055924550366111203328)
        upper := ((118112317181926052214591707037924890387440422676097 : ℚ) / 204610229226326408548515876580279622751830556016640)
      }
      lower := ((558019882341273094668713988111295014266850732770863488746611488245517209678078148776750922736955689 : ℚ) / 1674613836161993504597697017636928857848520345527615771638480620532620265012022191218002276158275584)
      upper := ((13950519470083904132553903928855379504013411934356470272340964594717697628357049832092698442975153409 : ℚ) / 41865345904049837614942425440923221446213008638190394290962015513315506625300554780450056903956889600)
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
    word := 1061726552
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1057603930
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1643819 : ℚ) / 2097152)
    runtimeValue := ((4513965 : ℚ) / 8388608)
    localError := ((266425358221759411709813832435955239927120706125389549499 : ℚ) / 98310982386889980956744629164513501662015877293255442279956480)
    outputLower := ((31532079599680373491294951849154875236777314321317232640 : ℚ) / 58598231704052421152232420302735461689540945743568212771)
    outputUpper := ((6306415919936074698258990369830975047355462864263446528 : ℚ) / 11719582365380523318856314321102321346046433126122408185)
    expCertificate := {
      argument := ((-1643819 : ℚ) / 2097152)
      halvings := 0
      reduced := {
        argument := ((-1643819 : ℚ) / 2097152)
        terms := 8
        lower := ((3673980775834606812474992428563198132048052734658496761 : ℚ) / 8045601589545916506381321892539123213998380391463911424)
        upper := ((18370223756322838620325810840039845619549043786248655651 : ℚ) / 40228007947729582531906609462695616069991901957319557120)
      }
      lower := ((3673980775834606812474992428563198132048052734658496761 : ℚ) / 8045601589545916506381321892539123213998380391463911424)
      upper := ((18370223756322838620325810840039845619549043786248655651 : ℚ) / 40228007947729582531906609462695616069991901957319557120)
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
    word := 1011568904
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1003262970
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1665569 : ℚ) / 134217728)
    runtimeValue := ((6703613 : ℚ) / 1073741824)
    localError := ((257912924312638819135542500929456423025714033766291269491613878724497 : ℚ) / 3452342108134375598774310557573763435018598063850369810157755531146571970248704)
    outputLower := ((140514475050516114147817888659375337372815913702970155194754069954560 : ℚ) / 22506708984207947917097922892663800765958416995549049904697805414941443)
    outputUpper := ((20073496435788016306831126951339333910402273386138593599250581422080 : ℚ) / 3215244140601135416677510885124805788526868507126690643055136810193371)
    expCertificate := {
      argument := ((-1665569 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-1665569 : ℚ) / 134217728)
        terms := 8
        lower := ((1597647340572097028997489979903627948108639841774256294188920195240411 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
        upper := ((11183531384004679203337776556115555883030816338082009462634289110270723 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((1597647340572097028997489979903627948108639841774256294188920195240411 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
      upper := ((11183531384004679203337776556115555883030816338082009462634289110270723 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
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
    word := 3189524982
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180356249
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5121275 : ℚ) / 33554432)
    runtimeValue := ((-9462425 : ℚ) / 134217728)
    localError := ((76051607739565562528064893542045938416735713549432322744835450125 : ℚ) / 30122095108830029097988794591713829538709881466145596047089435924519452672)
    outputLower := ((-15822235499712677205587713641681906523303509327089027703531110400 : ℚ) / 224427097354839719995643785022998902723034517135707511655698984299)
    outputUpper := ((-15822235499712677205587713641681906523303509327089027703531110400 : ℚ) / 224427097356543161705052812335743230124636601404440373533140390549)
    expCertificate := {
      argument := ((5121275 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((5121275 : ℚ) / 33554432)
        terms := 8
        lower := ((120760310243603739339880726521885820909122157600791980264736615787 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
        upper := ((120760310245307181049289753834630148310724241869524842142178022037 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      }
      lower := ((120760310243603739339880726521885820909122157600791980264736615787 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      upper := ((120760310245307181049289753834630148310724241869524842142178022037 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
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
    word := 985107136
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 976726950
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((187947 : ℚ) / 134217728)
    runtimeValue := ((6018515 : ℚ) / 8589934592)
    localError := ((46151239047476189875955810135451573626383204231296741054925350844085 : ℚ) / 9256885865351161246526431730346828090016212368410484384170832411466961629741056)
    outputLower := ((755047961510861113293212873423111219140601215181236412540969287680 : ℚ) / 1077643347130059409715052662690499342281396077993615109493354383328343)
    outputUpper := ((5285335730576027793052490113961778533984208506268654887786785013760 : ℚ) / 7543503429910415868005368635719534324518722817712951144243592876171679)
    expCertificate := {
      argument := ((-187947 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-187947 : ℚ) / 134217728)
        terms := 8
        lower := ((3769110896509326296751986523536786030209522598557270996889087441281439 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
        upper := ((538444413787046613821712360950106728808653189542803659871282178344023 : ℚ) / 539198933343012795893340301740392613472742888450811449622072204984320)
      }
      lower := ((3769110896509326296751986523536786030209522598557270996889087441281439 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
      upper := ((538444413787046613821712360950106728808653189542803659871282178344023 : ℚ) / 539198933343012795893340301740392613472742888450811449622072204984320)
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
    word := 3195133884
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3184881835
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3962863 : ℚ) / 16777216)
    runtimeValue := ((-13988011 : ℚ) / 134217728)
    localError := ((370379727266849466330764931218091385866972510839414216331697127 : ℚ) / 123183524088779214562586033359083702787539809127609979353960022317989888)
    outputLower := ((-95650850555858097972683413257099802311585791139773551252340736 : ℚ) / 917788774436557401437953363054124286677984961327984775259792971)
    outputUpper := ((-478254252779290489863417066285499011557928955698867756261703680 : ℚ) / 4588943873277612683255545186997853076011230246489112210224234633)
    expCertificate := {
      argument := ((3962863 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((3962863 : ℚ) / 16777216)
        terms := 8
        lower := ((512840387283291852001378915784151310842389806894720980763846219 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
        upper := ((2564201937511284936072672950647988196833254474322793237744500873 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((512840387283291852001378915784151310842389806894720980763846219 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      upper := ((2564201937511284936072672950647988196833254474322793237744500873 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
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
    word := 3196620871
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3186420389
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8949831 : ℚ) / 33554432)
    runtimeValue := ((-15526565 : ℚ) / 134217728)
    localError := ((131972444008296711348434412095246634990036416452262394886814636645 : ℚ) / 17822822612970863610214298881316267558194104978951188698672696000319062016)
    outputLower := ((-3072289046176738964148192106445880049214393121165476260000825344 : ℚ) / 26558075252057549846148803907863907724172884694409836263608272243)
    outputUpper := ((-15361445230883694820740960532229400246071965605827381300004126720 : ℚ) / 132790376342615959124373636255534496591941304348045503338222920897)
    expCertificate := {
      argument := ((8949831 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((8949831 : ℚ) / 33554432)
        terms := 8
        lower := ((15039543350809107551064019629962454189293733634974777220168009075 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((75197716836373747648949714866027228917545549050870208121021605057 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((15039543350809107551064019629962454189293733634974777220168009075 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((75197716836373747648949714866027228917545549050870208121021605057 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
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
    word := 3205177680
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192681530
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-569877 : ℚ) / 1048576)
    runtimeValue := ((-6699549 : ℚ) / 33554432)
    localError := ((16681752432573194670031386043251166867242954450440667 : ℚ) / 683446691634642177654538847041038545753958932143498103619584)
    outputLower := ((-4066778166880971495689264167059849699181952489226240 : ℚ) / 20368298638899391223625506372482733301936356191143337)
    outputUpper := ((-4066778166880971495689264167059849699181952489226240 : ℚ) / 20368301817097688933693540598283989100506655248841303)
    expCertificate := {
      argument := ((569877 : ℚ) / 1048576)
      halvings := 0
      reduced := {
        argument := ((569877 : ℚ) / 1048576)
        terms := 8
        lower := ((12885410255765168282422640028975364241297981571106217 : ℚ) / 7482888383134222941202866343507369060638374620037120)
        upper := ((12885413433963465992490674254776620039868280628804183 : ℚ) / 7482888383134222941202866343507369060638374620037120)
      }
      lower := ((12885410255765168282422640028975364241297981571106217 : ℚ) / 7482888383134222941202866343507369060638374620037120)
      upper := ((12885413433963465992490674254776620039868280628804183 : ℚ) / 7482888383134222941202866343507369060638374620037120)
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

def replay0 : Float32AffineSiLUReplay 64 256 where
  affine := GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0
  activation := ![activation0_0, activation0_1, activation0_2, activation0_3, activation0_4, activation0_5, activation0_6, activation0_7, activation0_8, activation0_9, activation0_10, activation0_11, activation0_12, activation0_13, activation0_14, activation0_15, activation0_16, activation0_17, activation0_18, activation0_19, activation0_20, activation0_21, activation0_22, activation0_23, activation0_24, activation0_25, activation0_26, activation0_27, activation0_28, activation0_29, activation0_30, activation0_31, activation0_32, activation0_33, activation0_34, activation0_35, activation0_36, activation0_37, activation0_38, activation0_39, activation0_40, activation0_41, activation0_42, activation0_43, activation0_44, activation0_45, activation0_46, activation0_47, activation0_48, activation0_49, activation0_50, activation0_51, activation0_52, activation0_53, activation0_54, activation0_55, activation0_56, activation0_57, activation0_58, activation0_59, activation0_60, activation0_61, activation0_62, activation0_63]
  radius := ((2557317865345752800923 : ℚ) / 1180591620717411303424)

theorem replay0_is_accepted : replay0.check = true := by
  refine replay0.check_of_observed_radius_and_affine_budget
    ((9085401 : ℚ) / 4194304) GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0_is_accepted ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [replay0]
  · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
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
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]
    · norm_num [replay0, GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0,
        GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture.replay0Output,
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
        Float32AffineReplay.ofRows]

def certificateBatch : Float32AffineSiLUReplayBatch 64 256 where
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

end GeneratedAuthenticatedAffineSiLUReplaySite0Invocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
