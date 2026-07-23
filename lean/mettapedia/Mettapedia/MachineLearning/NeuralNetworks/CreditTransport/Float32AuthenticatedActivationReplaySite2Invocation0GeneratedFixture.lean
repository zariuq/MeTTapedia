import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedActivationReplaySite2Invocation0Fixture

open Float32CheckpointMatrix
open Float32ActivationReplayCertificate
open Float32ActivationReplayBatchCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: beb12bfe26f0d944d8a2c55afb8bbb3b1937978f40a171bdae2875ae190c117b
-- Site 2, flat indices [0, 64).
-- Source invocation indices: 0

def replay0 : Float32ActivationReplay where
  input := {
    word := 3192599260
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3182893700
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3329207 : ℚ) / 16777216)
    runtimeValue := ((-2999969 : ℚ) / 33554432)
    localError := ((4462098068440925520353141215818865309688093038032188329150167 : ℚ) / 2393497833940684117028655214100817766282104709293523859987661024395264)
    outputLower := ((-6377493602649379060585771789022499232834739520934379561943040 : ℚ) / 71331794081350687653680301132822566219630977788374539017309577)
    outputUpper := ((-6377493602649379060585771789022499232834739520934379561943040 : ℚ) / 71331794085662485075825432038854795574671650815740818294649463)
    expCertificate := {
      argument := ((3329207 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((3329207 : ℚ) / 16777216)
        terms := 8
        lower := ((39193033196170882142841059285999314169186917912718682311282057 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((39193033200482679564986190192031543524227590940084961588621943 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      }
      lower := ((39193033196170882142841059285999314169186917912718682311282057 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((39193033200482679564986190192031543524227590940084961588621943 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
    }
  }

theorem replay0_is_accepted : replay0.check = true := by
  norm_num [replay0, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay1 : Float32ActivationReplay where
  input := {
    word := 3197859382
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3187935774
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5094171 : ℚ) / 16777216)
    runtimeValue := ((-4326671 : ℚ) / 33554432)
    localError := ((55850367628268510494908816851517041376042229337621643726139951 : ℚ) / 17775699162484525560503361149598888152113925340029465547550462488608768)
    outputLower := ((-68309450491697851725381741544396529736962239061940175204515840 : ℚ) / 529757117107049392476778064656224493745384375453873442040397599)
    outputUpper := ((-68309450491697851725381741544396529736962239061940175204515840 : ℚ) / 529757118014072077420153086611796996671346969928594930168938721)
    expCertificate := {
      argument := ((5094171 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((5094171 : ℚ) / 16777216)
        terms := 8
        lower := ((304785790910790753900903371728461729392275956324282445098204959 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((304785791817813438844278393684034232318238550799003933226746081 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((304785790910790753900903371728461729392275956324282445098204959 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((304785791817813438844278393684034232318238550799003933226746081 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
    }
  }

theorem replay1_is_accepted : replay1.check = true := by
  norm_num [replay1, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay2 : Float32ActivationReplay where
  input := {
    word := 3187811400
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3178480649
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1066121 : ℚ) / 8388608)
    runtimeValue := ((-15975433 : ℚ) / 268435456)
    localError := ((273138129894108610007883128090621666711138275064587072965031 : ℚ) / 647702220962811597053963605492231287797626377358334689060993711996928)
    outputLower := ((-143597960026477936133366539242115556585343202589194699407360 : ℚ) / 2412878800044997025482220968202618091544607197338099364418513)
    outputUpper := ((-143597960026477936133366539242115556585343202589194699407360 : ℚ) / 2412878800049288696753495795299873938741253669463139375098927)
    expCertificate := {
      argument := ((1066121 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((1066121 : ℚ) / 8388608)
        terms := 8
        lower := ((1283000487675394487991778872025238136646183217334573152097233 : ℚ) / 1129878312369602537490442096177379954898423980003526212321280)
        upper := ((1283000487679686159263053699122493983842829689459613162777647 : ℚ) / 1129878312369602537490442096177379954898423980003526212321280)
      }
      lower := ((1283000487675394487991778872025238136646183217334573152097233 : ℚ) / 1129878312369602537490442096177379954898423980003526212321280)
      upper := ((1283000487679686159263053699122493983842829689459613162777647 : ℚ) / 1129878312369602537490442096177379954898423980003526212321280)
    }
  }

theorem replay2_is_accepted : replay2.check = true := by
  norm_num [replay2, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay3 : Float32ActivationReplay where
  input := {
    word := 1040091826
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1032268667
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((8340825 : ℚ) / 67108864)
    runtimeValue := ((8858491 : ℚ) / 134217728)
    localError := ((440377612059061356654795923433744032278546132162995320906403613631 : ℚ) / 745291620305805761025156226668452340097097464749664796914147011534360936448)
    outputLower := ((366493449574396281074144538210782589645608501950502114662180454400 : ℚ) / 5552855285300357349404366513106616885193418448788410402194760825741)
    outputUpper := ((366493449574396281074144538210782589645608501950502114662180454400 : ℚ) / 5552855285290987511760283847198223662555192035183896495883725669491)
    expCertificate := {
      argument := ((-8340825 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-8340825 : ℚ) / 67108864)
        terms := 8
        lower := ((2604111118571386284218579072055451557626129363968521380763018298483 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
        upper := ((2604111118580756121862661737963844780264355777573035287074053454733 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
      }
      lower := ((2604111118571386284218579072055451557626129363968521380763018298483 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
      upper := ((2604111118580756121862661737963844780264355777573035287074053454733 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
    }
  }

theorem replay3_is_accepted : replay3.check = true := by
  norm_num [replay3, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay4 : Float32ActivationReplay where
  input := {
    word := 3190018492
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3180772934
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-2684015 : ℚ) / 16777216)
    runtimeValue := ((-4939555 : ℚ) / 67108864)
    localError := ((37274736803406193363477130895674591087893378039510807156170375 : ℚ) / 6562874846064400251905181997197567176406916030056568206676120687345664)
    outputLower := ((-7198171783455027697291687893134464931073287648798336740229120 : ℚ) / 97794455976253751693743199068271624690397322625764730672182451)
    outputUpper := ((-7198171783455027697291687893134464931073287648798336740229120 : ℚ) / 97794455977331058739701692144895811460439142402201408697338701)
    expCertificate := {
      argument := ((2684015 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((2684015 : ℚ) / 16777216)
        terms := 8
        lower := ((52800190737002023978568260482719071819775638799846531283743923 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((52800190738079331024526753559343258589817458576283209308900173 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((52800190737002023978568260482719071819775638799846531283743923 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((52800190738079331024526753559343258589817458576283209308900173 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
    }
  }

theorem replay4_is_accepted : replay4.check = true := by
  norm_num [replay4, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay5 : Float32ActivationReplay where
  input := {
    word := 3205201534
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192704503
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4570943 : ℚ) / 8388608)
    runtimeValue := ((-13422071 : ℚ) / 67108864)
    localError := ((26761271064566050795988290068273974997241272900813667844986799 : ℚ) / 1446058359779852401317727519913872662189389258204019264402099424722944)
    outputLower := ((-4309685890608255496104862340091616111073835804105378008924160 : ℚ) / 21547948714790529032315723894743213984212119254529763227732471)
    outputUpper := ((-4309685890608255496104862340091616111073835804105378008924160 : ℚ) / 21547952144986640005704922393403116129477692288192889922516489)
    expCertificate := {
      argument := ((4570943 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((4570943 : ℚ) / 8388608)
        terms := 8
        lower := ((13638800528203311269882629221501554299923151394505079741483511 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((13638803958399422243271827720161456445188724428168206436267529 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((13638800528203311269882629221501554299923151394505079741483511 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((13638803958399422243271827720161456445188724428168206436267529 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
    }
  }

theorem replay5_is_accepted : replay5.check = true := by
  norm_num [replay5, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay6 : Float32ActivationReplay where
  input := {
    word := 1053688881
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1047980543
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((13501489 : ℚ) / 33554432)
    runtimeValue := ((16181759 : ℚ) / 67108864)
    localError := ((100489306489037264214613260255025031876103336906941078167453967179 : ℚ) / 11609284235314250425374380682950781403460586677582136184926765545760489472)
    outputLower := ((29794999230071782410740803841163745136487436490925447493881692160 : ℚ) / 123565585507702329065673640449939746054284677956024713091190662639)
    outputUpper := ((41712998922100495375037125377629243191082411087295626491434369024 : ℚ) / 172991815735612070938563059016328772954055468404026868714791022923)
    expCertificate := {
      argument := ((-13501489 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-13501489 : ℚ) / 33554432)
        terms := 8
        lower := ((69325028624376090282800000515215691140143108869111337323828654411 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
        upper := ((49517880428248057168700027234858973330061564002513619240503256559 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      }
      lower := ((69325028624376090282800000515215691140143108869111337323828654411 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      upper := ((49517880428248057168700027234858973330061564002513619240503256559 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
    }
  }

theorem replay6_is_accepted : replay6.check = true := by
  norm_num [replay6, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay7 : Float32ActivationReplay where
  input := {
    word := 1045368081
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1038346663
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((13569297 : ℚ) / 67108864)
    runtimeValue := ((14936487 : ℚ) / 134217728)
    localError := ((2258452749274123476218352929853281231370554718017830748297709409761 : ℚ) / 513638817969872056954907146379844496448912367587735119813671732651757666304)
    outputLower := ((425879288733386405643373429564817591385092217127497450618680770560 : ℚ) / 3826907410993218846283161240665946129328849670199566482109365855543)
    outputUpper := ((425879288733386405643373429564817591385092217127497450618680770560 : ℚ) / 3826907410664828227757183931932938786490936399038123622093491165897)
    expCertificate := {
      argument := ((-13569297 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-13569297 : ℚ) / 67108864)
        terms := 8
        lower := ((1720661577293684493798823378259530140113034491027141397007271615177 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
        upper := ((1720661577622075112324800686992537482950947762188584257023146304823 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
      }
      lower := ((1720661577293684493798823378259530140113034491027141397007271615177 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
      upper := ((1720661577622075112324800686992537482950947762188584257023146304823 : ℚ) / 2106245833371143733958360553673408646377901908010982225086219550720)
    }
  }

theorem replay7_is_accepted : replay7.check = true := by
  norm_num [replay7, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay8 : Float32ActivationReplay where
  input := {
    word := 3213630184
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196880825
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1147741 : ℚ) / 1048576)
    runtimeValue := ((-9209785 : ℚ) / 33554432)
    localError := ((20700968455819751734552397521249777204238081008076422419683402493900681356186781439959635436337190376011732423 : ℚ) / 176772642702253903843795381278538909272801991178299728395013372774801528161820494215625103428109695642540829958995968)
    outputLower := ((-1445988864449191040116542765304822577371283732610896564157552219785221938386356370781971464690339287750672384 : ℚ) / 5268235287137445922010999360040989794516622757264963638633888148510501627976313060987743837479045857266808449)
    outputUpper := ((-36149721611229776002913569132620564434282093315272414103938805494630548459658909269549286617258482193766809600 : ℚ) / 131705933458422948629708500513643008477054316921844561639810334591720358077033137745278524097691348219419153049)
    expCertificate := {
      argument := ((1147741 : ℚ) / 1048576)
      halvings := 1
      reduced := {
        argument := ((1147741 : ℚ) / 2097152)
        terms := 8
        lower := ((1986751137995688863001206932854608324407959116506328255 : ℚ) / 1149371655649416643768760270362731887714054341637701632)
        upper := ((9933758271075752267190785823346134266089567877242445893 : ℚ) / 5746858278247083218843801351813659438570271708188508160)
      }
      lower := ((3947180084327164731323166524346987716617801323504033711361036977023634051349345811539413150887613461811345025 : ℚ) / 1321055202810281190687832835694002077898821433760929927272851171486867576626967249448330686591432395455463424)
      upper := ((98679553388165918862512679621292956529583781077821313457989055304548668661358956509070256932905538333032567449 : ℚ) / 33026380070257029767195820892350051947470535844023248181821279287171689415674181236208267164785809886386585600)
    }
  }

theorem replay8_is_accepted : replay8.check = true := by
  norm_num [replay8, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay9 : Float32ActivationReplay where
  input := {
    word := 3204696398
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192205470
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4318375 : ℚ) / 8388608)
    runtimeValue := ((-6461519 : ℚ) / 33554432)
    localError := ((352747310218232833656890334494045981745825234774824302438531 : ℚ) / 15765681860786361489811373727976237115647888482405366287121915052032)
    outputLower := ((-90478970740248299982407398249202177628255874799447834624000 : ℚ) / 469853933476995274120908192633874330390926852297942825768051)
    outputUpper := ((-12925567248606899997486771178457453946893696399921119232000 : ℚ) / 67121997407457131886624825733279073279277330136321980132043)
    expCertificate := {
      argument := ((4318375 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((4318375 : ℚ) / 8388608)
        terms := 8
        lower := ((294095084886168212733506088784059670740060899852949859406963 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((42013590465910408831281668040448407614867908358465842080459 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
      }
      lower := ((294095084886168212733506088784059670740060899852949859406963 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      upper := ((42013590465910408831281668040448407614867908358465842080459 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
    }
  }

theorem replay9_is_accepted : replay9.check = true := by
  norm_num [replay9, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay10 : Float32ActivationReplay where
  input := {
    word := 3207236749
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3194454078
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11177101 : ℚ) / 16777216)
    runtimeValue := ((-7585823 : ℚ) / 33554432)
    localError := ((35446560849229705381806264177625206482782341650140722287128395767 : ℚ) / 200205357645663365726519763338563023549279650521090787629725400592023552)
    outputLower := ((-1348897523581728793940867689596313899214567672077175137616527360 : ℚ) / 5966584612299900225595228771524519430079449728759848702839773911)
    outputUpper := ((-1348897523581728793940867689596313899214567672077175137616527360 : ℚ) / 5966588996656884228914508766316483638028322895729639229999916329)
    expCertificate := {
      argument := ((11177101 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((11177101 : ℚ) / 16777216)
        terms := 8
        lower := ((3941842676533572478412356535174654550901473956593529730360040151 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((3941847060890556481731636529966618758850347123563320257520182569 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((3941842676533572478412356535174654550901473956593529730360040151 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((3941847060890556481731636529966618758850347123563320257520182569 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
    }
  }

theorem replay10_is_accepted : replay10.check = true := by
  norm_num [replay10, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay11 : Float32ActivationReplay where
  input := {
    word := 3210554837
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196266929
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14495189 : ℚ) / 16777216)
    runtimeValue := ((-8595889 : ℚ) / 33554432)
    localError := ((100451534421196240409095883574399577057356002312065206872641044019 : ℚ) / 76376396552802187418468691790190728577081972507317937432492823185195008)
    outputLower := ((-583112578295842419691084834510961404405969847340816913850695680 : ℚ) / 2276193992877071720912119501536808269532977715352712197080040669)
    outputUpper := ((-116622515659168483938216966902192280881193969468163382770139136 : ℚ) / 455241137263511682946054867903816760935144735975695528140062471)
    expCertificate := {
      argument := ((14495189 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((14495189 : ℚ) / 16777216)
        terms := 8
        lower := ((1601280014288295805184495422753519976473652457963939206253462749 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((320258341545756499800530052147159102323279684497940929974746887 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
      }
      lower := ((1601280014288295805184495422753519976473652457963939206253462749 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((320258341545756499800530052147159102323279684497940929974746887 : ℚ) / 134982795717755183145524815756657658611865051477754598165315584)
    }
  }

theorem replay11_is_accepted : replay11.check = true := by
  norm_num [replay11, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay12 : Float32ActivationReplay where
  input := {
    word := 1042622167
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1035104475
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((10823383 : ℚ) / 67108864)
    runtimeValue := ((11694299 : ℚ) / 134217728)
    localError := ((10218762913436702180090350136776433023179057038609072478252950208209 : ℚ) / 10988972085246730343768766354253642896173866229259642896796858914168517951488)
    outputLower := ((7133645002265743395601366293646194526559881818644794902120643952640 : ℚ) / 81874222198476868448918807165724358679159479061213455325341663615171)
    outputUpper := ((1426729000453148679120273258729238905311976363728958980424128790528 : ℚ) / 16374844439469385647159901085757302893714930604127387720248220452825)
    expCertificate := {
      argument := ((-10823383 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-10823383 : ℚ) / 67108864)
        terms := 8
        lower := ((7528611939310581964534786760328986578927742590481262374886098339801 : ℚ) / 8846232500158803682625114325428316314787188013646125345362122113024)
        upper := ((37643059697682850035793235538582777105223538992982828598531053050051 : ℚ) / 44231162500794018413125571627141581573935940068230626726810610565120)
      }
      lower := ((7528611939310581964534786760328986578927742590481262374886098339801 : ℚ) / 8846232500158803682625114325428316314787188013646125345362122113024)
      upper := ((37643059697682850035793235538582777105223538992982828598531053050051 : ℚ) / 44231162500794018413125571627141581573935940068230626726810610565120)
    }
  }

theorem replay12_is_accepted : replay12.check = true := by
  norm_num [replay12, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay13 : Float32ActivationReplay where
  input := {
    word := 3196597062
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3186385306
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4463011 : ℚ) / 16777216)
    runtimeValue := ((-7745741 : ℚ) / 67108864)
    localError := ((118802706667256682838374392113475754754667471005547793958174147 : ℚ) / 44737994589961866716103143023080763982887028053162102757128432221421568)
    outputLower := ((-76944875133773379370845878144877696073778840719902305975009280 : ℚ) / 666648068469745656981705464380058396544899773651182368979506993)
    outputUpper := ((-76944875133773379370845878144877696073778840719902305975009280 : ℚ) / 666648068874506156386481866584431588394746602373750548915988687)
    expCertificate := {
      argument := ((4463011 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((4463011 : ℚ) / 16777216)
        terms := 8
        lower := ((377399220503127407384152287758649128090903234770279658625259313 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
        upper := ((377399220907887906788928689963022319940750063492847838561741007 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      }
      lower := ((377399220503127407384152287758649128090903234770279658625259313 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
      upper := ((377399220907887906788928689963022319940750063492847838561741007 : ℚ) / 289248847966618249597553176621409268453996538880902710354247680)
    }
  }

theorem replay13_is_accepted : replay13.check = true := by
  norm_num [replay13, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay14 : Float32ActivationReplay where
  input := {
    word := 1062852704
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1058580658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((446147 : ℚ) / 524288)
    runtimeValue := ((5002329 : ℚ) / 8388608)
    localError := ((42614183522819916572449163502784078845981775163374827 : ℚ) / 7347844912439721818210629295411742372823668861360381362176)
    outputLower := ((522344054824664200943153645259830548392453844500480 : ℚ) / 875940790096492312033484895357098962701679665332963)
    outputUpper := ((522344054824664200943153645259830548392453844500480 : ℚ) / 875931371741261698986366903234927937128981216115997)
    expCertificate := {
      argument := ((-446147 : ℚ) / 524288)
      halvings := 0
      reduced := {
        argument := ((-446147 : ℚ) / 524288)
        terms := 8
        lower := ((262100684062282473340819273494089068873489548066077 : ℚ) / 613830687678979225645547629740838868255491668049920)
        upper := ((262110102417513086387937265616260094446187997283043 : ℚ) / 613830687678979225645547629740838868255491668049920)
      }
      lower := ((262100684062282473340819273494089068873489548066077 : ℚ) / 613830687678979225645547629740838868255491668049920)
      upper := ((262110102417513086387937265616260094446187997283043 : ℚ) / 613830687678979225645547629740838868255491668049920)
    }
  }

theorem replay14_is_accepted : replay14.check = true := by
  norm_num [replay14, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay15 : Float32ActivationReplay where
  input := {
    word := 3198308658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188247833
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5318809 : ℚ) / 16777216)
    runtimeValue := ((-8965401 : ℚ) / 67108864)
    localError := ((101826246504841412626749591528180223689693949702148843800095213 : ℚ) / 64488790690747171708200251971714316467092077514940931977032236888227840)
    outputLower := ((-641895272173366899410842984709011821040852674173126628857610240 : ℚ) / 4804789314866734235041502771716754360614815380997353004410670647)
    outputUpper := ((-128379054434673379882168596941802364208170534834625325771522048 : ℚ) / 960957865279125745716694771822010226057351790591194212094429685)
    expCertificate := {
      argument := ((5318809 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((5318809 : ℚ) / 16777216)
        terms := 8
        lower := ((2780047379100406487858630535366889481436839608831034031930936887 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((556009478125860196280120324552037250221756636157930417598482933 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      }
      lower := ((2780047379100406487858630535366889481436839608831034031930936887 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((556009478125860196280120324552037250221756636157930417598482933 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
    }
  }

theorem replay15_is_accepted : replay15.check = true := by
  norm_num [replay15, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay16 : Float32ActivationReplay where
  input := {
    word := 1058339215
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1052713832
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9763215 : ℚ) / 16777216)
    runtimeValue := ((1565805 : ℚ) / 4194304)
    localError := ((7180613352338593326313207422561593229683504027081585809318575 : ℚ) / 42025609068374399914773000148111000790039525107780942732090400571392)
    outputLower := ((3740520863003739772564272267669826469036057019697444379688960 : ℚ) / 10019690717382095030758630258300813743228851522368183281818123)
    outputUpper := ((3740520863003739772564272267669826469036057019697444379688960 : ℚ) / 10019685999959564188664674794223547170171624447770343478224373)
    expCertificate := {
      argument := ((-9763215 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-9763215 : ℚ) / 16777216)
        terms := 8
        lower := ((3591933822923603086496826424858896760082812472639172137018869 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
        upper := ((3591938540346133928590781888936163333140039547237011940612619 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      }
      lower := ((3591933822923603086496826424858896760082812472639172137018869 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
      upper := ((3591938540346133928590781888936163333140039547237011940612619 : ℚ) / 6427752177035961102167848369364650410088811975131171341205504)
    }
  }

theorem replay16_is_accepted : replay16.check = true := by
  norm_num [replay16, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay17 : Float32ActivationReplay where
  input := {
    word := 3201694660
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190417485
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3505905 : ℚ) / 8388608)
    runtimeValue := ((-11135053 : ℚ) / 67108864)
    localError := ((58279189335428391220615308840094866361758591703309427327273 : ℚ) / 29709471996351419654144574212028286819732833658529241093346672246784)
    outputLower := ((-73456028231242126065897938358495767634304666162331469742080 : ℚ) / 442705622071938002824073190221045490230971434695191075460531)
    outputUpper := ((-73456028231242126065897938358495767634304666162331469742080 : ℚ) / 442705631201735431762703868925992948110890890039939300616781)
    expCertificate := {
      argument := ((3505905 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((3505905 : ℚ) / 8388608)
        terms := 8
        lower := ((266946773481110941436671086371230830580105482250198109099443 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((266946782610908370375301765076178288460024937594946334255693 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      }
      lower := ((266946773481110941436671086371230830580105482250198109099443 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      upper := ((266946782610908370375301765076178288460024937594946334255693 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
    }
  }

theorem replay17_is_accepted : replay17.check = true := by
  norm_num [replay17, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay18 : Float32ActivationReplay where
  input := {
    word := 3216970855
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196862643
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-12522599 : ℚ) / 8388608)
    runtimeValue := ((-9191603 : ℚ) / 33554432)
    localError := ((10533083756965605313475898386761149101987430997488116137470931502790349315685448272085470004698998147711865223781829280367730893 : ℚ) / 9254770019846375065419770126051694391627586943937727401895923330457521891551659559127687293768726208074486738025805280691771521630208)
    outputLower := ((-75554252019547506688972213964599679957818778617253047709223527877343717154035720959871869625839449675668195326170684509388800 : ℚ) / 275813639755439015192382637442698907602655498502782803830382923199460562811841355536213138513825124742820463717752852460496769)
    outputUpper := ((-3022170080781900267558888558583987198312751144690121908368941115093748686161428838394874785033577987026727813046827380375552 : ℚ) / 11032591506001795308077811596482910245838971954019620103648893700392032926688614421477126194079833797239708435780832460533673)
    expCertificate := {
      argument := ((12522599 : ℚ) / 8388608)
      halvings := 1
      reduced := {
        argument := ((12522599 : ℚ) / 16777216)
        terms := 8
        lower := ((474554045546906708524652522814520148487792130451053571317683263 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((94911050998193350391748938607926463814889545389750829601576333 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((225201542144935606835126621671439874865793264963330022978901999811263869420311268121472089589534423246676761547087001590327169 : ℚ) / 50612097610503408357256015771259032736862233539452780851480923388196693391530087414741048924290701496143702170665850870169600)
      upper := ((9008107601581658973787570965632548936364482612441508869589656764864165191027410924887484237108205737393960348954198425726889 : ℚ) / 2024483904420136334290240630850361309474489341578111234059236935527867735661203496589641956971628059845748086826634034806784)
    }
  }

theorem replay18_is_accepted : replay18.check = true := by
  norm_num [replay18, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay19 : Float32ActivationReplay where
  input := {
    word := 3199735111
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189200826
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-12064071 : ℚ) / 33554432)
    runtimeValue := ((-4959197 : ℚ) / 33554432)
    localError := ((56763230502942803801026899438624607097992258201991223569573600669 : ℚ) / 4701101031301259747612328116053461733376834423721970162680790119669039104)
    outputLower := ((-4141342242730444565037065403112377716540785276912145977892143104 : ℚ) / 28020745522915474866204016778504617169323583957299696828125810035)
    outputUpper := ((-20706711213652222825185327015561888582703926384560729889460715520 : ℚ) / 140103728511967055428395513178511313598657680264770095428251925697)
    expCertificate := {
      argument := ((12064071 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((12064071 : ℚ) / 33554432)
        terms := 8
        lower := ((16502213621667032571119232500603163634444432897864637784685546867 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((82511069005724843952971591789004045924261924967594800211050609857 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      }
      lower := ((16502213621667032571119232500603163634444432897864637784685546867 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((82511069005724843952971591789004045924261924967594800211050609857 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
    }
  }

theorem replay19_is_accepted : replay19.check = true := by
  norm_num [replay19, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay20 : Float32ActivationReplay where
  input := {
    word := 3215105972
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3197014527
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-2664429 : ℚ) / 2097152)
    runtimeValue := ((-9343487 : ℚ) / 33554432)
    localError := ((593828595485866215979124714884341847001336799115773675940065485643263087358139002800551974826488872536406387005483073 : ℚ) / 1804093338220599155565208785202069266106890077029249802673067499513059458766851930260251741304565084314979113188148402716672)
    outputLower := ((-14971617348564335106643784372759668303670144600935402560285599229660205852943235447268919085439414728607573160755200 : ℚ) / 53766171283143733607685827767910637441482844264186912854703292236121280752624628849633089938895853886454674994592321)
    outputUpper := ((-14971617348564335106643784372759668303670144600935402560285599229660205852943235447268919085439414728607573160755200 : ℚ) / 53766237113405291112939925965707371210695763608360932824514820718894483560007958725732293789262350380048170910317121)
    expCertificate := {
      argument := ((2664429 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((2664429 : ℚ) / 4194304)
        terms := 8
        lower := ((6479361389814411949585137047048063347786140765258096649439 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((6479366469808549539307429762061119870596273682538088028961 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((41982124019817748003427569925460459972922619506784527071442389057361268748209569523709633844600438442121638059014721 : ℚ) / 11784047263325985604258257842450177468560224757402385783260903178760012004415059325923456094295415444333036935577600)
      upper := ((41982189850079305508681668123257193742135538850958547041253917540134471555592899399808837694966934935715133974739521 : ℚ) / 11784047263325985604258257842450177468560224757402385783260903178760012004415059325923456094295415444333036935577600)
    }
  }

theorem replay20_is_accepted : replay20.check = true := by
  norm_num [replay20, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay21 : Float32ActivationReplay where
  input := {
    word := 1043601866
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1036248552
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((5901541 : ℚ) / 33554432)
    runtimeValue := ((1604797 : ℚ) / 16777216)
    localError := ((68584031512920291906378233279574607214566151720908918117244252933 : ℚ) / 15989868341027239659600105758221678780052772103646413043131989000835825664)
    outputLower := ((91164379488711163478373374943393081122809374362535020715080417280 : ℚ) / 953070422472193220829969987763266490701006180265332045741795837929)
    outputUpper := ((91164379488711163478373374943393081122809374362535020715080417280 : ℚ) / 953070422445708467379586602063279994711951436639034052686591817751)
    expCertificate := {
      argument := ((-5901541 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-5901541 : ℚ) / 33554432)
        terms := 8
        lower := ((434736486889528564100771309557714585642389638964456395731779975191 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
        upper := ((434736486916013317551154695257701081631444382590754388786983995369 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((434736486889528564100771309557714585642389638964456395731779975191 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      upper := ((434736486916013317551154695257701081631444382590754388786983995369 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
    }
  }

theorem replay21_is_accepted : replay21.check = true := by
  norm_num [replay21, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay22 : Float32ActivationReplay where
  input := {
    word := 3201017622
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190009103
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6673291 : ℚ) / 16777216)
    runtimeValue := ((-10726671 : ℚ) / 67108864)
    localError := ((1887088908554537160314529412195085205107135981969312590954656039 : ℚ) / 338130755277254270355126449613279784740827926172267282632296460804161536)
    outputLower := ((-805359610156536880631788769303764471377996988213988953958645760 : ℚ) / 5038540818190380557738438949028830476927975306604447282616587671)
    outputUpper := ((-805359610156536880631788769303764471377996988213988953958645760 : ℚ) / 5038540888983819937037325644690987240386425348703075686578399849)
    expCertificate := {
      argument := ((6673291 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((6673291 : ℚ) / 16777216)
        terms := 8
        lower := ((3013798882424052810555566712678965597749999534438128310136853911 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((3013798953217492189854453408341122361208449576536756714098666089 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      }
      lower := ((3013798882424052810555566712678965597749999534438128310136853911 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((3013798953217492189854453408341122361208449576536756714098666089 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
    }
  }

theorem replay22_is_accepted : replay22.check = true := by
  norm_num [replay22, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay23 : Float32ActivationReplay where
  input := {
    word := 1041585693
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1033909466
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9786909 : ℚ) / 67108864)
    runtimeValue := ((5249645 : ℚ) / 67108864)
    localError := ((2713329635298288480999422137838278183626214486343524797647755408525 : ℚ) / 1844601649112901153119095407265498177907301609073775989758675250712330371072)
    outputLower := ((430033964275800671133979534196671435217249211944368416854007349248 : ℚ) / 5497341302407379279470491579407241607943922341134206591012673512173)
    outputUpper := ((2150169821379003355669897670983357176086246059721842084270036746240 : ℚ) / 27486706511868553655134073008082779912759387628343343582133580009823)
    expCertificate := {
      argument := ((-9786909 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((-9786909 : ℚ) / 67108864)
        terms := 8
        lower := ((12742985678270547517425549132368919388114074272266468006530043154783 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
        upper := ((2548597135687778051928786804264469503014859669918831475891966141165 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
      }
      lower := ((12742985678270547517425549132368919388114074272266468006530043154783 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      upper := ((2548597135687778051928786804264469503014859669918831475891966141165 : ℚ) / 2948744166719601227541704775142772104929062671215375115120707371008)
    }
  }

theorem replay23_is_accepted : replay23.check = true := by
  norm_num [replay23, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay24 : Float32ActivationReplay where
  input := {
    word := 1059249248
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1054145617
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((333539 : ℚ) / 524288)
    runtimeValue := ((13958225 : ℚ) / 33554432)
    localError := ((11546664847684843576841521465768567272639362807094995 : ℚ) / 31498836138494582640647653810145501205773517380696254971904)
    outputLower := ((390503833270567039380245801689395247038018103541760 : ℚ) / 938739388455050871890720118588956415536773575488483)
    outputUpper := ((390503833270567039380245801689395247038018103541760 : ℚ) / 938738469436603267212142163817450440102026384493597)
    expCertificate := {
      argument := ((-333539 : ℚ) / 524288)
      halvings := 0
      reduced := {
        argument := ((-333539 : ℚ) / 524288)
        terms := 8
        lower := ((324907781757624041566594534076611571846534716443677 : ℚ) / 613830687678979225645547629740838868255491668049920)
        upper := ((324908700776071646245172488848117547281281907438563 : ℚ) / 613830687678979225645547629740838868255491668049920)
      }
      lower := ((324907781757624041566594534076611571846534716443677 : ℚ) / 613830687678979225645547629740838868255491668049920)
      upper := ((324908700776071646245172488848117547281281907438563 : ℚ) / 613830687678979225645547629740838868255491668049920)
    }
  }

theorem replay24_is_accepted : replay24.check = true := by
  norm_num [replay24, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay25 : Float32ActivationReplay where
  input := {
    word := 3205230614
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3192732428
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4585483 : ℚ) / 8388608)
    runtimeValue := ((-3362499 : ℚ) / 16777216)
    localError := ((684705646431717386284576254942939911887479420197023137326031 : ℚ) / 17233883278184096736142871569230717912880482014091783711575964123136)
    outputLower := ((-205875944830556796090574459016551207213699415806870038773760 : ℚ) / 1027219490896707578667573426319999570422201276665436250661371)
    outputUpper := ((-205875944830556796090574459016551207213699415806870038773760 : ℚ) / 1027219658442648960362545759857679629617818423231998249311749)
    expCertificate := {
      argument := ((4585483 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((4585483 : ℚ) / 8388608)
        terms := 8
        lower := ((650593386773506732837426060927539585456059949997594179887611 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
        upper := ((650593554319448114532398394465219644651677096564156178537989 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
      }
      lower := ((650593386773506732837426060927539585456059949997594179887611 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
      upper := ((650593554319448114532398394465219644651677096564156178537989 : ℚ) / 376626104123200845830147365392459984966141326667842070773760)
    }
  }

theorem replay25_is_accepted : replay25.check = true := by
  norm_num [replay25, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay26 : Float32ActivationReplay where
  input := {
    word := 3202873502
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3191098740
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7601231 : ℚ) / 16777216)
    runtimeValue := ((-2954077 : ℚ) / 16777216)
    localError := ((396571806825109721830785010900954705212879768052560852309591191 : ℚ) / 29136031978787225191903841383589992593974007211169173531615503509880832)
    outputLower := ((-305782381080528482358587008952735260435320614906938094486814720 : ℚ) / 1736642836260034155363073431467413460849166346262048097349137277)
    outputUpper := ((-305782381080528482358587008952735260435320614906938094486814720 : ℚ) / 1736642903128706001915351904953115455386543771797206229196475523)
    expCertificate := {
      argument := ((7601231 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((7601231 : ℚ) / 16777216)
        terms := 8
        lower := ((1061728857671258239635449352684125167789841088873275106522559357 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((1061728924539930086187727826169827162327218514408433238369897603 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      }
      lower := ((1061728857671258239635449352684125167789841088873275106522559357 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((1061728924539930086187727826169827162327218514408433238369897603 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
    }
  }

theorem replay26_is_accepted : replay26.check = true := by
  norm_num [replay26, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay27 : Float32ActivationReplay where
  input := {
    word := 3195274952
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3184989746
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1999065 : ℚ) / 8388608)
    runtimeValue := ((-7047961 : ℚ) / 67108864)
    localError := ((13275120760604507788783027931435383597769952989170510039763 : ℚ) / 3823424077256105784005825123301249248569295674039273656608758956032)
    outputLower := ((-41884584743764603075075982419553964447374146607452614819840 : ℚ) / 398814209311402617166009760478132332117276644113456909285491)
    outputUpper := ((-5983512106252086153582283202793423492482020943921802117120 : ℚ) / 56973458487631466746417062331754703053374524027694369205963)
    expCertificate := {
      argument := ((1999065 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((1999065 : ℚ) / 8388608)
        terms := 8
        lower := ((223055360720575555778607656628317672466410691668463942924403 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((31865051546084743691073904638924037388965102249838231154379 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
      }
      lower := ((223055360720575555778607656628317672466410691668463942924403 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      upper := ((31865051546084743691073904638924037388965102249838231154379 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
    }
  }

theorem replay27_is_accepted : replay27.check = true := by
  norm_num [replay27, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay28 : Float32ActivationReplay where
  input := {
    word := 1028709440
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1020669738
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((213873 : ℚ) / 4194304)
    runtimeValue := ((7018389 : ℚ) / 268435456)
    localError := ((1421199204735688052959864817206959714923499323296195552533 : ℚ) / 1797155387778688536190046245301544823642113006665270962414579351552)
    outputLower := ((175042414221288431901986944287416575027209026027787386880 : ℚ) / 6694925530920507521145218034466895549156192714964117714817)
    outputUpper := ((35008482844257686380397388857483315005441805205557477376 : ℚ) / 1338985106184099753142212470667256869814102424228290789811)
    expCertificate := {
      argument := ((-213873 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((-213873 : ℚ) / 4194304)
        terms := 8
        lower := ((652427103876181544597673002503918355552907297490037014963 : ℚ) / 686558002307918208544539468163338514261195126738253774848)
        upper := ((3262135519380916478422520693650202977850217081272848840577 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((652427103876181544597673002503918355552907297490037014963 : ℚ) / 686558002307918208544539468163338514261195126738253774848)
      upper := ((3262135519380916478422520693650202977850217081272848840577 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
    }
  }

theorem replay28_is_accepted : replay28.check = true := by
  norm_num [replay28, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay29 : Float32ActivationReplay where
  input := {
    word := 1059267942
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1054175455
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((5345971 : ℚ) / 8388608)
    runtimeValue := ((13988063 : ℚ) / 33554432)
    localError := ((32990184658015790030044416360204545954635748372295625647416971 : ℚ) / 81140594716770096212326758317206496723195838717604534759662339227648)
    outputLower := ((5040416340851528063851858802247570593843219017937662267883520 : ℚ) / 12090902820796626577824482564659702258147493525553528599261993)
    outputUpper := ((1008083268170305612770371760449514118768643803587532453576704 : ℚ) / 2418178162478509432444773862278655073737974128651754103888939)
    expCertificate := {
      argument := ((-5345971 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-5345971 : ℚ) / 8388608)
        terms := 8
        lower := ((836348525161065879958154927630323136880180556646817406639147 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
        upper := ((4181754634209408815391387891418042573858525665528845113013033 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((836348525161065879958154927630323136880180556646817406639147 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
      upper := ((4181754634209408815391387891418042573858525665528845113013033 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
    }
  }

theorem replay29_is_accepted : replay29.check = true := by
  norm_num [replay29, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay30 : Float32ActivationReplay where
  input := {
    word := 3208754590
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3195499867
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6347471 : ℚ) / 8388608)
    runtimeValue := ((-16217435 : ℚ) / 67108864)
    localError := ((768790924638857888364840664604964066869174712133584365567318195 : ℚ) / 1661947555161579795221117925359284100203467082924538679286920825012224)
    outputLower := ((-5984674543030852522579307303268421988236114872865526403563520 : ℚ) / 24764948415183719921426742156733335557631657763191143859727991)
    outputUpper := ((-5984674543030852522579307303268421988236114872865526403563520 : ℚ) / 24764995847934118791938297396349715094721673140969865966801289)
    expCertificate := {
      argument := ((6347471 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((6347471 : ℚ) / 8388608)
        terms := 8
        lower := ((16855800228596502158993647483491675873342689903166460373479031 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((16855847661346901029505202723108055410432705280945182480552329 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((16855800228596502158993647483491675873342689903166460373479031 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((16855847661346901029505202723108055410432705280945182480552329 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
    }
  }

theorem replay30_is_accepted : replay30.check = true := by
  norm_num [replay30, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay31 : Float32ActivationReplay where
  input := {
    word := 3190387162
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3181081876
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-5552365 : ℚ) / 33554432)
    runtimeValue := ((-2547013 : ℚ) / 33554432)
    localError := ((407738274714999459066461113481741686367546500114658675292727813 : ℚ) / 361091342224684646747038805186973808639290095202965134199634052973068288)
    outputLower := ((-816861561960943775139728975174728939229113002829723804410839040 : ℚ) / 10761360592385668955655062353222781677224936938374195522059024959)
    outputUpper := ((-816861561960943775139728975174728939229113002829723804410839040 : ℚ) / 10761360592540517550751582658586621018690588172171873005394806209)
    expCertificate := {
      argument := ((5552365 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((5552365 : ℚ) / 33554432)
        terms := 8
        lower := ((5824846920422050829190154805550730162276729341473455932013197887 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
        upper := ((5824846920576899424286675110914569503742380575271133415348979137 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
      }
      lower := ((5824846920422050829190154805550730162276729341473455932013197887 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
      upper := ((5824846920576899424286675110914569503742380575271133415348979137 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
    }
  }

theorem replay31_is_accepted : replay31.check = true := by
  norm_num [replay31, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay32 : Float32ActivationReplay where
  input := {
    word := 3188744478
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3179689920
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4731023 : ℚ) / 33554432)
    runtimeValue := ((-137439 : ℚ) / 2097152)
    localError := ((911298961593773861305285644170943218354744950656930197985254487 : ℚ) / 2338646818201139224350962769121941542503909399898573604871350199175348224)
    outputLower := ((-73082738244438317851717786836491751024499698421948355744460963840 : ℚ) / 1115153702831811535048943886338206073047594737958227922855067348087)
    outputUpper := ((-14616547648887663570343557367298350204899939684389671148892192768 : ℚ) / 223030740567265837839502860177074613166232065403036480470441218229)
    expCertificate := {
      argument := ((4731023 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((4731023 : ℚ) / 33554432)
        terms := 8
        lower := ((596819767275631631770128593832640663978032940283650265900255505527 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
        upper := ((119363953456029857183739801675961531352319705868120949079478849717 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
      }
      lower := ((596819767275631631770128593832640663978032940283650265900255505527 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      upper := ((119363953456029857183739801675961531352319705868120949079478849717 : ℚ) / 103666787111235980655763058501113081813912359534915531390962368512)
    }
  }

theorem replay32_is_accepted : replay32.check = true := by
  norm_num [replay32, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay33 : Float32ActivationReplay where
  input := {
    word := 1015584720
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1007270741
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((559485 : ℚ) / 33554432)
    runtimeValue := ((9026389 : ℚ) / 1073741824)
    localError := ((2723740484986957756229023900074402164733293906049493773282463409 : ℚ) / 24531346394776667872302949349712878511096301915639747291351331279841787904)
    outputLower := ((192059451960622809453770832172682724325712377741575956610416640 : ℚ) / 22846596683167543143316124891594870491974336947910252298555645421)
    outputUpper := ((192059451960622809453770832172682724325712377741575956610416640 : ℚ) / 22846596683167543139475803506318583162304184957346428310405489171)
    expCertificate := {
      argument := ((-559485 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-559485 : ℚ) / 33554432)
        terms := 8
        lower := ((11328064781919100844391019228417129627425033897911369266965226003 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
        upper := ((11328064781919100848231340613693416957095185888475193255115382253 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((11328064781919100844391019228417129627425033897911369266965226003 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      upper := ((11328064781919100848231340613693416957095185888475193255115382253 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
    }
  }

theorem replay33_is_accepted : replay33.check = true := by
  norm_num [replay33, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay34 : Float32ActivationReplay where
  input := {
    word := 1069769258
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1067483421
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6402325 : ℚ) / 4194304)
    runtimeValue := ((10518813 : ℚ) / 8388608)
    localError := ((144063756278813329851133623909351377375887471763489640803524394952650696574008562401803776597477525259975326606368693036811 : ℚ) / 25551025867005375088548678259341548089865989672832830925838654277935729489479050880266259153236083122242384782489847175183335424)
    outputLower := ((3819418332505660502179001751208969643358366949103021621465678010912706376468436387878921358844813469034875229115200307200 : ℚ) / 3045934628451961106573400714681529408185443483007273711674850821235262305536749475986540652849907324674310182757597824953)
    outputUpper := ((3819418332505660502179001751208969643358366949103021621465678010912706376468436387878921358844813469034875229115200307200 : ℚ) / 3045919640899345289295754225175565253480194768051246515016395363561598001656419143708498376993666067390726182757597824953)
    expCertificate := {
      argument := ((-6402325 : ℚ) / 4194304)
      halvings := 1
      reduced := {
        argument := ((-6402325 : ℚ) / 8388608)
        terms := 8
        lower := ((737383644654199176250788592517814814176165571264868575045867 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
        upper := ((737393807240151765757343607284756680586204076978308516452117 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
      }
      lower := ((543734639403510281399186062656045202402411005419608789815006939218377686279260281041246812743454384536942078861153781689 : ℚ) / 2502185001495835007896568162519520051077783762631637725201388424343220315377158862667251564250211682853784103896444043264)
      upper := ((543749626956126098676832552162009357107659720375635986473462396892041990159590613319289088599695641820526078861153781689 : ℚ) / 2502185001495835007896568162519520051077783762631637725201388424343220315377158862667251564250211682853784103896444043264)
    }
  }

theorem replay34_is_accepted : replay34.check = true := by
  norm_num [replay34, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay35 : Float32ActivationReplay where
  input := {
    word := 3202486715
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190879364
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-14815675 : ℚ) / 33554432)
    runtimeValue := ((-2899233 : ℚ) / 16777216)
    localError := ((1370153847170970233665592118816961830256454997197780375028303777 : ℚ) / 211616040458384946662365908203017059929745071712223140817071707892219904)
    outputLower := ((-2179675763752149879509597096781615073345014023429523856215244800 : ℚ) / 12613298522322682211165436154848232367179391596828427853648168319)
    outputUpper := ((-2179675763752149879509597096781615073345014023429523856215244800 : ℚ) / 12613298920296725431821698439301077123269144994749018002573949569)
    expCertificate := {
      argument := ((14815675 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((14815675 : ℚ) / 33554432)
        terms := 8
        lower := ((7676784850359064084700528607176180852231183999927688263602341247 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
        upper := ((7676785248333107305356790891629025608320937397848278412528122497 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
      }
      lower := ((7676784850359064084700528607176180852231183999927688263602341247 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
      upper := ((7676785248333107305356790891629025608320937397848278412528122497 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
    }
  }

theorem replay35_is_accepted : replay35.check = true := by
  norm_num [replay35, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay36 : Float32ActivationReplay where
  input := {
    word := 1035296228
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1027433579
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2971513 : ℚ) / 33554432)
    runtimeValue := ((12412011 : ℚ) / 268435456)
    localError := ((262268429465931317189233906847450241081573679983885869520575041539 : ℚ) / 266486369876940689573473069864138055688295363326845060631069802771339280384)
    outputLower := ((45902610655020201591603227444860046666876101079385795508347863040 : ℚ) / 992739088374900406500224284321584014923480761523712652292362610889)
    outputUpper := ((6557515807860028798800461063551435238125157297055113644049694720 : ℚ) / 141819869767827283898355402894541226214702774501705527658669032273)
    expCertificate := {
      argument := ((-2971513 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-2971513 : ℚ) / 33554432)
        terms := 8
        lower := ((67772164688373012001381789679460453490479660548194433807981626193 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
        upper := ((474405152818720503221408991816018605853918963849134995337550768329 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
      }
      lower := ((67772164688373012001381789679460453490479660548194433807981626193 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      upper := ((474405152818720503221408991816018605853918963849134995337550768329 : ℚ) / 518333935556179903278815292505565409069561797674577656954811842560)
    }
  }

theorem replay36_is_accepted : replay36.check = true := by
  norm_num [replay36, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay37 : Float32ActivationReplay where
  input := {
    word := 3199771543
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3189224417
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-12100503 : ℚ) / 33554432)
    runtimeValue := ((-9941985 : ℚ) / 67108864)
    localError := ((5213011636468796878265334597017927824719414486844902564100656237 : ℚ) / 1881643482840179161210578177804639581442356660207368353322883126015295488)
    outputLower := ((-20769242916502428015619563670322205454582836036704050043273871360 : ℚ) / 140193363316471865575454811839815317367039338608651037788699094463)
    outputUpper := ((-4153848583300485603123912734064441090916567207340810008654774272 : ℚ) / 28038672847154425996699604061315053424870322051754122276945160717)
    expCertificate := {
      argument := ((12100503 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((12100503 : ℚ) / 33554432)
        terms := 8
        lower := ((82600703810229654100030890450308049692643583311475742571497778623 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
        upper := ((16520140945905983701614819783413599889991170992319063233504897549 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
      }
      lower := ((82600703810229654100030890450308049692643583311475742571497778623 : ℚ) / 57592659506242211475423921389507267674395755297175295217201315840)
      upper := ((16520140945905983701614819783413599889991170992319063233504897549 : ℚ) / 11518531901248442295084784277901453534879151059435059043440263168)
    }
  }

theorem replay37_is_accepted : replay37.check = true := by
  norm_num [replay37, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay38 : Float32ActivationReplay where
  input := {
    word := 1066238996
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1062511819
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2318597 : ℚ) / 2097152)
    runtimeValue := ((13935819 : ℚ) / 16777216)
    localError := ((6205373600344344633931107666250973051085282839768891840645661730500339575247255844747758317920276906959274791402941061 : ℚ) / 21314836117795772224769739890769037083733455287839233247973169355300887967397440680933413452795605696730561551048644856119296)
    outputLower := ((21536680992681863938255573706308168142413877436471966890051139194455804939907037072673719269101186250197390747238400 : ℚ) / 25927832034897886829906204816583752542722496975990687570866563921223666570451968542266977806826978744912036424962529)
    outputUpper := ((1055297368641411332974523111609100238978279994387126377612505820528334442055444816561012244185958126259672146614681600 : ℚ) / 1270463235246883167312725775883736436589566188325836256025622448641114709818210642393434849548077922864589783611812881)
    expCertificate := {
      argument := ((-2318597 : ℚ) / 2097152)
      halvings := 1
      reduced := {
        argument := ((-2318597 : ℚ) / 4194304)
        terms := 8
        lower := ((17775134511937689788656689296924134961234651998515649229591 : ℚ) / 30895110103856319384504276067350233141753780703221419868160)
        upper := ((2539307077991672220373267435648986932191901861937370378127 : ℚ) / 4413587157693759912072039438192890448821968671888774266880)
      }
      lower := ((315955406917478333367806890645272061636187982976243007581489291161553737460590836993634905910149271873613791830027281 : ℚ) / 954507828329404833944918885238464374953378205349593248444133157479560972357619805399799943637928650990975991781785600)
      upper := ((6448080436338604504499696954574275502857635642325519235272009686946912032541360268801672834624353214483954960028129 : ℚ) / 19479751598559282325406507862009477039864861333665168335594554234276754537910608273465304972202625530428081464934400)
    }
  }

theorem replay38_is_accepted : replay38.check = true := by
  norm_num [replay38, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay39 : Float32ActivationReplay where
  input := {
    word := 1056188274
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1050060047
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((8000441 : ℚ) / 16777216)
    runtimeValue := ((9872655 : ℚ) / 33554432)
    localError := ((4046065602698131493924175365254105195563953189729662766913998535 : ℚ) / 110110688169691024242773349931288905829175091257837556569033281323925504)
    outputLower := ((193105082480004965400689667909802786395973249252391780930813952 : ℚ) / 656310905857442288582831162748473697605302206652773372646960885)
    outputUpper := ((965525412400024827003448339549013931979866246261958904654069760 : ℚ) / 3281554227164120204531352219918039614831658937270568506986894647)
    expCertificate := {
      argument := ((-8000441 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-8000441 : ℚ) / 16777216)
        terms := 8
        lower := ((1256812291397792457348479983568174735653683165104249534507160887 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
        upper := ((251362518704176739146256715478500721769707052219509578151014133 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
      }
      lower := ((1256812291397792457348479983568174735653683165104249534507160887 : ℚ) / 2024741935766327747182872236349864879177975772166318972479733760)
      upper := ((251362518704176739146256715478500721769707052219509578151014133 : ℚ) / 404948387153265549436574447269972975835595154433263794495946752)
    }
  }

theorem replay39_is_accepted : replay39.check = true := by
  norm_num [replay39, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay40 : Float32ActivationReplay where
  input := {
    word := 1031999025
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1023885132
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((8588849 : ℚ) / 134217728)
    runtimeValue := ((2215891 : ℚ) / 67108864)
    localError := ((1677319492316227416986433499967165465051854921000765367257404230611193 : ℚ) / 1472667829169349214862271503946327523133606707673567535340428535852115513311232)
    outputLower := ((724591781261028679377661042679220859069286584699788189185982867701760 : ℚ) / 21944460707446176035140030144845359372103314216041081180280872223557763)
    outputUpper := ((103513111608718382768237291811317265581326654957112598455140409671680 : ℚ) / 3134922958206571194032996760592172138653161702380626727698159907234651)
    expCertificate := {
      argument := ((-8588849 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-8588849 : ℚ) / 134217728)
        terms := 8
        lower := ((1517326158177532806352975855370994298234933037028192378831943292281691 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
        upper := ((10621283107242907321379883808297114489175713558574040738217355918887043 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
      }
      lower := ((1517326158177532806352975855370994298234933037028192378831943292281691 : ℚ) / 1617596800029038387680020905221177840418228665352434348866216614952960)
      upper := ((10621283107242907321379883808297114489175713558574040738217355918887043 : ℚ) / 11323177600203268713760146336548244882927600657467040442063516304670720)
    }
  }

theorem replay40_is_accepted : replay40.check = true := by
  norm_num [replay40, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay41 : Float32ActivationReplay where
  input := {
    word := 3207730848
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3194817998
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-364725 : ℚ) / 524288)
    runtimeValue := ((-7767783 : ℚ) / 33554432)
    localError := ((921702994050239433120928264353761781734418000153627 : ℚ) / 4126247102799378140081471610184862622225336733322646126592)
    outputLower := ((-28467737523869285338538151964470857775940475289600 : ℚ) / 122971746408920828702493655985142666763822338978131)
    outputUpper := ((-28467737523869285338538151964470857775940475289600 : ℚ) / 122971871660801337767544000670573212789273999134381)
    expCertificate := {
      argument := ((364725 : ℚ) / 524288)
      halvings := 0
      reduced := {
        argument := ((364725 : ℚ) / 524288)
        terms := 8
        lower := ((82049700563655546992790480669086742213456227774803 : ℚ) / 40922045845265281709703175316055924550366111203328)
        upper := ((82049825815536056057840825354517288238907887931053 : ℚ) / 40922045845265281709703175316055924550366111203328)
      }
      lower := ((82049700563655546992790480669086742213456227774803 : ℚ) / 40922045845265281709703175316055924550366111203328)
      upper := ((82049825815536056057840825354517288238907887931053 : ℚ) / 40922045845265281709703175316055924550366111203328)
    }
  }

theorem replay41_is_accepted : replay41.check = true := by
  norm_num [replay41, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay42 : Float32ActivationReplay where
  input := {
    word := 1054883028
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1049119014
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((3673909 : ℚ) / 8388608)
    runtimeValue := ((4465811 : ℚ) / 16777216)
    localError := ((6463470693350647742283299393596179227973992235053790108698699 : ℚ) / 218327082698693244374046645097016753705024420291832451445753523470336)
    outputLower := ((3463922823075826003833151867136310659533309653002670393262080 : ℚ) / 13013308806550328381373885529708569147027159961702736401209449)
    outputUpper := ((3463922823075826003833151867136310659533309653002670393262080 : ℚ) / 13013308209102943204286494558871790987552667873611000266418071)
    expCertificate := {
      argument := ((-3673909 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-3673909 : ℚ) / 8388608)
        terms := 8
        lower := ((5104160022515725441853399885630131303263700013586316780169111 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
        upper := ((5104160619963110618940790856466909462738192101678052914960489 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      }
      lower := ((5104160022515725441853399885630131303263700013586316780169111 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
      upper := ((5104160619963110618940790856466909462738192101678052914960489 : ℚ) / 7909148186587217762433094673241659684288967860024683486248960)
    }
  }

theorem replay42_is_accepted : replay42.check = true := by
  norm_num [replay42, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay43 : Float32ActivationReplay where
  input := {
    word := 1066801338
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1063599048
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4918365 : ℚ) / 4194304)
    runtimeValue := ((1877881 : ℚ) / 2097152)
    localError := ((43574699691920603854930065366948070949195829469193328873229062780276750663224724587485363924405653568322208067069494367 : ℚ) / 84837282593649380955526199046340504219434064820891776410503172872213346505096348109921880952577004765395960932021759740215296)
    outputLower := ((36223903511430194491554791458301541940722006149338365720555007539251241526309295788465949458262044363666910754782576640 : ℚ) / 40453595529594397363114943572629714191981235526172318599453489239347410748454811678230955996555655134949327204315341673)
    outputUpper := ((36223903511430194491554791458301541940722006149338365720555007539251241526309295788465949458262044363666910754782576640 : ℚ) / 40453568741631212690127467654390575513569862757154358105899416385752366306827711157761517025269033796976070848475341673)
    expCertificate := {
      argument := ((-4918365 : ℚ) / 4194304)
      halvings := 1
      reduced := {
        argument := ((-4918365 : ℚ) / 8388608)
        terms := 8
        lower := ((97787503719329807768306180555043212162602141128716037851923 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
        upper := ((97787640689512116179821998850472161282272041834135988008173 : ℚ) / 175758848590827061387402103849814659650865952444992966361088)
      }
      lower := ((9562395883657940987700700215877982290387347169109447918227954356823720437973898038412732281439259934583674504074797929 : ℚ) / 30891172857973271702426767438512593223182515588044910187671462028928645868853813119348784743829773862392396344400543744)
      upper := ((9562422671621125660688176134117120968798719938127408411782027210418764879600998558882171252725881272556930859914797929 : ℚ) / 30891172857973271702426767438512593223182515588044910187671462028928645868853813119348784743829773862392396344400543744)
    }
  }

theorem replay43_is_accepted : replay43.check = true := by
  norm_num [replay43, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay44 : Float32ActivationReplay where
  input := {
    word := 1052549133
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1046412201
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((12361741 : ℚ) / 33554432)
    runtimeValue := ((14613417 : ℚ) / 67108864)
    localError := ((21318081015728011994185912026141696333504662759928876137022835239 : ℚ) / 8407160800482914294089426660286196834395656740170902851211699779176235008)
    outputLower := ((27279810662168208674608662438363009884855465916001504147317719040 : ℚ) / 125276458270593200535914699141475511109764229359789235162909325647)
    outputUpper := ((27279810662168208674608662438363009884855465916001504147317719040 : ℚ) / 125276456868387959347226051315756296769843704752674579190513583793)
    expCertificate := {
      argument := ((-12361741 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-12361741 : ℚ) / 33554432)
        terms := 8
        lower := ((51228751788933687450252438100675524045620590799163485339826177713 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
        upper := ((51228753191138928638941085926394738385541115406278141312221919567 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      }
      lower := ((51228751788933687450252438100675524045620590799163485339826177713 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
      upper := ((51228753191138928638941085926394738385541115406278141312221919567 : ℚ) / 74047705079454271896973613215080772724223113953511093850687406080)
    }
  }

theorem replay44_is_accepted : replay44.check = true := by
  norm_num [replay44, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay45 : Float32ActivationReplay where
  input := {
    word := 3193326154
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3183473435
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-7021861 : ℚ) / 33554432)
    runtimeValue := ((-12579611 : ℚ) / 134217728)
    localError := ((4013885144151148604094580434819847941889979325966219293380162185 : ℚ) / 493121505095138536679424924505694349488339972185977309496296158431019008)
    outputLower := ((-344351061474562918554912032461206310220616419559528670693425152 : ℚ) / 3674041517787713830764777395916688065889030487730930071296514261)
    outputUpper := ((-1721755307372814592774560162306031551103082097797643353467125760 : ℚ) / 18370207590627258569668388658961415245811035062157444381707994071)
    expCertificate := {
      argument := ((7021861 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((7021861 : ℚ) / 33554432)
        terms := 8
        lower := ((2028536960466507788609808213359337560906294622097350207947905237 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
        upper := ((10142684804021228358893542746174662720897355733989545064964948951 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
      }
      lower := ((2028536960466507788609808213359337560906294622097350207947905237 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
      upper := ((10142684804021228358893542746174662720897355733989545064964948951 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
    }
  }

theorem replay45_is_accepted : replay45.check = true := by
  norm_num [replay45, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay46 : Float32ActivationReplay where
  input := {
    word := 3184846170
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3175733020
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6976173 : ℚ) / 67108864)
    runtimeValue := ((-3306951 : ℚ) / 67108864)
    localError := ((2419887095933935966601076163213201241314759997509548005141877747111 : ℚ) / 2087259655168811038577904081948686334285979431458693271388901898294849961984)
    outputLower := ((-1532655167563019741650171371275341354575700605082554896397662945280 : ℚ) / 31102592575074108248010383639559354119282335544472044732547066410719)
    outputUpper := ((-1532655167563019741650171371275341354575700605082554896397662945280 : ℚ) / 31102592575085327604083777695129608128755978218595583310557930146081)
    expCertificate := {
      argument := ((6976173 : ℚ) / 67108864)
      halvings := 0
      reduced := {
        argument := ((6976173 : ℚ) / 67108864)
        terms := 8
        lower := ((16358871741476102110301859763845493594637022188395169156943529555679 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
        upper := ((16358871741487321466375253819415747604110664862518707734954393291041 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      }
      lower := ((16358871741476102110301859763845493594637022188395169156943529555679 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
      upper := ((16358871741487321466375253819415747604110664862518707734954393291041 : ℚ) / 14743720833598006137708523875713860524645313356076875575603536855040)
    }
  }

theorem replay46_is_accepted : replay46.check = true := by
  norm_num [replay46, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay47 : Float32ActivationReplay where
  input := {
    word := 3192516116
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3182826897
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-3308421 : ℚ) / 16777216)
    runtimeValue := ((-11933073 : ℚ) / 134217728)
    localError := ((59225275023588792280714737989428082595156300727563513837856113 : ℚ) / 66972346286066739733163284180322621667625474947384866793400926772133888)
    outputLower := ((-6337675537258831103323476037389566324471365631692244118405120 : ℚ) / 71283266248674986033551095185176081961494020596215502189263657)
    outputUpper := ((-44363728760811817723264332261726964271299559421845708828835840 : ℚ) / 498982863769432453313196332606096727159809134508556625197834721)
    expCertificate := {
      argument := ((3308421 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((3308421 : ℚ) / 16777216)
        terms := 8
        lower := ((39144505363495180522711853338352829911049960720559645483236137 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((274011537573173814737321639678333962806700715378965628255642081 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((39144505363495180522711853338352829911049960720559645483236137 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((274011537573173814737321639678333962806700715378965628255642081 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
    }
  }

theorem replay47_is_accepted : replay47.check = true := by
  norm_num [replay47, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay48 : Float32ActivationReplay where
  input := {
    word := 1021865473
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1013692945
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((15232513 : ℚ) / 536870912)
    runtimeValue := ((15448593 : ℚ) / 1073741824)
    localError := ((143313322864327674336360171130385205473401198421881897374328670704550987871 : ℚ) / 673416824115983955623561452159938336559750277611105241298186263290667532420506451968)
    outputLower := ((9023461041943625836609481791645517332574191985578713061798527776399032320 : ℚ) / 627168290425077039397844534516277105137473230819315874295482657189171325807)
    outputUpper := ((63164227293605380856266372541518621328019343899050991432589694434793226240 : ℚ) / 4390178032975539223612013276220031038503597549758728941920239795813296967671)
    expCertificate := {
      argument := ((-15232513 : ℚ) / 536870912)
      halvings := 0
      reduced := {
        argument := ((-15232513 : ℚ) / 536870912)
        terms := 8
        lower := ((2163950731354774968337058425283953708560967839695449054687015982184596049911 : ℚ) / 2226227301620764255274954850936077329942629710063279887233223813628700917760)
        upper := ((309135818764967860072850984382551772288526129381704461833593540956499766127 : ℚ) / 318032471660109179324993550133725332848947101437611412461889116232671559680)
      }
      lower := ((2163950731354774968337058425283953708560967839695449054687015982184596049911 : ℚ) / 2226227301620764255274954850936077329942629710063279887233223813628700917760)
      upper := ((309135818764967860072850984382551772288526129381704461833593540956499766127 : ℚ) / 318032471660109179324993550133725332848947101437611412461889116232671559680)
    }
  }

theorem replay48_is_accepted : replay48.check = true := by
  norm_num [replay48, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay49 : Float32ActivationReplay where
  input := {
    word := 3190561920
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3181227624
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-88121 : ℚ) / 524288)
    runtimeValue := ((-1291725 : ℚ) / 16777216)
    localError := ((317921847942034200539768688545623965473536742306805 : ℚ) / 67444898296947911589606227181177816018550883992508158705664)
    outputLower := ((-309513324903255434092204872209887286622288787537920 : ℚ) / 4020029204836478673242140816163876942967975764767031)
    outputUpper := ((-309513324903255434092204872209887286622288787537920 : ℚ) / 4020029204901928400373830031226743222388677835017929)
    expCertificate := {
      argument := ((88121 : ℚ) / 524288)
      halvings := 0
      reduced := {
        argument := ((88121 : ℚ) / 524288)
        terms := 8
        lower := ((2178537141799540996305497926941360338201500760617271 : ℚ) / 1841492063036937676936642889222516604766475004149760)
        upper := ((2178537141864990723437187142004226617622202830868169 : ℚ) / 1841492063036937676936642889222516604766475004149760)
      }
      lower := ((2178537141799540996305497926941360338201500760617271 : ℚ) / 1841492063036937676936642889222516604766475004149760)
      upper := ((2178537141864990723437187142004226617622202830868169 : ℚ) / 1841492063036937676936642889222516604766475004149760)
    }
  }

theorem replay49_is_accepted : replay49.check = true := by
  norm_num [replay49, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay50 : Float32ActivationReplay where
  input := {
    word := 1065915192
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1061894909
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1118823 : ℚ) / 1048576)
    runtimeValue := ((13318909 : ℚ) / 16777216)
    localError := ((1038880583819409382185115047833684243045995346207315549558912196972734176290173276972503043625074427037345176451 : ℚ) / 4054590678136261465929409191411812049961620115044189856006170542490597393269493604232510765840470211215964393518923776)
    outputLower := ((191856279144066054020557739045232809525724680042930550832320491858551583002782280094218133567306789244685516800 : ℚ) / 241672514323734733565975685263498190306724486630093225093569444029120515628197790531695746450956060121401100161)
    outputUpper := ((191856279144066054020557739045232809525724680042930550832320491858551583002782280094218133567306789244685516800 : ℚ) / 241672437079922048206890177214849713442422158422719827652345332055723511771529531731159136643437755776403212161)
    expCertificate := {
      argument := ((-1118823 : ℚ) / 1048576)
      halvings := 1
      reduced := {
        argument := ((-1118823 : ℚ) / 2097152)
        terms := 8
        lower := ((7865249238663733642521938137909435777078447091364217919 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
        upper := ((7865254149111338605307344581954638977118770751196806081 : ℚ) / 13409335982576527510635536487565205356663967319106519040)
      }
      lower := ((61862145586300441696601819023166097283971463271926587551318367047788758286192322778469682079603901950520690561 : ℚ) / 179810291493621606510288358191683616158450695150793240101026965007934753485337208952689454563833853825882521600)
      upper := ((61862222830113127055687327071814574148273791479299984992542479021185762142860581579006291887122206295518578561 : ℚ) / 179810291493621606510288358191683616158450695150793240101026965007934753485337208952689454563833853825882521600)
    }
  }

theorem replay50_is_accepted : replay50.check = true := by
  norm_num [replay50, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay51 : Float32ActivationReplay where
  input := {
    word := 1002499856
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 994148471
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((790257 : ℚ) / 134217728)
    runtimeValue := ((12681335 : ℚ) / 4294967296)
    localError := ((2696549081067518533739452016480809882963023271965838434427704215605495 : ℚ) / 32326617743871890457433735686915364244974808388738818569817061541067988259569664)
    outputLower := ((22223145665734595368131875901126877358674299997011649058818291138560 : ℚ) / 7526627216458295112809874645645820583565386751018775016871922686399361)
    outputUpper := ((22223145665734595368131875901126877358674299997011649058818291138560 : ℚ) / 7526627216458295112809570433319398259039690808565080764195197620677759)
    expCertificate := {
      argument := ((-790257 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-790257 : ℚ) / 134217728)
        terms := 8
        lower := ((3752234683057205541556188321136649964730490589409400616840692185787519 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
        upper := ((3752234683057205541556492533463072289256186531863094869517417251509121 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
      }
      lower := ((3752234683057205541556188321136649964730490589409400616840692185787519 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
      upper := ((3752234683057205541556492533463072289256186531863094869517417251509121 : ℚ) / 3774392533401089571253382112182748294309200219155680147354505434890240)
    }
  }

theorem replay51_is_accepted : replay51.check = true := by
  norm_num [replay51, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay52 : Float32ActivationReplay where
  input := {
    word := 3199029592
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3188736635
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-1419819 : ℚ) / 4194304)
    runtimeValue := ((-9454203 : ℚ) / 67108864)
    localError := ((5127057017867129391794791222185459606963333989286109362843 : ℚ) / 553547813442190709975027851719884203461947506287107932539685175296)
    outputLower := ((-1162037964199574140235781053481344134783525232851959152640 : ℚ) / 8248505196603994220123109992144766501515321527229367681439)
    outputUpper := ((-1162037964199574140235781053481344134783525232851959152640 : ℚ) / 8248505229632875538008715928601286274840521541713676762721)
    expCertificate := {
      argument := ((1419819 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((1419819 : ℚ) / 4194304)
        terms := 8
        lower := ((4815715185064403177400412651328073930209345893538098807199 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((4815715218093284495286018587784593703534545908022407888481 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      }
      lower := ((4815715185064403177400412651328073930209345893538098807199 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      upper := ((4815715218093284495286018587784593703534545908022407888481 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
    }
  }

theorem replay52_is_accepted : replay52.check = true := by
  norm_num [replay52, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay53 : Float32ActivationReplay where
  input := {
    word := 3207369329
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3194553997
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-11309681 : ℚ) / 16777216)
    runtimeValue := ((-15271565 : ℚ) / 67108864)
    localError := ((23250206010824543986138075755968082065460372056817396335202881575 : ℚ) / 134169802815847551744151357213020245326100401673454827731308096130121728)
    outputLower := ((-454965937154286252699036074814668817850082083720559806088478720 : ℚ) / 1999285859105699535372128445104066212864226127765399630834282877)
    outputUpper := ((-454965937154286252699036074814668817850082083720559806088478720 : ℚ) / 1999287465137327725830032352875744597723535319349598250381102723)
    expCertificate := {
      argument := ((11309681 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((11309681 : ℚ) / 16777216)
        terms := 8
        lower := ((1324371880516923619644504366320777919804900870376626640007704957 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
        upper := ((1324373486548551810102408274092456304664210061960825259554524803 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      }
      lower := ((1324371880516923619644504366320777919804900870376626640007704957 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
      upper := ((1324373486548551810102408274092456304664210061960825259554524803 : ℚ) / 674913978588775915727624078783288293059325257388772990826577920)
    }
  }

theorem replay53_is_accepted : replay53.check = true := by
  norm_num [replay53, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay54 : Float32ActivationReplay where
  input := {
    word := 3201472466
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3190284845
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-6900713 : ℚ) / 16777216)
    runtimeValue := ((-11002413 : ℚ) / 67108864)
    localError := ((73518166342414479183087967480192595379024261034656830806197101 : ℚ) / 37876782019655320600914813768288165709553418931724777350417855197216768)
    outputLower := ((-18506795827266723377500056980343110190480135182106700864815104 : ℚ) / 112881604818929831259770965284891006526147401183598114043668979)
    outputUpper := ((-92533979136333616887500284901715550952400675910533504324075520 : ℚ) / 564408034379114517583173718575956906520626231010627409076956737)
    expCertificate := {
      argument := ((6900713 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((6900713 : ℚ) / 16777216)
        terms := 8
        lower := ((67887339579678103544596026699338453655525717357679914655230451 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((339436708182855879007299025648194142167517811881036412134764097 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((67887339579678103544596026699338453655525717357679914655230451 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((339436708182855879007299025648194142167517811881036412134764097 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
    }
  }

theorem replay54_is_accepted : replay54.check = true := by
  norm_num [replay54, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay55 : Float32ActivationReplay where
  input := {
    word := 1058688988
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1053259285
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((2528247 : ℚ) / 4194304)
    runtimeValue := ((13071893 : ℚ) / 33554432)
    localError := ((38702105152727071542299992154145613427991003448385821245013 : ℚ) / 178224699304966620744796566377946251457482466730263088680767848448)
    outputLower := ((295602970406155464819176925380835551647684198718515445760 : ℚ) / 758787612128972972698520533234999250736271445423727586423)
    outputUpper := ((2069220792843088253734238477665848861533789391029608120320 : ℚ) / 5311509946136671922945873927412815435453726849861833115839)
    expCertificate := {
      argument := ((-2528247 : ℚ) / 4194304)
      halvings := 0
      reduced := {
        argument := ((-2528247 : ℚ) / 4194304)
        terms := 8
        lower := ((1878719934597080880223176586596122864147751216170564241599 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
        upper := ((268389039051888538023849484546900311978274926324974890103 : ℚ) / 490398573077084434674671048688098938757996519098752696320)
      }
      lower := ((1878719934597080880223176586596122864147751216170564241599 : ℚ) / 3432790011539591042722697340816692571305975633691268874240)
      upper := ((268389039051888538023849484546900311978274926324974890103 : ℚ) / 490398573077084434674671048688098938757996519098752696320)
    }
  }

theorem replay55_is_accepted : replay55.check = true := by
  norm_num [replay55, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay56 : Float32ActivationReplay where
  input := {
    word := 3196269862
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3185899873
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4299411 : ℚ) / 16777216)
    runtimeValue := ((-15006049 : ℚ) / 134217728)
    localError := ((132873799486992802917747595055711011005285249202415688939289729 : ℚ) / 69210127430948695449961035696501096028391946635157863598550897790025728)
    outputLower := ((-8236035232312190103004148937934172446814283485058154018897920 : ℚ) / 73665090330591996568357412736249789071276788019981594816399977)
    outputUpper := ((-57652246626185330721029042565539207127699984395407078132285440 : ℚ) / 515655632547651942446537581805147946092426379286928948749236001)
    expCertificate := {
      argument := ((4299411 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((4299411 : ℚ) / 16777216)
        terms := 8
        lower := ((41526329445412191057518170889426537020832728144325738110372457 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
        upper := ((290684306351393303870662888877385181739317960157337951807043361 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      }
      lower := ((41526329445412191057518170889426537020832728144325738110372457 : ℚ) / 32138760885179805510839241846823252050444059875655856706027520)
      upper := ((290684306351393303870662888877385181739317960157337951807043361 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
    }
  }

theorem replay56_is_accepted : replay56.check = true := by
  norm_num [replay56, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay57 : Float32ActivationReplay where
  input := {
    word := 3196179071
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3185764081
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-8508031 : ℚ) / 33554432)
    runtimeValue := ((-14870257 : ℚ) / 134217728)
    localError := ((2677069038080286138027090622048992999533102251463909952071567323 : ℚ) / 505451549383889398328688540714604403948402958877660260799291895329062912)
    outputLower := ((-417232626209559975982957619704085510202013588238428000162414592 : ℚ) / 3765907506524692463343505119641158014151476017219277179235904629)
    outputUpper := ((-2086163131047799879914788098520427551010067941192140000812072960 : ℚ) / 18829537540467947819596858239836873277038416542090681820777849271)
    expCertificate := {
      argument := ((8508031 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((8508031 : ℚ) / 33554432)
        terms := 8
        lower := ((2120402949203486421188535937083807509168740151585697315887295605 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
        upper := ((10602014753861917608822012327050120752124737213922782504034804151 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
      }
      lower := ((2120402949203486421188535937083807509168740151585697315887295605 : ℚ) / 1645504557321206042154969182557350504982735865633579863348609024)
      upper := ((10602014753861917608822012327050120752124737213922782504034804151 : ℚ) / 8227522786606030210774845912786752524913679328167899316743045120)
    }
  }

theorem replay57_is_accepted : replay57.check = true := by
  norm_num [replay57, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay58 : Float32ActivationReplay where
  input := {
    word := 3205515658
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3193001581
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4728005 : ℚ) / 8388608)
    runtimeValue := ((-13719149 : ℚ) / 67108864)
    localError := ((2014293136885603890024858100295551273273838781059499915737287 : ℚ) / 41810195130337373241689829263470368907100858690932011251068523511808)
    outputLower := ((-127364881283641878253638689111164410439956738223470972764160 : ℚ) / 623020457183381516362575132600521578000498692556202579305597)
    outputUpper := ((-891554168985493147775470823778150873079697167564296809349120 : ℚ) / 4361144099213760863822541788746932226384430877188856056545429)
    expCertificate := {
      argument := ((4728005 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((4728005 : ℚ) / 8388608)
        terms := 8
        lower := ((397044794709461008864486713365045587020813896555497336841341 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
        upper := ((2779314461896317311335922854098600289526637305183919359295637 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
      }
      lower := ((397044794709461008864486713365045587020813896555497336841341 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      upper := ((2779314461896317311335922854098600289526637305183919359295637 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
    }
  }

theorem replay58_is_accepted : replay58.check = true := by
  norm_num [replay58, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay59 : Float32ActivationReplay where
  input := {
    word := 1043942554
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1036649703
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6071885 : ℚ) / 33554432)
    runtimeValue := ((13239527 : ℚ) / 134217728)
    localError := ((16163266344743789930803652626479020684975810184222754752482331409 : ℚ) / 8508231889612300014000388156154664452419063433303886694628109021624664064)
    outputLower := ((893293121966445846790384506139061287428179308310379004648488960 : ℚ) / 9055895347584425718712518356218283887628372677169088357224918209)
    outputUpper := ((6253051853765120927532691542973429011997255158172653032539422720 : ℚ) / 63391267430873960360887558431585613283657010147749533464223958713)
    expCertificate := {
      argument := ((-6071885 : ℚ) / 33554432)
      halvings := 0
      reduced := {
        argument := ((-6071885 : ℚ) / 33554432)
        terms := 8
        lower := ((28835671727128633475633205597881252679019556969444356333903169209 : ℚ) / 34555595703745326885254352833704360604637453178305177130320789504)
        upper := ((4119381675620807592247610808546232372680165080268348767179091137 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
      }
      lower := ((28835671727128633475633205597881252679019556969444356333903169209 : ℚ) / 34555595703745326885254352833704360604637453178305177130320789504)
      upper := ((4119381675620807592247610808546232372680165080268348767179091137 : ℚ) / 4936513671963618126464907547672051514948207596900739590045827072)
    }
  }

theorem replay59_is_accepted : replay59.check = true := by
  norm_num [replay59, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay60 : Float32ActivationReplay where
  input := {
    word := 3213106010
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3196767920
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-4328877 : ℚ) / 4194304)
    runtimeValue := ((-568555 : ℚ) / 2097152)
    localError := ((8752506409286498807007013633684982034759944452689757831622237952448739395834502696000279765035229969344611989078553445 : ℚ) / 125829042256042605129019551248167352507240601715792123796467886961309867128005245387735033410377843436373001569662484518797312)
    outputLower := ((-16266483152144388579274449755820215844887940072432961595116424990357495052817681367865291086449379822199637732963123200 : ℚ) / 59999962928792288364896560310443569425220776422401487253412192803053792537691710180156246857823297231852055344420664081)
    outputUpper := ((-650659326085775543170977990232808633795517602897318463804656999614299802112707254714611643457975192887985509318524928 : ℚ) / 2399999109977886542357584516447288101882833269362096374125021170917716535134093400124257348269507476123868840271268281)
    expCertificate := {
      argument := ((4328877 : ℚ) / 4194304)
      halvings := 1
      reduced := {
        argument := ((4328877 : ℚ) / 8388608)
        terms := 8
        lower := ((210331073430043846861959464369189237325296570555319511983209 : ℚ) / 125542034707733615276715788464153328322047108889280690257920)
        upper := ((42066221732354034590113144397120320143053798087832271891435 : ℚ) / 25108406941546723055343157692830665664409421777856138051584)
      }
      lower := ((44239160450234496679984944270386123903188880714215308586232875441355503829092825935590540355869330975529404148297937681 : ℚ) / 15760802478557791684911616040057445522031895708186178667179317361698288708598884244565706501953966256322651196122726400)
      upper := ((1769567010835574874961119874844990281001557441034649227437848476449784986790138030341629088191348825870962792426359225 : ℚ) / 630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056)
    }
  }

theorem replay60_is_accepted : replay60.check = true := by
  norm_num [replay60, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay61 : Float32ActivationReplay where
  input := {
    word := 1062537090
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1058304206
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((6980545 : ℚ) / 8388608)
    runtimeValue := ((4864103 : ℚ) / 8388608)
    localError := ((12721263613113608120643868412253700887442033260969974921823829 : ℚ) / 2720411702861777065372574938464135308153164960460566004863311282176)
    outputLower := ((1316312905028831243883693858523933918496726349603080849326080 : ℚ) / 2270108720999386951007494084696708277131973381200081346898229)
    outputUpper := ((188044700718404463411956265503419131213818049943297264189440 : ℚ) / 324298346383783467456409327800766862410684223229952574355997)
    expCertificate := {
      argument := ((-6980545 : ℚ) / 8388608)
      halvings := 0
      reduced := {
        argument := ((-6980545 : ℚ) / 8388608)
        terms := 8
        lower := ((98322683909862959958320908565290871430999427229247331891741 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
        upper := ((688279083681943398520875150048376340274179809195144649648437 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
      }
      lower := ((98322683909862959958320908565290871430999427229247331891741 : ℚ) / 225975662473920507498088419235475990979684796000705242464256)
      upper := ((688279083681943398520875150048376340274179809195144649648437 : ℚ) / 1581829637317443552486618934648331936857793572004936697249792)
    }
  }

theorem replay61_is_accepted : replay61.check = true := by
  norm_num [replay61, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay62 : Float32ActivationReplay where
  input := {
    word := 1023947266
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1015707038
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((4462849 : ℚ) / 134217728)
    runtimeValue := ((4537039 : ℚ) / 268435456)
    localError := ((9990623013427208653835146992637769291145402111430684783614648177035591 : ℚ) / 17939037707939594797098788974968539742234945058690524120372348017433850658422784)
    outputLower := ((1129514690411602502523416772140219765771818749604585557501525916385280 : ℚ) / 66828123137129823852698463853331430786233190665731296391682133143521289)
    outputUpper := ((1129514690411602502523416772140219765771818749604585557501525916385280 : ℚ) / 66828123137129821020197623572281461472848650304087234277100754447431671)
    expCertificate := {
      argument := ((-4462849 : ℚ) / 134217728)
      halvings := 0
      reduced := {
        argument := ((-4462849 : ℚ) / 134217728)
        terms := 8
        lower := ((32858590336520014878917184562636726824065848331686112950910205533419511 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
        upper := ((32858590336520017711418024843686696137450388693330175065491584229509129 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      }
      lower := ((32858590336520014878917184562636726824065848331686112950910205533419511 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
      upper := ((32858590336520017711418024843686696137450388693330175065491584229509129 : ℚ) / 33969532800609806141280439009644734648782801972401121326190548914012160)
    }
  }

theorem replay62_is_accepted : replay62.check = true := by
  norm_num [replay62, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay63 : Float32ActivationReplay where
  input := {
    word := 1057590361
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1051566826
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9014361 : ℚ) / 16777216)
    runtimeValue := ((5689717 : ℚ) / 16777216)
    localError := ((362938020148360405278156796756271754700860335848307919885712949 : ℚ) / 5979863455896386506959598101448829537385917978240249152845651292192768)
    outputLower := ((24175319063446905821460013065516954424820551421325672015986688 : ℚ) / 71285544858530957781385437027695029719622820434471072483709837)
    outputUpper := ((120876595317234529107300065327584772124102757106628360079933440 : ℚ) / 356427637094043881115889436092902990423793672218337604573109823)
    expCertificate := {
      argument := ((-9014361 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-9014361 : ℚ) / 16777216)
        terms := 8
        lower := ((131456310897785242540014743165140226070685253088746607630917183 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
        upper := ((26291279619279230066210498442142476849001136608552873095271309 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((131456310897785242540014743165140226070685253088746607630917183 : ℚ) / 224971326196258638575874692927762764353108419129590996942192640)
      upper := ((26291279619279230066210498442142476849001136608552873095271309 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
    }
  }

theorem replay63_is_accepted : replay63.check = true := by
  norm_num [replay63, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def certificateBatch : Float32ActivationReplayBatch where
  expectedCount := 64
  entries := [replay0, replay1, replay2, replay3, replay4, replay5, replay6, replay7, replay8, replay9, replay10, replay11, replay12, replay13, replay14, replay15, replay16, replay17, replay18, replay19, replay20, replay21, replay22, replay23, replay24, replay25, replay26, replay27, replay28, replay29, replay30, replay31, replay32, replay33, replay34, replay35, replay36, replay37, replay38, replay39, replay40, replay41, replay42, replay43, replay44, replay45, replay46, replay47, replay48, replay49, replay50, replay51, replay52, replay53, replay54, replay55, replay56, replay57, replay58, replay59, replay60, replay61, replay62, replay63]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32ActivationReplayBatch.check,
    replay0_is_accepted, replay1_is_accepted, replay2_is_accepted, replay3_is_accepted, replay4_is_accepted, replay5_is_accepted, replay6_is_accepted, replay7_is_accepted, replay8_is_accepted, replay9_is_accepted, replay10_is_accepted, replay11_is_accepted, replay12_is_accepted, replay13_is_accepted, replay14_is_accepted, replay15_is_accepted, replay16_is_accepted, replay17_is_accepted, replay18_is_accepted, replay19_is_accepted, replay20_is_accepted, replay21_is_accepted, replay22_is_accepted, replay23_is_accepted, replay24_is_accepted, replay25_is_accepted, replay26_is_accepted, replay27_is_accepted, replay28_is_accepted, replay29_is_accepted, replay30_is_accepted, replay31_is_accepted, replay32_is_accepted, replay33_is_accepted, replay34_is_accepted, replay35_is_accepted, replay36_is_accepted, replay37_is_accepted, replay38_is_accepted, replay39_is_accepted, replay40_is_accepted, replay41_is_accepted, replay42_is_accepted, replay43_is_accepted, replay44_is_accepted, replay45_is_accepted, replay46_is_accepted, replay47_is_accepted, replay48_is_accepted, replay49_is_accepted, replay50_is_accepted, replay51_is_accepted, replay52_is_accepted, replay53_is_accepted, replay54_is_accepted, replay55_is_accepted, replay56_is_accepted, replay57_is_accepted, replay58_is_accepted, replay59_is_accepted, replay60_is_accepted, replay61_is_accepted, replay62_is_accepted, replay63_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalAbsoluteError ≤ certificateBatch.totalCertifiedError :=
  certificateBatch.totalAbsoluteError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end

end GeneratedAuthenticatedActivationReplaySite2Invocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
