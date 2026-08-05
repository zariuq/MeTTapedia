import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32HiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineSiLUReplaySite0Invocation0GeneratedFixture
import Mathlib.Tactic

/-! This file is generated from authenticated source-side replay records.
The kernel checks only the exact word arithmetic and interior connections;
the recorded SHA-256 values bind those words to external source artifacts. -/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedHiddenStageReplaySite0Invocation0Fixture

open Float32CheckpointMatrix
open Float32AffineSiLUReplayCertificate
open Float32AddMaskReplayCertificate
open Float32HiddenStageReplayCertificate

noncomputable section

-- source probe SHA-256: beb12bfe26f0d944d8a2c55afb8bbb3b1937978f40a171bdae2875ae190c117b
-- affine-SiLU batch SHA-256: 11660564ae150fe65b3a6a6ee024cd8c110b47d00227691df77e93b141392e72

def invocation0Row0Activation : FiniteFloat32Word where
  word := 1065094412
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Error : FiniteFloat32Word where
  word := 2988749820
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Sum : FiniteFloat32Word where
  word := 1065094412
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Center : FiniteFloat32Word where
  word := 1065094412
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Add : Float32AddReplay where
  left := invocation0Row0Activation
  right := invocation0Row0Error
  output := invocation0Row0Sum
  localError := ((2698495 : ℚ) / 281474976710656)

def invocation0Row0Mask : Float32MaskReplay where
  active := true
  input := invocation0Row0Sum
  output := invocation0Row0Center
  localError := (0 : ℚ)

def invocation0Row0AddMask : Float32AddMaskReplay where
  add := invocation0Row0Add
  mask := invocation0Row0Mask

theorem invocation0Row0AddMask_is_accepted : invocation0Row0AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row0AddMask, invocation0Row0Add, invocation0Row0Mask,
    boolRat, invocation0Row0Activation, invocation0Row0Error, invocation0Row0Sum, invocation0Row0Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row1Activation : FiniteFloat32Word where
  word := 1021703469
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row1Error : FiniteFloat32Word where
  word := 836714018
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row1Sum : FiniteFloat32Word where
  word := 1021703472
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row1Center : FiniteFloat32Word where
  word := 1021703472
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row1Add : Float32AddReplay where
  left := invocation0Row1Activation
  right := invocation0Row1Error
  output := invocation0Row1Sum
  localError := ((1023761 : ℚ) / 1125899906842624)

def invocation0Row1Mask : Float32MaskReplay where
  active := true
  input := invocation0Row1Sum
  output := invocation0Row1Center
  localError := (0 : ℚ)

def invocation0Row1AddMask : Float32AddMaskReplay where
  add := invocation0Row1Add
  mask := invocation0Row1Mask

theorem invocation0Row1AddMask_is_accepted : invocation0Row1AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row1AddMask, invocation0Row1Add, invocation0Row1Mask,
    boolRat, invocation0Row1Activation, invocation0Row1Error, invocation0Row1Sum, invocation0Row1Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row2Activation : FiniteFloat32Word where
  word := 3185844902
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row2Error : FiniteFloat32Word where
  word := 850125265
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row2Sum : FiniteFloat32Word where
  word := 3185844899
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row2Center : FiniteFloat32Word where
  word := 3185844899
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row2Add : Float32AddReplay where
  left := invocation0Row2Activation
  right := invocation0Row2Error
  output := invocation0Row2Sum
  localError := ((1318447 : ℚ) / 562949953421312)

def invocation0Row2Mask : Float32MaskReplay where
  active := true
  input := invocation0Row2Sum
  output := invocation0Row2Center
  localError := (0 : ℚ)

def invocation0Row2AddMask : Float32AddMaskReplay where
  add := invocation0Row2Add
  mask := invocation0Row2Mask

theorem invocation0Row2AddMask_is_accepted : invocation0Row2AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row2AddMask, invocation0Row2Add, invocation0Row2Mask,
    boolRat, invocation0Row2Activation, invocation0Row2Error, invocation0Row2Sum, invocation0Row2Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row3Activation : FiniteFloat32Word where
  word := 3176030409
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row3Error : FiniteFloat32Word where
  word := 3002034842
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row3Sum : FiniteFloat32Word where
  word := 3176030416
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row3Center : FiniteFloat32Word where
  word := 3176030416
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row3Add : Float32AddReplay where
  left := invocation0Row3Activation
  right := invocation0Row3Error
  output := invocation0Row3Sum
  localError := ((505165 : ℚ) / 281474976710656)

def invocation0Row3Mask : Float32MaskReplay where
  active := true
  input := invocation0Row3Sum
  output := invocation0Row3Center
  localError := (0 : ℚ)

def invocation0Row3AddMask : Float32AddMaskReplay where
  add := invocation0Row3Add
  mask := invocation0Row3Mask

theorem invocation0Row3AddMask_is_accepted : invocation0Row3AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row3AddMask, invocation0Row3Add, invocation0Row3Mask,
    boolRat, invocation0Row3Activation, invocation0Row3Error, invocation0Row3Sum, invocation0Row3Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row4Activation : FiniteFloat32Word where
  word := 1041636217
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row4Error : FiniteFloat32Word where
  word := 848533491
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row4Sum : FiniteFloat32Word where
  word := 1041636218
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row4Center : FiniteFloat32Word where
  word := 1041636218
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row4Add : Float32AddReplay where
  left := invocation0Row4Activation
  right := invocation0Row4Error
  output := invocation0Row4Sum
  localError := ((1284083 : ℚ) / 562949953421312)

def invocation0Row4Mask : Float32MaskReplay where
  active := true
  input := invocation0Row4Sum
  output := invocation0Row4Center
  localError := (0 : ℚ)

def invocation0Row4AddMask : Float32AddMaskReplay where
  add := invocation0Row4Add
  mask := invocation0Row4Mask

theorem invocation0Row4AddMask_is_accepted : invocation0Row4AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row4AddMask, invocation0Row4Add, invocation0Row4Mask,
    boolRat, invocation0Row4Activation, invocation0Row4Error, invocation0Row4Sum, invocation0Row4Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row5Activation : FiniteFloat32Word where
  word := 3186184765
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row5Error : FiniteFloat32Word where
  word := 850422040
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row5Sum : FiniteFloat32Word where
  word := 3186184762
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row5Center : FiniteFloat32Word where
  word := 3186184762
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row5Add : Float32AddReplay where
  left := invocation0Row5Activation
  right := invocation0Row5Error
  output := invocation0Row5Sum
  localError := ((127709 : ℚ) / 70368744177664)

def invocation0Row5Mask : Float32MaskReplay where
  active := true
  input := invocation0Row5Sum
  output := invocation0Row5Center
  localError := (0 : ℚ)

def invocation0Row5AddMask : Float32AddMaskReplay where
  add := invocation0Row5Add
  mask := invocation0Row5Mask

theorem invocation0Row5AddMask_is_accepted : invocation0Row5AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row5AddMask, invocation0Row5Add, invocation0Row5Mask,
    boolRat, invocation0Row5Activation, invocation0Row5Error, invocation0Row5Sum, invocation0Row5Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row6Activation : FiniteFloat32Word where
  word := 1016813015
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row6Error : FiniteFloat32Word where
  word := 2992187589
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row6Sum : FiniteFloat32Word where
  word := 1016813008
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row6Center : FiniteFloat32Word where
  word := 1016813008
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row6Add : Float32AddReplay where
  left := invocation0Row6Activation
  right := invocation0Row6Error
  output := invocation0Row6Sum
  localError := ((448315 : ℚ) / 1125899906842624)

def invocation0Row6Mask : Float32MaskReplay where
  active := true
  input := invocation0Row6Sum
  output := invocation0Row6Center
  localError := (0 : ℚ)

def invocation0Row6AddMask : Float32AddMaskReplay where
  add := invocation0Row6Add
  mask := invocation0Row6Mask

theorem invocation0Row6AddMask_is_accepted : invocation0Row6AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row6AddMask, invocation0Row6Add, invocation0Row6Mask,
    boolRat, invocation0Row6Activation, invocation0Row6Error, invocation0Row6Sum, invocation0Row6Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row7Activation : FiniteFloat32Word where
  word := 3180544020
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row7Error : FiniteFloat32Word where
  word := 2971389572
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row7Sum : FiniteFloat32Word where
  word := 3180544020
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row7Center : FiniteFloat32Word where
  word := 3180544020
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row7Add : Float32AddReplay where
  left := invocation0Row7Activation
  right := invocation0Row7Error
  output := invocation0Row7Sum
  localError := ((2552737 : ℚ) / 1125899906842624)

def invocation0Row7Mask : Float32MaskReplay where
  active := true
  input := invocation0Row7Sum
  output := invocation0Row7Center
  localError := (0 : ℚ)

def invocation0Row7AddMask : Float32AddMaskReplay where
  add := invocation0Row7Add
  mask := invocation0Row7Mask

theorem invocation0Row7AddMask_is_accepted : invocation0Row7AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row7AddMask, invocation0Row7Add, invocation0Row7Mask,
    boolRat, invocation0Row7Activation, invocation0Row7Error, invocation0Row7Sum, invocation0Row7Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row8Activation : FiniteFloat32Word where
  word := 3180242278
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row8Error : FiniteFloat32Word where
  word := 2991979496
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row8Sum : FiniteFloat32Word where
  word := 3180242280
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row8Center : FiniteFloat32Word where
  word := 3180242280
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row8Add : Float32AddReplay where
  left := invocation0Row8Activation
  right := invocation0Row8Error
  output := invocation0Row8Sum
  localError := ((344195 : ℚ) / 140737488355328)

def invocation0Row8Mask : Float32MaskReplay where
  active := true
  input := invocation0Row8Sum
  output := invocation0Row8Center
  localError := (0 : ℚ)

def invocation0Row8AddMask : Float32AddMaskReplay where
  add := invocation0Row8Add
  mask := invocation0Row8Mask

theorem invocation0Row8AddMask_is_accepted : invocation0Row8AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row8AddMask, invocation0Row8Add, invocation0Row8Mask,
    boolRat, invocation0Row8Activation, invocation0Row8Error, invocation0Row8Sum, invocation0Row8Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row9Activation : FiniteFloat32Word where
  word := 3185284870
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row9Error : FiniteFloat32Word where
  word := 858488656
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row9Sum : FiniteFloat32Word where
  word := 3185284865
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row9Center : FiniteFloat32Word where
  word := 3185284865
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row9Add : Float32AddReplay where
  left := invocation0Row9Activation
  right := invocation0Row9Error
  output := invocation0Row9Sum
  localError := ((47093 : ℚ) / 17592186044416)

def invocation0Row9Mask : Float32MaskReplay where
  active := true
  input := invocation0Row9Sum
  output := invocation0Row9Center
  localError := (0 : ℚ)

def invocation0Row9AddMask : Float32AddMaskReplay where
  add := invocation0Row9Add
  mask := invocation0Row9Mask

theorem invocation0Row9AddMask_is_accepted : invocation0Row9AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row9AddMask, invocation0Row9Add, invocation0Row9Mask,
    boolRat, invocation0Row9Activation, invocation0Row9Error, invocation0Row9Sum, invocation0Row9Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row10Activation : FiniteFloat32Word where
  word := 3181749974
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row10Error : FiniteFloat32Word where
  word := 852153568
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row10Sum : FiniteFloat32Word where
  word := 3181749971
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row10Center : FiniteFloat32Word where
  word := 3181749971
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row10Add : Float32AddReplay where
  left := invocation0Row10Activation
  right := invocation0Row10Error
  output := invocation0Row10Sum
  localError := ((22183 : ℚ) / 17592186044416)

def invocation0Row10Mask : Float32MaskReplay where
  active := true
  input := invocation0Row10Sum
  output := invocation0Row10Center
  localError := (0 : ℚ)

def invocation0Row10AddMask : Float32AddMaskReplay where
  add := invocation0Row10Add
  mask := invocation0Row10Mask

theorem invocation0Row10AddMask_is_accepted : invocation0Row10AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row10AddMask, invocation0Row10Add, invocation0Row10Mask,
    boolRat, invocation0Row10Activation, invocation0Row10Error, invocation0Row10Sum, invocation0Row10Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row11Activation : FiniteFloat32Word where
  word := 1024387795
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row11Error : FiniteFloat32Word where
  word := 3000980926
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row11Sum : FiniteFloat32Word where
  word := 1024387788
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row11Center : FiniteFloat32Word where
  word := 1024387788
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row11Add : Float32AddReplay where
  left := invocation0Row11Activation
  right := invocation0Row11Error
  output := invocation0Row11Sum
  localError := ((21793 : ℚ) / 281474976710656)

def invocation0Row11Mask : Float32MaskReplay where
  active := true
  input := invocation0Row11Sum
  output := invocation0Row11Center
  localError := (0 : ℚ)

def invocation0Row11AddMask : Float32AddMaskReplay where
  add := invocation0Row11Add
  mask := invocation0Row11Mask

theorem invocation0Row11AddMask_is_accepted : invocation0Row11AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row11AddMask, invocation0Row11Add, invocation0Row11Mask,
    boolRat, invocation0Row11Activation, invocation0Row11Error, invocation0Row11Sum, invocation0Row11Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row12Activation : FiniteFloat32Word where
  word := 3188478670
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row12Error : FiniteFloat32Word where
  word := 2992311745
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row12Sum : FiniteFloat32Word where
  word := 3188478671
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row12Center : FiniteFloat32Word where
  word := 3188478671
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row12Add : Float32AddReplay where
  left := invocation0Row12Activation
  right := invocation0Row12Error
  output := invocation0Row12Sum
  localError := ((2421311 : ℚ) / 1125899906842624)

def invocation0Row12Mask : Float32MaskReplay where
  active := true
  input := invocation0Row12Sum
  output := invocation0Row12Center
  localError := (0 : ℚ)

def invocation0Row12AddMask : Float32AddMaskReplay where
  add := invocation0Row12Add
  mask := invocation0Row12Mask

theorem invocation0Row12AddMask_is_accepted : invocation0Row12AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row12AddMask, invocation0Row12Add, invocation0Row12Mask,
    boolRat, invocation0Row12Activation, invocation0Row12Error, invocation0Row12Sum, invocation0Row12Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row13Activation : FiniteFloat32Word where
  word := 1046549265
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row13Error : FiniteFloat32Word where
  word := 2989242520
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row13Sum : FiniteFloat32Word where
  word := 1046549264
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row13Center : FiniteFloat32Word where
  word := 1046549264
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row13Add : Float32AddReplay where
  left := invocation0Row13Activation
  right := invocation0Row13Error
  output := invocation0Row13Sum
  localError := ((686317 : ℚ) / 140737488355328)

def invocation0Row13Mask : Float32MaskReplay where
  active := true
  input := invocation0Row13Sum
  output := invocation0Row13Center
  localError := (0 : ℚ)

def invocation0Row13AddMask : Float32AddMaskReplay where
  add := invocation0Row13Add
  mask := invocation0Row13Mask

theorem invocation0Row13AddMask_is_accepted : invocation0Row13AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row13AddMask, invocation0Row13Add, invocation0Row13Mask,
    boolRat, invocation0Row13Activation, invocation0Row13Error, invocation0Row13Sum, invocation0Row13Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row14Activation : FiniteFloat32Word where
  word := 1064459206
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row14Error : FiniteFloat32Word where
  word := 3009987008
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row14Sum : FiniteFloat32Word where
  word := 1064459205
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row14Center : FiniteFloat32Word where
  word := 1064459205
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row14Add : Float32AddReplay where
  left := invocation0Row14Activation
  right := invocation0Row14Error
  output := invocation0Row14Sum
  localError := ((23801 : ℚ) / 4398046511104)

def invocation0Row14Mask : Float32MaskReplay where
  active := true
  input := invocation0Row14Sum
  output := invocation0Row14Center
  localError := (0 : ℚ)

def invocation0Row14AddMask : Float32AddMaskReplay where
  add := invocation0Row14Add
  mask := invocation0Row14Mask

theorem invocation0Row14AddMask_is_accepted : invocation0Row14AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row14AddMask, invocation0Row14Add, invocation0Row14Mask,
    boolRat, invocation0Row14Activation, invocation0Row14Error, invocation0Row14Sum, invocation0Row14Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row15Activation : FiniteFloat32Word where
  word := 1057025057
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row15Error : FiniteFloat32Word where
  word := 3006331131
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row15Sum : FiniteFloat32Word where
  word := 1057025056
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row15Center : FiniteFloat32Word where
  word := 1057025056
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row15Add : Float32AddReplay where
  left := invocation0Row15Activation
  right := invocation0Row15Error
  output := invocation0Row15Sum
  localError := ((5179141 : ℚ) / 281474976710656)

def invocation0Row15Mask : Float32MaskReplay where
  active := true
  input := invocation0Row15Sum
  output := invocation0Row15Center
  localError := (0 : ℚ)

def invocation0Row15AddMask : Float32AddMaskReplay where
  add := invocation0Row15Add
  mask := invocation0Row15Mask

theorem invocation0Row15AddMask_is_accepted : invocation0Row15AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row15AddMask, invocation0Row15Add, invocation0Row15Mask,
    boolRat, invocation0Row15Activation, invocation0Row15Error, invocation0Row15Sum, invocation0Row15Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row16Activation : FiniteFloat32Word where
  word := 1067387212
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row16Error : FiniteFloat32Word where
  word := 3004496435
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row16Sum : FiniteFloat32Word where
  word := 1067387212
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row16Center : FiniteFloat32Word where
  word := 1067387212
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row16Add : Float32AddReplay where
  left := invocation0Row16Activation
  right := invocation0Row16Error
  output := invocation0Row16Sum
  localError := ((9763379 : ℚ) / 281474976710656)

def invocation0Row16Mask : Float32MaskReplay where
  active := true
  input := invocation0Row16Sum
  output := invocation0Row16Center
  localError := (0 : ℚ)

def invocation0Row16AddMask : Float32AddMaskReplay where
  add := invocation0Row16Add
  mask := invocation0Row16Mask

theorem invocation0Row16AddMask_is_accepted : invocation0Row16AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row16AddMask, invocation0Row16Add, invocation0Row16Mask,
    boolRat, invocation0Row16Activation, invocation0Row16Error, invocation0Row16Sum, invocation0Row16Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row17Activation : FiniteFloat32Word where
  word := 1063967663
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row17Error : FiniteFloat32Word where
  word := 815187258
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row17Sum : FiniteFloat32Word where
  word := 1063967663
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row17Center : FiniteFloat32Word where
  word := 1063967663
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row17Add : Float32AddReplay where
  left := invocation0Row17Activation
  right := invocation0Row17Error
  output := invocation0Row17Sum
  localError := ((4940445 : ℚ) / 4503599627370496)

def invocation0Row17Mask : Float32MaskReplay where
  active := true
  input := invocation0Row17Sum
  output := invocation0Row17Center
  localError := (0 : ℚ)

def invocation0Row17AddMask : Float32AddMaskReplay where
  add := invocation0Row17Add
  mask := invocation0Row17Mask

theorem invocation0Row17AddMask_is_accepted : invocation0Row17AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row17AddMask, invocation0Row17Add, invocation0Row17Mask,
    boolRat, invocation0Row17Activation, invocation0Row17Error, invocation0Row17Sum, invocation0Row17Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row18Activation : FiniteFloat32Word where
  word := 1059933159
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row18Error : FiniteFloat32Word where
  word := 855761094
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row18Sum : FiniteFloat32Word where
  word := 1059933160
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row18Center : FiniteFloat32Word where
  word := 1059933160
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row18Add : Float32AddReplay where
  left := invocation0Row18Activation
  right := invocation0Row18Error
  output := invocation0Row18Sum
  localError := ((4132765 : ℚ) / 140737488355328)

def invocation0Row18Mask : Float32MaskReplay where
  active := true
  input := invocation0Row18Sum
  output := invocation0Row18Center
  localError := (0 : ℚ)

def invocation0Row18AddMask : Float32AddMaskReplay where
  add := invocation0Row18Add
  mask := invocation0Row18Mask

theorem invocation0Row18AddMask_is_accepted : invocation0Row18AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row18AddMask, invocation0Row18Add, invocation0Row18Mask,
    boolRat, invocation0Row18Activation, invocation0Row18Error, invocation0Row18Sum, invocation0Row18Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row19Activation : FiniteFloat32Word where
  word := 3176043014
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row19Error : FiniteFloat32Word where
  word := 3002782028
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row19Sum : FiniteFloat32Word where
  word := 3176043022
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row19Center : FiniteFloat32Word where
  word := 3176043022
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row19Add : Float32AddReplay where
  left := invocation0Row19Activation
  right := invocation0Row19Error
  output := invocation0Row19Sum
  localError := ((84909 : ℚ) / 140737488355328)

def invocation0Row19Mask : Float32MaskReplay where
  active := true
  input := invocation0Row19Sum
  output := invocation0Row19Center
  localError := (0 : ℚ)

def invocation0Row19AddMask : Float32AddMaskReplay where
  add := invocation0Row19Add
  mask := invocation0Row19Mask

theorem invocation0Row19AddMask_is_accepted : invocation0Row19AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row19AddMask, invocation0Row19Add, invocation0Row19Mask,
    boolRat, invocation0Row19Activation, invocation0Row19Error, invocation0Row19Sum, invocation0Row19Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row20Activation : FiniteFloat32Word where
  word := 3172196239
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row20Error : FiniteFloat32Word where
  word := 3005553048
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row20Sum : FiniteFloat32Word where
  word := 3172196249
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row20Center : FiniteFloat32Word where
  word := 3172196249
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row20Add : Float32AddReplay where
  left := invocation0Row20Activation
  right := invocation0Row20Error
  output := invocation0Row20Sum
  localError := ((41779 : ℚ) / 35184372088832)

def invocation0Row20Mask : Float32MaskReplay where
  active := true
  input := invocation0Row20Sum
  output := invocation0Row20Center
  localError := (0 : ℚ)

def invocation0Row20AddMask : Float32AddMaskReplay where
  add := invocation0Row20Add
  mask := invocation0Row20Mask

theorem invocation0Row20AddMask_is_accepted : invocation0Row20AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row20AddMask, invocation0Row20Add, invocation0Row20Mask,
    boolRat, invocation0Row20Activation, invocation0Row20Error, invocation0Row20Sum, invocation0Row20Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row21Activation : FiniteFloat32Word where
  word := 1028080081
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row21Error : FiniteFloat32Word where
  word := 855112540
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row21Sum : FiniteFloat32Word where
  word := 1028080089
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row21Center : FiniteFloat32Word where
  word := 1028080089
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row21Add : Float32AddReplay where
  left := invocation0Row21Activation
  right := invocation0Row21Error
  output := invocation0Row21Sum
  localError := ((131369 : ℚ) / 140737488355328)

def invocation0Row21Mask : Float32MaskReplay where
  active := true
  input := invocation0Row21Sum
  output := invocation0Row21Center
  localError := (0 : ℚ)

def invocation0Row21AddMask : Float32AddMaskReplay where
  add := invocation0Row21Add
  mask := invocation0Row21Mask

theorem invocation0Row21AddMask_is_accepted : invocation0Row21AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row21AddMask, invocation0Row21Add, invocation0Row21Mask,
    boolRat, invocation0Row21Activation, invocation0Row21Error, invocation0Row21Sum, invocation0Row21Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row22Activation : FiniteFloat32Word where
  word := 3188977551
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row22Error : FiniteFloat32Word where
  word := 3006227510
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row22Sum : FiniteFloat32Word where
  word := 3188977554
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row22Center : FiniteFloat32Word where
  word := 3188977554
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row22Add : Float32AddReplay where
  left := invocation0Row22Activation
  right := invocation0Row22Error
  output := invocation0Row22Sum
  localError := ((544229 : ℚ) / 140737488355328)

def invocation0Row22Mask : Float32MaskReplay where
  active := true
  input := invocation0Row22Sum
  output := invocation0Row22Center
  localError := (0 : ℚ)

def invocation0Row22AddMask : Float32AddMaskReplay where
  add := invocation0Row22Add
  mask := invocation0Row22Mask

theorem invocation0Row22AddMask_is_accepted : invocation0Row22AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row22AddMask, invocation0Row22Add, invocation0Row22Mask,
    boolRat, invocation0Row22Activation, invocation0Row22Error, invocation0Row22Sum, invocation0Row22Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row23Activation : FiniteFloat32Word where
  word := 1067483009
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row23Error : FiniteFloat32Word where
  word := 3003881797
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row23Sum : FiniteFloat32Word where
  word := 1067483009
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row23Center : FiniteFloat32Word where
  word := 1067483009
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row23Add : Float32AddReplay where
  left := invocation0Row23Activation
  right := invocation0Row23Error
  output := invocation0Row23Sum
  localError := ((9148741 : ℚ) / 281474976710656)

def invocation0Row23Mask : Float32MaskReplay where
  active := true
  input := invocation0Row23Sum
  output := invocation0Row23Center
  localError := (0 : ℚ)

def invocation0Row23AddMask : Float32AddMaskReplay where
  add := invocation0Row23Add
  mask := invocation0Row23Mask

theorem invocation0Row23AddMask_is_accepted : invocation0Row23AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row23AddMask, invocation0Row23Add, invocation0Row23Mask,
    boolRat, invocation0Row23Activation, invocation0Row23Error, invocation0Row23Sum, invocation0Row23Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row24Activation : FiniteFloat32Word where
  word := 3189296718
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row24Error : FiniteFloat32Word where
  word := 856220996
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row24Sum : FiniteFloat32Word where
  word := 3189296716
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row24Center : FiniteFloat32Word where
  word := 3189296716
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row24Add : Float32AddReplay where
  left := invocation0Row24Activation
  right := invocation0Row24Error
  output := invocation0Row24Sum
  localError := ((145745 : ℚ) / 70368744177664)

def invocation0Row24Mask : Float32MaskReplay where
  active := true
  input := invocation0Row24Sum
  output := invocation0Row24Center
  localError := (0 : ℚ)

def invocation0Row24AddMask : Float32AddMaskReplay where
  add := invocation0Row24Add
  mask := invocation0Row24Mask

theorem invocation0Row24AddMask_is_accepted : invocation0Row24AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row24AddMask, invocation0Row24Add, invocation0Row24Mask,
    boolRat, invocation0Row24Activation, invocation0Row24Error, invocation0Row24Sum, invocation0Row24Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row25Activation : FiniteFloat32Word where
  word := 1073266839
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row25Error : FiniteFloat32Word where
  word := 3008788182
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row25Sum : FiniteFloat32Word where
  word := 1073266839
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row25Center : FiniteFloat32Word where
  word := 1073266839
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row25Add : Float32AddReplay where
  left := invocation0Row25Activation
  right := invocation0Row25Error
  output := invocation0Row25Sum
  localError := ((7027563 : ℚ) / 140737488355328)

def invocation0Row25Mask : Float32MaskReplay where
  active := true
  input := invocation0Row25Sum
  output := invocation0Row25Center
  localError := (0 : ℚ)

def invocation0Row25AddMask : Float32AddMaskReplay where
  add := invocation0Row25Add
  mask := invocation0Row25Mask

theorem invocation0Row25AddMask_is_accepted : invocation0Row25AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row25AddMask, invocation0Row25Add, invocation0Row25Mask,
    boolRat, invocation0Row25Activation, invocation0Row25Error, invocation0Row25Sum, invocation0Row25Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row26Activation : FiniteFloat32Word where
  word := 3180008433
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row26Error : FiniteFloat32Word where
  word := 2993019320
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row26Sum : FiniteFloat32Word where
  word := 3180008435
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row26Center : FiniteFloat32Word where
  word := 3180008435
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row26Add : Float32AddReplay where
  left := invocation0Row26Activation
  right := invocation0Row26Error
  output := invocation0Row26Sum
  localError := ((214217 : ℚ) / 140737488355328)

def invocation0Row26Mask : Float32MaskReplay where
  active := true
  input := invocation0Row26Sum
  output := invocation0Row26Center
  localError := (0 : ℚ)

def invocation0Row26AddMask : Float32AddMaskReplay where
  add := invocation0Row26Add
  mask := invocation0Row26Mask

theorem invocation0Row26AddMask_is_accepted : invocation0Row26AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row26AddMask, invocation0Row26Add, invocation0Row26Mask,
    boolRat, invocation0Row26Activation, invocation0Row26Error, invocation0Row26Sum, invocation0Row26Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row27Activation : FiniteFloat32Word where
  word := 3156336022
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row27Error : FiniteFloat32Word where
  word := 3008958886
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row27Sum : FiniteFloat32Word where
  word := 3156336076
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row27Center : FiniteFloat32Word where
  word := 3156336076
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row27Add : Float32AddReplay where
  left := invocation0Row27Activation
  right := invocation0Row27Error
  output := invocation0Row27Sum
  localError := ((35027 : ℚ) / 140737488355328)

def invocation0Row27Mask : Float32MaskReplay where
  active := true
  input := invocation0Row27Sum
  output := invocation0Row27Center
  localError := (0 : ℚ)

def invocation0Row27AddMask : Float32AddMaskReplay where
  add := invocation0Row27Add
  mask := invocation0Row27Mask

theorem invocation0Row27AddMask_is_accepted : invocation0Row27AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row27AddMask, invocation0Row27Add, invocation0Row27Mask,
    boolRat, invocation0Row27Activation, invocation0Row27Error, invocation0Row27Sum, invocation0Row27Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row28Activation : FiniteFloat32Word where
  word := 1045493257
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row28Error : FiniteFloat32Word where
  word := 2992818249
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row28Sum : FiniteFloat32Word where
  word := 1045493256
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row28Center : FiniteFloat32Word where
  word := 1045493256
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row28Add : Float32AddReplay where
  left := invocation0Row28Activation
  right := invocation0Row28Error
  output := invocation0Row28Sum
  localError := ((1914807 : ℚ) / 1125899906842624)

def invocation0Row28Mask : Float32MaskReplay where
  active := true
  input := invocation0Row28Sum
  output := invocation0Row28Center
  localError := (0 : ℚ)

def invocation0Row28AddMask : Float32AddMaskReplay where
  add := invocation0Row28Add
  mask := invocation0Row28Mask

theorem invocation0Row28AddMask_is_accepted : invocation0Row28AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row28AddMask, invocation0Row28Add, invocation0Row28Mask,
    boolRat, invocation0Row28Activation, invocation0Row28Error, invocation0Row28Sum, invocation0Row28Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row29Activation : FiniteFloat32Word where
  word := 1054301389
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row29Error : FiniteFloat32Word where
  word := 2969875575
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row29Sum : FiniteFloat32Word where
  word := 1054301389
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row29Center : FiniteFloat32Word where
  word := 1054301389
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row29Add : Float32AddReplay where
  left := invocation0Row29Activation
  right := invocation0Row29Error
  output := invocation0Row29Sum
  localError := ((8696951 : ℚ) / 4503599627370496)

def invocation0Row29Mask : Float32MaskReplay where
  active := true
  input := invocation0Row29Sum
  output := invocation0Row29Center
  localError := (0 : ℚ)

def invocation0Row29AddMask : Float32AddMaskReplay where
  add := invocation0Row29Add
  mask := invocation0Row29Mask

theorem invocation0Row29AddMask_is_accepted : invocation0Row29AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row29AddMask, invocation0Row29Add, invocation0Row29Mask,
    boolRat, invocation0Row29Activation, invocation0Row29Error, invocation0Row29Sum, invocation0Row29Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row30Activation : FiniteFloat32Word where
  word := 3190587324
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row30Error : FiniteFloat32Word where
  word := 3004884254
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row30Sum : FiniteFloat32Word where
  word := 3190587326
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row30Center : FiniteFloat32Word where
  word := 3190587326
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row30Add : Float32AddReplay where
  left := invocation0Row30Activation
  right := invocation0Row30Error
  output := invocation0Row30Sum
  localError := ((881295 : ℚ) / 140737488355328)

def invocation0Row30Mask : Float32MaskReplay where
  active := true
  input := invocation0Row30Sum
  output := invocation0Row30Center
  localError := (0 : ℚ)

def invocation0Row30AddMask : Float32AddMaskReplay where
  add := invocation0Row30Add
  mask := invocation0Row30Mask

theorem invocation0Row30AddMask_is_accepted : invocation0Row30AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row30AddMask, invocation0Row30Add, invocation0Row30Mask,
    boolRat, invocation0Row30Activation, invocation0Row30Error, invocation0Row30Sum, invocation0Row30Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row31Activation : FiniteFloat32Word where
  word := 1056217437
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row31Error : FiniteFloat32Word where
  word := 3005082293
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row31Sum : FiniteFloat32Word where
  word := 1056217436
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row31Center : FiniteFloat32Word where
  word := 1056217436
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row31Add : Float32AddReplay where
  left := invocation0Row31Activation
  right := invocation0Row31Error
  output := invocation0Row31Sum
  localError := ((1960629 : ℚ) / 281474976710656)

def invocation0Row31Mask : Float32MaskReplay where
  active := true
  input := invocation0Row31Sum
  output := invocation0Row31Center
  localError := (0 : ℚ)

def invocation0Row31AddMask : Float32AddMaskReplay where
  add := invocation0Row31Add
  mask := invocation0Row31Mask

theorem invocation0Row31AddMask_is_accepted : invocation0Row31AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row31AddMask, invocation0Row31Add, invocation0Row31Mask,
    boolRat, invocation0Row31Activation, invocation0Row31Error, invocation0Row31Sum, invocation0Row31Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row32Activation : FiniteFloat32Word where
  word := 3192736517
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row32Error : FiniteFloat32Word where
  word := 2988593296
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row32Sum : FiniteFloat32Word where
  word := 3192736518
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row32Center : FiniteFloat32Word where
  word := 3192736518
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row32Add : Float32AddReplay where
  left := invocation0Row32Activation
  right := invocation0Row32Error
  output := invocation0Row32Sum
  localError := ((383735 : ℚ) / 70368744177664)

def invocation0Row32Mask : Float32MaskReplay where
  active := true
  input := invocation0Row32Sum
  output := invocation0Row32Center
  localError := (0 : ℚ)

def invocation0Row32AddMask : Float32AddMaskReplay where
  add := invocation0Row32Add
  mask := invocation0Row32Mask

theorem invocation0Row32AddMask_is_accepted : invocation0Row32AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row32AddMask, invocation0Row32Add, invocation0Row32Mask,
    boolRat, invocation0Row32Activation, invocation0Row32Error, invocation0Row32Sum, invocation0Row32Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row33Activation : FiniteFloat32Word where
  word := 1016388321
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row33Error : FiniteFloat32Word where
  word := 2971466842
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row33Sum : FiniteFloat32Word where
  word := 1016388320
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row33Center : FiniteFloat32Word where
  word := 1016388320
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row33Add : Float32AddReplay where
  left := invocation0Row33Activation
  right := invocation0Row33Error
  output := invocation0Row33Sum
  localError := ((949805 : ℚ) / 2251799813685248)

def invocation0Row33Mask : Float32MaskReplay where
  active := true
  input := invocation0Row33Sum
  output := invocation0Row33Center
  localError := (0 : ℚ)

def invocation0Row33AddMask : Float32AddMaskReplay where
  add := invocation0Row33Add
  mask := invocation0Row33Mask

theorem invocation0Row33AddMask_is_accepted : invocation0Row33AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row33AddMask, invocation0Row33Add, invocation0Row33Mask,
    boolRat, invocation0Row33Activation, invocation0Row33Error, invocation0Row33Sum, invocation0Row33Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row34Activation : FiniteFloat32Word where
  word := 3195404437
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row34Error : FiniteFloat32Word where
  word := 858615241
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row34Sum : FiniteFloat32Word where
  word := 3195404434
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row34Center : FiniteFloat32Word where
  word := 3195404434
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row34Add : Float32AddReplay where
  left := invocation0Row34Activation
  right := invocation0Row34Error
  output := invocation0Row34Sum
  localError := ((1217079 : ℚ) / 281474976710656)

def invocation0Row34Mask : Float32MaskReplay where
  active := true
  input := invocation0Row34Sum
  output := invocation0Row34Center
  localError := (0 : ℚ)

def invocation0Row34AddMask : Float32AddMaskReplay where
  add := invocation0Row34Add
  mask := invocation0Row34Mask

theorem invocation0Row34AddMask_is_accepted : invocation0Row34AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row34AddMask, invocation0Row34Add, invocation0Row34Mask,
    boolRat, invocation0Row34Activation, invocation0Row34Error, invocation0Row34Sum, invocation0Row34Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row35Activation : FiniteFloat32Word where
  word := 3158085078
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row35Error : FiniteFloat32Word where
  word := 3000362976
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row35Sum : FiniteFloat32Word where
  word := 3158085105
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row35Center : FiniteFloat32Word where
  word := 3158085105
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row35Add : Float32AddReplay where
  left := invocation0Row35Activation
  right := invocation0Row35Error
  output := invocation0Row35Sum
  localError := ((4289 : ℚ) / 17592186044416)

def invocation0Row35Mask : Float32MaskReplay where
  active := true
  input := invocation0Row35Sum
  output := invocation0Row35Center
  localError := (0 : ℚ)

def invocation0Row35AddMask : Float32AddMaskReplay where
  add := invocation0Row35Add
  mask := invocation0Row35Mask

theorem invocation0Row35AddMask_is_accepted : invocation0Row35AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row35AddMask, invocation0Row35Add, invocation0Row35Mask,
    boolRat, invocation0Row35Activation, invocation0Row35Error, invocation0Row35Sum, invocation0Row35Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row36Activation : FiniteFloat32Word where
  word := 1049506757
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row36Error : FiniteFloat32Word where
  word := 2959929855
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row36Sum : FiniteFloat32Word where
  word := 1049506757
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row36Center : FiniteFloat32Word where
  word := 1049506757
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row36Add : Float32AddReplay where
  left := invocation0Row36Activation
  right := invocation0Row36Error
  output := invocation0Row36Sum
  localError := ((15528447 : ℚ) / 18014398509481984)

def invocation0Row36Mask : Float32MaskReplay where
  active := true
  input := invocation0Row36Sum
  output := invocation0Row36Center
  localError := (0 : ℚ)

def invocation0Row36AddMask : Float32AddMaskReplay where
  add := invocation0Row36Add
  mask := invocation0Row36Mask

theorem invocation0Row36AddMask_is_accepted : invocation0Row36AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row36AddMask, invocation0Row36Add, invocation0Row36Mask,
    boolRat, invocation0Row36Activation, invocation0Row36Error, invocation0Row36Sum, invocation0Row36Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row37Activation : FiniteFloat32Word where
  word := 1045365151
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row37Error : FiniteFloat32Word where
  word := 854877444
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row37Sum : FiniteFloat32Word where
  word := 1045365153
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row37Center : FiniteFloat32Word where
  word := 1045365153
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row37Add : Float32AddReplay where
  left := invocation0Row37Activation
  right := invocation0Row37Error
  output := invocation0Row37Sum
  localError := ((190143 : ℚ) / 140737488355328)

def invocation0Row37Mask : Float32MaskReplay where
  active := true
  input := invocation0Row37Sum
  output := invocation0Row37Center
  localError := (0 : ℚ)

def invocation0Row37AddMask : Float32AddMaskReplay where
  add := invocation0Row37Add
  mask := invocation0Row37Mask

theorem invocation0Row37AddMask_is_accepted : invocation0Row37AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row37AddMask, invocation0Row37Add, invocation0Row37Mask,
    boolRat, invocation0Row37Activation, invocation0Row37Error, invocation0Row37Sum, invocation0Row37Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row38Activation : FiniteFloat32Word where
  word := 1057982966
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row38Error : FiniteFloat32Word where
  word := 835128193
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row38Sum : FiniteFloat32Word where
  word := 1057982966
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row38Center : FiniteFloat32Word where
  word := 1057982966
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row38Add : Float32AddReplay where
  left := invocation0Row38Activation
  right := invocation0Row38Error
  output := invocation0Row38Sum
  localError := ((13044609 : ℚ) / 2251799813685248)

def invocation0Row38Mask : Float32MaskReplay where
  active := true
  input := invocation0Row38Sum
  output := invocation0Row38Center
  localError := (0 : ℚ)

def invocation0Row38AddMask : Float32AddMaskReplay where
  add := invocation0Row38Add
  mask := invocation0Row38Mask

theorem invocation0Row38AddMask_is_accepted : invocation0Row38AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row38AddMask, invocation0Row38Add, invocation0Row38Mask,
    boolRat, invocation0Row38Activation, invocation0Row38Error, invocation0Row38Sum, invocation0Row38Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row39Activation : FiniteFloat32Word where
  word := 3192056027
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row39Error : FiniteFloat32Word where
  word := 2998355495
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row39Sum : FiniteFloat32Word where
  word := 3192056028
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row39Center : FiniteFloat32Word where
  word := 3192056028
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row39Add : Float32AddReplay where
  left := invocation0Row39Activation
  right := invocation0Row39Error
  output := invocation0Row39Sum
  localError := ((3622439 : ℚ) / 562949953421312)

def invocation0Row39Mask : Float32MaskReplay where
  active := true
  input := invocation0Row39Sum
  output := invocation0Row39Center
  localError := (0 : ℚ)

def invocation0Row39AddMask : Float32AddMaskReplay where
  add := invocation0Row39Add
  mask := invocation0Row39Mask

theorem invocation0Row39AddMask_is_accepted : invocation0Row39AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row39AddMask, invocation0Row39Add, invocation0Row39Mask,
    boolRat, invocation0Row39Activation, invocation0Row39Error, invocation0Row39Sum, invocation0Row39Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row40Activation : FiniteFloat32Word where
  word := 3188333046
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row40Error : FiniteFloat32Word where
  word := 2974116131
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row40Sum : FiniteFloat32Word where
  word := 3188333046
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row40Center : FiniteFloat32Word where
  word := 3188333046
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row40Add : Float32AddReplay where
  left := invocation0Row40Activation
  right := invocation0Row40Error
  output := invocation0Row40Sum
  localError := ((12937507 : ℚ) / 4503599627370496)

def invocation0Row40Mask : Float32MaskReplay where
  active := true
  input := invocation0Row40Sum
  output := invocation0Row40Center
  localError := (0 : ℚ)

def invocation0Row40AddMask : Float32AddMaskReplay where
  add := invocation0Row40Add
  mask := invocation0Row40Mask

theorem invocation0Row40AddMask_is_accepted : invocation0Row40AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row40AddMask, invocation0Row40Add, invocation0Row40Mask,
    boolRat, invocation0Row40Activation, invocation0Row40Error, invocation0Row40Sum, invocation0Row40Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row41Activation : FiniteFloat32Word where
  word := 3189952464
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row41Error : FiniteFloat32Word where
  word := 823735764
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row41Sum : FiniteFloat32Word where
  word := 3189952464
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row41Center : FiniteFloat32Word where
  word := 3189952464
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row41Add : Float32AddReplay where
  left := invocation0Row41Activation
  right := invocation0Row41Error
  output := invocation0Row41Sum
  localError := ((2510197 : ℚ) / 1125899906842624)

def invocation0Row41Mask : Float32MaskReplay where
  active := true
  input := invocation0Row41Sum
  output := invocation0Row41Center
  localError := (0 : ℚ)

def invocation0Row41AddMask : Float32AddMaskReplay where
  add := invocation0Row41Add
  mask := invocation0Row41Mask

theorem invocation0Row41AddMask_is_accepted : invocation0Row41AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row41AddMask, invocation0Row41Add, invocation0Row41Mask,
    boolRat, invocation0Row41Activation, invocation0Row41Error, invocation0Row41Sum, invocation0Row41Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row42Activation : FiniteFloat32Word where
  word := 3179060619
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row42Error : FiniteFloat32Word where
  word := 2983678646
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row42Sum : FiniteFloat32Word where
  word := 3179060621
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row42Center : FiniteFloat32Word where
  word := 3179060621
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row42Add : Float32AddReplay where
  left := invocation0Row42Activation
  right := invocation0Row42Error
  output := invocation0Row42Sum
  localError := ((1332901 : ℚ) / 1125899906842624)

def invocation0Row42Mask : Float32MaskReplay where
  active := true
  input := invocation0Row42Sum
  output := invocation0Row42Center
  localError := (0 : ℚ)

def invocation0Row42AddMask : Float32AddMaskReplay where
  add := invocation0Row42Add
  mask := invocation0Row42Mask

theorem invocation0Row42AddMask_is_accepted : invocation0Row42AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row42AddMask, invocation0Row42Add, invocation0Row42Mask,
    boolRat, invocation0Row42Activation, invocation0Row42Error, invocation0Row42Sum, invocation0Row42Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row43Activation : FiniteFloat32Word where
  word := 1058087120
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row43Error : FiniteFloat32Word where
  word := 2997062742
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row43Sum : FiniteFloat32Word where
  word := 1058087120
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row43Center : FiniteFloat32Word where
  word := 1058087120
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row43Add : Float32AddReplay where
  left := invocation0Row43Activation
  right := invocation0Row43Error
  output := invocation0Row43Sum
  localError := ((5359147 : ℚ) / 281474976710656)

def invocation0Row43Mask : Float32MaskReplay where
  active := true
  input := invocation0Row43Sum
  output := invocation0Row43Center
  localError := (0 : ℚ)

def invocation0Row43AddMask : Float32AddMaskReplay where
  add := invocation0Row43Add
  mask := invocation0Row43Mask

theorem invocation0Row43AddMask_is_accepted : invocation0Row43AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row43AddMask, invocation0Row43Add, invocation0Row43Mask,
    boolRat, invocation0Row43Activation, invocation0Row43Error, invocation0Row43Sum, invocation0Row43Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row44Activation : FiniteFloat32Word where
  word := 1052146841
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row44Error : FiniteFloat32Word where
  word := 2998633308
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row44Sum : FiniteFloat32Word where
  word := 1052146840
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row44Center : FiniteFloat32Word where
  word := 1052146840
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row44Add : Float32AddReplay where
  left := invocation0Row44Activation
  right := invocation0Row44Error
  output := invocation0Row44Sum
  localError := ((1122089 : ℚ) / 140737488355328)

def invocation0Row44Mask : Float32MaskReplay where
  active := true
  input := invocation0Row44Sum
  output := invocation0Row44Center
  localError := (0 : ℚ)

def invocation0Row44AddMask : Float32AddMaskReplay where
  add := invocation0Row44Add
  mask := invocation0Row44Mask

theorem invocation0Row44AddMask_is_accepted : invocation0Row44AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row44AddMask, invocation0Row44Add, invocation0Row44Mask,
    boolRat, invocation0Row44Activation, invocation0Row44Error, invocation0Row44Sum, invocation0Row44Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row45Activation : FiniteFloat32Word where
  word := 1051443671
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row45Error : FiniteFloat32Word where
  word := 2993793484
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row45Sum : FiniteFloat32Word where
  word := 1051443671
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row45Center : FiniteFloat32Word where
  word := 1051443671
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row45Add : Float32AddReplay where
  left := invocation0Row45Activation
  right := invocation0Row45Error
  output := invocation0Row45Sum
  localError := ((3959411 : ℚ) / 281474976710656)

def invocation0Row45Mask : Float32MaskReplay where
  active := true
  input := invocation0Row45Sum
  output := invocation0Row45Center
  localError := (0 : ℚ)

def invocation0Row45AddMask : Float32AddMaskReplay where
  add := invocation0Row45Add
  mask := invocation0Row45Mask

theorem invocation0Row45AddMask_is_accepted : invocation0Row45AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row45AddMask, invocation0Row45Add, invocation0Row45Mask,
    boolRat, invocation0Row45Activation, invocation0Row45Error, invocation0Row45Sum, invocation0Row45Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row46Activation : FiniteFloat32Word where
  word := 3190342760
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row46Error : FiniteFloat32Word where
  word := 830385183
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row46Sum : FiniteFloat32Word where
  word := 3190342760
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row46Center : FiniteFloat32Word where
  word := 3190342760
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row46Add : Float32AddReplay where
  left := invocation0Row46Activation
  right := invocation0Row46Error
  output := invocation0Row46Sum
  localError := ((16690207 : ℚ) / 4503599627370496)

def invocation0Row46Mask : Float32MaskReplay where
  active := true
  input := invocation0Row46Sum
  output := invocation0Row46Center
  localError := (0 : ℚ)

def invocation0Row46AddMask : Float32AddMaskReplay where
  add := invocation0Row46Add
  mask := invocation0Row46Mask

theorem invocation0Row46AddMask_is_accepted : invocation0Row46AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row46AddMask, invocation0Row46Add, invocation0Row46Mask,
    boolRat, invocation0Row46Activation, invocation0Row46Error, invocation0Row46Sum, invocation0Row46Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row47Activation : FiniteFloat32Word where
  word := 1054271179
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row47Error : FiniteFloat32Word where
  word := 861117697
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row47Sum : FiniteFloat32Word where
  word := 1054271181
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row47Center : FiniteFloat32Word where
  word := 1054271181
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row47Add : Float32AddReplay where
  left := invocation0Row47Activation
  right := invocation0Row47Error
  output := invocation0Row47Sum
  localError := ((2908927 : ℚ) / 281474976710656)

def invocation0Row47Mask : Float32MaskReplay where
  active := true
  input := invocation0Row47Sum
  output := invocation0Row47Center
  localError := (0 : ℚ)

def invocation0Row47AddMask : Float32AddMaskReplay where
  add := invocation0Row47Add
  mask := invocation0Row47Mask

theorem invocation0Row47AddMask_is_accepted : invocation0Row47AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row47AddMask, invocation0Row47Add, invocation0Row47Mask,
    boolRat, invocation0Row47Activation, invocation0Row47Error, invocation0Row47Sum, invocation0Row47Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row48Activation : FiniteFloat32Word where
  word := 1058584326
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row48Error : FiniteFloat32Word where
  word := 3006326442
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row48Sum : FiniteFloat32Word where
  word := 1058584325
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row48Center : FiniteFloat32Word where
  word := 1058584325
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row48Add : Float32AddReplay where
  left := invocation0Row48Activation
  right := invocation0Row48Error
  output := invocation0Row48Sum
  localError := ((2591915 : ℚ) / 140737488355328)

def invocation0Row48Mask : Float32MaskReplay where
  active := true
  input := invocation0Row48Sum
  output := invocation0Row48Center
  localError := (0 : ℚ)

def invocation0Row48AddMask : Float32AddMaskReplay where
  add := invocation0Row48Add
  mask := invocation0Row48Mask

theorem invocation0Row48AddMask_is_accepted : invocation0Row48AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row48AddMask, invocation0Row48Add, invocation0Row48Mask,
    boolRat, invocation0Row48Activation, invocation0Row48Error, invocation0Row48Sum, invocation0Row48Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row49Activation : FiniteFloat32Word where
  word := 1038039726
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row49Error : FiniteFloat32Word where
  word := 2981002325
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row49Sum : FiniteFloat32Word where
  word := 1038039725
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row49Center : FiniteFloat32Word where
  word := 1038039725
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row49Add : Float32AddReplay where
  left := invocation0Row49Activation
  right := invocation0Row49Error
  output := invocation0Row49Sum
  localError := ((5342123 : ℚ) / 2251799813685248)

def invocation0Row49Mask : Float32MaskReplay where
  active := true
  input := invocation0Row49Sum
  output := invocation0Row49Center
  localError := (0 : ℚ)

def invocation0Row49AddMask : Float32AddMaskReplay where
  add := invocation0Row49Add
  mask := invocation0Row49Mask

theorem invocation0Row49AddMask_is_accepted : invocation0Row49AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row49AddMask, invocation0Row49Add, invocation0Row49Mask,
    boolRat, invocation0Row49Activation, invocation0Row49Error, invocation0Row49Sum, invocation0Row49Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row50Activation : FiniteFloat32Word where
  word := 1038856620
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row50Error : FiniteFloat32Word where
  word := 3002837143
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row50Sum : FiniteFloat32Word where
  word := 1038856616
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row50Center : FiniteFloat32Word where
  word := 1038856616
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row50Add : Float32AddReplay where
  left := invocation0Row50Activation
  right := invocation0Row50Error
  output := invocation0Row50Sum
  localError := ((284521 : ℚ) / 562949953421312)

def invocation0Row50Mask : Float32MaskReplay where
  active := true
  input := invocation0Row50Sum
  output := invocation0Row50Center
  localError := (0 : ℚ)

def invocation0Row50AddMask : Float32AddMaskReplay where
  add := invocation0Row50Add
  mask := invocation0Row50Mask

theorem invocation0Row50AddMask_is_accepted : invocation0Row50AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row50AddMask, invocation0Row50Add, invocation0Row50Mask,
    boolRat, invocation0Row50Activation, invocation0Row50Error, invocation0Row50Sum, invocation0Row50Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row51Activation : FiniteFloat32Word where
  word := 1046534197
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row51Error : FiniteFloat32Word where
  word := 2995926828
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row51Sum : FiniteFloat32Word where
  word := 1046534196
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row51Center : FiniteFloat32Word where
  word := 1046534196
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row51Add : Float32AddReplay where
  left := invocation0Row51Activation
  right := invocation0Row51Error
  output := invocation0Row51Sum
  localError := ((298443 : ℚ) / 140737488355328)

def invocation0Row51Mask : Float32MaskReplay where
  active := true
  input := invocation0Row51Sum
  output := invocation0Row51Center
  localError := (0 : ℚ)

def invocation0Row51AddMask : Float32AddMaskReplay where
  add := invocation0Row51Add
  mask := invocation0Row51Mask

theorem invocation0Row51AddMask_is_accepted : invocation0Row51AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row51AddMask, invocation0Row51Add, invocation0Row51Mask,
    boolRat, invocation0Row51Activation, invocation0Row51Error, invocation0Row51Sum, invocation0Row51Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row52Activation : FiniteFloat32Word where
  word := 1053534955
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row52Error : FiniteFloat32Word where
  word := 3009589583
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row52Sum : FiniteFloat32Word where
  word := 1053534953
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row52Center : FiniteFloat32Word where
  word := 1053534953
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row52Add : Float32AddReplay where
  left := invocation0Row52Activation
  right := invocation0Row52Error
  output := invocation0Row52Sum
  localError := ((1920689 : ℚ) / 281474976710656)

def invocation0Row52Mask : Float32MaskReplay where
  active := true
  input := invocation0Row52Sum
  output := invocation0Row52Center
  localError := (0 : ℚ)

def invocation0Row52AddMask : Float32AddMaskReplay where
  add := invocation0Row52Add
  mask := invocation0Row52Mask

theorem invocation0Row52AddMask_is_accepted : invocation0Row52AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row52AddMask, invocation0Row52Add, invocation0Row52Mask,
    boolRat, invocation0Row52Activation, invocation0Row52Error, invocation0Row52Sum, invocation0Row52Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row53Activation : FiniteFloat32Word where
  word := 1055676088
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row53Error : FiniteFloat32Word where
  word := 2996057421
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row53Sum : FiniteFloat32Word where
  word := 1055676087
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row53Center : FiniteFloat32Word where
  word := 1055676087
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row53Add : Float32AddReplay where
  left := invocation0Row53Activation
  right := invocation0Row53Error
  output := invocation0Row53Sum
  localError := ((7064243 : ℚ) / 562949953421312)

def invocation0Row53Mask : Float32MaskReplay where
  active := true
  input := invocation0Row53Sum
  output := invocation0Row53Center
  localError := (0 : ℚ)

def invocation0Row53AddMask : Float32AddMaskReplay where
  add := invocation0Row53Add
  mask := invocation0Row53Mask

theorem invocation0Row53AddMask_is_accepted : invocation0Row53AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row53AddMask, invocation0Row53Add, invocation0Row53Mask,
    boolRat, invocation0Row53Activation, invocation0Row53Error, invocation0Row53Sum, invocation0Row53Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row54Activation : FiniteFloat32Word where
  word := 3192459622
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row54Error : FiniteFloat32Word where
  word := 842329312
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row54Sum : FiniteFloat32Word where
  word := 3192459621
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row54Center : FiniteFloat32Word where
  word := 3192459621
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row54Add : Float32AddReplay where
  left := invocation0Row54Activation
  right := invocation0Row54Error
  output := invocation0Row54Sum
  localError := ((153753 : ℚ) / 35184372088832)

def invocation0Row54Mask : Float32MaskReplay where
  active := true
  input := invocation0Row54Sum
  output := invocation0Row54Center
  localError := (0 : ℚ)

def invocation0Row54AddMask : Float32AddMaskReplay where
  add := invocation0Row54Add
  mask := invocation0Row54Mask

theorem invocation0Row54AddMask_is_accepted : invocation0Row54AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row54AddMask, invocation0Row54Add, invocation0Row54Mask,
    boolRat, invocation0Row54Activation, invocation0Row54Error, invocation0Row54Sum, invocation0Row54Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row55Activation : FiniteFloat32Word where
  word := 3183375066
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row55Error : FiniteFloat32Word where
  word := 3006922796
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row55Sum : FiniteFloat32Word where
  word := 3183375072
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row55Center : FiniteFloat32Word where
  word := 3183375072
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row55Add : Float32AddReplay where
  left := invocation0Row55Activation
  right := invocation0Row55Error
  output := invocation0Row55Sum
  localError := ((98293 : ℚ) / 70368744177664)

def invocation0Row55Mask : Float32MaskReplay where
  active := true
  input := invocation0Row55Sum
  output := invocation0Row55Center
  localError := (0 : ℚ)

def invocation0Row55AddMask : Float32AddMaskReplay where
  add := invocation0Row55Add
  mask := invocation0Row55Mask

theorem invocation0Row55AddMask_is_accepted : invocation0Row55AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row55AddMask, invocation0Row55Add, invocation0Row55Mask,
    boolRat, invocation0Row55Activation, invocation0Row55Error, invocation0Row55Sum, invocation0Row55Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row56Activation : FiniteFloat32Word where
  word := 1062405026
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row56Error : FiniteFloat32Word where
  word := 3002366850
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row56Sum : FiniteFloat32Word where
  word := 1062405026
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row56Center : FiniteFloat32Word where
  word := 1062405026
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row56Add : Float32AddReplay where
  left := invocation0Row56Activation
  right := invocation0Row56Error
  output := invocation0Row56Sum
  localError := ((8011201 : ℚ) / 281474976710656)

def invocation0Row56Mask : Float32MaskReplay where
  active := true
  input := invocation0Row56Sum
  output := invocation0Row56Center
  localError := (0 : ℚ)

def invocation0Row56AddMask : Float32AddMaskReplay where
  add := invocation0Row56Add
  mask := invocation0Row56Mask

theorem invocation0Row56AddMask_is_accepted : invocation0Row56AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row56AddMask, invocation0Row56Add, invocation0Row56Mask,
    boolRat, invocation0Row56Activation, invocation0Row56Error, invocation0Row56Sum, invocation0Row56Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row57Activation : FiniteFloat32Word where
  word := 1057603930
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row57Error : FiniteFloat32Word where
  word := 2991033060
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row57Sum : FiniteFloat32Word where
  word := 1057603930
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row57Center : FiniteFloat32Word where
  word := 1057603930
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row57Add : Float32AddReplay where
  left := invocation0Row57Activation
  right := invocation0Row57Error
  output := invocation0Row57Sum
  localError := ((3269305 : ℚ) / 281474976710656)

def invocation0Row57Mask : Float32MaskReplay where
  active := true
  input := invocation0Row57Sum
  output := invocation0Row57Center
  localError := (0 : ℚ)

def invocation0Row57AddMask : Float32AddMaskReplay where
  add := invocation0Row57Add
  mask := invocation0Row57Mask

theorem invocation0Row57AddMask_is_accepted : invocation0Row57AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row57AddMask, invocation0Row57Add, invocation0Row57Mask,
    boolRat, invocation0Row57Activation, invocation0Row57Error, invocation0Row57Sum, invocation0Row57Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row58Activation : FiniteFloat32Word where
  word := 1003262970
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row58Error : FiniteFloat32Word where
  word := 2993679927
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row58Sum : FiniteFloat32Word where
  word := 1003262940
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row58Center : FiniteFloat32Word where
  word := 1003262940
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row58Add : Float32AddReplay where
  left := invocation0Row58Activation
  right := invocation0Row58Error
  output := invocation0Row58Sum
  localError := ((4553 : ℚ) / 1125899906842624)

def invocation0Row58Mask : Float32MaskReplay where
  active := true
  input := invocation0Row58Sum
  output := invocation0Row58Center
  localError := (0 : ℚ)

def invocation0Row58AddMask : Float32AddMaskReplay where
  add := invocation0Row58Add
  mask := invocation0Row58Mask

theorem invocation0Row58AddMask_is_accepted : invocation0Row58AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row58AddMask, invocation0Row58Add, invocation0Row58Mask,
    boolRat, invocation0Row58Activation, invocation0Row58Error, invocation0Row58Sum, invocation0Row58Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row59Activation : FiniteFloat32Word where
  word := 3180356249
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row59Error : FiniteFloat32Word where
  word := 859631285
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row59Sum : FiniteFloat32Word where
  word := 3180356243
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row59Center : FiniteFloat32Word where
  word := 3180356243
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row59Add : Float32AddReplay where
  left := invocation0Row59Activation
  right := invocation0Row59Error
  output := invocation0Row59Sum
  localError := ((201035 : ℚ) / 281474976710656)

def invocation0Row59Mask : Float32MaskReplay where
  active := true
  input := invocation0Row59Sum
  output := invocation0Row59Center
  localError := (0 : ℚ)

def invocation0Row59AddMask : Float32AddMaskReplay where
  add := invocation0Row59Add
  mask := invocation0Row59Mask

theorem invocation0Row59AddMask_is_accepted : invocation0Row59AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row59AddMask, invocation0Row59Add, invocation0Row59Mask,
    boolRat, invocation0Row59Activation, invocation0Row59Error, invocation0Row59Sum, invocation0Row59Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row60Activation : FiniteFloat32Word where
  word := 976726950
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row60Error : FiniteFloat32Word where
  word := 832305716
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row60Sum : FiniteFloat32Word where
  word := 976727028
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row60Center : FiniteFloat32Word where
  word := 976727028
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row60Add : Float32AddReplay where
  left := invocation0Row60Activation
  right := invocation0Row60Error
  output := invocation0Row60Sum
  localError := ((371 : ℚ) / 562949953421312)

def invocation0Row60Mask : Float32MaskReplay where
  active := true
  input := invocation0Row60Sum
  output := invocation0Row60Center
  localError := (0 : ℚ)

def invocation0Row60AddMask : Float32AddMaskReplay where
  add := invocation0Row60Add
  mask := invocation0Row60Mask

theorem invocation0Row60AddMask_is_accepted : invocation0Row60AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row60AddMask, invocation0Row60Add, invocation0Row60Mask,
    boolRat, invocation0Row60Activation, invocation0Row60Error, invocation0Row60Sum, invocation0Row60Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row61Activation : FiniteFloat32Word where
  word := 3184881835
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row61Error : FiniteFloat32Word where
  word := 829765775
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row61Sum : FiniteFloat32Word where
  word := 3184881835
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row61Center : FiniteFloat32Word where
  word := 3184881835
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row61Add : Float32AddReplay where
  left := invocation0Row61Activation
  right := invocation0Row61Error
  output := invocation0Row61Sum
  localError := ((16070799 : ℚ) / 4503599627370496)

def invocation0Row61Mask : Float32MaskReplay where
  active := true
  input := invocation0Row61Sum
  output := invocation0Row61Center
  localError := (0 : ℚ)

def invocation0Row61AddMask : Float32AddMaskReplay where
  add := invocation0Row61Add
  mask := invocation0Row61Mask

theorem invocation0Row61AddMask_is_accepted : invocation0Row61AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row61AddMask, invocation0Row61Add, invocation0Row61Mask,
    boolRat, invocation0Row61Activation, invocation0Row61Error, invocation0Row61Sum, invocation0Row61Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row62Activation : FiniteFloat32Word where
  word := 3186420389
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row62Error : FiniteFloat32Word where
  word := 860098231
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row62Sum : FiniteFloat32Word where
  word := 3186420383
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row62Center : FiniteFloat32Word where
  word := 3186420383
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row62Add : Float32AddReplay where
  left := invocation0Row62Activation
  right := invocation0Row62Error
  output := invocation0Row62Sum
  localError := ((265911 : ℚ) / 281474976710656)

def invocation0Row62Mask : Float32MaskReplay where
  active := true
  input := invocation0Row62Sum
  output := invocation0Row62Center
  localError := (0 : ℚ)

def invocation0Row62AddMask : Float32AddMaskReplay where
  add := invocation0Row62Add
  mask := invocation0Row62Mask

theorem invocation0Row62AddMask_is_accepted : invocation0Row62AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row62AddMask, invocation0Row62Add, invocation0Row62Mask,
    boolRat, invocation0Row62Activation, invocation0Row62Error, invocation0Row62Sum, invocation0Row62Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def invocation0Row63Activation : FiniteFloat32Word where
  word := 3192681530
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row63Error : FiniteFloat32Word where
  word := 852123131
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row63Sum : FiniteFloat32Word where
  word := 3192681528
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row63Center : FiniteFloat32Word where
  word := 3192681528
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row63Add : Float32AddReplay where
  left := invocation0Row63Activation
  right := invocation0Row63Error
  output := invocation0Row63Sum
  localError := ((3514885 : ℚ) / 562949953421312)

def invocation0Row63Mask : Float32MaskReplay where
  active := true
  input := invocation0Row63Sum
  output := invocation0Row63Center
  localError := (0 : ℚ)

def invocation0Row63AddMask : Float32AddMaskReplay where
  add := invocation0Row63Add
  mask := invocation0Row63Mask

theorem invocation0Row63AddMask_is_accepted : invocation0Row63AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row63AddMask, invocation0Row63Add, invocation0Row63Mask,
    boolRat, invocation0Row63Activation, invocation0Row63Error, invocation0Row63Sum, invocation0Row63Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def hiddenReplay0 : Float32HiddenStageReplay 64 256 where
  affineSiLU := GeneratedAuthenticatedAffineSiLUReplaySite0Invocation0Fixture.replay0
  errorSite := ![invocation0Row0Error, invocation0Row1Error, invocation0Row2Error, invocation0Row3Error, invocation0Row4Error, invocation0Row5Error, invocation0Row6Error, invocation0Row7Error, invocation0Row8Error, invocation0Row9Error, invocation0Row10Error, invocation0Row11Error, invocation0Row12Error, invocation0Row13Error, invocation0Row14Error, invocation0Row15Error, invocation0Row16Error, invocation0Row17Error, invocation0Row18Error, invocation0Row19Error, invocation0Row20Error, invocation0Row21Error, invocation0Row22Error, invocation0Row23Error, invocation0Row24Error, invocation0Row25Error, invocation0Row26Error, invocation0Row27Error, invocation0Row28Error, invocation0Row29Error, invocation0Row30Error, invocation0Row31Error, invocation0Row32Error, invocation0Row33Error, invocation0Row34Error, invocation0Row35Error, invocation0Row36Error, invocation0Row37Error, invocation0Row38Error, invocation0Row39Error, invocation0Row40Error, invocation0Row41Error, invocation0Row42Error, invocation0Row43Error, invocation0Row44Error, invocation0Row45Error, invocation0Row46Error, invocation0Row47Error, invocation0Row48Error, invocation0Row49Error, invocation0Row50Error, invocation0Row51Error, invocation0Row52Error, invocation0Row53Error, invocation0Row54Error, invocation0Row55Error, invocation0Row56Error, invocation0Row57Error, invocation0Row58Error, invocation0Row59Error, invocation0Row60Error, invocation0Row61Error, invocation0Row62Error, invocation0Row63Error]
  addMask := ![invocation0Row0AddMask, invocation0Row1AddMask, invocation0Row2AddMask, invocation0Row3AddMask, invocation0Row4AddMask, invocation0Row5AddMask, invocation0Row6AddMask, invocation0Row7AddMask, invocation0Row8AddMask, invocation0Row9AddMask, invocation0Row10AddMask, invocation0Row11AddMask, invocation0Row12AddMask, invocation0Row13AddMask, invocation0Row14AddMask, invocation0Row15AddMask, invocation0Row16AddMask, invocation0Row17AddMask, invocation0Row18AddMask, invocation0Row19AddMask, invocation0Row20AddMask, invocation0Row21AddMask, invocation0Row22AddMask, invocation0Row23AddMask, invocation0Row24AddMask, invocation0Row25AddMask, invocation0Row26AddMask, invocation0Row27AddMask, invocation0Row28AddMask, invocation0Row29AddMask, invocation0Row30AddMask, invocation0Row31AddMask, invocation0Row32AddMask, invocation0Row33AddMask, invocation0Row34AddMask, invocation0Row35AddMask, invocation0Row36AddMask, invocation0Row37AddMask, invocation0Row38AddMask, invocation0Row39AddMask, invocation0Row40AddMask, invocation0Row41AddMask, invocation0Row42AddMask, invocation0Row43AddMask, invocation0Row44AddMask, invocation0Row45AddMask, invocation0Row46AddMask, invocation0Row47AddMask, invocation0Row48AddMask, invocation0Row49AddMask, invocation0Row50AddMask, invocation0Row51AddMask, invocation0Row52AddMask, invocation0Row53AddMask, invocation0Row54AddMask, invocation0Row55AddMask, invocation0Row56AddMask, invocation0Row57AddMask, invocation0Row58AddMask, invocation0Row59AddMask, invocation0Row60AddMask, invocation0Row61AddMask, invocation0Row62AddMask, invocation0Row63AddMask]

theorem hiddenReplay0_is_accepted : hiddenReplay0.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff hiddenReplay0).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff
      GeneratedAuthenticatedAffineSiLUReplaySite0Invocation0Fixture.replay0).mp
      GeneratedAuthenticatedAffineSiLUReplaySite0Invocation0Fixture.replay0_is_accepted, ?_⟩
  intro row
  fin_cases row
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row0AddMask).mp
        invocation0Row0AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row1AddMask).mp
        invocation0Row1AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row2AddMask).mp
        invocation0Row2AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row3AddMask).mp
        invocation0Row3AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row4AddMask).mp
        invocation0Row4AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row5AddMask).mp
        invocation0Row5AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row6AddMask).mp
        invocation0Row6AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row7AddMask).mp
        invocation0Row7AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row8AddMask).mp
        invocation0Row8AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row9AddMask).mp
        invocation0Row9AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row10AddMask).mp
        invocation0Row10AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row11AddMask).mp
        invocation0Row11AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row12AddMask).mp
        invocation0Row12AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row13AddMask).mp
        invocation0Row13AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row14AddMask).mp
        invocation0Row14AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row15AddMask).mp
        invocation0Row15AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row16AddMask).mp
        invocation0Row16AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row17AddMask).mp
        invocation0Row17AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row18AddMask).mp
        invocation0Row18AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row19AddMask).mp
        invocation0Row19AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row20AddMask).mp
        invocation0Row20AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row21AddMask).mp
        invocation0Row21AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row22AddMask).mp
        invocation0Row22AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row23AddMask).mp
        invocation0Row23AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row24AddMask).mp
        invocation0Row24AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row25AddMask).mp
        invocation0Row25AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row26AddMask).mp
        invocation0Row26AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row27AddMask).mp
        invocation0Row27AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row28AddMask).mp
        invocation0Row28AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row29AddMask).mp
        invocation0Row29AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row30AddMask).mp
        invocation0Row30AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row31AddMask).mp
        invocation0Row31AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row32AddMask).mp
        invocation0Row32AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row33AddMask).mp
        invocation0Row33AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row34AddMask).mp
        invocation0Row34AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row35AddMask).mp
        invocation0Row35AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row36AddMask).mp
        invocation0Row36AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row37AddMask).mp
        invocation0Row37AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row38AddMask).mp
        invocation0Row38AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row39AddMask).mp
        invocation0Row39AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row40AddMask).mp
        invocation0Row40AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row41AddMask).mp
        invocation0Row41AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row42AddMask).mp
        invocation0Row42AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row43AddMask).mp
        invocation0Row43AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row44AddMask).mp
        invocation0Row44AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row45AddMask).mp
        invocation0Row45AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row46AddMask).mp
        invocation0Row46AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row47AddMask).mp
        invocation0Row47AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row48AddMask).mp
        invocation0Row48AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row49AddMask).mp
        invocation0Row49AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row50AddMask).mp
        invocation0Row50AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row51AddMask).mp
        invocation0Row51AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row52AddMask).mp
        invocation0Row52AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row53AddMask).mp
        invocation0Row53AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row54AddMask).mp
        invocation0Row54AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row55AddMask).mp
        invocation0Row55AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row56AddMask).mp
        invocation0Row56AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row57AddMask).mp
        invocation0Row57AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row58AddMask).mp
        invocation0Row58AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row59AddMask).mp
        invocation0Row59AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row60AddMask).mp
        invocation0Row60AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row61AddMask).mp
        invocation0Row61AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row62AddMask).mp
        invocation0Row62AddMask_is_accepted, rfl, rfl⟩
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row63AddMask).mp
        invocation0Row63AddMask_is_accepted, rfl, rfl⟩

def certificateBatch : Float32HiddenStageReplayBatch 64 256 where
  expectedCount := 1
  entries := [hiddenReplay0]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [Float32HiddenStageReplayBatch.check, certificateBatch,
    hiddenReplay0_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end
end GeneratedAuthenticatedHiddenStageReplaySite0Invocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
