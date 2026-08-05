import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureCommon
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock00
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock01
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock02
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock03
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock04
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock05
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock06
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock07
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock08
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock09
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock10
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock11
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock12
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock13
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock14
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineReplaySite0Invocation0GeneratedFixtureBlock15

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate

set_option maxRecDepth 100000

open GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon

def sharedWeightRows : Fin 64 → Fin 256 → FiniteFloat32Word :=
  ![GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.weightRow0, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.weightRow1, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.weightRow2, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.weightRow3, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.weightRow4, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.weightRow5, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.weightRow6, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.weightRow7, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.weightRow8, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.weightRow9, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.weightRow10, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.weightRow11, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.weightRow12, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.weightRow13, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.weightRow14, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.weightRow15, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.weightRow16, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.weightRow17, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.weightRow18, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.weightRow19, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.weightRow20, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.weightRow21, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.weightRow22, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.weightRow23, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.weightRow24, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.weightRow25, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.weightRow26, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.weightRow27, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.weightRow28, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.weightRow29, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.weightRow30, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.weightRow31, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.weightRow32, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.weightRow33, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.weightRow34, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.weightRow35, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.weightRow36, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.weightRow37, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.weightRow38, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.weightRow39, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.weightRow40, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.weightRow41, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.weightRow42, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.weightRow43, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.weightRow44, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.weightRow45, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.weightRow46, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.weightRow47, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.weightRow48, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.weightRow49, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.weightRow50, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.weightRow51, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.weightRow52, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.weightRow53, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.weightRow54, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.weightRow55, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.weightRow56, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.weightRow57, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.weightRow58, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.weightRow59, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.weightRow60, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.weightRow61, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.weightRow62, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.weightRow63]

def replay0Output : Fin 64 → FiniteFloat32Word :=
  GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output

def replay0 : Float32AffineReplay 64 256 :=
  Float32AffineReplay.ofRows
    GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
    sharedWeightRows
    GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
    replay0Output
    ((4830463782067867 : ℚ) / 1180591620717411303424)

theorem replay0_coordinate0_is_bounded :
    |(replay0.output 0).toRat -
        replay0.idealOutputRat 0| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 0 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 0).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 0).toRat +
          ∑ column, (sharedWeightRows 0 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 0 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.replay0_coordinate0_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 0) 0 hrow)

theorem replay0_coordinate1_is_bounded :
    |(replay0.output 1).toRat -
        replay0.idealOutputRat 1| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 1 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 1).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 1).toRat +
          ∑ column, (sharedWeightRows 1 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 1 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.replay0_coordinate1_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 1) 1 hrow)

theorem replay0_coordinate2_is_bounded :
    |(replay0.output 2).toRat -
        replay0.idealOutputRat 2| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 2 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 2).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 2).toRat +
          ∑ column, (sharedWeightRows 2 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 2 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.replay0_coordinate2_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 2) 2 hrow)

theorem replay0_coordinate3_is_bounded :
    |(replay0.output 3).toRat -
        replay0.idealOutputRat 3| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 3 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 3).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 3).toRat +
          ∑ column, (sharedWeightRows 3 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 3 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock00.replay0_coordinate3_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 3) 3 hrow)

theorem replay0_coordinate4_is_bounded :
    |(replay0.output 4).toRat -
        replay0.idealOutputRat 4| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 4 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 4).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 4).toRat +
          ∑ column, (sharedWeightRows 4 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 4 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.replay0_coordinate4_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 4) 4 hrow)

theorem replay0_coordinate5_is_bounded :
    |(replay0.output 5).toRat -
        replay0.idealOutputRat 5| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 5 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 5).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 5).toRat +
          ∑ column, (sharedWeightRows 5 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 5 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.replay0_coordinate5_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 5) 5 hrow)

theorem replay0_coordinate6_is_bounded :
    |(replay0.output 6).toRat -
        replay0.idealOutputRat 6| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 6 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 6).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 6).toRat +
          ∑ column, (sharedWeightRows 6 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 6 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.replay0_coordinate6_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 6) 6 hrow)

theorem replay0_coordinate7_is_bounded :
    |(replay0.output 7).toRat -
        replay0.idealOutputRat 7| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 7 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 7).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 7).toRat +
          ∑ column, (sharedWeightRows 7 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 7 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock01.replay0_coordinate7_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 7) 7 hrow)

theorem replay0_coordinate8_is_bounded :
    |(replay0.output 8).toRat -
        replay0.idealOutputRat 8| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 8 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 8).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 8).toRat +
          ∑ column, (sharedWeightRows 8 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 8 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.replay0_coordinate8_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 8) 8 hrow)

theorem replay0_coordinate9_is_bounded :
    |(replay0.output 9).toRat -
        replay0.idealOutputRat 9| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 9 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 9).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 9).toRat +
          ∑ column, (sharedWeightRows 9 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 9 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.replay0_coordinate9_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 9) 9 hrow)

theorem replay0_coordinate10_is_bounded :
    |(replay0.output 10).toRat -
        replay0.idealOutputRat 10| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 10 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 10).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 10).toRat +
          ∑ column, (sharedWeightRows 10 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 10 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.replay0_coordinate10_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 10) 10 hrow)

theorem replay0_coordinate11_is_bounded :
    |(replay0.output 11).toRat -
        replay0.idealOutputRat 11| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 11 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 11).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 11).toRat +
          ∑ column, (sharedWeightRows 11 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 11 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock02.replay0_coordinate11_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 11) 11 hrow)

theorem replay0_coordinate12_is_bounded :
    |(replay0.output 12).toRat -
        replay0.idealOutputRat 12| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 12 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 12).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 12).toRat +
          ∑ column, (sharedWeightRows 12 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 12 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.replay0_coordinate12_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 12) 12 hrow)

theorem replay0_coordinate13_is_bounded :
    |(replay0.output 13).toRat -
        replay0.idealOutputRat 13| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 13 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 13).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 13).toRat +
          ∑ column, (sharedWeightRows 13 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 13 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.replay0_coordinate13_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 13) 13 hrow)

theorem replay0_coordinate14_is_bounded :
    |(replay0.output 14).toRat -
        replay0.idealOutputRat 14| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 14 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 14).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 14).toRat +
          ∑ column, (sharedWeightRows 14 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 14 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.replay0_coordinate14_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 14) 14 hrow)

theorem replay0_coordinate15_is_bounded :
    |(replay0.output 15).toRat -
        replay0.idealOutputRat 15| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 15 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 15).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 15).toRat +
          ∑ column, (sharedWeightRows 15 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 15 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock03.replay0_coordinate15_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 15) 15 hrow)

theorem replay0_coordinate16_is_bounded :
    |(replay0.output 16).toRat -
        replay0.idealOutputRat 16| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 16 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 16).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 16).toRat +
          ∑ column, (sharedWeightRows 16 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 16 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.replay0_coordinate16_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 16) 16 hrow)

theorem replay0_coordinate17_is_bounded :
    |(replay0.output 17).toRat -
        replay0.idealOutputRat 17| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 17 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 17).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 17).toRat +
          ∑ column, (sharedWeightRows 17 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 17 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.replay0_coordinate17_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 17) 17 hrow)

theorem replay0_coordinate18_is_bounded :
    |(replay0.output 18).toRat -
        replay0.idealOutputRat 18| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 18 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 18).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 18).toRat +
          ∑ column, (sharedWeightRows 18 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 18 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.replay0_coordinate18_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 18) 18 hrow)

theorem replay0_coordinate19_is_bounded :
    |(replay0.output 19).toRat -
        replay0.idealOutputRat 19| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 19 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 19).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 19).toRat +
          ∑ column, (sharedWeightRows 19 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 19 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock04.replay0_coordinate19_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 19) 19 hrow)

theorem replay0_coordinate20_is_bounded :
    |(replay0.output 20).toRat -
        replay0.idealOutputRat 20| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 20 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 20).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 20).toRat +
          ∑ column, (sharedWeightRows 20 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 20 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.replay0_coordinate20_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 20) 20 hrow)

theorem replay0_coordinate21_is_bounded :
    |(replay0.output 21).toRat -
        replay0.idealOutputRat 21| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 21 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 21).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 21).toRat +
          ∑ column, (sharedWeightRows 21 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 21 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.replay0_coordinate21_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 21) 21 hrow)

theorem replay0_coordinate22_is_bounded :
    |(replay0.output 22).toRat -
        replay0.idealOutputRat 22| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 22 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 22).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 22).toRat +
          ∑ column, (sharedWeightRows 22 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 22 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.replay0_coordinate22_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 22) 22 hrow)

theorem replay0_coordinate23_is_bounded :
    |(replay0.output 23).toRat -
        replay0.idealOutputRat 23| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 23 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 23).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 23).toRat +
          ∑ column, (sharedWeightRows 23 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 23 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock05.replay0_coordinate23_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 23) 23 hrow)

theorem replay0_coordinate24_is_bounded :
    |(replay0.output 24).toRat -
        replay0.idealOutputRat 24| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 24 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 24).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 24).toRat +
          ∑ column, (sharedWeightRows 24 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 24 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.replay0_coordinate24_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 24) 24 hrow)

theorem replay0_coordinate25_is_bounded :
    |(replay0.output 25).toRat -
        replay0.idealOutputRat 25| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 25 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 25).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 25).toRat +
          ∑ column, (sharedWeightRows 25 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 25 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.replay0_coordinate25_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 25) 25 hrow)

theorem replay0_coordinate26_is_bounded :
    |(replay0.output 26).toRat -
        replay0.idealOutputRat 26| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 26 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 26).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 26).toRat +
          ∑ column, (sharedWeightRows 26 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 26 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.replay0_coordinate26_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 26) 26 hrow)

theorem replay0_coordinate27_is_bounded :
    |(replay0.output 27).toRat -
        replay0.idealOutputRat 27| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 27 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 27).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 27).toRat +
          ∑ column, (sharedWeightRows 27 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 27 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock06.replay0_coordinate27_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 27) 27 hrow)

theorem replay0_coordinate28_is_bounded :
    |(replay0.output 28).toRat -
        replay0.idealOutputRat 28| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 28 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 28).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 28).toRat +
          ∑ column, (sharedWeightRows 28 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 28 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.replay0_coordinate28_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 28) 28 hrow)

theorem replay0_coordinate29_is_bounded :
    |(replay0.output 29).toRat -
        replay0.idealOutputRat 29| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 29 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 29).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 29).toRat +
          ∑ column, (sharedWeightRows 29 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 29 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.replay0_coordinate29_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 29) 29 hrow)

theorem replay0_coordinate30_is_bounded :
    |(replay0.output 30).toRat -
        replay0.idealOutputRat 30| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 30 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 30).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 30).toRat +
          ∑ column, (sharedWeightRows 30 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 30 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.replay0_coordinate30_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 30) 30 hrow)

theorem replay0_coordinate31_is_bounded :
    |(replay0.output 31).toRat -
        replay0.idealOutputRat 31| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 31 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 31).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 31).toRat +
          ∑ column, (sharedWeightRows 31 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 31 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock07.replay0_coordinate31_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 31) 31 hrow)

theorem replay0_coordinate32_is_bounded :
    |(replay0.output 32).toRat -
        replay0.idealOutputRat 32| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 32 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 32).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 32).toRat +
          ∑ column, (sharedWeightRows 32 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 32 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.replay0_coordinate32_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 32) 32 hrow)

theorem replay0_coordinate33_is_bounded :
    |(replay0.output 33).toRat -
        replay0.idealOutputRat 33| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 33 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 33).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 33).toRat +
          ∑ column, (sharedWeightRows 33 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 33 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.replay0_coordinate33_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 33) 33 hrow)

theorem replay0_coordinate34_is_bounded :
    |(replay0.output 34).toRat -
        replay0.idealOutputRat 34| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 34 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 34).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 34).toRat +
          ∑ column, (sharedWeightRows 34 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 34 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.replay0_coordinate34_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 34) 34 hrow)

theorem replay0_coordinate35_is_bounded :
    |(replay0.output 35).toRat -
        replay0.idealOutputRat 35| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 35 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 35).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 35).toRat +
          ∑ column, (sharedWeightRows 35 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 35 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock08.replay0_coordinate35_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 35) 35 hrow)

theorem replay0_coordinate36_is_bounded :
    |(replay0.output 36).toRat -
        replay0.idealOutputRat 36| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 36 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 36).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 36).toRat +
          ∑ column, (sharedWeightRows 36 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 36 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.replay0_coordinate36_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 36) 36 hrow)

theorem replay0_coordinate37_is_bounded :
    |(replay0.output 37).toRat -
        replay0.idealOutputRat 37| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 37 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 37).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 37).toRat +
          ∑ column, (sharedWeightRows 37 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 37 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.replay0_coordinate37_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 37) 37 hrow)

theorem replay0_coordinate38_is_bounded :
    |(replay0.output 38).toRat -
        replay0.idealOutputRat 38| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 38 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 38).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 38).toRat +
          ∑ column, (sharedWeightRows 38 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 38 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.replay0_coordinate38_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 38) 38 hrow)

theorem replay0_coordinate39_is_bounded :
    |(replay0.output 39).toRat -
        replay0.idealOutputRat 39| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 39 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 39).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 39).toRat +
          ∑ column, (sharedWeightRows 39 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 39 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock09.replay0_coordinate39_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 39) 39 hrow)

theorem replay0_coordinate40_is_bounded :
    |(replay0.output 40).toRat -
        replay0.idealOutputRat 40| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 40 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 40).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 40).toRat +
          ∑ column, (sharedWeightRows 40 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 40 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.replay0_coordinate40_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 40) 40 hrow)

theorem replay0_coordinate41_is_bounded :
    |(replay0.output 41).toRat -
        replay0.idealOutputRat 41| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 41 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 41).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 41).toRat +
          ∑ column, (sharedWeightRows 41 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 41 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.replay0_coordinate41_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 41) 41 hrow)

theorem replay0_coordinate42_is_bounded :
    |(replay0.output 42).toRat -
        replay0.idealOutputRat 42| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 42 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 42).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 42).toRat +
          ∑ column, (sharedWeightRows 42 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 42 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.replay0_coordinate42_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 42) 42 hrow)

theorem replay0_coordinate43_is_bounded :
    |(replay0.output 43).toRat -
        replay0.idealOutputRat 43| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 43 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 43).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 43).toRat +
          ∑ column, (sharedWeightRows 43 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 43 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock10.replay0_coordinate43_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 43) 43 hrow)

theorem replay0_coordinate44_is_bounded :
    |(replay0.output 44).toRat -
        replay0.idealOutputRat 44| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 44 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 44).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 44).toRat +
          ∑ column, (sharedWeightRows 44 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 44 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.replay0_coordinate44_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 44) 44 hrow)

theorem replay0_coordinate45_is_bounded :
    |(replay0.output 45).toRat -
        replay0.idealOutputRat 45| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 45 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 45).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 45).toRat +
          ∑ column, (sharedWeightRows 45 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 45 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.replay0_coordinate45_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 45) 45 hrow)

theorem replay0_coordinate46_is_bounded :
    |(replay0.output 46).toRat -
        replay0.idealOutputRat 46| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 46 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 46).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 46).toRat +
          ∑ column, (sharedWeightRows 46 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 46 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.replay0_coordinate46_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 46) 46 hrow)

theorem replay0_coordinate47_is_bounded :
    |(replay0.output 47).toRat -
        replay0.idealOutputRat 47| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 47 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 47).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 47).toRat +
          ∑ column, (sharedWeightRows 47 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 47 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock11.replay0_coordinate47_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 47) 47 hrow)

theorem replay0_coordinate48_is_bounded :
    |(replay0.output 48).toRat -
        replay0.idealOutputRat 48| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 48 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 48).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 48).toRat +
          ∑ column, (sharedWeightRows 48 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 48 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.replay0_coordinate48_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 48) 48 hrow)

theorem replay0_coordinate49_is_bounded :
    |(replay0.output 49).toRat -
        replay0.idealOutputRat 49| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 49 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 49).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 49).toRat +
          ∑ column, (sharedWeightRows 49 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 49 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.replay0_coordinate49_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 49) 49 hrow)

theorem replay0_coordinate50_is_bounded :
    |(replay0.output 50).toRat -
        replay0.idealOutputRat 50| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 50 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 50).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 50).toRat +
          ∑ column, (sharedWeightRows 50 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 50 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.replay0_coordinate50_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 50) 50 hrow)

theorem replay0_coordinate51_is_bounded :
    |(replay0.output 51).toRat -
        replay0.idealOutputRat 51| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 51 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 51).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 51).toRat +
          ∑ column, (sharedWeightRows 51 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 51 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock12.replay0_coordinate51_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 51) 51 hrow)

theorem replay0_coordinate52_is_bounded :
    |(replay0.output 52).toRat -
        replay0.idealOutputRat 52| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 52 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 52).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 52).toRat +
          ∑ column, (sharedWeightRows 52 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 52 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.replay0_coordinate52_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 52) 52 hrow)

theorem replay0_coordinate53_is_bounded :
    |(replay0.output 53).toRat -
        replay0.idealOutputRat 53| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 53 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 53).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 53).toRat +
          ∑ column, (sharedWeightRows 53 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 53 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.replay0_coordinate53_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 53) 53 hrow)

theorem replay0_coordinate54_is_bounded :
    |(replay0.output 54).toRat -
        replay0.idealOutputRat 54| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 54 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 54).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 54).toRat +
          ∑ column, (sharedWeightRows 54 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 54 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.replay0_coordinate54_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 54) 54 hrow)

theorem replay0_coordinate55_is_bounded :
    |(replay0.output 55).toRat -
        replay0.idealOutputRat 55| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 55 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 55).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 55).toRat +
          ∑ column, (sharedWeightRows 55 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 55 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock13.replay0_coordinate55_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 55) 55 hrow)

theorem replay0_coordinate56_is_bounded :
    |(replay0.output 56).toRat -
        replay0.idealOutputRat 56| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 56 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 56).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 56).toRat +
          ∑ column, (sharedWeightRows 56 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 56 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.replay0_coordinate56_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 56) 56 hrow)

theorem replay0_coordinate57_is_bounded :
    |(replay0.output 57).toRat -
        replay0.idealOutputRat 57| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 57 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 57).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 57).toRat +
          ∑ column, (sharedWeightRows 57 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 57 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.replay0_coordinate57_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 57) 57 hrow)

theorem replay0_coordinate58_is_bounded :
    |(replay0.output 58).toRat -
        replay0.idealOutputRat 58| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 58 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 58).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 58).toRat +
          ∑ column, (sharedWeightRows 58 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 58 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.replay0_coordinate58_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 58) 58 hrow)

theorem replay0_coordinate59_is_bounded :
    |(replay0.output 59).toRat -
        replay0.idealOutputRat 59| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 59 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 59).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 59).toRat +
          ∑ column, (sharedWeightRows 59 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 59 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock14.replay0_coordinate59_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 59) 59 hrow)

theorem replay0_coordinate60_is_bounded :
    |(replay0.output 60).toRat -
        replay0.idealOutputRat 60| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 60 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 60).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 60).toRat +
          ∑ column, (sharedWeightRows 60 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 60 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.replay0_coordinate60_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 60) 60 hrow)

theorem replay0_coordinate61_is_bounded :
    |(replay0.output 61).toRat -
        replay0.idealOutputRat 61| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 61 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 61).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 61).toRat +
          ∑ column, (sharedWeightRows 61 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 61 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.replay0_coordinate61_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 61) 61 hrow)

theorem replay0_coordinate62_is_bounded :
    |(replay0.output 62).toRat -
        replay0.idealOutputRat 62| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 62 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 62).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 62).toRat +
          ∑ column, (sharedWeightRows 62 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 62 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.replay0_coordinate62_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 62) 62 hrow)

theorem replay0_coordinate63_is_bounded :
    |(replay0.output 63).toRat -
        replay0.idealOutputRat 63| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 63 := by
  have hrow :
      |(GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output 63).toRat -
        ((GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias 63).toRat +
          ∑ column, (sharedWeightRows 63 column).toRat *
            (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input column).toRat)| ≤
        GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 63 := by
    simpa [sharedWeightRows,
      replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Output,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias,
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget] using GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureBlock15.replay0_coordinate63_arithmetic
  simpa [replay0] using
    (Float32AffineReplay.ofRows_coordinate_bound
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0Input
      sharedWeightRows
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.sharedBias
      replay0Output
      ((4830463782067867 : ℚ) / 1180591620717411303424) (GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget 63) 63 hrow)

theorem replay0_all_coordinates_are_bounded : ∀ row,
    |(replay0.output row).toRat -
        replay0.idealOutputRat row| ≤
      GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget row := by
  intro row
  fin_cases row
  · exact replay0_coordinate0_is_bounded
  · exact replay0_coordinate1_is_bounded
  · exact replay0_coordinate2_is_bounded
  · exact replay0_coordinate3_is_bounded
  · exact replay0_coordinate4_is_bounded
  · exact replay0_coordinate5_is_bounded
  · exact replay0_coordinate6_is_bounded
  · exact replay0_coordinate7_is_bounded
  · exact replay0_coordinate8_is_bounded
  · exact replay0_coordinate9_is_bounded
  · exact replay0_coordinate10_is_bounded
  · exact replay0_coordinate11_is_bounded
  · exact replay0_coordinate12_is_bounded
  · exact replay0_coordinate13_is_bounded
  · exact replay0_coordinate14_is_bounded
  · exact replay0_coordinate15_is_bounded
  · exact replay0_coordinate16_is_bounded
  · exact replay0_coordinate17_is_bounded
  · exact replay0_coordinate18_is_bounded
  · exact replay0_coordinate19_is_bounded
  · exact replay0_coordinate20_is_bounded
  · exact replay0_coordinate21_is_bounded
  · exact replay0_coordinate22_is_bounded
  · exact replay0_coordinate23_is_bounded
  · exact replay0_coordinate24_is_bounded
  · exact replay0_coordinate25_is_bounded
  · exact replay0_coordinate26_is_bounded
  · exact replay0_coordinate27_is_bounded
  · exact replay0_coordinate28_is_bounded
  · exact replay0_coordinate29_is_bounded
  · exact replay0_coordinate30_is_bounded
  · exact replay0_coordinate31_is_bounded
  · exact replay0_coordinate32_is_bounded
  · exact replay0_coordinate33_is_bounded
  · exact replay0_coordinate34_is_bounded
  · exact replay0_coordinate35_is_bounded
  · exact replay0_coordinate36_is_bounded
  · exact replay0_coordinate37_is_bounded
  · exact replay0_coordinate38_is_bounded
  · exact replay0_coordinate39_is_bounded
  · exact replay0_coordinate40_is_bounded
  · exact replay0_coordinate41_is_bounded
  · exact replay0_coordinate42_is_bounded
  · exact replay0_coordinate43_is_bounded
  · exact replay0_coordinate44_is_bounded
  · exact replay0_coordinate45_is_bounded
  · exact replay0_coordinate46_is_bounded
  · exact replay0_coordinate47_is_bounded
  · exact replay0_coordinate48_is_bounded
  · exact replay0_coordinate49_is_bounded
  · exact replay0_coordinate50_is_bounded
  · exact replay0_coordinate51_is_bounded
  · exact replay0_coordinate52_is_bounded
  · exact replay0_coordinate53_is_bounded
  · exact replay0_coordinate54_is_bounded
  · exact replay0_coordinate55_is_bounded
  · exact replay0_coordinate56_is_bounded
  · exact replay0_coordinate57_is_bounded
  · exact replay0_coordinate58_is_bounded
  · exact replay0_coordinate59_is_bounded
  · exact replay0_coordinate60_is_bounded
  · exact replay0_coordinate61_is_bounded
  · exact replay0_coordinate62_is_bounded
  · exact replay0_coordinate63_is_bounded

theorem replay0_is_accepted : replay0.check = true := by
  refine replay0.check_of_coordinate_bounds
    GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget (by norm_num) (by norm_num) ?_
    replay0_all_coordinates_are_bounded ?_
  · change 0 ≤ ((4830463782067867 : ℚ) / 1180591620717411303424)
    norm_num
  · change (∑ row, GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget row) ≤ ((4830463782067867 : ℚ) / 1180591620717411303424)
    norm_num [GeneratedAuthenticatedAffineReplaySite0Invocation0FixtureCommon.replay0CoordinateBudget, Fin.sum_univ_succ]

def certificateBatch : Float32AffineReplayBatch 64 256 where
  expectedCount := 1
  entries := [replay0]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32AffineReplayBatch.check,
    replay0_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end GeneratedAuthenticatedAffineReplaySite0Invocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
