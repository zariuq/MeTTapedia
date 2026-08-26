import Mettapedia.Languages.Metamath.MM2TransformationCanary

namespace Mettapedia.OSLF.Tools.ExportMetamathMM2Canary

open Mettapedia.Languages.Metamath.MM2TransformationCanary

private def emit (rendered : Option String)
    (outputPath : Option String) : IO UInt32 := do
  match rendered with
  | some output =>
      match outputPath with
      | none =>
          IO.print output
          pure 0
      | some outputPath =>
          IO.FS.writeFile outputPath output
          pure 0
  | none =>
      IO.eprintln "the Metamath-to-MM2 canary is outside the ordinary MM2 surface"
      pure 1

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => emit renderHypothesisCanary? none
  | [outputPath] => emit renderHypothesisCanary? (some outputPath)
  | ["positive", outputPath] =>
      emit renderHypothesisCanary? (some outputPath)
  | ["severed", outputPath] =>
      emit renderSeveredCanary? (some outputPath)
  | ["expected", outputPath] =>
      emit (renderAcceptedFact?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["assertion-positive", outputPath] =>
      emit renderAssertionCanary? (some outputPath)
  | ["assertion-severed", outputPath] =>
      emit renderAssertionSeveredCanary? (some outputPath)
  | ["assertion-expected", outputPath] =>
      emit (renderAssertionAcceptedFact?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["assertion-repeated", outputPath] =>
      emit renderRepeatedAssertionCanary? (some outputPath)
  | ["assertion-repeated-expected", outputPath] =>
      emit (renderRepeatedAssertionAcceptedFact?.map
        (fun line => line ++ "\n")) (some outputPath)
  | ["essential-positive", outputPath] =>
      emit renderEssentialCanary? (some outputPath)
  | ["essential-wrong", outputPath] =>
      emit renderEssentialWrongCanary? (some outputPath)
  | ["essential-expected", outputPath] =>
      emit (renderEssentialAcceptedFact?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["dv-positive", outputPath] =>
      emit renderDVCanary? (some outputPath)
  | ["dv-missing-caller", outputPath] =>
      emit renderDVMissingCaller? (some outputPath)
  | ["dv-expected", outputPath] =>
      emit (renderDVAcceptedFact?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["dv-cross-product", outputPath] =>
      emit renderDVCrossProduct? (some outputPath)
  | ["dv-cross-product-missing-last", outputPath] =>
      emit renderDVCrossProductMissingLast? (some outputPath)
  | ["dv-cross-product-expected", outputPath] =>
      emit (renderDVCrossProductExpected?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["body-match-positive", outputPath] =>
      emit renderBodyMatchPositive? (some outputPath)
  | ["body-match-wrong", outputPath] =>
      emit renderBodyMatchWrong? (some outputPath)
  | ["body-match-expected", outputPath] =>
      emit (renderBodyMatchSuccess?.map (fun line => line ++ "\n"))
        (some outputPath)
  | ["body-build-positive", outputPath] =>
      emit renderBodyBuildPositive? (some outputPath)
  | ["body-build-severed", outputPath] =>
      emit renderBodyBuildSevered? (some outputPath)
  | ["body-build-expected", outputPath] =>
      emit (renderBodyBuildExpected?.map (fun line => line ++ "\n"))
        (some outputPath)
  | _ =>
      IO.eprintln
        "usage: ExportMetamathMM2Canary [positive|severed|expected|assertion-positive|assertion-severed|assertion-expected|assertion-repeated|assertion-repeated-expected|essential-positive|essential-wrong|essential-expected|dv-positive|dv-missing-caller|dv-expected|dv-cross-product|dv-cross-product-missing-last|dv-cross-product-expected|body-match-positive|body-match-wrong|body-match-expected|body-build-positive|body-build-severed|body-build-expected] output.mm2"
      pure 1

end Mettapedia.OSLF.Tools.ExportMetamathMM2Canary

def main (args : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportMetamathMM2Canary.run args
