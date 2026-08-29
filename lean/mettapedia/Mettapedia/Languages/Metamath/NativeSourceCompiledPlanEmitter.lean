import Mettapedia.Languages.Metamath.NativeSourceCompiledPlan

/-!
# Emit the admitted native-source compiled-plan canary

This executable bridge writes the exact `CGP1` packet produced by the generic
validated-presentation compiler to standard output.  Structural admission is
part of emission: an unsupported or malformed compiler result produces no
packet and exits with an error.
-/

open Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
open Mettapedia.Languages.Metamath.NativeSourceCalculus

def main : IO Unit := do
  match compileValidatedBytes? validatedDefinition with
  | none =>
      throw (IO.userError "compiled packet failed structural admission")
  | some bytes =>
      let stdout <- IO.getStdout
      stdout.write bytes.toByteArray
