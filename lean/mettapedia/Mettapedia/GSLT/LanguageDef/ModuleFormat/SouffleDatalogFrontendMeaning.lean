import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogNormalizationReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAgreement
import Mettapedia.Languages.Datalog.IRCodecProgramInverse

/-! The ordinary frontend agrees with the authored structural elaboration
and independent literal/name meaning. Full text readback, selected source
constructor data and the canonical semantic program payload remain distinct. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

def Denotes (environment : Engine.RelationEnv) (source : Pattern) (program : Mettapedia.Languages.Datalog.Program) : Prop :=
  ∃ projected, ReferenceStep.Step environment ProgramProjection.language (ProgramProjection.Program.call source) projected ∧
    Normalizes projected (IRCodec.program program)

theorem read_sound (environment : Engine.RelationEnv) (input : String) (tree : Frontend.SourceAtom)
    (program : Mettapedia.Languages.Datalog.Program)
    (accepted : Frontend.read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program) :
    ∃ source, SelectedReader.core? input tree = some source ∧ CorePrinter.printText? "DlProgram" source = some input ∧
      Denotes environment source program := by
  obtain ⟨source, sourceRead, textRead⟩ := Frontend.read_preserves_input input tree program accepted
  unfold Frontend.read at accepted
  simp only [sourceRead] at accepted
  cases projectedRead : ProgramProjection.Reference.projectProgram? source with
  | none => simp [projectedRead] at accepted
  | some projected =>
    simp only [projectedRead] at accepted
    cases normalizedRead : Frontend.normalize? projected with
    | none => simp [normalizedRead] at accepted
    | some normalized =>
      simp only [normalizedRead] at accepted
      cases decoded : IRCodec.program? normalized with
      | none => simp [decoded] at accepted
      | some actual =>
        simp only [decoded] at accepted
        change Except.ok actual = Except.ok program at accepted
        have same : actual = program := Except.ok.inj accepted
        subst actual
        refine ⟨source,sourceRead,textRead,projected,
          ProgramProjection.Program.step_of_reference environment source projected projectedRead,?_⟩
        rw [IRCodec.program_inverse normalized program decoded]
        exact normalization_sound projected normalized normalizedRead

theorem read_complete (environment : Engine.RelationEnv) (input : String) (tree : Frontend.SourceAtom)
    (source : Pattern) (program : Mettapedia.Languages.Datalog.Program)
    (sourceRead : SelectedReader.core? input tree = some source)
    (meaning : Denotes environment source program) :
    Frontend.read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program := by
  obtain ⟨projected,step,normalized⟩ := meaning
  have projectedRead := (ProgramProjection.Program.reference_exact environment source projected).mp step
  have normalizedRead := normalization_complete normalized
  simp only [Frontend.read,sourceRead,projectedRead,normalizedRead,IRCodec.program_roundtrip]
  rfl

theorem read_exact (environment : Engine.RelationEnv) (input : String) (tree : Frontend.SourceAtom)
    (program : Mettapedia.Languages.Datalog.Program) :
    Frontend.read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program ↔
      ∃ source, SelectedReader.core? input tree = some source ∧ Denotes environment source program := by
  constructor
  · intro accepted
    obtain ⟨source, read, _, meaning⟩ := read_sound environment input tree program accepted
    exact ⟨source, read, meaning⟩
  · rintro ⟨source,sourceRead,meaning⟩
    exact read_complete environment input tree source program sourceRead meaning

theorem denotes_functional (environment : Engine.RelationEnv) (source : Pattern)
    (first second : Mettapedia.Languages.Datalog.Program) (left : Denotes environment source first) (right : Denotes environment source second) :
    first = second := by
  obtain ⟨firstData,firstStep,firstReading⟩ := left
  obtain ⟨secondData,secondStep,secondReading⟩ := right
  have same := ProgramProjection.Program.functional environment source firstData secondData firstStep secondStep
  subst secondData
  exact IRCodec.program_injective (normalization_functional firstData _ _ firstReading secondReading)

#print axioms read_sound
#print axioms read_complete
#print axioms read_exact
#print axioms denotes_functional

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
