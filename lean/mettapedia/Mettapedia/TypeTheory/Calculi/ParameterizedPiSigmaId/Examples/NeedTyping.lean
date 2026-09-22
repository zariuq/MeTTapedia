import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton

/-! # Typed need references and a wrong-handle counterexample -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedNeedComputation
open ScopedComputation (OperationSignature)

namespace Examples

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def operationSignature : OperationSignature Tower.Head Empty where
  input operation := nomatch operation
  output operation := nomatch operation

def context : Tower.Ctx 1 := .snoc .nil ground

def noNeeds : Fin 0 → Tower.Tm 1 := Fin.elim0

def identityFamily : Tower.Tm 2 := .id ground (.var 0) (.var 0)

theorem sigma_formed :
    FormationSensitive.Typing Tower.rules context (.sigma ground identityFamily)
      (sortTm (.max Tower.zero Tower.zero)) :=
  .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

/-- The second force is below a native binder. It still refers to the same
need coordinate, while the returned reflexivity uses the first selected
native value at de Bruijn index one. -/
def boundBody : Code Tower.Head Empty Bool 1 1 :=
  .sequenceSigma (.force 0)
    (.sequence (.force 0) (.returnValue (.refl (.var 1))))

def source : Code Tower.Head Empty Bool 1 0 :=
  .letNeed (.emit true (.returnValue (.var 0))) boundBody

theorem boundBody_typing :
    Typing Tower.rules operationSignature context (extendNeedTypes ground noNeeds)
      boundBody (.sigma ground identityFamily) := by
  apply Typing.sequenceSigma sigma_formed (.sort _) (.force 0)
  apply Typing.sequence (A := ground) (B := identityFamily)
  · exact .headType .legacyGround
  · exact .sort Tower.zero
  · exact .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)
  · exact .sort Tower.zero
  · exact .force 0
  · exact .returnValue (.reflIntro (.var 1))

theorem source_typing :
    Typing Tower.rules operationSignature context noNeeds source (.sigma ground identityFamily) :=
  .letNeed (.headType .legacyGround) (.sort Tower.zero) sigma_formed (.sort _)
    (.emit (.returnValue (.var 0))) boundBody_typing

theorem source_judgment :
    Judgment Tower.rules operationSignature context noNeeds source (.sigma ground identityFamily) :=
  ⟨.snoc .nil (.headType .legacyGround) (.sort Tower.zero),
    (fun index => Fin.elim0 index), source_typing⟩

def firstTypes : Fin 1 → Tower.Tm 1 := fun _ => ground

/-- Both target handle types are genuine native types, but their coordinates
are intentionally different from the source coordinate. -/
def secondTypes : Fin 2 → Tower.Tm 1 :=
  Fin.cases (.pi ground ground) (fun _ => ground)

theorem secondTypes_formed : NeedFormation Tower.rules context secondTypes := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact ⟨.sort (.max Tower.zero Tower.zero), .sort _,
      .piForm (.headType .legacyGround) (.sort Tower.zero)
        (.headType .legacyGround) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)⟩
  · intro prior
    exact ⟨.sort Tower.zero, .sort _, .headType .legacyGround⟩

theorem correctly_renamed_force :
    Typing Tower.rules operationSignature context secondTypes
      (.force 1 : Code Tower.Head Empty Bool 1 2) ground := by
  have original : Typing Tower.rules operationSignature context firstTypes
      (.force 0 : Code Tower.Head Empty Bool 1 1) ground := .force 0
  exact original.renameHandles (ρ := fun _ => 1) (fun _ => rfl)

/-- Merely reusing coordinate zero fails the actual computation typing,
including its conversion tails, despite formation of both target types. -/
theorem incorrect_handle_not_admitted :
    ¬ Typing Tower.rules operationSignature context secondTypes
      (.force 0 : Code Tower.Head Empty Bool 1 2) ground := by
  intro typing
  exact TowerConversionSkeleton.not_conv_pi_head ground ground .legacyGround
    (typing.force_conversion rfl)

#print axioms source_judgment
#print axioms secondTypes_formed
#print axioms correctly_renamed_force
#print axioms incorrect_handle_not_admitted

end Examples

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedNeedComputation
