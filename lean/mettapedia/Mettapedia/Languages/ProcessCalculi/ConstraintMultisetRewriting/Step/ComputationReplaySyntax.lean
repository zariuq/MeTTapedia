import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode

/-!
# Replayable structural instructions retain original equation positions

The existing table and structural decoders supply the replay algorithm.
The adapter converts their accepted finite syntax into the focused event
representation. Original codes, including duplicate table ordinals, remain
available as execution provenance. Head replay uses an explicitly supplied
decision procedure; the semantic computation bridge does not require it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplaySyntax

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open AlgebraicSchema AlgebraicParallel ComputationSyntax

variable {Head : Type} {rules : Rules Head} (presentation : SchemaPresentation rules)
  (table : SchemaTable Head)
  (same : ∀ {arity : Nat} (left right : Tm Head arity), presentation.schema left right ↔ table.family left right)

include presentation same in
theorem presents {n : Nat} {left right : Tm Head n} :
    rules.computation.step left right ↔ SchemaStep table.family left right := by
  constructor
  · intro step
    obtain ⟨arity, source, target, arguments, selected, rfl, rfl⟩ := presentation.cover step
    exact .instantiate ((same source target).mp selected) arguments
  · intro step
    cases step with
    | instantiate selected arguments => exact presentation.sound ((same _ _).mpr selected) arguments

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  SchemaTableConversionCode.presentedDecoder table rules.computation (presents presentation table same)

theorem selected (index : Fin table.length) : table.family (table.get index).2.1 (table.get index).2.2 := by
  have member := List.get_mem table index
  rcases row : table.get index with ⟨arity, left, right⟩
  change (⟨arity, left, right⟩ : Σ a : Nat, Tm Head a × Tm Head a) ∈ table
  rwa [row] at member

def rootEvent {n : Nat} (code : SchemaTableConversionCode.Code Head n) : Option (Event presentation n) :=
  (SchemaTableConversionCode.decodeInstance table (fun _ => true) code).map fun parsed =>
    ⟨n, .hole, .declared (table.get parsed.index).2.1 (table.get parsed.index).2.2
      ((same _ _).mpr (selected table parsed.index)) parsed.substitution⟩

variable [DecidableRel rules.headEq]

def decodeEvent : {n : Nat} →
    StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n → Option (Event presentation n)
  | _, .betaPi body argument => some ⟨_, .hole, .beta body argument⟩
  | _, .betaSigmaFst first second => some ⟨_, .hole, .first first second⟩
  | _, .betaSigmaSnd first second => some ⟨_, .hole, .second first second⟩
  | _, .head left right => if h : rules.headEq left right then some ⟨_, .hole, .head left right h⟩ else none
  | _, .root code => rootEvent presentation table same code
  | _, .congPiDom code codomain => (decodeEvent code).map fun e => ⟨_, .piDom e.context codomain, e.action⟩
  | _, .congPiCod domain code => (decodeEvent code).map fun e => ⟨_, .piCod domain e.context, e.action⟩
  | _, .congSigmaDom code codomain => (decodeEvent code).map fun e => ⟨_, .sigmaDom e.context codomain, e.action⟩
  | _, .congSigmaCod domain code => (decodeEvent code).map fun e => ⟨_, .sigmaCod domain e.context, e.action⟩
  | _, .congIdTy code left right => (decodeEvent code).map fun e => ⟨_, .idType e.context left right, e.action⟩
  | _, .congIdLeft type code right => (decodeEvent code).map fun e => ⟨_, .idLeft type e.context right, e.action⟩
  | _, .congIdRight type left code => (decodeEvent code).map fun e => ⟨_, .idRight type left e.context, e.action⟩
  | _, .congLam code => (decodeEvent code).map fun e => ⟨_, .lam e.context, e.action⟩
  | _, .congAppFun code argument => (decodeEvent code).map fun e => ⟨_, .appFun e.context argument, e.action⟩
  | _, .congAppArg function code => (decodeEvent code).map fun e => ⟨_, .appArg function e.context, e.action⟩
  | _, .congPairFst code second => (decodeEvent code).map fun e => ⟨_, .pairFst e.context second, e.action⟩
  | _, .congPairSnd first code => (decodeEvent code).map fun e => ⟨_, .pairSnd first e.context, e.action⟩
  | _, .congFst code => (decodeEvent code).map fun e => ⟨_, .fst e.context, e.action⟩
  | _, .congSnd code => (decodeEvent code).map fun e => ⟨_, .snd e.context, e.action⟩
  | _, .congRefl code => (decodeEvent code).map fun e => ⟨_, .refl e.context, e.action⟩

theorem decode_agrees {n : Nat}
    (code : StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n) :
    (decodeEvent presentation table same code).map (fun event => (event.source, event.target)) =
      StructuralConversionCode.StepCode.decode rules.headEq (decoder presentation table same).decode code := by
  induction code
  case betaPi => rfl
  case betaSigmaFst => rfl
  case betaSigmaSnd => rfl
  case head left right =>
    by_cases h : rules.headEq left right <;>
      simp only [decodeEvent, StructuralConversionCode.StepCode.decode, h, dite_true, dite_false,
        if_true, if_false, Option.map_some, Option.map_none, Event.source, Event.target,
        Context.plug, Action.source, Action.target]
  case root code =>
    simp only [decodeEvent, rootEvent, StructuralConversionCode.StepCode.decode, decoder,
      SchemaTableConversionCode.presentedDecoder, SchemaTableConversionCode.decode, Option.map_map]
    rfl
  all_goals
    rename_i ih
    simp only [decodeEvent, StructuralConversionCode.StepCode.decode, StructuralConversionCode.mapEndpoints]
    rw [← ih]
    simp only [Option.map_map]
    rfl

theorem decoded_iff {n : Nat}
    (code : StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n)
    {left right : Tm Head n} :
    StructuralConversionCode.StepCode.decode rules.headEq (decoder presentation table same).decode code = some (left, right) ↔
      ∃ event, decodeEvent presentation table same code = some event ∧ event.source = left ∧ event.target = right := by
  rw [← decode_agrees]
  cases parsed : decodeEvent presentation table same code with
  | none => simp
  | some event => simp [Prod.mk.injEq]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplaySyntax

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplaySyntax.decode_agrees
