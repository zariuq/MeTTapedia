import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeZero
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeEnvironment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.DirectedSyntax

/-!
# Actual primitive and authored root computations in the compiled source program

Beta and schema instantiation invoke the finite substitution helper program.
Projection rules are literal source equations. The selected native table entry
is the one supplied by the development compiler, with no semantic step used as
an admission predicate of the target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
namespace RootRewrites

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization AlgebraicSchema AlgebraicParallel
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open RuleBuilder RuleInstances

variable {dev : Definitions.Development} (built : Compiled dev)

theorem fixed_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.fixed) :
    rule ∈ built.rules := by simp [Compiled.rules, ProgramLayout.rows, member]

theorem helper_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ RuntimeSubstitution.rules) :
    rule ∈ built.rules := by simp [Compiled.rules, ProgramLayout.rows, member]

theorem authored_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ built.authored) :
    rule ∈ built.rules := by simp [Compiled.rules, ProgramLayout.rows, member]

theorem primitive_member {rule : ProgramBinders.Equation MSig [] ()} (member : rule ∈ ContextRules.primitive) :
    rule ∈ built.rules := fixed_member built (by simp [ContextRules.fixed, member])

theorem beta {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) (continuation : MClosed) :
    Steps built.rules (rootC (encodeTm (.app (.lam body) argument)) continuation)
      (resumeC (encodeTm (inst0 argument body)) continuation) := by
  have first := RuleInstances.template
    (ContextRules.active (n := 3) "hd-root" [node "prime-tm-app" [node "prime-tm-lam" [slot 0], slot 1], slot 2])
    (ContextRules.active "hd-subst-zero" [slot 1, literal (encodeNat 0), slot 0, slot 2])
    (primitive_member built (by simp [ContextRules.primitive])) ![encodeTm body, encodeTm argument, continuation]
  have entry : ProgramBinders.Rewrites built.rules.get
      (rootC (encodeTm (.app (.lam body) argument)) continuation)
      (substituteZeroC (encodeTm argument) 0 (encodeTm body) continuation) := by
    simpa [rootC, substituteZeroC, activeC, ContextRules.active] using first
  have helper := RuleInstances.steps_mono (fun rule member => helper_member built member)
    (RuntimeSubstitution.zero_runs (rawTm argument) 0 (rawTm body) continuation)
  have result : Steps built.rules (substituteZeroC (encodeTm argument) 0 (encodeTm body) continuation)
      (resumeC (encodeTm (inst0 argument body)) continuation) := by
    simpa only [quoteRaw_rawTm, quoteRaw_substituteZero] using helper
  exact (Relation.ReflTransGen.single entry).trans result

theorem first {n : Nat} (left right : Tower.Tm n) (continuation : MClosed) :
    Steps built.rules (rootC (encodeTm (.fst (.pair left right))) continuation)
      (resumeC (encodeTm left) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-root" [node "prime-tm-fst" [node "prime-tm-pair" [slot 0, slot 1]], slot 2])
    (ContextRules.active "hd-resume" [slot 0, slot 2])
    (primitive_member built (by simp [ContextRules.primitive])) ![encodeTm left, encodeTm right, continuation]
  exact .single (by simpa [rootC, resumeC, activeC, ContextRules.active] using step)

theorem second {n : Nat} (left right : Tower.Tm n) (continuation : MClosed) :
    Steps built.rules (rootC (encodeTm (.snd (.pair left right))) continuation)
      (resumeC (encodeTm right) continuation) := by
  have step := RuleInstances.template
    (ContextRules.active (n := 3) "hd-root" [node "prime-tm-snd" [node "prime-tm-pair" [slot 0, slot 1]], slot 2])
    (ContextRules.active "hd-resume" [slot 1, slot 2])
    (primitive_member built (by simp [ContextRules.primitive])) ![encodeTm left, encodeTm right, continuation]
  exact .single (by simpa [rootC, resumeC, activeC, ContextRules.active] using step)

theorem declared {slots ambient : Nat} (left right : Tower.Tm slots)
    (selected : (⟨slots, (left, right)⟩ : Σ k : Nat, Tower.Tm k × Tower.Tm k) ∈
      Vectors.vectorEquations ++ built.nativeRows)
    (substitution : Sub Tower.Head slots ambient) (continuation : MClosed) :
    Steps built.rules (rootC (encodeTm (subst substitution left)) continuation)
      (resumeC (encodeTm (subst substitution right)) continuation) := by
  obtain ⟨rule, member, compiled⟩ := RowCompilation.member built.compiled selected
  have first := RuleInstances.of_member (authored_member built member)
    (RowInstances.compiled_row_instance ⟨slots, (left, right)⟩ compiled substitution continuation)
  have covered : DeclarationCheck.coveredB left right = true := by
    unfold RowCompiler.row at compiled
    split at compiled
    · assumption
    · cases compiled
  have helper := RuleInstances.steps_mono (fun rule member => helper_member built member)
    (RuntimeSubstitution.scoped_environment_runs (RowInstances.padded left substitution) right continuation)
  have helper' : Steps built.rules
      (substituteEnvironmentC (environmentC (DataEmbedding.rawEnvironment (RowInstances.padded left substitution)))
        (encodeTm right) continuation)
      (resumeC (encodeTm (subst substitution right)) continuation) := by
    simpa only [RuntimeSubstitution.encodeRawEnv_environmentC, RowInstances.padded_right left right substitution covered]
      using helper
  exact (Relation.ReflTransGen.single first).trans helper'

def presentation : SchemaPresentation (Definitions.devPackage dev built.nativeRows) :=
  DeclarationCheck.checkedPresentation (Definitions.devBase dev) (by intro n left right impossible; exact impossible)
    (Vectors.vectorEquations ++ built.nativeRows)

theorem action {n : Nat} (operation : ComputationSyntax.Action (presentation built) n)
    (allowed : DirectedSyntax.allowed operation = true) (continuation : MClosed) :
    Steps built.rules (rootC (encodeTm operation.source) continuation)
      (resumeC (encodeTm operation.target) continuation) := by
  cases operation with
  | beta body argument => exact beta built body argument continuation
  | first left right => exact first built left right continuation
  | second left right => exact second built left right continuation
  | head left right same => cases allowed
  | declared left right selected substitution => exact declared built left right selected substitution continuation

end RootRewrites
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
