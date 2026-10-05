import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNativeControls

/-!
# Joined unary execution and source-history controls

A retained closed definition can fetch, call and repeat through the actual
private-session lowering. Its compiled loop returns to the supplied starting
configuration and charges every administrative communication. Two genuine
equal-endpoint carrier events have distinct owners; erasing those owners before
compilation loses that distinction. Source history must therefore remain
available beside the compiled execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNativeControls

/-- The actual closed source loop has a unary path at the same literal endpoint. -/
noncomputable def unaryLoop : ExecutionPath (operationalTheory [Srt.nm])
    (compileUnary loopingDefinition closedNames returnName)
    (compileUnary loopingDefinition closedNames returnName) :=
  compilePath closedNames returnName sourceLoop

theorem loop_counts_administration : 2 ≤ unaryLoop.length ∧ unaryLoop.length ≤ 8 :=
  compilePath_bounds closedNames returnName sourceLoop

/-- Every finite prefix of persistent self-application compiles with a
positive account; bounds are over the complete actual unary execution. -/
theorem repeated_loop_bounds (count : Nat) :
    2 * count ≤ (compilePath closedNames returnName (repeatedLoop count)).length ∧
      (compilePath closedNames returnName (repeatedLoop count)).length ≤ 8 * count := by
  have bounds := compilePath_bounds closedNames returnName (repeatedLoop count)
  have length := repeatedLoop_length count
  constructor
  · exact Nat.le_trans (Nat.le_of_eq length.symm) bounds.1
  · calc
      _ ≤ 4 * (repeatedLoop count).length := bounds.2
      _ = 4 * (2 * count) := congrArg (fun n => 4 * n) length
      _ = 8 * count := (Nat.mul_assoc 4 2 count).symm

theorem source_fetch_has_unary_native_reachability :
    (semanticDiamond (operationalTheory [Srt.nm]).closure
      (classPredicate (compileUnary releasedCall closedNames returnName))).1
      (compileUnary loopingDefinition closedNames returnName) :=
  step_reaches_native first_fetch closedNames returnName

def value : Expr [Srt.nm] := .lam (.var .zero)
def twoDeclarations : Expr [Srt.nm] :=
  .carrier .zero value (.carrier .zero value (.var .zero))
def remainingDeclaration : Expr [Srt.nm] := .carrier .zero value value

def outerCertificate : NamePassing.Environment.EventCertificate
    .carrierFetch twoDeclarations remainingDeclaration :=
  .carrierFetch .zero value (.carrier .zero value (.here .zero value))

def innerCertificate : NamePassing.Environment.EventCertificate
    .carrierFetch twoDeclarations remainingDeclaration :=
  .carrier .zero value (.carrierFetch .zero value (.here .zero value))

def outerHistory : OccurrencePath (NamePassingEnvironmentOrigins.events [Srt.nm])
    twoDeclarations remainingDeclaration :=
  .cons ⟨outerCertificate.origin, outerCertificate, rfl⟩ (.refl _)

def innerHistory : OccurrencePath (NamePassingEnvironmentOrigins.events [Srt.nm])
    twoDeclarations remainingDeclaration :=
  .cons ⟨innerCertificate.origin, innerCertificate, rfl⟩ (.refl _)

/-- This is actual source occurrence multiplicity, witnessed by different
constructor derivations for the independently authored environment relation. -/
theorem source_owners_distinct : outerHistory.sites ≠ innerHistory.sites := by
  intro same
  have owners := congrArg (List.map NamePassing.Environment.EventOrigin.owner) same
  change [[]] = [[NamePassing.Environment.Position.carrierBody]] at owners
  cases owners

/-- The occurrence erasure really does lose the selected declaration owner. -/
theorem erased_paths_equal :
    NamePassingEnvironmentOrigins.erasePath outerHistory =
      NamePassingEnvironmentOrigins.erasePath innerHistory := rfl

def references : Ren sig [Srt.nm] [Srt.nm, Srt.nm] := fun _ name => .succ name
def result : Var [Srt.nm, Srt.nm] .nm := .zero

/-- Compiling erased histories cannot recover information already erased. -/
theorem erased_compiled_histories_equal :
    compileHistory references result outerHistory =
      compileHistory references result innerHistory := rfl

theorem actual_owner_history_compiles :
    1 ≤ (compileHistory references result outerHistory).length ∧
      (compileHistory references result outerHistory).length ≤ 4 :=
  compileHistory_bounds references result outerHistory

/-- A target execution alone is not a declaration-owner certificate. -/
theorem no_owner_readout_from_erased_execution :
    ¬ ∃ readout : ExecutionPath (operationalTheory [Srt.nm, Srt.nm])
        (compileUnary twoDeclarations references result)
        (compileUnary remainingDeclaration references result) →
          List NamePassing.Environment.EventOrigin,
      readout (compileHistory references result outerHistory) = outerHistory.sites ∧
        readout (compileHistory references result innerHistory) = innerHistory.sites := by
  rintro ⟨readout, outer, inner⟩
  have same := congrArg readout erased_compiled_histories_equal
  exact source_owners_distinct (outer.symm.trans (same.trans inner))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic.Controls
