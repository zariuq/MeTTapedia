import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Strict

/-!
# What the sealed carrier excludes

The source of every theorem of this folder is the calculus on closed processes whose quotes are
sealed (`RhoProcess`: a binder never reaches inside a quote). Every process written with the syntax
of the 2005 paper's section 2 has a sealed representative there, since a name inside a quote body is
never a bound occurrence (quote bodies are impervious to substitution, §2.0.4). What lies outside is
a quote body that follows a bound name: the derived names that the paper's own translation of the
π-calculus builds from received names (its §5.4, `n_l = @(n[n])` under `n'(n)`).

**The datum** (the smallest process of that shape, `@0(n).@(n!(*n))!(0)`):

* it is not a closed process of the carrier: its quote contains the bound index
  (`derived_not_sealed`, `derived_not_in_carrier`);
* the translation on syntax still applies to it (`derived_translates`);
* on the step, receiving `q` makes, by ordinary instantiation, the output on the derived name
  `@(@q!(q))` (`derived_by_instantiation`), and two receptions give two different channels
  (`derived_follows`): the derived name follows the received one, as §5.4 needs;
* the calculus's substitution as the paper defines it in §2.7, and as the tree implements it, leaves
  the quote alone with the bound index inside (`derived_by_substitution`): its contractum is not a
  closed process (`substitution_leaves_carrier`), while the made row of the step is closed
  (`instantiation_stays_closed`).

**So the first half does not extend there by this translation**: on this process the calculus's
reduction (published substitution) leaves the closed processes, the step's does not, and the two
results are different terms. Operational correspondence for the published substitution is not
available beyond the sealed carrier. Whether the instantiation reading is the one the paper's §5.4
needs is a different question: Lybech (EPTCS 2022) shows that the paper's correctness claim for its
§5.4 encoding fails; nothing here claims that the step repairs that encoding.

Just outside the carrier the two can agree (`ByInstantiation.quote_drop_of_bound_name`, `@(*y)!(0)`),
and with two twins under a quote they differ (`ByInstantiation.outside_the_carrier`). Sealing is
sufficient for the correspondence; that the two agree on some processes outside it rests on that one
example, and which processes outside the carrier correspond is not characterized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess)
open ByInstantiation (sig G Closed read inputT outputT zeroT quoteT)

/-- `@(n!(*n))!(0)` with `n` bound: an output on the name derived from the received name. -/
def derivedOutput : G [.nm, .pr] .pr :=
  outputT (quoteT (outputT ByInstantiation.nameVar ByInstantiation.twinVar)) zeroT

/-- `@0(n).@(n!(*n))!(0)` as a pattern of the source syntax. -/
def derivedProcess : Pattern := read (inputT ByInstantiation.nameZero derivedOutput)

/-- **The quote of the continuation contains the bound index.** -/
theorem derived_not_sealed : binderSafeAt "NQuote" 1 (read derivedOutput) = false := by
  decide

/-- **The process is not a closed process of the sealed carrier**: no process of the carrier has it as
its pattern. -/
theorem derived_not_in_carrier (P : RhoProcess) : P.1 ≠ derivedProcess := by
  intro same
  have sealed := ((rhoClosedTermWellSorted_process_iff _).mp P.2).2
  rw [same] at sealed
  revert sealed
  decide

/-- **The translation on syntax applies to it**: its twin term is the input with the derived output as
continuation. -/
theorem derived_translates :
    ByInstantiation.toTwin 0 .pr derivedProcess = some (inputT ByInstantiation.nameZero derivedOutput) :=
  ByInstantiation.toTwin_read _ 0 rfl

/-- **Ordinary instantiation makes the derived name of the received process**: receiving `q`, the
output is on `@(@q!(q))`. -/
theorem derived_by_instantiation (q : G [] .pr) :
    bind (ByInstantiation.received q) derivedOutput = outputT (quoteT (outputT (quoteT q) q)) zeroT :=
  rfl

/-- **Two receptions, two derived channels.** -/
theorem derived_follows :
    bind (ByInstantiation.received zeroT) derivedOutput ≠
      bind (ByInstantiation.received ByInstantiation.outputZero) derivedOutput := by
  rw [derived_by_instantiation, derived_by_instantiation]
  intro same
  have channels := congrArg read same
  revert channels
  decide

/-- **The published substitution leaves the quote alone**, with the bound index inside. -/
theorem derived_by_substitution :
    semanticCommSubst (read derivedOutput) (read (zeroT : G [] .pr)) =
      .apply "POutput" [.apply "NQuote" [.apply "POutput" [.bvar 0, .apply "PDrop" [.bvar 0]]],
        .apply "PZero" []] := by
  decide

/-- **The published contractum leaves the closed processes**: it is not sealed at depth zero. -/
theorem substitution_leaves_carrier :
    binderSafeAt "NQuote" 0 (semanticCommSubst (read derivedOutput) (read (zeroT : G [] .pr))) = false := by
  rw [derived_by_substitution]
  decide

/-- **The made row of the step stays closed.** -/
theorem instantiation_stays_closed (q : G [] .pr) (closed : Closed q) :
    Closed (bind (ByInstantiation.received q) derivedOutput) := by
  rw [derived_by_instantiation]
  change binderSafeAt "NQuote" 0 (read (outputT (quoteT (outputT (quoteT q) q)) zeroT)) = true
  rw [ByInstantiation.read_output, ByInstantiation.read_quote, ByInstantiation.read_output,
    ByInstantiation.read_quote, ByInstantiation.read_zero]
  simp [binderSafeAt, binderSafeListAt, closed]

#print axioms derived_not_sealed
#print axioms derived_not_in_carrier
#print axioms derived_translates
#print axioms derived_by_instantiation
#print axioms derived_follows
#print axioms derived_by_substitution
#print axioms substitution_leaves_carrier
#print axioms instantiation_stays_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
