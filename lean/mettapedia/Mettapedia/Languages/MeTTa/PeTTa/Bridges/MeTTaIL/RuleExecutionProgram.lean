import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram

/-!
# Retained rule operations and conservative matcher composition

Rule execution extends the retained matching program with distinct authored
function names. Existing matcher paths transport through the ordinary PeTTa
program-agreement theorem: dispatch, argument demand and selected bodies are
checked against both loaded sources. Captured values remain data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rule_execution.metta"
    sha256 "d5da4012ee1bc3858d85462e50e48f2bd8abc58a9d02b271e522565688c5dd5a"

/-- Shared operations used by the existing ordered premise dispatcher. -/
def premiseSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_premise_operations.metta"
    sha256 "113de1196a63b2784a7780d82c7b6972f0f949baceda161e82b5b0a5e0ff52db"

def program : Program :=
  MatchAutomataProgram.program.append (source.program.append premiseSource.program)

/-- Lookup is by the authored function name, independently of file position. -/
def equations (head : String) : List Equation :=
  program.equations.filter (fun equation => equation.head == head)

/-- The extension's namespace and dynamic evaluation are outside the retained
matcher's static code support. Captured values are not scanned as code. -/
def matcherHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:rule:") && !(head.startsWith "gslt:premise:")

theorem matcher_bodies_within :
    MatchAutomataProgram.program.equations.all (fun equation =>
      !matcherHead equation.head || codeWithin matcherHead equation.body) = true := by
  decide +kernel

theorem matcher_program_closed : ProgramClosed matcherHead MatchAutomataProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp matcher_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

theorem extension_equations_fresh :
    (source.program.append premiseSource.program).equations.all (fun equation => !matcherHead equation.head) = true := by
  decide +kernel

theorem extension_declarations_fresh :
    (source.program.append premiseSource.program).declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !matcherHead head
      | _ => true) = true := by
  decide +kernel

theorem matcher_program_agreement :
    ProgramAgreementOn matcherHead MatchAutomataProgram.program program := by
  apply appended_program_agreement
  · intro equation member
    have checked := List.all_eq_true.mp extension_equations_fresh equation member
    cases result : matcherHead equation.head with
    | false => rfl
    | true => simp [result] at checked
  · intro name types member
    have checked := List.all_eq_true.mp extension_declarations_fresh
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases result : matcherHead name with
    | false => rfl
    | true => simp [result] at checked

/-- Every supported existing matcher computation keeps its store, answer and
I/O after the actual rule-operation source is loaded. -/
theorem automata_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin matcherHead code = true)
    (checked : PureReturns MatchAutomataProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement matcher_program_closed matcher_program_agreement
    ⟨supported, rfl⟩ checked

theorem no_initializers : source.program.initializers = [] := by decide +kernel

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

#print axioms matcher_program_agreement
#print axioms automata_captured_returns

/-- Complete scoped conditional operations, including final receipt readout.
The quoted artifact is independent of the source execution judgments. -/
def scopedSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_scoped_execution.metta"
    sha256 "1d3159a8a5f569b1227820f092f6b3441b729bc62b4dc244345418f03d4a45e4"

def scopedProgram : Program := scopedSource.program

/-- A call fragment retains the ordered equations and arrow declarations for
its operation family. It carries no initializers or facts. Its canonical layout
places those equations before those declarations. -/
def callFragmentWhere (owns : String → Bool) (source : Program := scopedProgram) : Program :=
  let equations := source.equations.filter (fun equation => owns equation.head)
  let declarations := source.declarations.filter (retainedCallDeclaration owns)
  { equations, declarations
    layout := List.replicate equations.length .equation ++
      List.replicate declarations.length .declaration }

def callFragment (heads : List String) (source : Program := scopedProgram) : Program :=
  callFragmentWhere heads.contains source

def scopedMachineProgram : Program :=
  callFragmentWhere fun head =>
    head != "gslt:rule:site-replacement-represented" && head != "gslt:rule:job-finish-root"

def premiseAssignmentProgram : Program :=
  callFragment ["gslt:premise:type-context-lookup", "gslt:premise:check-assignment"]

def premiseAdministrationProgram : Program :=
  callFragment ["gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:machine-deliver", "gslt:premise:machine-evaluate", "gslt:premise:machine-expand"]

def premiseEnvironmentProgram : Program :=
  callFragment ["gslt:premise:constructor-declarations", "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:signature-candidates", "gslt:premise:signature", "gslt:premise:check-values", "gslt:premise:check-row"]

def premiseGroundProgram : Program :=
  callFragment ["gslt:premise:ground-at", "gslt:premise:ground-list-at"]

def premiseReflectionSelectionProgram : Program :=
  callFragment ["gslt:premise:reflective-rules", "gslt:premise:reflective-presentations", "gslt:premise:presentation-named", "gslt:premise:substitution-presentation"]

def premiseQueryProgram : Program :=
  callFragment ["gslt:premise:query-site", "gslt:premise:query-matching-request", "gslt:premise:query-expand-in"]

def premiseAdmissionProgram : Program :=
  callFragment ["gslt:premise:admission-keys", "gslt:premise:admission-occurrence-keys", "gslt:premise:admission-nodup", "gslt:premise:admission-context-covered", "gslt:premise:admission-occurrences", "gslt:premise:binding-admitted"]

def premiseFullEnvironmentProgram : Program :=
  callFragment ["gslt:premise:query-obligations", "gslt:premise:machine-deliver-in", "gslt:premise:machine-evaluate-in", "gslt:premise:machine-expand-in"]

def matcherEraseProgram : Program :=
  callFragment ["gslt:rule:scope-match-erase-at"]

def scopedInstantiationProgram : Program :=
  callFragment ["gslt:rule:scope-binder-operation", "gslt:rule:scope-instantiate-slot", "gslt:rule:scope-instantiate-at", "gslt:rule:scope-instantiate-args-at", "gslt:rule:scope-reduct"]

def scopedReflectionProgram : Program :=
  callFragment ["gslt:rule:scope-reflective-normalize", "gslt:rule:scope-reflective-normalize-list", "gslt:rule:scope-reflective-normalize-finish", "gslt:rule:scope-reflective-replacement", "gslt:rule:scope-reflective-normalized-mark", "gslt:rule:scope-reflective-name-mark", "gslt:rule:scope-reflective-unmark", "gslt:rule:scope-reflective-drop-finish", "gslt:rule:scope-reflective-instantiate-at", "gslt:rule:scope-reflective-instantiate-list-at", "gslt:rule:scope-reflective-instantiate-apply", "gslt:rule:scope-reflective-instantiate-unary", "gslt:rule:scope-reflective-binder-operation"]

def scopedMatcherProgram : Program :=
  callFragment ["gslt:rule:scope-matcher-capture", "gslt:rule:scope-matcher-captured-work", "gslt:rule:scope-matcher-split-at", "gslt:rule:scope-matcher-start", "gslt:rule:scope-matcher-complete", "gslt:rule:scope-matcher-expand-tree", "gslt:rule:scope-matcher-expand", "gslt:rule:scope-matcher-advance-branches", "gslt:rule:scope-matcher-advance", "gslt:rule:scope-matcher-tick", "gslt:rule:scope-matcher-run"]

def premiseSchedulerProgram : Program :=
  callFragment ["gslt:premise:machine-commit", "gslt:premise:machine-complete"]

def premiseMachineRunProgram : Program :=
  callFragment ["gslt:premise:machine-start", "gslt:premise:machine-tick", "gslt:premise:machine-run"]

def premiseMatchingProgram : Program :=
  callFragment ["gslt:premise:root-match-expand-in", "gslt:premise:target-match-expand-in", "gslt:premise:root-body-deliver-in", "gslt:premise:stepped-deliver-in"]

def ruleJobReadoutProgram : Program :=
  callFragment ["gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root"]

theorem scoped_equation_count : scopedProgram.equations.length = 226 := by rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem scoped_machine_equation_count : scopedMachineProgram.equations.length = 224 := by rfl
theorem scoped_no_initializers : scopedProgram.initializers = [] := by rfl
theorem scoped_no_facts : scopedProgram.facts = [] := by rfl
theorem callFragmentWhere_balanced (owns : String → Bool) (source : Program) :
    SpaceSemantics.Balanced (callFragmentWhere owns source) := by
  simp [callFragmentWhere, SpaceSemantics.Balanced, List.count_replicate]

theorem callFragment_balanced (heads : List String) (source : Program) :
    SpaceSemantics.Balanced (callFragment heads source) :=
  callFragmentWhere_balanced heads.contains source

theorem premiseAssignmentProgram_equation_count : premiseAssignmentProgram.equations.length = 2 := by rfl

theorem premiseAdministrationProgram_equation_count : premiseAdministrationProgram.equations.length = 5 := by rfl

theorem premiseEnvironmentProgram_equation_count : premiseEnvironmentProgram.equations.length = 7 := by rfl

theorem premiseGroundProgram_equation_count : premiseGroundProgram.equations.length = 2 := by rfl

theorem premiseReflectionSelectionProgram_equation_count : premiseReflectionSelectionProgram.equations.length = 4 := by rfl

theorem premiseQueryProgram_equation_count : premiseQueryProgram.equations.length = 3 := by rfl

theorem premiseAdmissionProgram_equation_count : premiseAdmissionProgram.equations.length = 6 := by rfl

theorem premiseFullEnvironmentProgram_equation_count : premiseFullEnvironmentProgram.equations.length = 4 := by rfl

theorem matcherEraseProgram_equation_count : matcherEraseProgram.equations.length = 1 := by rfl

theorem scopedInstantiationProgram_equation_count : scopedInstantiationProgram.equations.length = 5 := by rfl

theorem scopedReflectionProgram_equation_count : scopedReflectionProgram.equations.length = 13 := by rfl

theorem scopedMatcherProgram_equation_count : scopedMatcherProgram.equations.length = 11 := by rfl

theorem premiseSchedulerProgram_equation_count : premiseSchedulerProgram.equations.length = 2 := by rfl

theorem premiseMachineRunProgram_equation_count : premiseMachineRunProgram.equations.length = 3 := by rfl


private def interpretedTypedSitesSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_typed_sites.metta"
    sha256 "70cbcf95d6ff191c34c3240f18ce26ac8d4289eb3990e61679ffb89cc000f01c"

private def interpretedDescentExecutionSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_descent_execution.metta"
    sha256 "ac6898f665cc26f9e7cc3190f110adb1e1cbf773a0fe114bb78501d62a502bf9"

private def interpretedCompleteSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_complete.metta"
    sha256 "86918154a2bd3259288bbe0e7bfc8c1881ec6ccaa0359904c045b87d5ea394a9"

private def interpretedCollectionLawsSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_laws.metta"
    sha256 "24a3e67c782270ba3ac7633d38c91b76ec14b2d4bd37269f811776e64fd30212"

private def interpretedCanonicalSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_canonical.metta"
    sha256 "43e88bc231cafbcf276cdd566d90a9160634f9582539c4832a6e37f55af8c9c5"

private def interpretedCollectionSelectionSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_selection.metta"
    sha256 "2c505e3b3b6241668e0c3f95d50ac1983666560234f4d03161d39e88dd659593"

private def interpretedCollectionMachineSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_machine.metta"
    sha256 "34addb0bd7d4b78a6883cc7238a0c4741358085b9b22bdf490398a4cbd0e2b46"

private def interpretedCollectionLoggedSearchSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_logged_search.metta"
    sha256 "5a7619553f9217e7a984cf38845db3aa270bdc8674539235c7501b2201a97362"

private def interpretedCollectionBackendSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_backend.metta"
    sha256 "f84721542634893db493c69002d0b2689ca04ed4ac633981f34f62c15d3c5b03"

private def interpretedCollectionContextsSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_contexts.metta"
    sha256 "81fee57af76a29ea16a1419c43fbb063be3ec88a6fc58e90eedfe03ab860ac93"

private def interpretedRecursiveCollectionSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_recursive_collection.metta"
    sha256 "e4ed176d2a640e0f98edca03c71ca922c0b5bae94697a50fad9cc2c3496a7628"

private def interpretedCollectionPresentationSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_presentation.metta"
    sha256 "01c97faf6f6a8aa54f5af704c39cbce46166a1f076de29fef855861b47929a0b"

private def interpretedCollectionHandoffSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_handoff.metta"
    sha256 "14b11b539d59f89ae41722a5175b97b61502f582fcb7b8cde847441e3dbccc6d"

/-- Earlier source snapshot retained as the closed primitive transport donor.
The selected source owner quotes the current physical artifact. -/
private def interpretedCollectionContinuationSource : ProgramQuotation.QuotedProgram :=
  petta_source% "; A prepared recursive allocation owns one retained typed/premise state.\n(: gslt:collection-continuation:begin\n  (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))\n(= (gslt:collection-continuation:begin\n     $environment $depth $bound $type $index $rule $spec $prepared)\n  (case $prepared\n    (((PreparedCollectionMatch $source $answer $history)\n      (let* (($next-depth (+ $depth 1))\n             ($goal (DescentRootGoal $next-depth $bound $type $source $index))\n             ($tail (DescentDone $goal))\n             ($expanded (gslt:descent:continue-root-answer\n               $environment $depth $bound $type $source $index $rule $spec\n               $answer $tail LNil))\n             ($state (gslt:collection-backend:expansion-state $expanded)))\n        (RecursiveCollectionContinuation $prepared $state))))))\n\n(: gslt:collection-continuation:run (-> Atom Atom Atom %Undefined%))\n(= (gslt:collection-continuation:run $environment $work $frame)\n  (case $frame\n    (((RecursiveCollectionContinuation $prepared $state)\n      (let $next (gslt:descent:run $environment $work $state)\n        (RecursiveCollectionContinuation $prepared $next))))))\n\n(: gslt:collection-continuation:results (-> Atom Atom Atom %Undefined%))\n(= (gslt:collection-continuation:results $prepared $expected $answers)\n  (case $answers\n    ((LNil LNil)\n     ((LCons (PremiseResult $goal (RootAnswer $trace $captured $completed $history $target)) $rest)\n      (let $later (gslt:collection-continuation:results $prepared $expected $rest)\n        (if (== $captured $expected)\n          (LCons (RecursiveCollectionContinued $prepared\n                   (RootAnswer $trace $captured $completed $history $target)) $later)\n          $later))))))\n\n(: gslt:collection-continuation:publication (-> Atom %Undefined%))\n(= (gslt:collection-continuation:publication $frame)\n  (case $frame\n    (((RecursiveCollectionContinuation\n        (PreparedCollectionMatch $source (ScopedMatcherAnswer $captured $trace) $allocation-history)\n        (PremiseState $tasks $answers $unresolved $work))\n      (gslt:collection-continuation:results\n        (PreparedCollectionMatch $source (ScopedMatcherAnswer $captured $trace) $allocation-history)\n        $captured $answers)))))\n"
    sha256 "9e633218ef92c971c475a1ffbcf43a8c319d277f513f5a0a155426e99e56f86f"

private def interpretedCollectionOccurrencesSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_occurrences.metta"
    sha256 "1a1cfbef65f6a0320ea0fa2e1a067665f14b950ea2f6fedcdc6e573839b2d352"

private def interpretedCollectionInstallSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_install.metta"
    sha256 "d1892fde9b7cecf4f826095d08629fb0d65892dd0e7e1cedf4261ae601f18a85"

private def interpretedCollectionMatchLanesSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_match_lanes.metta"
    sha256 "e03684e60d567dd54beecd15074f74a4c9a8eb25ac36038112f6f1ff638e077c"

/-- Earlier source snapshot retained as the closed primitive transport donor.
The selected source owner quotes the current physical artifact. -/
private def interpretedCollectionCollectorSource : ProgramQuotation.QuotedProgram :=
  petta_source% "; Prepare one newly published recursive match and start its shared continuation.\n(: gslt:occurrence-collector:allocate (-> Atom Atom Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-collector:allocate $names $environment $depth $origin $query $answer)\n  (case (OccurrenceAllocationInput $origin $query $environment)\n    (((OccurrenceAllocationInput\n        (RecursiveOccurrenceJob\n          (RuleJob $index $declaration $original-site)\n          (CollectionSiteVariant $origin-site\n            (RuleJobSite $address $context $focus $bound $type $frames)))\n        (ScopedMatcherRequest $rule $spec $ambient $side $path $match-depth $initial $schema $target)\n        (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free))\n      (if (gslt:premise:binding-admitted $rule $spec)\n        (if (gslt:premise:open-well-sorted $declarations $free $bound $type $focus)\n          (case (gslt:collection-handoff:prepare $names $query $answer)\n            ((None None)\n             ((Some $prepared)\n              (let* (($allocated-origin\n                        (RecursiveCollectionOrigin\n                          (RuleJob $index $declaration $original-site)\n                          (CollectionSiteVariant $origin-site\n                            (RuleJobSite $address $context $focus $bound $type $frames))\n                          $answer))\n                     ($frame (gslt:occurrence-batch:frame-begin\n                       $allocated-origin $environment $depth $bound $type $index $rule $spec $prepared)))\n                (Some $frame)))))\n          None)\n        None)))))\n\n(: gslt:occurrence-collector:collect (-> Atom Atom Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-collector:collect $names $environment $depth $origin $query $answers)\n  (case $answers\n    ((LNil LNil)\n     ((LCons $answer $rest)\n      (let* (($first (gslt:occurrence-collector:allocate\n                       $names $environment $depth $origin $query $answer))\n             ($later (gslt:occurrence-collector:collect\n                       $names $environment $depth $origin $query $rest)))\n        (case $first\n          ((None $later)\n           ((Some $frame) (LCons $frame $later)))))))))\n\n; Advance one retained matcher and prepare only its fresh answer suffix.\n(: gslt:occurrence-collector:advance-lane (-> Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-collector:advance-lane $names $environment $depth $lane)\n  (case $lane\n    (((RecursiveOccurrenceLane $origin $query $state $spent)\n      (case (gslt:occurrence-matcher:advance $names $lane)\n        (((RecursiveOccurrenceMatches $next $answers)\n          (let $frames (gslt:occurrence-collector:collect\n                         $names $environment $depth $origin $query $answers)\n            (RecursiveOccurrenceLaneAllocations $next $frames)))))))))\n\n(: gslt:occurrence-collector:advance-lanes (-> Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-collector:advance-lanes $names $environment $depth $lanes)\n  (case $lanes\n    ((LNil (RecursiveOccurrenceLanesAllocations LNil LNil))\n     ((LCons $lane $rest)\n      (case (gslt:occurrence-collector:advance-lane $names $environment $depth $lane)\n        (((RecursiveOccurrenceLaneAllocations $next $fresh)\n          (case (gslt:occurrence-collector:advance-lanes $names $environment $depth $rest)\n            (((RecursiveOccurrenceLanesAllocations $next-rest $later)\n              (let $all (gslt:automata:append $fresh $later)\n                (RecursiveOccurrenceLanesAllocations (LCons $next $next-rest) $all))))))))))))\n"
    sha256 "3d2b3b9a27806ba08536065927c3fc24c8e306443c3cd955325a36e105be063d"

private def interpretedCollectionOccurrenceMachineSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_machine.metta"
    sha256 "bfbca7b35bfa678b4145030bf631bbe7bc4e6291cfb2e10561e152db0468f0df"

private def interpretedCollectionOccurrenceDiscoverySource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_discovery.metta"
    sha256 "e9a6245831dd80046f26c38e13509251840c3c5c4a6d7c5460e1fdab76fadcdc"

/-- Earlier source snapshot retained as the closed primitive transport donor.
The selected source owner quotes the current physical artifact. -/
private def interpretedCollectionOccurrenceSearchSource : ProgramQuotation.QuotedProgram :=
  petta_source% "; Retained occurrence execution behind the shared search interface.\n(: gslt:occurrence-search:run (-> Atom Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-search:run $names $depth $plan $source $work)\n  (case $plan\n    (((CompletePlan\n        (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)\n        $permissions $bound $expected $rules $equations $admitted)\n      (let* (($canonical (gslt:canon:canon $names $source))\n             ($initial (gslt:occurrence-discovery:begin\n               $declarations $free $permissions $bound $expected $canonical $rules))\n             ($state (gslt:occurrence-machine:run $names\n               (PremiseEnvironment $declarations $rewrites $specifications $provider $reflection $free)\n               $depth $work $initial)))\n        (gslt:occurrence-search:with-state $plan $source $state))))))\n\n(: gslt:occurrence-search:resume (-> Atom Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-search:resume $names $depth $run $work)\n  (case $run\n    (((RecursiveOccurrenceRun\n        (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)\n        $source $state $published)\n      (let $next (gslt:occurrence-machine:run $names $environment $depth $work $state)\n        (gslt:occurrence-search:with-state\n          (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)\n          $source $next))))))\n\n(: gslt:occurrence-search:lanes-complete (-> Atom %Undefined%))\n(= (gslt:occurrence-search:lanes-complete $lanes)\n  (case $lanes\n    ((LNil True)\n     ((LCons (RecursiveOccurrenceLane $origin $request $state $spent) $rest)\n      (if (gslt:recursive-collection:complete $state)\n        (gslt:occurrence-search:lanes-complete $rest) False)))))\n\n(: gslt:occurrence-search:frames-idle (-> Atom %Undefined%))\n(= (gslt:occurrence-search:frames-idle $frames)\n  (case $frames\n    ((LNil True)\n     ((LCons (RecursiveOccurrenceFrame $origin\n        (RecursiveCollectionContinuation $prepared\n          (PremiseState $agenda $answers $unresolved $work))) $rest)\n      (case $agenda\n        ((LNil (gslt:occurrence-search:frames-idle $rest))\n         ((LCons $task $tasks) False)))))))\n\n(: gslt:occurrence-search:frames-resolved (-> Atom %Undefined%))\n(= (gslt:occurrence-search:frames-resolved $frames)\n  (case $frames\n    ((LNil True)\n     ((LCons (RecursiveOccurrenceFrame $origin\n        (RecursiveCollectionContinuation $prepared\n          (PremiseState $agenda $answers $unresolved $work))) $rest)\n      (case $unresolved\n        ((LNil (gslt:occurrence-search:frames-resolved $rest))\n         ((LCons $obligation $obligations) False)))))))\n\n(: gslt:occurrence-search:status (-> Atom %Undefined%))\n(= (gslt:occurrence-search:status $run)\n  (case $run\n    (((RecursiveOccurrenceRun $plan $source\n        (RecursiveOccurrenceState $lanes (RecursiveOccurrenceBatch $frames $log)) $published)\n      (if (gslt:occurrence-search:lanes-complete $lanes)\n        (if (gslt:occurrence-search:frames-idle $frames)\n          (if (gslt:occurrence-search:frames-resolved $frames)\n            SearchComplete SearchBlocked)\n          SearchPending)\n        SearchPending)))))\n\n(: gslt:occurrence-search:finish (-> Atom Atom %Undefined%))\n(= (gslt:occurrence-search:finish $plan $packet)\n  (case (OccurrenceFinishInput $plan $packet)\n    (((OccurrenceFinishInput\n        (CompletePlan $environment $permissions $bound $expected $rules $equations $admitted)\n        (RecursiveOccurrencePublication\n          (RecursiveCollectionOrigin\n            (RuleJob $ordinal $declaration $originalSite)\n            (CollectionSiteVariant $original\n              (RuleJobSite $address $context $focus $focusBound $focusType $frames))\n            $allocation)\n          (RecursiveCollectionContinued\n            (PreparedCollectionMatch $preparedSource\n              (ScopedMatcherAnswer $captured $trace) $allocationHistory)\n            (RootAnswer $outcomeTrace $outcomeCaptured $completed $history $target))))\n      (let* (($presented (gslt:rule:scope-fill $context $preparedSource))\n             ($job (RuleJob $ordinal $declaration\n               (RuleJobSite $address $context $preparedSource $focusBound $focusType $frames)))\n             ($request (RuleJobRequestProjection\n               $environment $permissions $bound $expected $presented $job))\n             ($result (PremiseResult (RootGoal $focusBound $focusType $preparedSource $ordinal)\n               (RootAnswer $trace $captured $completed $history $target))))\n        (gslt:rule:job-finish-root $request $result))))))\n\n(: gslt:occurrence-search:read-log (-> Atom Atom %Undefined%))\n(= (gslt:occurrence-search:read-log $plan $packets)\n  (case $packets\n    ((LNil LNil)\n     ((LCons $packet $rest)\n      (let* (($finished (gslt:occurrence-search:finish $plan $packet))\n             ($later (gslt:occurrence-search:read-log $plan $rest)))\n        (case $finished\n          (((Some $receipt) (LCons $receipt $later))\n           (None $later))))))))\n\n(: gslt:occurrence-search:with-state (-> Atom Atom Atom %Undefined%))\n(= (gslt:occurrence-search:with-state $plan $source $state)\n  (case $state\n    (((RecursiveOccurrenceState $lanes (RecursiveOccurrenceBatch $frames $log))\n      (let $published (gslt:occurrence-search:read-log $plan $log)\n        (RecursiveOccurrenceRun $plan $source $state $published))))))\n\n(: gslt:occurrence-search:publication (-> Atom %Undefined%))\n(= (gslt:occurrence-search:publication $run)\n  (case $run\n    (((RecursiveOccurrenceRun $plan $source $state $published) $published))))\n\n(: gslt:occurrence-search:target (-> Atom Atom %Undefined%))\n(= (gslt:occurrence-search:target $names $receipt)\n  (case $receipt\n    (((RuleJobReceipt $job $trace $captured $completed $history $local $target)\n      (gslt:canon:canon $names $target)))))\n"
    sha256 "a3288d04780aa15ff63e44d38f3ecdc4a8691e28f12cf244b4dac159e32a3d6c"

private def interpretedRunnerSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../metta/gslt/lib/gslt_runner.metta"
    sha256 "c7f97a840f35d77a9b41a121b4e3dc5ff30a50bac7241f25cde4e96b9544f21a"

/-- The shared source artifacts loaded after the scoped operations. These are
constructor data only; their execution laws are proved by their existing owners. -/
def interpretedPremiseSupportSources : List ProgramQuotation.QuotedProgram :=
  [
    interpretedTypedSitesSource,
    interpretedDescentExecutionSource,
    interpretedCompleteSource,
    interpretedCollectionLawsSource,
    interpretedCanonicalSource,
    interpretedCollectionSelectionSource,
    interpretedCollectionMachineSource,
    interpretedCollectionLoggedSearchSource,
    interpretedCollectionBackendSource,
    interpretedCollectionContextsSource,
    interpretedRecursiveCollectionSource,
    interpretedCollectionPresentationSource,
    interpretedCollectionHandoffSource,
    interpretedCollectionContinuationSource,
    interpretedCollectionOccurrencesSource,
    interpretedCollectionInstallSource,
    interpretedCollectionMatchLanesSource,
    interpretedCollectionCollectorSource,
    interpretedCollectionOccurrenceMachineSource,
    interpretedCollectionOccurrenceDiscoverySource,
    interpretedCollectionOccurrenceSearchSource,
    interpretedRunnerSource
  ]

/-- One raw source view for both ordinary and interpreted retained matching.
Matching dispatch is placed after its implementations; all selected source
rows retain their order. This definition grants no execution capability. -/
def interpretedPremiseProgram : Program :=
  let base := callFragmentWhere
    (fun head => !head.startsWith "gslt:premise:matching-") scopedProgram
  let support := interpretedPremiseSupportSources.foldl
    (fun loaded source => loaded.append source.program) base
  support.append (callFragmentWhere
    (fun head => head.startsWith "gslt:premise:matching-") scopedProgram)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem interpretedPremiseProgram_equation_count :
    interpretedPremiseProgram.equations.length = 566 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem interpretedPremiseProgram_no_initializers :
    interpretedPremiseProgram.initializers = [] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem interpretedPremiseProgram_no_facts :
    interpretedPremiseProgram.facts = [] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem interpretedPremiseProgram_no_test_heads :
    interpretedPremiseProgram.equations.all
      (fun row => !row.head.startsWith "native-probe:") = true := by decide +kernel

#print axioms scoped_equation_count
#print axioms scoped_machine_equation_count
#print axioms scoped_no_initializers
#print axioms scoped_no_facts
#print axioms callFragment_balanced

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
