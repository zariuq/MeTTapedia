import Mettapedia.OSLF.MeTTaIL.Complete.DescentCoherence
import Mettapedia.OSLF.MeTTaIL.GeneralRhoStandardSites

/-!
# The GeneralRho.Standard.plan calculus: the canonical explorer is complete modulo its parallel laws

The GeneralRho.Standard.plan plan with its standard reduction contexts (`GeneralRho.Standard.plan`) declares the
parallel composition `PPar` as a bag that flattens, with unit `PZero`, and reduces inside parallel
compositions. Its one rule, COMM, matches a channel name twice: two presentations of the same name
may list a quoted parallel composition in different orders. The presented GSLT steps modulo the
plan's parallel laws: permutation, flattening and removal of `PZero`, in every context. The plan
declares no other equality: the name equation `@*x = x` and the identification of an empty or
singleton parallel composition with `PZero` or with its element are not among its laws, so
presentations that differ only by them are distinct states.

The plan meets every admission condition of `Complete.DescentCoherence`, so the explorer that
commits the sorted normal form explores every state reachable by steps modulo the parallel laws,
up to those laws (`rho_explores`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags Coherence RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## Short spines are increasing -/

theorem arguments?_length {rule : RewriteRule} {spec : RuleBindingSpec} {name : String} {site : RulePatternSite}
    {path : List Nat} {arguments : List Pattern} (found : arguments? rule spec name site path = some arguments) :
    ∃ dependencies, dependencies? spec name = some dependencies ∧ arguments.length = dependencies.length := by
  unfold arguments? at found
  simp only [bind, Option.bind_eq_some_iff, guard, pure] at found
  obtain ⟨dependencies, declared, _, _, rest⟩ := found
  refine ⟨dependencies, declared, ?_⟩
  split at rest
  · split at rest
    · cases rest
      rename_i empty
      simp only [List.isEmpty_iff] at empty
      simp [empty]
    · cases rest
  · split at rest
    · cases rest
      rename_i matching
      simp only [Bool.and_eq_true, beq_iff_eq] at matching
      exact matching.2
    · cases rest
  · cases rest

/-- **A rule whose metavariables depend on at most one bound variable has increasing spines.** -/
theorem increasingSpines_of_short {rule : RewriteRule} {spec : RuleBindingSpec}
    (short : ∀ name dependencies, dependencies? spec name = some dependencies → dependencies.length ≤ 1) :
    IncreasingSpines rule spec := by
  intro name site path arguments found depth indices spine
  obtain ⟨dependencies, declared, length⟩ := arguments?_length found
  have argumentsShort := length ▸ short name dependencies declared
  have indicesLength : indices.length = arguments.length := by
    rw [variableSpine?_arguments spine, List.length_map]
  match indices, indicesLength with
  | [], _ => exact .nil
  | [_], _ => exact List.pairwise_singleton _ _
  | _ :: _ :: _, same => simp at same; omega

/-! ## The GeneralRho.Standard.plan plan -/

theorem laws_eq : Normalized.laws GeneralRho.Standard.plan = [⟨.hashBag, some "PZero"⟩] := by decide

theorem comm_binder_compatible :
    BinderLawsFor (Normalized.laws GeneralRho.Standard.plan)
      (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).reflection GeneralRho.comm := by
  apply (checkBinderLawsFor_iff _ _ _).mp
  rw [laws_eq]
  decide +kernel

theorem comm_conflicting_unit_refused :
    checkBinderLawsFor [⟨.hashBag, some "Other"⟩]
      (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).reflection GeneralRho.comm = false := by
  decide +kernel

theorem extrusions_eq : Normalized.extrusions GeneralRho.Standard.plan = [] := by decide

theorem checked : Predecessors.equationsChecked GeneralRho.Standard.plan = true := by decide

theorem terms_eq : (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language.terms = rhoCalc.terms := rfl

theorem rewrites_eq : (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language.rewrites = [GeneralRho.comm] := by
  show GeneralRho.Standard.plan.rules.map RulePlan.rule = _
  rw [GeneralRho.Standard.compiled_rules]; rfl

theorem rules_zipIdx : GeneralRho.Standard.plan.rules.zipIdx = [(GeneralRho.declaration, 0)] := by
  rw [GeneralRho.Standard.compiled_rules]; rfl

theorem specification_eq : GeneralPremise.specification? (GeneralPlanEnvironment.environment GeneralRho.Standard.plan) 0 =
    some Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec := by
  unfold GeneralPremise.specification?
  show Option.map Prod.snd (List.find? (fun entry => entry.1 == 0)
    (GeneralRho.Standard.plan.rules.zipIdx.map fun (rule, index) => (index, rule.binding.spec))) = _
  rw [rules_zipIdx]; rfl

/-- The rule at a declared ordinal is COMM with its binding specification. -/
theorem rule_at {declaration : RulePlan} {ordinal : Nat} (member : (declaration, ordinal) ∈ GeneralRho.Standard.plan.rules.zipIdx)
    {rule : RewriteRule} {spec : RuleBindingSpec}
    (selected : (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language.rewrites[ordinal]? = some rule)
    (specified : GeneralPremise.specification? (GeneralPlanEnvironment.environment GeneralRho.Standard.plan) ordinal = some spec) :
    ordinal = 0 ∧ rule = GeneralRho.comm ∧ spec = Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec := by
  rw [rules_zipIdx, List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨_, rfl⟩ := member
  rw [rewrites_eq] at selected
  rw [specification_eq] at specified
  simp only [List.getElem?_cons_zero, Option.some.injEq] at selected specified
  exact ⟨rfl, selected.symm, specified.symm⟩

theorem dependencies?_mem {spec : RuleBindingSpec} {name : String} {dependencies : List TypeExpr}
    (found : dependencies? spec name = some dependencies) : ∃ entry, (entry, dependencies) ∈ spec.dependencies := by
  unfold dependencies? at found
  generalize filtered : spec.dependencies.filter (fun entry => entry.1 == name) = matching at found
  match matching, found with
  | [(entry, _)], found =>
    cases found
    exact ⟨entry, List.mem_of_mem_filter (by rw [filtered]; exact .head _)⟩

theorem comm_dependencies {name : String} {dependencies : List TypeExpr}
    (found : dependencies? Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec name = some dependencies) :
    dependencies = [] ∨ dependencies = [.base "Name"] := by
  obtain ⟨entry, member⟩ := dependencies?_mem found
  simp only [Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec, List.mem_cons, Prod.mk.injEq,
    List.mem_nil_iff, or_false] at member
  rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact .inl rfl
  · exact .inr rfl
  · exact .inl rfl
  · exact .inl rfl

/-- **COMM fires at canonical forms.** -/
theorem canonical : CanonicalCoherence.RulesAdmissible GeneralRho.Standard.plan := by
  refine ⟨by unfold CanonicalBags.NoSetDescent; decide,
    fun declaration ordinal member rule spec selected specified => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := rule_at member selected specified
  refine ⟨increasingSpines_of_short fun name dependencies found => ?_, rfl, by decide,
    (checkBinderLawsFor_iff _ _ _).mp (by decide +kernel)⟩
  rcases comm_dependencies found with rfl | rfl <;> simp

/-- The language's terms, one by one. -/
theorem mem_terms {rule : GrammarRule} (member : rule ∈ (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language.terms) :
    rule = rhoCalc.terms[0] ∨ rule = rhoCalc.terms[1] ∨ rule = rhoCalc.terms[2] ∨ rule = rhoCalc.terms[3] ∨
      rule = rhoCalc.terms[4] ∨ rule = rhoCalc.terms[5] := by
  rw [terms_eq] at member
  simp only [rhoCalc, List.mem_cons, List.mem_nil_iff, or_false] at member
  simpa [rhoCalc] using member

theorem laws_found {kind : CollType} {law : CollectionLaws.Laws}
    (found : CollectionLaws.lawFor (Normalized.laws GeneralRho.Standard.plan) kind = some law) :
    kind = .hashBag ∧ law = ⟨.hashBag, some "PZero"⟩ := by
  rw [laws_eq] at found
  simp only [CollectionLaws.lawFor, List.find?] at found
  split at found
  · rename_i same; cases found; exact ⟨(by simpa using same : CollType.hashBag = kind).symm, rfl⟩
  · simp at found

/-- `PPar` is the only bare constructor, and only for bags. -/
theorem bare_rule {rule : GrammarRule}
    (member : rule ∈ (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language.terms)
    {name : String} {kind : CollType} {element : TypeExpr} (parameters : rule.params = [.simple name (.collection kind element)]) :
    rule = rhoCalc.terms[3] ∧ kind = .hashBag ∧ element = .base "Proc" := by
  rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [rhoCalc, TypeExpr.bag, TypeExpr.proc, TypeExpr.name, TypeExpr.baseType]

theorem lawTypeOk_proc_bag : LawTypeOk (Normalized.laws GeneralRho.Standard.plan)
    (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language (.collection .hashBag (.base "Proc")) := by
  refine .inr ⟨rhoCalc.terms[3], by rw [terms_eq]; simp [rhoCalc], "ps", rfl, rfl⟩

/-- **The rho laws are strictly typed.** -/
theorem typed : LawsTypedStrict (Normalized.laws GeneralRho.Standard.plan)
    (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language GeneralRho.Standard.plan.snapshot.free where
  homogeneous law kind found rule member name element parameters := by
    obtain ⟨rfl, _, rfl⟩ := bare_rule member parameters
    rfl
  units law kind found label unit rule member name element parameters := by
    obtain ⟨_, rfl⟩ := laws_found found
    obtain ⟨rfl, _, _⟩ := bare_rule member parameters
    simp only [Option.some.injEq] at unit
    subst unit
    exact ⟨rhoCalc.terms[0], by rw [terms_eq]; simp [rhoCalc], rfl, rfl, rfl⟩
  parameters rule member parameter parameterMember type typedParameter := by
    rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_cons, List.mem_nil_iff,
        or_false] at parameterMember <;>
      rcases parameterMember with rfl | rfl <;>
      simp only [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType, TypeExpr.bag, TypeExpr.funType,
        Option.some.injEq] at typedParameter <;>
      subst typedParameter <;>
      first | trivial | exact ⟨trivial, trivial⟩ | exact lawTypeOk_proc_bag
  freeNames name type found := by
    simp [Snapshot.free, GeneralRho.Standard.plan, GeneralExecutionAdmission.compile, GeneralRho.snapshot] at found

/-- **One bare constructor category for bags.** -/
theorem unique : UniqueBare (Normalized.laws GeneralRho.Standard.plan)
    (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language := by
  intro law kind found first firstMember second secondMember name element name' element' firstParameters secondParameters
  obtain ⟨rfl, _, _⟩ := bare_rule firstMember firstParameters
  obtain ⟨rfl, _, _⟩ := bare_rule secondMember secondParameters
  rfl

theorem comm_left : GeneralRho.comm.left = .collection .hashBag
    [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")], .apply "POutput" [.fvar "n", .fvar "q"]] (some "rest") := rfl

theorem comm_right : GeneralRho.comm.right =
    .collection .hashBag [.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])] (some "rest") := rfl

/-- COMM's left side is safe for the bag laws. -/
theorem comm_flatSafe : FlatSafe (Normalized.laws GeneralRho.Standard.plan) GeneralRho.comm.left := by
  rw [comm_left]
  refine .collection ?_ ?_
  · intro element member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · refine .apply fun argument inside => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at inside
      rcases inside with rfl | rfl
      · exact .fvar _
      · exact .lambda (.fvar _)
    · refine .apply fun argument inside => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at inside
      rcases inside with rfl | rfl <;> exact .fvar _
  · intro law found element member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;>
      exact ⟨(by intro _ same; cases same), (by intro _ _ same; cases same), (by intro _ _ same; cases same)⟩

theorem comm_sorts {name : String} {sort : TypeExpr} (found : GeneralRho.comm.typeContext.lookup name = some sort) :
    sort = .base "Name" ∨ sort = .base "Proc" ∨ sort = .collection .hashBag (.base "Proc") := by
  obtain ⟨front, back, split, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (name, sort) ∈ GeneralRho.comm.typeContext := by rw [split]; simp
  simp only [GeneralRho.comm, rhoCommRewrite, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq,
    List.mem_nil_iff, or_false, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at member
  rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- **COMM fires at law-normal forms.** -/
theorem rules : LawCoherence.LawRulesAdmissible GeneralRho.Standard.plan := by
  intro declaration ordinal member rule spec selected specified
  obtain ⟨rfl, rfl, rfl⟩ := rule_at member selected specified
  refine ⟨comm_flatSafe, rfl, fun name sort found => ?_, fun name dependencies found entry inside => ?_,
    comm_binder_compatible⟩
  · rcases comm_sorts found with rfl | rfl | rfl
    · trivial
    · trivial
    · exact lawTypeOk_proc_bag
  · rcases comm_dependencies found with rfl | rfl
    · simp at inside
    · simp only [List.mem_singleton] at inside; subst inside; trivial

/-- **COMM is extended for bags.** -/
theorem comm_extended : ExtendedAt (GeneralPlanEnvironment.environment GeneralRho.Standard.plan) 0 .hashBag := by
  intro rule spec selected specified
  rw [rewrites_eq] at selected
  rw [specification_eq] at specified
  simp only [List.getElem?_cons_zero, Option.some.injEq] at selected specified
  subst selected; subst specified
  refine ⟨_, _, "rest", comm_left, comm_right, ?_, ?_, by decide, by decide, by decide, rfl⟩
  · intro schema member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> simp [Pattern.freeFvarNames]
  · intro schema member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    subst member; simp [Pattern.freeFvarNames]

/-- **COMM admits reduction inside parallel compositions.** -/
theorem descent : DescentCoherence.DescentRulesAdmissible GeneralRho.Standard.plan := by
  intro declaration ordinal member rule spec selected specified
  obtain ⟨rfl, rfl, rfl⟩ := rule_at member selected specified
  refine ⟨(by intro name same; rw [comm_left] at same; cases same),
    (by intro kind law label _ _ same; rw [comm_left] at same; cases same), fun kind law elements rest same found => ?_⟩
  rw [comm_left] at same
  cases same
  exact ⟨comm_extended, by decide⟩

/-- **The rho plan admits reduction inside collections of a flattening kind.** -/
theorem descentAdmissible : DescentCoherence.DescentAdmissible GeneralRho.Standard.plan :=
  ⟨typed, unique, rules, descent⟩

/-- The rho plan has no equations. -/
theorem noEquations (bound : List TypeExpr) (expected : TypeExpr) (left right : Pattern) :
    ¬ GeneralOccurrenceSemantics.Equation GeneralRho.Standard.plan bound expected left right := by
  rintro ⟨receipt, complete, _⟩
  have member := complete.job.1
  rw [GeneralRho.Standard.compilation_has_no_equations] at member
  simp at member

/-- **The canonical explorer is complete for rho modulo its parallel laws**: every closed
process reachable from a well-sorted closed process by finitely many steps modulo the parallel
laws (permutation, flattening and removal of `PZero` in parallel compositions) is explored from
the process's sorted normal form, up to those laws. -/
theorem rho_explores (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source)
    {target : Pattern} (reaches : (Presented.gslt GeneralRho.Standard.plan [] (.base "Proc")).MultiStep source target) :
    ∃ state, Explore.Explored (S := CanonicalCoherence.search GeneralRho.Standard.plan [] (.base "Proc"))
        (lawNormal (Normalized.laws GeneralRho.Standard.plan) source) state ∧
      Presented.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") state target :=
  DescentCoherence.presented_explores_descent checked (noEquations [] (.base "Proc")) extrusions_eq canonical
    descentAdmissible (fun _ member => absurd member List.not_mem_nil)
    (show LawTypeOk _ _ (.base "Proc") from trivial) source sorted reaches

end Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented
