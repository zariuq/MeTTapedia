import Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

/-!
# Runtime bridge for Metamath finite substitutions

The side-condition calculus deliberately represents a substitution as a list:
that makes every binding, including duplicate keys, visible to derivations.
The live `mm-lean4` verifier instead consumes a `Std.HashMap`.  This file gives
the exact bridge between those representations and then relates proof-relevant
body substitution to the live `Metamath.Verify.Formula.subst` computation.

The map below keeps the first list binding at a duplicate key.  All exact
relational lookup and substitution equivalences therefore carry the source
invariant `SubstitutionKeysUnique`; separate boundary theorems state what
happens for absent and duplicate keys.
-/

namespace Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Finite list to live `HashMap` -/

/-- A proof-friendly materialization of finite substitution syntax as the map
consumed by the live verifier.  Recursing through the tail before insertion
makes the first source binding win when duplicate keys are present. -/
def RuntimeSubstitutionMap : FiniteSubstitution →
    Std.HashMap String RuntimeFormula
  | [] => {}
  | binding :: rest =>
      (RuntimeSubstitutionMap rest).insert binding.variableName
        binding.replacement.toRuntime

@[simp] theorem runtimeSubstitutionMap_nil :
    RuntimeSubstitutionMap [] = ({} : Std.HashMap String RuntimeFormula) := by
  rfl

@[simp] theorem runtimeSubstitutionMap_cons (binding : FormulaBinding)
    (rest : FiniteSubstitution) :
    RuntimeSubstitutionMap (binding :: rest) =
      (RuntimeSubstitutionMap rest).insert binding.variableName
        binding.replacement.toRuntime := by
  rfl

@[simp] theorem runtimeSubstitutionMap_lookup_head (binding : FormulaBinding)
    (rest : FiniteSubstitution) :
    (RuntimeSubstitutionMap (binding :: rest))[binding.variableName]? =
      some binding.replacement.toRuntime := by
  simp [RuntimeSubstitutionMap]

theorem runtimeSubstitutionMap_lookup_of_ne (binding : FormulaBinding)
    (rest : FiniteSubstitution) {name : String}
    (hne : name ≠ binding.variableName) :
    (RuntimeSubstitutionMap (binding :: rest))[name]? =
      (RuntimeSubstitutionMap rest)[name]? := by
  exact KernelExtras.HashMap.find?_insert_ne
    (RuntimeSubstitutionMap rest) hne binding.replacement.toRuntime

/-- A successful runtime lookup always came from an actual list binding, even
without key uniqueness.  At duplicate keys it identifies the first binding. -/
theorem runtimeSubstitutionMap_lookup_some_origin
    (substitution : FiniteSubstitution) (name : String)
    (runtime : RuntimeFormula)
    (hlookup : (RuntimeSubstitutionMap substitution)[name]? = some runtime) :
    ∃ replacement : ConstantHeadedFormula,
      LookupSemantics substitution name replacement ∧
        runtime = replacement.toRuntime := by
  induction substitution with
  | nil =>
      simp [RuntimeSubstitutionMap] at hlookup
  | cons binding rest ih =>
      by_cases hname : name = binding.variableName
      · subst name
        rw [runtimeSubstitutionMap_lookup_head] at hlookup
        have hruntime : runtime = binding.replacement.toRuntime := by
          exact Option.some.inj hlookup.symm
        exact ⟨binding.replacement, by simp [LookupSemantics], hruntime⟩
      · rw [runtimeSubstitutionMap_lookup_of_ne binding rest hname] at hlookup
        obtain ⟨replacement, hsemantics, hruntime⟩ := ih hlookup
        refine ⟨replacement, ?_, hruntime⟩
        exact List.mem_cons_of_mem binding hsemantics

/-- Every relational binding is the value selected by the runtime map once
duplicate source keys have been excluded. -/
theorem runtimeSubstitutionMap_lookup_of_semantics
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {name : String} {replacement : ConstantHeadedFormula}
    (hsemantics : LookupSemantics substitution name replacement) :
    (RuntimeSubstitutionMap substitution)[name]? =
      some replacement.toRuntime := by
  induction substitution with
  | nil => simp [LookupSemantics] at hsemantics
  | cons binding rest ih =>
      have hunique' := hunique
      simp only [SubstitutionKeysUnique, List.map_cons, List.nodup_cons]
        at hunique'
      rcases hunique' with ⟨hkey, hrest⟩
      change ({ variableName := name, replacement } : FormulaBinding) ∈
        binding :: rest at hsemantics
      rcases List.mem_cons.mp hsemantics with hhere | hthere
      · have hname : name = binding.variableName :=
          congrArg FormulaBinding.variableName hhere
        have hreplacement : replacement = binding.replacement :=
          congrArg FormulaBinding.replacement hhere
        subst name
        subst replacement
        exact runtimeSubstitutionMap_lookup_head binding rest
      · have hname : name ≠ binding.variableName := by
          intro heq
          have hlisted : name ∈
              rest.map fun entry => entry.variableName :=
            List.mem_map_of_mem
              (f := fun entry : FormulaBinding => entry.variableName) hthere
          exact hkey (by simpa [heq] using hlisted)
        rw [runtimeSubstitutionMap_lookup_of_ne binding rest hname]
        exact ih hrest hthere

/-- Exact lookup correspondence at the representation boundary. -/
theorem runtimeSubstitutionMap_lookup_iff
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (name : String) (replacement : ConstantHeadedFormula) :
    (RuntimeSubstitutionMap substitution)[name]? =
        some replacement.toRuntime ↔
      LookupSemantics substitution name replacement := by
  constructor
  · intro hlookup
    obtain ⟨actual, hactual, hruntime⟩ :=
      runtimeSubstitutionMap_lookup_some_origin substitution name
        replacement.toRuntime hlookup
    have : actual = replacement :=
      ConstantHeadedFormula.toRuntime_injective hruntime.symm
    simpa [this] using hactual
  · exact runtimeSubstitutionMap_lookup_of_semantics hunique

/-- Runtime absence means that no relational binding exists.  This statement
does not need key uniqueness. -/
theorem runtimeSubstitutionMap_lookup_none_iff
    (substitution : FiniteSubstitution) (name : String) :
    (RuntimeSubstitutionMap substitution)[name]? = none ↔
      ∀ replacement : ConstantHeadedFormula,
        ¬LookupSemantics substitution name replacement := by
  constructor
  · intro hnone replacement hsemantics
    induction substitution with
    | nil => simp [LookupSemantics] at hsemantics
    | cons binding rest ih =>
        change ({ variableName := name, replacement } : FormulaBinding) ∈
          binding :: rest at hsemantics
        rcases List.mem_cons.mp hsemantics with hhere | hthere
        · have hname : name = binding.variableName :=
            congrArg FormulaBinding.variableName hhere
          subst name
          rw [runtimeSubstitutionMap_lookup_head] at hnone
          contradiction
        · by_cases hname : name = binding.variableName
          · subst name
            rw [runtimeSubstitutionMap_lookup_head] at hnone
            contradiction
          · rw [runtimeSubstitutionMap_lookup_of_ne binding rest hname] at hnone
            exact ih hnone hthere
  · intro habsent
    cases hlookup : (RuntimeSubstitutionMap substitution)[name]? with
    | none => rfl
    | some runtime =>
        obtain ⟨replacement, hsemantics, _⟩ :=
          runtimeSubstitutionMap_lookup_some_origin substitution name runtime hlookup
        exact False.elim (habsent replacement hsemantics)

/-- Duplicate relational bindings are both visible, while the live map keeps
the first one.  Distinct replacements therefore cannot both satisfy the exact
runtime lookup equation. -/
theorem duplicate_key_boundary (name : String)
    (first second : ConstantHeadedFormula) (rest : FiniteSubstitution)
    (hne : first ≠ second) :
    LookupSemantics
        ({ variableName := name, replacement := first } ::
          { variableName := name, replacement := second } :: rest)
        name first ∧
      LookupSemantics
        ({ variableName := name, replacement := first } ::
          { variableName := name, replacement := second } :: rest)
        name second ∧
      (RuntimeSubstitutionMap
          ({ variableName := name, replacement := first } ::
            { variableName := name, replacement := second } :: rest))[name]? =
        some first.toRuntime ∧
      (RuntimeSubstitutionMap
          ({ variableName := name, replacement := first } ::
            { variableName := name, replacement := second } :: rest))[name]? ≠
        some second.toRuntime := by
  constructor
  · simp [LookupSemantics]
  constructor
  · simp [LookupSemantics]
  constructor
  · exact runtimeSubstitutionMap_lookup_head _ _
  · intro heq
    have hruntime : first.toRuntime = second.toRuntime := by
      simpa using
        (runtimeSubstitutionMap_lookup_head
          ({ variableName := name, replacement := first } : FormulaBinding)
          ({ variableName := name, replacement := second } :: rest)).symm.trans heq
    exact hne (ConstantHeadedFormula.toRuntime_injective hruntime)

/-! ## Proof-relevant body substitution and the live fold -/

private theorem replacement_fold_eq_body_fold
    (replacement : ConstantHeadedFormula) (acc : RuntimeFormula) :
    replacement.toRuntime.foldl (init := acc) (start := 1) Array.push =
      replacement.body.foldl Array.push acc := by
  apply Array.ext'
  rw [Metamath.Kernel.array_foldl_push_toList,
    Metamath.Kernel.list_foldl_push_toList]
  simp [ConstantHeadedFormula.toRuntime]

private theorem body_fold_eq_runtime_tail
    (typecode : String) (body : List RuntimeSym) :
    body.foldl Array.push #[.const typecode] =
      ({ typecode, body } : ConstantHeadedFormula).toRuntime := by
  apply Array.ext'
  rw [Metamath.Kernel.list_foldl_push_toList]
  simp [ConstantHeadedFormula.toRuntime]

/-- A semantic body-substitution derivation computes exactly the same array as
the verifier's `substStep` fold, from any accumulator. -/
theorem foldlM_substStep_of_bodySubstitution
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {source result : List RuntimeSym}
    (hsemantics : BodySubstitution substitution source result)
    (acc : RuntimeFormula) :
    source.foldlM
        (Metamath.Verify.Formula.substStep
          (RuntimeSubstitutionMap substitution)) acc =
      .ok (result.foldl Array.push acc) := by
  induction hsemantics generalizing acc with
  | nil => rfl
  | @const name sourceTail resultTail tail ih =>
      simpa [List.foldlM_cons, Metamath.Verify.Formula.substStep,
        Bind.bind, Except.bind] using ih (acc.push (.const name))
  | @var name replacement sourceTail resultTail binding tail ih =>
      have hlookup :
          (RuntimeSubstitutionMap substitution)[name]? =
            some replacement.toRuntime :=
        runtimeSubstitutionMap_lookup_of_semantics hunique binding
      have hreplacement := replacement_fold_eq_body_fold replacement acc
      simpa [List.foldlM_cons, Metamath.Verify.Formula.substStep, hlookup,
        Bind.bind, Except.bind, hreplacement, List.foldl_append] using
        ih (replacement.body.foldl Array.push acc)

/-- Formula substitution semantics implies the exact result produced by the
live verifier, not merely the existence of some successful output. -/
theorem runtime_subst_of_formulaSubstitutionSemantics
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {source result : ConstantHeadedFormula}
    (hsemantics : FormulaSubstitutionSemantics substitution source result) :
    source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
      .ok result.toRuntime := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases result with ⟨resultTypecode, resultBody⟩
  change sourceTypecode = resultTypecode ∧
      BodySubstitution substitution sourceBody resultBody at hsemantics
  rcases hsemantics with ⟨htypecode, hbody⟩
  subst resultTypecode
  have hfold :=
    foldlM_substStep_of_bodySubstitution hunique hbody
      (#[.const sourceTypecode] : RuntimeFormula)
  have hlist :
      (.const sourceTypecode :: sourceBody).foldlM
          (Metamath.Verify.Formula.substStep
            (RuntimeSubstitutionMap substitution)) #[] =
        .ok (resultBody.foldl Array.push #[.const sourceTypecode]) := by
    simpa [List.foldlM_cons, Metamath.Verify.Formula.substStep,
      Bind.bind, Except.bind] using hfold
  rw [body_fold_eq_runtime_tail sourceTypecode resultBody] at hlist
  unfold Metamath.Verify.Formula.subst
  rw [← Array.foldlM_toList]
  simpa [ConstantHeadedFormula.toRuntime] using hlist

/-! ## Success reflection -/

/-- If a `substStep` fold succeeds, every variable it encountered had a live
map entry.  This is the converse of the lookup-coverage lemma in
`Metamath.Kernel` and is the critical missing-variable reflection fact. -/
theorem foldlM_substStep_lookup_of_success
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    {symbols : List RuntimeSym} {acc result : RuntimeFormula}
    (hfold : symbols.foldlM
        (Metamath.Verify.Formula.substStep runtimeSubstitution) acc =
      .ok result) :
    ∀ {name : String}, .var name ∈ symbols →
      ∃ replacement : RuntimeFormula,
        runtimeSubstitution[name]? = some replacement := by
  induction symbols generalizing acc with
  | nil => simp
  | cons symbol rest ih =>
      intro name hmem
      cases symbol with
      | const constant =>
          have htail :
              rest.foldlM
                  (Metamath.Verify.Formula.substStep runtimeSubstitution)
                  (acc.push (.const constant)) = .ok result := by
            simpa [List.foldlM_cons, Metamath.Verify.Formula.substStep,
              Bind.bind, Except.bind] using hfold
          have hrest : .var name ∈ rest := by
            simpa using hmem
          exact ih htail hrest
      | var variableName =>
          cases hlookup : runtimeSubstitution[variableName]? with
          | none =>
              simp [List.foldlM_cons, Metamath.Verify.Formula.substStep,
                hlookup, Bind.bind, Except.bind] at hfold
          | some replacement =>
              rcases List.mem_cons.mp hmem with hhead | hrest
              · have hname : name = variableName := by
                  injection hhead
                subst name
                exact ⟨replacement, hlookup⟩
              · have htail :
                    rest.foldlM
                        (Metamath.Verify.Formula.substStep runtimeSubstitution)
                        (replacement.foldl (init := acc) (start := 1)
                          Array.push) = .ok result := by
                  simpa [List.foldlM_cons,
                    Metamath.Verify.Formula.substStep, hlookup,
                    Bind.bind, Except.bind] using hfold
                exact ih htail hrest

/-- A successful live substitution exposes an ordinary relational binding for
every variable in the canonical source body. -/
theorem lookupSemantics_of_runtime_subst_success
    {substitution : FiniteSubstitution}
    {source : ConstantHeadedFormula} {runtimeResult : RuntimeFormula}
    (hsubst : source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
      .ok runtimeResult) :
    ∀ {name : String}, .var name ∈ source.body →
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution name replacement := by
  intro name hmem
  have hfoldArray :
      source.toRuntime.foldlM
          (Metamath.Verify.Formula.substStep
            (RuntimeSubstitutionMap substitution)) #[] =
        .ok runtimeResult := hsubst
  have hfoldList :
      source.toRuntime.toList.foldlM
          (Metamath.Verify.Formula.substStep
            (RuntimeSubstitutionMap substitution)) #[] =
        .ok runtimeResult :=
    (Array.foldlM_toList
      (m := Except String) (xs := source.toRuntime)
      (f := Metamath.Verify.Formula.substStep
        (RuntimeSubstitutionMap substitution))
      (init := (#[] : RuntimeFormula))).trans hfoldArray
  have hmemRuntime : .var name ∈ source.toRuntime.toList := by
    simpa [ConstantHeadedFormula.toRuntime] using hmem
  obtain ⟨runtimeReplacement, hlookup⟩ :=
    foldlM_substStep_lookup_of_success
      (RuntimeSubstitutionMap substitution) hfoldList hmemRuntime
  obtain ⟨replacement, hsemantics, _⟩ :=
    runtimeSubstitutionMap_lookup_some_origin substitution name
      runtimeReplacement hlookup
  exact ⟨replacement, hsemantics⟩

/-- Lookup coverage constructs a proof-relevant body-substitution result. -/
theorem bodySubstitution_exists_of_lookupSemantics
    {substitution : FiniteSubstitution} {source : List RuntimeSym}
    (hlookup : ∀ {name : String}, .var name ∈ source →
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution name replacement) :
    ∃ result : List RuntimeSym,
      BodySubstitution substitution source result := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | cons symbol rest ih =>
      cases symbol with
      | const name =>
          have hrest : ∀ {variableName : String},
              .var variableName ∈ rest →
              ∃ replacement : ConstantHeadedFormula,
                LookupSemantics substitution variableName replacement := by
            intro variableName hmem
            exact hlookup (by simp [hmem])
          obtain ⟨resultTail, htail⟩ := ih hrest
          exact ⟨.const name :: resultTail, .const htail⟩
      | var name =>
          obtain ⟨replacement, hbinding⟩ :=
            hlookup (name := name) (by simp)
          have hrest : ∀ {variableName : String},
              .var variableName ∈ rest →
              ∃ image : ConstantHeadedFormula,
                LookupSemantics substitution variableName image := by
            intro variableName hmem
            exact hlookup (by simp [hmem])
          obtain ⟨resultTail, htail⟩ := ih hrest
          exact ⟨replacement.body ++ resultTail, .var hbinding htail⟩

/-- Every successful live computation has a canonical result related by the
independent formula-substitution semantics. -/
theorem formulaSubstitutionSemantics_exists_of_runtime_subst
    {substitution : FiniteSubstitution}
    {source : ConstantHeadedFormula} {runtimeResult : RuntimeFormula}
    (hsubst : source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
      .ok runtimeResult) :
    ∃ result : ConstantHeadedFormula,
      FormulaSubstitutionSemantics substitution source result := by
  have hlookup : ∀ {name : String}, .var name ∈ source.body →
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution name replacement :=
    lookupSemantics_of_runtime_subst_success hsubst
  obtain ⟨resultBody, hbody⟩ :=
    bodySubstitution_exists_of_lookupSemantics hlookup
  exact ⟨{ typecode := source.typecode, body := resultBody }, rfl, hbody⟩

/-- Under the source no-duplicate-key invariant, proof-relevant formula
substitution is exactly live verifier success with that exact result. -/
theorem formulaSubstitutionSemantics_iff_runtime_subst
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (source result : ConstantHeadedFormula) :
    FormulaSubstitutionSemantics substitution source result ↔
      source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
        .ok result.toRuntime := by
  constructor
  · exact runtime_subst_of_formulaSubstitutionSemantics hunique
  · intro hsubst
    obtain ⟨actual, hactual⟩ :=
      formulaSubstitutionSemantics_exists_of_runtime_subst hsubst
    have hactualRuntime :=
      runtime_subst_of_formulaSubstitutionSemantics hunique hactual
    have hruntime : actual.toRuntime = result.toRuntime :=
      Except.ok.inj (hactualRuntime.symm.trans hsubst)
    have hresult : actual = result :=
      ConstantHeadedFormula.toRuntime_injective hruntime
    simpa [hresult] using hactual

/-! ## Exact failure and derivability boundaries -/

/-- A key has some live map value exactly when the list relation contains at
least one binding at that key.  No uniqueness premise is required. -/
theorem runtimeSubstitutionMap_lookup_exists_iff
    (substitution : FiniteSubstitution) (name : String) :
    (∃ runtime : RuntimeFormula,
        (RuntimeSubstitutionMap substitution)[name]? = some runtime) ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution name replacement := by
  constructor
  · rintro ⟨runtime, hlookup⟩
    obtain ⟨replacement, hsemantics, _⟩ :=
      runtimeSubstitutionMap_lookup_some_origin substitution name runtime hlookup
    exact ⟨replacement, hsemantics⟩
  · rintro ⟨replacement, hsemantics⟩
    cases hlookup : (RuntimeSubstitutionMap substitution)[name]? with
    | none =>
        have habsent :=
          (runtimeSubstitutionMap_lookup_none_iff substitution name).mp hlookup
        exact False.elim (habsent replacement hsemantics)
    | some runtime => exact ⟨runtime, rfl⟩

/-- Once a prefix has successful lookup coverage, a missing next variable
produces the verifier's exact error message; the suffix is never evaluated. -/
theorem foldlM_substStep_error_at_first_missing
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (processed remainder : List RuntimeSym) (name : String)
    (acc : RuntimeFormula)
    (hprocessed : ∀ variableName,
      .var variableName ∈ processed →
        ∃ replacement, runtimeSubstitution[variableName]? = some replacement)
    (hmissing : runtimeSubstitution[name]? = none) :
    (processed ++ .var name :: remainder).foldlM
        (Metamath.Verify.Formula.substStep runtimeSubstitution) acc =
      .error s!"variable {name} not found" := by
  obtain ⟨middle, hfold⟩ :=
    Metamath.Kernel.foldlM_substStep_ok_of_lookup
      runtimeSubstitution processed acc hprocessed
  rw [List.foldlM_append, hfold]
  simp [List.foldlM_cons, Metamath.Verify.Formula.substStep, hmissing,
    Bind.bind, Except.bind]

/-- Source-list absence at the first uncovered variable is reflected with the
exact live `Formula.subst` error, including the variable name. -/
theorem runtime_subst_error_at_first_missing
    {substitution : FiniteSubstitution}
    {source : ConstantHeadedFormula}
    (processed remainder : List RuntimeSym)
    (name : String)
    (hbody : source.body = processed ++ .var name :: remainder)
    (hprocessed : ∀ variableName,
      .var variableName ∈ processed →
        ∃ replacement : ConstantHeadedFormula,
          LookupSemantics substitution variableName replacement)
    (hmissing : ∀ replacement : ConstantHeadedFormula,
      ¬LookupSemantics substitution name replacement) :
    source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
      .error s!"variable {name} not found" := by
  have hprefixRuntime : ∀ variableName,
      .var variableName ∈ (.const source.typecode :: processed) →
        ∃ replacement,
          (RuntimeSubstitutionMap substitution)[variableName]? =
            some replacement := by
    intro variableName hmem
    have hmemPrefix : .var variableName ∈ processed := by
      simpa using hmem
    obtain ⟨replacement, hsemantics⟩ :=
      hprocessed variableName hmemPrefix
    exact
      (runtimeSubstitutionMap_lookup_exists_iff substitution variableName).mpr
        ⟨replacement, hsemantics⟩
  have hmissingRuntime :
      (RuntimeSubstitutionMap substitution)[name]? = none :=
    (runtimeSubstitutionMap_lookup_none_iff substitution name).mpr hmissing
  have herror :=
    foldlM_substStep_error_at_first_missing
      (RuntimeSubstitutionMap substitution)
      (.const source.typecode :: processed) remainder name #[]
      hprefixRuntime hmissingRuntime
  unfold Metamath.Verify.Formula.subst
  rw [← Array.foldlM_toList]
  rw [show source.toRuntime.toList =
      .const source.typecode :: source.body by
        simp [ConstantHeadedFormula.toRuntime]]
  rw [hbody]
  simpa using herror

/-- Under unique keys, live failure is exactly the absence of any semantic
formula-substitution result. -/
theorem runtime_subst_failure_iff_no_semantic_result
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (source : ConstantHeadedFormula) :
    (∃ message : String,
        source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
          .error message) ↔
      ¬∃ result : ConstantHeadedFormula,
        FormulaSubstitutionSemantics substitution source result := by
  constructor
  · rintro ⟨message, herror⟩ ⟨result, hsemantics⟩
    have hsuccess :=
      runtime_subst_of_formulaSubstitutionSemantics hunique hsemantics
    rw [herror] at hsuccess
    contradiction
  · intro hnone
    cases hsubst : source.toRuntime.subst
        (RuntimeSubstitutionMap substitution) with
    | error message => exact ⟨message, rfl⟩
    | ok runtimeResult =>
        exact False.elim
          (hnone
            (formulaSubstitutionSemantics_exists_of_runtime_subst hsubst))

/-- The generated `ApplySubst` judgment checks exactly the same successful
substitution witness as the live verifier. -/
theorem applySubst_derivation_iff_runtime_subst
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (source result : ConstantHeadedFormula) :
    Nonempty
        (Derivation validatedSidePresentation
          (applySubst (encodeSubstitution substitution) (encodeFormula source)
            (encodeFormula result))) ↔
      source.toRuntime.subst (RuntimeSubstitutionMap substitution) =
        .ok result.toRuntime :=
  (applySubst_derivation_iff substitution source result).trans
    (formulaSubstitutionSemantics_iff_runtime_subst hunique source result)

end Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
