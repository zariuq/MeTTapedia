import Mettapedia.Languages.MM0.Upstream.Lean3Conversion
import Mettapedia.Languages.MM0.Presentation.SpecificationCorrespondence

/-!
# Upstream-style MM0 proofs and checked declaration streams

The reference predicates adapt `env.get_thm`, `proof`, and `env.extend` from
`mm0-lean/mm0/mm0.lean`, revision
`6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/mm0-lean/mm0/mm0.lean

`HistoricalProof` retains the original one-context safety and historical
conversion. `SpecifiedProof` uses the explicitly separated contexts and
current specified conversion. These predicates do not implement a checker.
The old theorem lookup erases numeric theorem identifiers; its correspondence
therefore quantifies an actual identifier with the same complete payload.

The extension adapter retains the historical `defn_def` rule separately. The
specified rule uses the source prefix on the source side, and is derived from
real checked specification runs. Structural extension alone is not admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3ProofAdmission

open Lean3Typing Lean3Typing.Reference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies dataEqualityHost)

namespace Reference

def getTheorem (environment : Env) (formal : Context) (hypotheses : List SExpr)
    (conclusion : SExpr) : Prop :=
  .ax formal hypotheses conclusion ∈ environment ∨ .thm formal hypotheses conclusion ∈ environment

inductive HistoricalProof (environment : Env) (context : Context) (hypotheses : Set SExpr) :
    SExpr → Prop where
  | hypothesis {expression : SExpr} : expression ∈ hypotheses →
      HistoricalProof environment context hypotheses expression
  | theoremApp {formal : Context} {premises : List SExpr} {conclusion : SExpr}
      {images : List SExpr} :
      getTheorem environment formal premises conclusion →
      List.Forall₂ (FitsBinder environment context) images formal →
      Lean3Admissibility.Reference.historicalSafeSubst context images →
      (∀ premise ∈ premises, HistoricalProof environment context hypotheses
        (Lean3Dependencies.Reference.substitute images premise)) →
      HistoricalProof environment context hypotheses
        (Lean3Dependencies.Reference.substitute images conclusion)
  | conversion {left right : SExpr} {sort : Nat} :
      Lean3Conversion.Reference.HistoricalConverts environment context left right [] sort →
      HistoricalProof environment context hypotheses left →
      HistoricalProof environment context hypotheses right

inductive SpecifiedProof (environment : Env) (context : Context) (hypotheses : Set SExpr) :
    SExpr → Prop where
  | hypothesis {expression : SExpr} : expression ∈ hypotheses →
      SpecifiedProof environment context hypotheses expression
  | theoremApp {formal : Context} {premises : List SExpr} {conclusion : SExpr}
      {images : List SExpr} :
      getTheorem environment formal premises conclusion →
      List.Forall₂ (FitsBinder environment context) images formal →
      Lean3Admissibility.Reference.specifiedSafeSubst formal context images →
      (∀ premise ∈ premises, SpecifiedProof environment context hypotheses
        (Lean3Dependencies.Reference.substitute images premise)) →
      SpecifiedProof environment context hypotheses
        (Lean3Dependencies.Reference.substitute images conclusion)
  | conversion {left right : SExpr} {sort : Nat} :
      Lean3Conversion.Reference.SpecifiedConverts environment context left right [] sort →
      SpecifiedProof environment context hypotheses left →
      SpecifiedProof environment context hypotheses right

inductive HistoricalExtends : Env → Env → Prop where
  | nil : HistoricalExtends [] []
  | keep {source target : Env} {declaration : Decl} : HistoricalExtends source target →
      HistoricalExtends (source ++ [declaration]) (target ++ [declaration])
  | definitionSkip {source target : Env} {symbol : Nat} {formal : Context} {returned : DepType}
      {body : Option (List Nat × SExpr)} : HistoricalExtends source target →
      HistoricalExtends source (target ++ [.defn symbol formal returned body])
  | definitionFill {source target : Env} {symbol : Nat} {formal : Context} {returned : DepType}
      {body : Option (List Nat × SExpr)} : HistoricalExtends source target →
      HistoricalExtends (target ++ [.defn symbol formal returned none])
        (target ++ [.defn symbol formal returned body])
  | theoremSkip {source target : Env} {formal : Context} {premises : List SExpr} {conclusion : SExpr} :
      HistoricalExtends source target →
      HistoricalExtends source (target ++ [.thm formal premises conclusion])

inductive SpecifiedExtends : Env → Env → Prop where
  | nil : SpecifiedExtends [] []
  | keep {source target : Env} {declaration : Decl} : SpecifiedExtends source target →
      SpecifiedExtends (source ++ [declaration]) (target ++ [declaration])
  | definitionSkip {source target : Env} {symbol : Nat} {formal : Context} {returned : DepType}
      {body : Option (List Nat × SExpr)} : SpecifiedExtends source target →
      SpecifiedExtends source (target ++ [.defn symbol formal returned body])
  | definitionFill {source target : Env} {symbol : Nat} {formal : Context} {returned : DepType}
      {body : List Nat × SExpr} : SpecifiedExtends source target →
      SpecifiedExtends (source ++ [.defn symbol formal returned none])
        (target ++ [.defn symbol formal returned (some body)])
  | theoremSkip {source target : Env} {formal : Context} {premises : List SExpr} {conclusion : SExpr} :
      SpecifiedExtends source target →
      SpecifiedExtends source (target ++ [.thm formal premises conclusion])

def theoremDecl (formal : Context) (premises : List SExpr) (conclusion : SExpr) : Kernel.TheoremDecl :=
  ⟨toContext formal, premises.map SExpr.toKernel, conclusion.toKernel⟩

@[simp] theorem theoremDecl_ofKernel (declaration : Kernel.TheoremDecl) :
    theoremDecl (ofContext declaration.arguments) (declaration.hypotheses.map SExpr.ofKernel)
      (SExpr.ofKernel declaration.conclusion) = declaration := by
  cases declaration
  simp [theoremDecl, List.map_map, Function.comp_def]

theorem theoremDecl_eq_iff (formal : Context) (premises : List SExpr) (conclusion : SExpr)
    (declaration : Kernel.TheoremDecl) : theoremDecl formal premises conclusion = declaration ↔
      formal = ofContext declaration.arguments ∧ premises = declaration.hypotheses.map SExpr.ofKernel ∧
        conclusion = SExpr.ofKernel declaration.conclusion := by
  constructor
  · intro same
    have translated := congrArg (fun d : Kernel.TheoremDecl =>
      (ofContext d.arguments, d.hypotheses.map SExpr.ofKernel, SExpr.ofKernel d.conclusion)) same
    simpa only [theoremDecl, ofContext_toContext, List.map_map, Function.comp_def,
      SExpr.ofKernel_toKernel, List.map_id', Prod.mk.injEq] using translated
  · rintro ⟨rfl, rfl, rfl⟩; exact theoremDecl_ofKernel _

theorem getTheorem_append (environment : Env) (declaration : Decl) (formal : Context)
    (premises : List SExpr) (conclusion : SExpr) :
    getTheorem (environment ++ [declaration]) formal premises conclusion ↔
      getTheorem environment formal premises conclusion ∨ declaration = .ax formal premises conclusion ∨
        declaration = .thm formal premises conclusion := by
  simp only [getTheorem, List.mem_append, List.mem_singleton]
  tauto

end Reference

/-- Complete payload agreement, including all hypotheses and their order.
The existential identifier reflects its erasure in the historical lookup. -/
def TheoremsRelated (environment : Env) (theory : Kernel.Theory) : Prop :=
  ∀ formal premises conclusion, Reference.getTheorem environment formal premises conclusion ↔
    ∃ index, theory.theoremSignature index = some (Reference.theoremDecl formal premises conclusion)

private theorem lookup_insert_iff {α : Type} (entries : List (Nat × α)) (key index : Nat)
    (entry value : α) (fresh : entries.lookup key = none) :
    ((key, entry) :: entries).lookup index = some value ↔
      (index = key ∧ entry = value) ∨ entries.lookup index = some value := by
  by_cases same : index = key
  · subst index; simp [fresh]
  · have unequal : (index == key) = false := by simp [same]
    simp [List.lookup_cons, unequal, same]

private theorem exists_insert_iff {α : Type} (entries : List (Nat × α)) (key : Nat)
    (entry value : α) (fresh : entries.lookup key = none) :
    (∃ index, ((key, entry) :: entries).lookup index = some value) ↔
      entry = value ∨ ∃ index, entries.lookup index = some value := by
  simp only [lookup_insert_iff entries key _ entry value fresh, exists_or,
    exists_eq_left]

private theorem stored_payload_iff (formal : Context) (premises : List SExpr) (conclusion : SExpr)
    (declaration : Kernel.TheoremDecl) : declaration = Reference.theoremDecl formal premises conclusion ↔
      ofContext declaration.arguments = formal ∧ declaration.hypotheses.map SExpr.ofKernel = premises ∧
        SExpr.ofKernel declaration.conclusion = conclusion := by
  rw [eq_comm, Reference.theoremDecl_eq_iff]
  constructor <;> rintro ⟨formalEq, premisesEq, conclusionEq⟩ <;>
    exact ⟨formalEq.symm, premisesEq.symm, conclusionEq.symm⟩

theorem empty_theorems_related : TheoremsRelated [] ({} : Kernel.Theory) := by
  intro formal premises conclusion
  simp [Reference.getTheorem, Kernel.Theory.theoremSignature]

theorem step_theorems_related {environment : Env} {before after : Kernel.Theory}
    {admission : Kernel.Admission} (related : TheoremsRelated environment before)
    (checked : Kernel.Theory.Step before admission after) :
    TheoremsRelated (environment ++ [projectAdmission admission]) after := by
  cases checked with
  | intro authorized =>
      intro formal premises conclusion
      rw [Reference.getTheorem_append]
      cases authorized with
      | sort fresh =>
          simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.theoremSignature]
            using (related formal premises conclusion)
      | term fresh admitted =>
          simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.theoremSignature]
            using (related formal premises conclusion)
      | definition fresh freshBody admitted body =>
          simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.theoremSignature]
            using (related formal premises conclusion)
      | axiomDecl fresh admitted =>
          rw [related]
          simp only [projectAdmission, Kernel.Admission.insert, Kernel.Theory.theoremSignature, reduceCtorEq]
          rw [exists_insert_iff _ _ _ _ fresh, stored_payload_iff]
          simp only [Decl.ax.injEq]
          tauto
      | theoremDecl fresh admitted allowed checkedProof =>
          rw [related]
          simp only [projectAdmission, Kernel.Admission.insert, Kernel.Theory.theoremSignature, reduceCtorEq]
          rw [exists_insert_iff _ _ _ _ fresh, stored_payload_iff]
          simp only [Decl.thm.injEq]
          tauto

theorem runs_theorems_related {environment : Env} {before after : Kernel.Theory}
    {admissions : List Kernel.Admission} (related : TheoremsRelated environment before)
    (checked : Kernel.Theory.Runs before admissions after) :
    TheoremsRelated (environment ++ projectRun admissions) after := by
  induction checked generalizing environment with
  | nil => simpa only [projectRun, List.map_nil, List.append_nil] using related
  | cons first rest ih =>
      simpa only [projectRun, List.map_cons, List.append_assoc, List.singleton_append] using
        ih (step_theorems_related related first)

theorem checked_run_theorems_related {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) :
    TheoremsRelated (projectRun admissions) theory := by
  simpa using runs_theorems_related empty_theorems_related
    ((Kernel.Theory.run_eq_some_iff _ _ _).mp checked)

private theorem typed_total_substitution {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory) {formal target : Context}
    {source : SExpr} {sort : Nat} {images : List SExpr}
    (typed : Typed environment formal source [] sort)
    (fits : List.Forall₂ (FitsBinder environment target) images formal) :
    Kernel.Preterm.Substitutes (Kernel.Substitution.ofList (images.map SExpr.toKernel)) source.toKernel
      (Lean3Dependencies.Reference.substitute images source).toKernel := by
  apply Kernel.Preterm.substitute_sound
  apply (Lean3Dependencies.substitution_iff _ _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.length_map, SExpr.ofKernel_toKernel] using
      Lean3Dependencies.typed_images_cover_source terms typed fits
  · simp only [List.map_map, Function.comp_def, SExpr.ofKernel_toKernel, List.map_id']

private theorem substitutions_map {images sources : List SExpr}
    (pointwise : ∀ source ∈ sources,
      Kernel.Preterm.Substitutes (Kernel.Substitution.ofList (images.map SExpr.toKernel)) source.toKernel
        (Lean3Dependencies.Reference.substitute images source).toKernel) :
    List.Forall₂ (Kernel.Preterm.Substitutes (Kernel.Substitution.ofList (images.map SExpr.toKernel)))
      (sources.map SExpr.toKernel)
      (sources.map (fun source => (Lean3Dependencies.Reference.substitute images source).toKernel)) := by
  revert pointwise
  induction sources with
  | nil => intro _; exact .nil
  | cons source sources ih =>
      intro pointwise
      exact .cons (pointwise _ (by simp))
        (ih (fun expression member => pointwise expression (List.mem_cons_of_mem _ member)))

/-- Actual admitted theorem typing supplies the full substitution domain;
neither historical total lookup defaults nor safety alone supply it. -/
theorem specified_instantiates {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory) (theorems : TheoremsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) {formal target : Context}
    {premises : List SExpr} {conclusion : SExpr} {images : List SExpr}
    (known : Reference.getTheorem environment formal premises conclusion)
    (fits : List.Forall₂ (FitsBinder environment target) images formal)
    (safe : Lean3Admissibility.Reference.specifiedSafeSubst formal target images) :
    ∃ index, theory.theoremSignature index = some (Reference.theoremDecl formal premises conclusion) ∧
      Kernel.TheoremDecl.Instantiates theory.termSignature (toContext target)
        (Reference.theoremDecl formal premises conclusion) (images.map SExpr.toKernel)
        ⟨premises.map (fun premise => (Lean3Dependencies.Reference.substitute images premise).toKernel),
          (Lean3Dependencies.Reference.substitute images conclusion).toKernel⟩ := by
  obtain ⟨index, lookup⟩ := (theorems _ _ _).mp known
  have admitted := valid.theorems _ _ lookup
  have imagesAdmissible : Kernel.Substitution.Admissible theory.termSignature
      (toContext formal) (toContext target) (images.map SExpr.toKernel) := by
    apply (Lean3Admissibility.admissible_iff terms _ _ _).mpr
    simpa only [ofContext_toContext, List.map_map, Function.comp_def,
      SExpr.ofKernel_toKernel, List.map_id'] using And.intro fits safe
  have substituted : ∀ source ∈ conclusion :: premises,
      Kernel.Preterm.Substitutes (Kernel.Substitution.ofList (images.map SExpr.toKernel)) source.toKernel
        (Lean3Dependencies.Reference.substitute images source).toKernel := by
    intro source member
    have statement : Kernel.Preterm.IsStatement theory.sortSignature theory.termSignature
        (toContext formal) source.toKernel := by
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted.conclusion
      · exact admitted.hypotheses _ (List.mem_map_of_mem member)
    obtain ⟨sort, info, typed, declared, provable⟩ := statement
    apply typed_total_substitution terms (sort := sort) _ fits
    simpa only [ofContext_toContext, SExpr.ofKernel_toKernel,
      show ofContext ([] : Kernel.Context) = [] from rfl] using typed_ofKernel terms typed
  refine ⟨index, lookup, imagesAdmissible, ?_, substituted conclusion (by simp)⟩
  exact substitutions_map (fun source member => substituted source (List.mem_cons_of_mem _ member))

def sourceHypotheses (hypotheses : List Kernel.Preterm) : Set SExpr :=
  {expression | expression.toKernel ∈ hypotheses}

theorem specified_proof_toKernel {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (theorems : TheoremsRelated environment theory) (valid : Kernel.Theory.WellFormed theory)
    {context : Context} {hypotheses : List Kernel.Preterm} {conclusion : SExpr}
    (derived : Reference.SpecifiedProof environment context (sourceHypotheses hypotheses) conclusion) :
    Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      (toContext context) hypotheses conclusion.toKernel := by
  induction derived with
  | hypothesis member => exact .hypothesis member
  | @theoremApp formal premises conclusion images known fits safe children ih =>
      obtain ⟨index, lookup, instantiation⟩ := specified_instantiates terms theorems valid known fits safe
      apply Kernel.Derives.theoremApp lookup instantiation
      apply (Kernel.derivesList_iff _ _ _ _ _ _).mpr
      intro result member
      change result ∈ premises.map (fun premise =>
        (Lean3Dependencies.Reference.substitute images premise).toKernel) at member
      obtain ⟨premise, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih premise sourceMember
  | conversion converted _ ih =>
      exact .conversion (Lean3Conversion.specified_toKernel terms bodies valid converted) ih

private theorem substituted_list_translation {arguments sources results : List Kernel.Preterm}
    (substituted : List.Forall₂ (Kernel.Preterm.Substitutes (Kernel.Substitution.ofList arguments))
      sources results) :
    results.map SExpr.ofKernel = sources.map (fun source =>
      Lean3Dependencies.Reference.substitute (arguments.map SExpr.ofKernel) (SExpr.ofKernel source)) := by
  induction substituted with
  | nil => rfl
  | cons first _ ih =>
      simp only [List.map_cons, Lean3Dependencies.substitution_of_derivation first, ih]

theorem specified_proof_ofKernel {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (theorems : TheoremsRelated environment theory) (valid : Kernel.Theory.WellFormed theory)
    {context : Kernel.Context} {hypotheses : List Kernel.Preterm} {conclusion : Kernel.Preterm}
    (derived : Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses conclusion) :
    Reference.SpecifiedProof environment (ofContext context) (sourceHypotheses hypotheses)
      (SExpr.ofKernel conclusion) := by
  induction derived using Kernel.Derives.rec
      (motive_2 := fun expressions _ => ∀ expression ∈ expressions,
        Reference.SpecifiedProof environment (ofContext context) (sourceHypotheses hypotheses)
          (SExpr.ofKernel expression)) with
  | hypothesis member => exact .hypothesis (by simpa only [sourceHypotheses, Set.mem_ofPred_eq,
        SExpr.toKernel_ofKernel] using member)
  | @theoremApp index declaration arguments instantiation lookup instantiated _ ih =>
      have known := (theorems (ofContext declaration.arguments)
        (declaration.hypotheses.map SExpr.ofKernel) (SExpr.ofKernel declaration.conclusion)).mpr
        ⟨index, by simpa only [Reference.theoremDecl_ofKernel] using lookup⟩
      have conditions := (Lean3Admissibility.admissible_iff terms _ _ _).mp instantiated.admissible
      have premises : ∀ premise ∈ declaration.hypotheses.map SExpr.ofKernel,
          Reference.SpecifiedProof environment (ofContext context) (sourceHypotheses hypotheses)
            (Lean3Dependencies.Reference.substitute (arguments.map SExpr.ofKernel) premise) := by
        intro premise member
        obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
        have inResults : Lean3Dependencies.Reference.substitute (arguments.map SExpr.ofKernel)
            (SExpr.ofKernel source) ∈ instantiation.hypotheses.map SExpr.ofKernel := by
          rw [substituted_list_translation instantiated.hypotheses]
          exact List.mem_map_of_mem sourceMember
        obtain ⟨result, member, same⟩ := List.mem_map.mp inResults
        exact same ▸ ih result member
      simpa only [Lean3Dependencies.substitution_of_derivation instantiated.conclusion] using
        Reference.SpecifiedProof.theoremApp known conditions.1 conditions.2 premises
  | conversion converted _ ih =>
      exact .conversion (Lean3Conversion.specified_ofKernel terms bodies valid converted) ih
  | nil => rename_i expression member; cases member
  | @cons expression expressions _ _ ihHead ihTail =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihHead
      · exact ihTail value member

theorem specified_proof_iff {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (theorems : TheoremsRelated environment theory) (valid : Kernel.Theory.WellFormed theory)
    (context : Kernel.Context) (hypotheses : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Reference.SpecifiedProof environment (ofContext context) (sourceHypotheses hypotheses)
      (SExpr.ofKernel conclusion) ↔
      Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses conclusion := by
  constructor
  · intro derived
    simpa only [toContext_ofContext, SExpr.toKernel_ofKernel] using
      specified_proof_toKernel terms bodies theorems valid derived
  · exact specified_proof_ofKernel terms bodies theorems valid

theorem checked_run_proof_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Reference.SpecifiedProof (projectRun admissions) (ofContext context) (sourceHypotheses hypotheses)
      (SExpr.ofKernel conclusion) ↔
      Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses conclusion :=
  specified_proof_iff (checked_run_environment_related checked)
    (Lean3Unfolding.checked_run_definitions_related checked) (checked_run_theorems_related checked)
    (Kernel.Theory.run_from_empty_wellFormed checked) context hypotheses conclusion

def projectSpecification : Kernel.SpecificationEntry → Decl
  | .sort index info => .sort index (SortData.ofKernel info)
  | .term index declaration => .term index (ofContext declaration.arguments)
      (declaration.resultSort, declaration.dependencies)
  | .definition index declaration body => .defn index (ofContext declaration.arguments)
      (declaration.resultSort, declaration.dependencies)
      (body.map (fun stored => (stored.dummies, SExpr.ofKernel stored.expression)))
  | .axiomDecl _ declaration => .ax (ofContext declaration.arguments)
      (declaration.hypotheses.map SExpr.ofKernel) (SExpr.ofKernel declaration.conclusion)
  | .theoremDecl _ declaration => .thm (ofContext declaration.arguments)
      (declaration.hypotheses.map SExpr.ofKernel) (SExpr.ofKernel declaration.conclusion)

private theorem specified_extends_append {source target : Env}
    (extended : Reference.SpecifiedExtends source target) (suffix : Env) :
    Reference.SpecifiedExtends (source ++ suffix) (target ++ suffix) := by
  induction suffix generalizing source target with
  | nil => simpa only [List.append_nil] using extended
  | cons declaration remaining ih =>
      simpa only [List.append_assoc, List.singleton_append] using
        ih (Reference.SpecifiedExtends.keep (declaration := declaration) extended)

theorem matched_specification_extension {source target : Env}
    (extended : Reference.SpecifiedExtends source target) {entry : Kernel.SpecificationEntry}
    {admission : Kernel.Admission} (matched : Kernel.SpecificationEntry.Matches entry admission) :
    Reference.SpecifiedExtends (source ++ [projectSpecification entry])
      (target ++ [projectAdmission admission]) := by
  cases matched with
  | sort => exact .keep extended
  | term => exact .keep extended
  | axiomDecl => exact .keep extended
  | theoremDecl => exact .keep extended
  | definition index declaration expected actual allowed =>
      rcases allowed with rfl | rfl
      · exact .definitionFill extended
      · exact .keep extended

theorem auxiliary_specification_extension {source target : Env}
    (extended : Reference.SpecifiedExtends source target) {admission : Kernel.Admission}
    (auxiliary : Kernel.ProofDeclaration.Auxiliary admission) :
    Reference.SpecifiedExtends source (target ++ [projectAdmission admission]) := by
  cases auxiliary with
  | definition => exact .definitionSkip extended
  | theoremDecl => exact .theoremSkip extended

/-- The actual ordered public/local stream constructs the specified extension;
neither the historical typo nor an assumed source/target equality is used. -/
theorem runs_specification_extension {before after : Kernel.SpecificationAdmission.State}
    {declarations : List Kernel.ProofDeclaration}
    (checked : Kernel.SpecificationAdmission.Runs before declarations after) :
    ∀ source target, Reference.SpecifiedExtends source target →
      Reference.SpecifiedExtends (source ++ before.pending.map projectSpecification)
        (target ++ projectRun (declarations.map Kernel.ProofDeclaration.admission) ++
          after.pending.map projectSpecification) := by
  induction checked with
  | nil state =>
      intro source target extended
      simpa only [List.map_nil, projectRun, List.append_nil] using
        specified_extends_append extended (state.pending.map projectSpecification)
  | @cons before middle after head tail step rest ih =>
      intro source target extended
      cases step with
      | @auxiliary prior next pending admission auxiliary step =>
          simpa only [List.map_cons, projectRun, List.map_nil, Kernel.ProofDeclaration.admission,
            List.append_assoc, List.singleton_append] using
            ih source (target ++ [projectAdmission admission])
              (auxiliary_specification_extension extended auxiliary)
      | @publicDecl prior next entry pending admission matched step =>
          simpa only [List.map_cons, projectRun, List.map_nil, Kernel.ProofDeclaration.admission,
            List.append_assoc, List.singleton_append] using
            ih (source ++ [projectSpecification entry]) (target ++ [projectAdmission admission])
              (matched_specification_extension extended matched)

theorem checked_specification_extension {specification : List Kernel.SpecificationEntry}
    {declarations : List Kernel.ProofDeclaration} {theory : Kernel.Theory}
    (checked : Kernel.SpecificationAdmission.verify? specification declarations = some theory) :
    Reference.SpecifiedExtends (specification.map projectSpecification)
      (projectRun (declarations.map Kernel.ProofDeclaration.admission)) := by
  simpa only [List.nil_append, List.map_nil, List.append_nil] using
    runs_specification_extension ((Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mp checked)
      [] [] Reference.SpecifiedExtends.nil

theorem checked_specification_proof_iff {specification : List Kernel.SpecificationEntry}
    {declarations : List Kernel.ProofDeclaration} {theory : Kernel.Theory}
    (checked : Kernel.SpecificationAdmission.verify? specification declarations = some theory)
    (context : Kernel.Context) (hypotheses : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Reference.SpecifiedProof (projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (ofContext context) (sourceHypotheses hypotheses) (SExpr.ofKernel conclusion) ↔
      Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses conclusion :=
  checked_run_proof_iff ((Kernel.Theory.run_eq_some_iff _ _ _).mpr
    ((Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mp checked).theory_run)
    context hypotheses conclusion

/-- The full authored specification entry establishes structural alignment and
the exact authorized axiom basis. It also retains the particular checked
witness; logical derivability elsewhere cannot replace that witness. -/
theorem authored_verified_proof {specification : List Kernel.SpecificationEntry}
    {declarations : List Kernel.ProofDeclaration} {theory : Kernel.Theory}
    (admitted : Applies Presentation.ComputationalSpecification.specificationProgram dataEqualityHost
      "mm0:spec-verify" [Presentation.ComputationalSpecification.encodeEntries specification,
        Presentation.ComputationalSpecification.encodeProofDeclarations declarations]
      (Presentation.ComputationalAdmission.encodeTheoryResult (some theory)))
    {context : Kernel.Context} {hypotheses : List Kernel.Preterm} {witness : Kernel.ProofWitness}
    {conclusion : Kernel.Preterm}
    (accepted : Applies Presentation.ComputationalSpecification.specificationProgram dataEqualityHost
      "mm0:check-proof" [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
        Presentation.ComputationalProof.encodeTheorems theory.theorems,
        Presentation.ComputationalContext.encodeContext context,
        Presentation.ComputationalArguments.encodeExpressions hypotheses,
        Presentation.ComputationalProof.encodeProof witness, Presentation.encode conclusion] (.sym "True")) :
    Reference.SpecifiedExtends (specification.map projectSpecification)
      (projectRun (declarations.map Kernel.ProofDeclaration.admission)) ∧
    Kernel.SpecificationAdmission.declarationAxioms declarations =
      Kernel.SpecificationAdmission.specificationAxioms specification ∧
    Kernel.ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses witness conclusion ∧
    Reference.SpecifiedProof (projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (ofContext context) (sourceHypotheses hypotheses) (SExpr.ofKernel conclusion) := by
  have runs := (Presentation.ComputationalSpecification.verify_accepts_iff _ _ _).mp admitted
  have verified := (Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mpr runs
  have checked := (Presentation.ComputationalSpecification.supplied_proof_accepts_iff _ _ _ _ _).mp accepted
  exact ⟨checked_specification_extension verified,
    Kernel.SpecificationAdmission.verified_axioms_exact verified, checked,
    (checked_specification_proof_iff verified context hypotheses conclusion).mpr checked.derives⟩

theorem authored_verified_proof_iff_exists {specification : List Kernel.SpecificationEntry}
    {declarations : List Kernel.ProofDeclaration} {theory : Kernel.Theory}
    (admitted : Applies Presentation.ComputationalSpecification.specificationProgram dataEqualityHost
      "mm0:spec-verify" [Presentation.ComputationalSpecification.encodeEntries specification,
        Presentation.ComputationalSpecification.encodeProofDeclarations declarations]
      (Presentation.ComputationalAdmission.encodeTheoryResult (some theory)))
    (context : Kernel.Context) (hypotheses : List Kernel.Preterm) (conclusion : Kernel.Preterm) :
    Reference.SpecifiedProof (projectRun (declarations.map Kernel.ProofDeclaration.admission))
      (ofContext context) (sourceHypotheses hypotheses) (SExpr.ofKernel conclusion) ↔
      ∃ witness, Applies Presentation.ComputationalSpecification.specificationProgram dataEqualityHost
        "mm0:check-proof" [Presentation.ComputationalTyping.encodeTable theory.terms,
          Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
          Presentation.ComputationalProof.encodeTheorems theory.theorems,
          Presentation.ComputationalContext.encodeContext context,
          Presentation.ComputationalArguments.encodeExpressions hypotheses,
          Presentation.ComputationalProof.encodeProof witness, Presentation.encode conclusion] (.sym "True") := by
  have verified := (Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mpr
    ((Presentation.ComputationalSpecification.verify_accepts_iff _ _ _).mp admitted)
  rw [checked_specification_proof_iff verified]
  exact Presentation.ComputationalSpecification.derives_iff_supplied_proof _ _ _ _

namespace Controls

open Kernel

private def claim : TheoremDecl := ⟨[], [], .term 0⟩
private def foldedClaim : TheoremDecl := ⟨[], [], .term 1⟩
private def foldWitness : ProofWitness :=
  .conversion (.symm (.unfold 1 [] [])) (.theoremApp 10 [] [])
private def history : List Admission := [
  .sort 0 {}, .sort 1 { provable := true }, .term 0 ⟨[], 1, ∅⟩,
  .definition 1 ⟨[], 1, ∅⟩ ⟨[], .term 0⟩, .axiomDecl 10 claim,
  .theoremDecl 11 foldedClaim [] foldWitness]
private def theory : Theory := history.foldl (fun state declaration => declaration.insert state) {}
private def specification : List SpecificationEntry := [
  .sort 0 {}, .sort 1 { provable := true }, .term 0 ⟨[], 1, ∅⟩,
  .definition 1 ⟨[], 1, ∅⟩ none, .axiomDecl 10 claim, .theoremDecl 11 foldedClaim]
private def declarations : List ProofDeclaration := history.map (fun admission => ⟨admission, false⟩)

theorem actual_specification_run_succeeds :
    SpecificationAdmission.verify? specification declarations = some theory := by
  apply (SpecificationAdmission.verify_eq_some_iff _ _ _).mpr
  refine .cons (.publicDecl (.sort _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
    (.cons (.publicDecl (.sort _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
      (.cons (.publicDecl (.term _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
        (.cons (.publicDecl (.definition _ _ none _ (.inl rfl))
          (.intro ((Admission.check_iff _ _).mp ?_)))
          (.cons (.publicDecl (.axiomDecl _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
            (.cons (.publicDecl (.theoremDecl _ _ _ _) (.intro ((Admission.check_iff _ _).mp ?_)))
              (.nil _))))))
  all_goals decide +kernel

theorem omitted_definition_is_filled_in_order :
    Reference.SpecifiedExtends (specification.map projectSpecification) (projectRun history) := by
  simpa only [declarations, List.map_map, Function.comp_def, projectRun] using
    checked_specification_extension actual_specification_run_succeeds

private theorem stored_proof_checked : ProofWitness.Checks theory.termSignature theory.definitionSignature
    theory.theoremSignature [] [] (.theoremApp 11 [] []) (.term 1) :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mp (by decide +kernel)

theorem stored_theorem_has_specified_source_proof :
    Reference.SpecifiedProof (projectRun history) [] (sourceHypotheses []) (.term 1) := by
  simpa only [declarations, List.map_map, Function.comp_def, ofContext, List.map_nil,
    SExpr.ofKernel, projectRun] using
    (checked_specification_proof_iff actual_specification_run_succeeds [] [] (.term 1)).mpr
      stored_proof_checked.derives

theorem admitted_axiom_basis_retains_full_payload :
    SpecificationAdmission.declarationAxioms declarations = [(10, claim)] := by
  rw [SpecificationAdmission.verified_axioms_exact actual_specification_run_succeeds]
  rfl

theorem bad_supplied_witness_cannot_use_another_derivation :
    Reference.SpecifiedProof (projectRun history) [] (sourceHypotheses []) (.term 1) ∧
      ¬ ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        [] [] (.hyp 0) (.term 1) := by
  refine ⟨stored_theorem_has_specified_source_proof, ?_⟩
  intro checked
  cases checked with
  | hyp lookup => simp at lookup

theorem logically_admissible_extra_axiom_is_not_specification_authorized :
    Admission.check theory (.axiomDecl 12 claim) = true ∧
      SpecificationAdmission.step? ⟨theory, []⟩ ⟨.axiomDecl 12 claim, false⟩ = none := by
  constructor
  · decide +kernel
  · rfl

theorem wrong_stored_conclusion_is_refused :
    ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
      [] [] (.theoremApp 11 [] []) (.term 0) = false := by decide +kernel

theorem preceding_empty_theory_cannot_use_the_later_theorem :
    ProofWitness.proof? ({} : Theory).termSignature ({} : Theory).definitionSignature
      ({} : Theory).theoremSignature [] [] (.theoremApp 11 [] []) = none := by decide +kernel

private def auxiliary : Decl := .defn 7 [] (1, ∅) (some ([], .term 0))
private def opaqueDefinition : Decl := .defn 8 [] (1, ∅) none
private def filled : Decl := .defn 8 [] (1, ∅) (some ([], .term 0))

theorem specified_fill_keeps_the_original_source_prefix :
    Reference.SpecifiedExtends [opaqueDefinition] [auxiliary, filled] :=
  .definitionFill (.definitionSkip .nil)

theorem historical_fill_uses_its_target_prefix_on_both_sides :
    Reference.HistoricalExtends [auxiliary, opaqueDefinition] [auxiliary, filled] :=
  .definitionFill (.definitionSkip .nil)

theorem structural_extension_does_not_check_undefined_bodies :
    Reference.SpecifiedExtends [] [.defn 0 [] (0, ∅) (some ([], .var 99))] ∧
      Theory.step? {} (.definition 0 ⟨[], 0, ∅⟩ ⟨[], .var 99⟩) = none := by
  exact ⟨.definitionSkip .nil, by decide +kernel⟩

private def repeatedClaim : TheoremDecl := ⟨[.bound 0, .regular 1 {0}], [.var 1, .var 1], .var 1⟩
private def repeatedHistory : List Admission := [
  .sort 0 {}, .sort 1 { provable := true }, .axiomDecl 10 repeatedClaim]
private def repeatedTheory : Theory := repeatedHistory.foldl (fun state declaration => declaration.insert state) {}
private def repeatedTarget : Kernel.Context := [.bound 0, .regular 1 {0}]

theorem dependent_repeated_premises_are_admitted : Theory.run? {} repeatedHistory = some repeatedTheory := by
  apply (Theory.run_eq_some_iff _ _ _).mpr
  refine .cons (.intro ((Admission.check_iff _ _).mp ?_))
    (.cons (.intro ((Admission.check_iff _ _).mp ?_))
      (.cons (.intro ((Admission.check_iff _ _).mp ?_)) (.nil _)))
  all_goals decide +kernel

theorem dependent_theorem_application_retains_both_premises :
    Reference.SpecifiedProof (projectRun repeatedHistory) (ofContext repeatedTarget)
      (sourceHypotheses [.var 1]) (.var 1) := by
  apply (checked_run_proof_iff dependent_repeated_premises_are_admitted repeatedTarget [.var 1] (.var 1)).mpr
  apply ProofWitness.Checks.derives (witness := .theoremApp 10 [.var 0, .var 1] [.hyp 0, .hyp 0])
  apply (ProofWitness.check_iff _ _ _ _ _ _ _).mp
  decide +kernel

theorem a_missing_repeated_premise_is_refused :
    ProofWitness.proof? repeatedTheory.termSignature repeatedTheory.definitionSignature
      repeatedTheory.theoremSignature repeatedTarget [.var 1]
      (.theoremApp 10 [.var 0, .var 1] [.hyp 0]) = none := by decide +kernel

private def duplicateHistory : List Admission :=
  [.axiomDecl 10 claim, .theoremDecl 10 foldedClaim [] (.hyp 0)]
private def duplicateTheory : Theory := { theorems := [(10, foldedClaim), (10, claim)] }

theorem raw_duplicate_history_retains_the_shadowed_payload :
    Reference.getTheorem (projectRun duplicateHistory) [] [] (.term 0) := by
  exact .inl (by simp [projectRun, duplicateHistory, projectAdmission, claim, ofContext, SExpr.ofKernel])

theorem raw_duplicate_payloads_are_not_coherent :
    ¬ TheoremsRelated (projectRun duplicateHistory) duplicateTheory := by
  intro related
  obtain ⟨index, found⟩ := (related [] [] (.term 0)).mp raw_duplicate_history_retains_the_shadowed_payload
  by_cases same : index = 10
  · subst index
    have payload : foldedClaim = Reference.theoremDecl [] [] (.term 0) := by
      simpa [duplicateTheory, Theory.theoremSignature, List.lookup_cons] using found
    have bad := congrArg TheoremDecl.conclusion payload
    change (Preterm.term 1) = Preterm.term 0 at bad
    cases bad
  · have unequal : (index == 10) = false := by simp [same]
    simp [duplicateTheory, Theory.theoremSignature, List.lookup_cons, unequal] at found

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3ProofAdmission
