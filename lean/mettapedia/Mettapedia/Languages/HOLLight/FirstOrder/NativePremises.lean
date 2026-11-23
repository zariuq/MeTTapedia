import Mettapedia.GSLT.LanguageDef.NativePremiseCompilation
import Mettapedia.Languages.HOLLight.FirstOrder.Completeness
import Mettapedia.Languages.HOLLight.FirstOrder.PortableKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability

/-! Two computational premises of the portable HOL Light rule catalog.
Type inference remains partial in the supplied binder frame. Type
instantiation works on the source's scoped representation and keeps a free
variable free even when its new type coincides with a binder annotation.
Both handlers leave theorem-producing rules and unselected calls in place. -/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.FirstOrder.NativePremises

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NativePremiseCompilation
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability

variable {axioms : List Sequent} {d : ValidatedCalculusLanguageDef}

def typeOf (Γ : List Ty) (t : DBTerm) : Handler :=
  functional "hol.TypeOf" [contextP Γ, groundP (encodeTerm t)]
    (fun _ => (t.inferType Γ).map (fun ty => groundP (encodeTy ty)))

def instType (entries : List (Ty × Ty)) (t : DBTerm) : Handler :=
  functional "hol.TermTyAct" [typeMapletsP entries, groundP (encodeTerm t)]
    (fun _ => some (groundP (encodeTerm ((TermSubst.mk (SourceSubstitution.typeSubstitution entries) []).applyDB t))))

variable (catalog : d.1 = holCalculus axioms) (policy : AxiomPolicy)
  (licensed : ∀ s ∈ axioms, s.hyp = ∅ ∧ policy s ∧ s.IsBool)

include catalog policy licensed in
theorem typeOf_valid (Γ : List Ty) (t : DBTerm) : ValidFor d (typeOf Γ t) := by
  apply valid_functional
  intro output
  constructor
  · rintro h
    obtain ⟨ty, inferred, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨deriveTypeOf catalog Γ t ty inferred⟩
  · rintro ⟨proof⟩
    have meaning : TypeOfMeaning (contextP Γ) (groundP (encodeTerm t)) output :=
      holCalculus_sound policy licensed catalog proof
    obtain ⟨term, ty, termEq, outEq, inferred⟩ := meaning Γ rfl
    obtain rfl := encodeTerm_injective (groundP_injective termEq)
    exact Option.map_eq_some_iff.mpr ⟨ty, inferred, outEq.symm⟩

include catalog policy licensed in
theorem instType_valid (entries : List (Ty × Ty)) (t : DBTerm) : ValidFor d (instType entries t) := by
  apply valid_functional
  intro output
  rw [applyDB_typeOnly]
  constructor
  · intro outputEq
    obtain rfl := Option.some.inj outputEq
    exact ⟨deriveTermTyAct catalog entries t⟩
  · rintro ⟨proof⟩
    have meaning : TermTyActMeaning (typeMapletsP entries) (groundP (encodeTerm t)) output :=
      holCalculus_sound policy licensed catalog proof
    exact congrArg some (meaning entries t rfl rfl).symm

include policy licensed in
/-- Literal module loading fixes the catalog used on both sides. Any
finite proof using the specialized premises has a protected source run,
and every protected source judgment remains derivable with specialization. -/
theorem compiled_iff_hosted
    (loaded : ModuleFormat.Portable.readValidatedCalculus? (kernelModule axioms) = some d)
    (Γ : List Ty) (entries : List (Ty × Ty)) (t : DBTerm) (goal : Pattern) :
    Mettapedia.Logic.Derives (NativePremiseCompilation.Rule d (NativePremiseCompilation.orElse (typeOf Γ t) (instType entries t))) goal ↔
      Reaches d goal := by
  rw [kernelModule_read] at loaded
  obtain rfl := Option.some.inj loaded
  exact (derives_iff (valid_orElse (typeOf_valid rfl policy licensed Γ t)
    (instType_valid rfl policy licensed entries t)) goal).trans (reaches_iff_derivation _ _).symm

/-! ## Occurrence emission

Use the existing protected kernel's locations, request encoding, rights and
installed rule IDs. Only the computation selecting the read slots changes. -/
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (mem_fire)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceSchemaActivation (Tm judgment)
open InferenceRequestExecution (Occurrence label location payload system postRule)

def activation (d : ValidatedCalculusLanguageDef) (h : Handler) :
    InferenceSchemaKernel.SourceSchema Unit → InferenceSchemaKernel.Inputs Tm →
      Option (Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleInstance Value)
  | .inl id, .inl args => do
      let schema ← d.1.lookupRule? id
      let (reads, result) ← compile d h ⟨id,args⟩
      return InferenceSchemaKernel.locate (InferenceSchemaActivation.fromResult id schema args reads result)
  | .inr (), .inr data => some (postRule data)
  | _, _ => none

/-- Fire with the residual reads in order. One protected occurrence may
serve several reads; a request occurrence can never serve as a theorem
premise. The result spends just its request and keeps the previous store
apart from that ticket and its single fresh output. -/
theorem compiled_fires (d : ValidatedCalculusLanguageDef) (h : Handler)
    (call : InferenceChecker.RuleInstance) (schema : RuleSchema) (ps : List Pattern) (goal : Pattern)
    (installed : d.1.lookupRule? call.ruleId = some schema)
    (compiled : compile d h call = some (ps,goal)) (before : Configuration Value Occurrence)
    (background : locatedAction.Consistent before.equations) (ticket : Occurrence)
    (live : ticket ∈ before.present)
    (input : label ticket = (.requests, InferenceSchemaActivation.request call.ruleId schema call.arguments))
    (available : ∀ p ∈ ps, ∃ o ∈ before.present, label o = (.judgments, judgment p)) :
    ∃ after output, (system d).authority.Step (activation d h) locatedAction label true before after ∧
      output ∉ before.present ∧ label output = (.judgments, judgment goal) ∧
      after.present = insert output (before.present.erase ticket) := by
  let request := InferenceSchemaActivation.request call.ruleId schema call.arguments
  obtain ⟨reads, present, labels⟩ := Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.exists_list_of_mem label before.present
    (ps.map (fun p => (Space.judgments, judgment p))) (by
      intro v m; obtain ⟨p, member, rfl⟩ := List.mem_map.mp m; exact available p member)
  obtain ⟨output, fresh, emitted⟩ := IndexedOccurrences.supply before.present (Space.judgments, judgment goal)
  let raw := InferenceSchemaActivation.fromResult call.ruleId schema call.arguments ps goal
  let rule := InferenceSchemaKernel.locate raw
  let picked : Selection Occurrence := ⟨[ticket], reads, [output]⟩
  have notRead : ticket ∉ reads := by
    intro m
    have inside := List.mem_map_of_mem (f := label) m
    rw [labels, input] at inside
    obtain ⟨_, _, impossible⟩ := List.mem_map.mp inside
    cases impossible
  have valid : picked.Valid locatedAction label rule before := by
    refine ⟨by simp [picked], by simp [picked], rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [picked, rule, raw, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult] using (congrArg List.length labels).symm
    · simpa [picked, rule, raw, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult] using emitted
    · constructor <;> simp [picked, Selection.commit, live, fresh, notRead]
      exact fun _ m => present _ (List.mem_toFinset.mp m)
    · obtain ⟨assignment, solved⟩ := background
      refine ⟨assignment, ?_⟩
      change locatedAction.Models assignment (before.equations ++
        Selection.equations label [(Space.requests, request)] [ticket] ++
        Selection.equations label ((ps.map judgment).map (fun v => (Space.judgments, v))) reads ++ [])
      simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true, List.map_map, Function.comp_def]
      rw [← labels, show (Space.requests, request) = label ticket from input.symm]
      exact ⟨⟨solved, RequestActivation.self_equations locatedAction assignment label [ticket]⟩,
        RequestActivation.self_equations locatedAction assignment label reads⟩
    · intro check member; cases member
  refine ⟨picked.result label rule before, output, ?_, fresh, emitted, ?_⟩
  · refine ⟨.inl call.ruleId, ?_, .inl call.arguments, rule, ?_, picked, valid, ?_, rfl⟩
    · refine List.mem_map.mpr ⟨schema, List.mem_of_find?_eq_some installed, ?_⟩
      exact congrArg Sum.inl (by simpa using List.find?_some installed)
    · simp [activation, installed, compiled, rule, raw]
    · intro occurrence made; rfl
  · ext o
    simp [Selection.result, picked, Selection.commit, mem_fire, and_comm, or_comm]

end Mettapedia.Languages.HOLLight.FirstOrder.NativePremises
