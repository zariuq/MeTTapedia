import Mettapedia.Languages.MM0.Presentation.TypingTheory

/-!
# The common typing fragment of the pinned MM0 Lean 3 specification

The independent `Reference` datatypes and four typing constructors below are
an attributable Lean 4 adaptation of `mm0-lean/mm0/mm0.lean`, lines 6–57 and
86–105, at upstream revision `6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/mm0-lean/mm0/mm0.lean

Application spines, bound slots, regular slots, residual arity and full term
declaration payloads are retained. The original environment uses membership;
the current store uses first-key lookup. `EnvironmentRelated` connects those
storage observations, and is derived for actual checked runs from empty.
It is not an assumed typing or checking equivalence.

This module does not port the historical free-variable, admissibility,
conversion or proof relations. Their recorded differences require separate
bridges. In particular, absence of an explicit transitivity constructor in
the old conversion relation is not asserted to separate its semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3Typing

namespace Reference

structure SortData where
  pure : Bool := false
  strict : Bool := false
  provable : Bool := false
  free : Bool := false
  deriving DecidableEq

inductive Binder where
  | bound : Nat → Binder
  | reg : Nat → Finset Nat → Binder
  deriving DecidableEq

def Binder.sort : Binder → Nat
  | .bound sort => sort
  | .reg sort _ => sort

inductive SExpr where
  | var : Nat → SExpr
  | term : Nat → SExpr
  | app1 : SExpr → SExpr → SExpr
  deriving DecidableEq

abbrev Context := List Binder
abbrev DepType := Nat × Finset Nat

inductive Decl where
  | sort : Nat → SortData → Decl
  | term : Nat → Context → DepType → Decl
  | defn : Nat → Context → DepType → Option (List Nat × SExpr) → Decl
  | ax : Context → List SExpr → SExpr → Decl
  | thm : Context → List SExpr → SExpr → Decl

abbrev Env := List Decl

def getSort (environment : Env) (index : Nat) (info : SortData) : Prop :=
  .sort index info ∈ environment

inductive GetTerm (environment : Env) (index : Nat) (arguments : Context) (result : DepType) :
    Option (List Nat × SExpr) → Prop where
  | term : .term index arguments result ∈ environment → GetTerm environment index arguments result none
  | defn {body : Option (List Nat × SExpr)} : .defn index arguments result body ∈ environment →
      GetTerm environment index arguments result body

/-- The upstream `sexpr.ok'`, including unsaturated expressions. -/
inductive Typed (environment : Env) (context : Context) : SExpr → Context → Nat → Prop where
  | var {index : Nat} {binder : Binder} : context[index]? = some binder →
      Typed environment context (.var index) [] binder.sort
  | term {index : Nat} {arguments : Context} {result : DepType}
      {body : Option (List Nat × SExpr)} : GetTerm environment index arguments result body →
      Typed environment context (.term index) arguments result.1
  | appVar {function : SExpr} {sort index result : Nat} {remaining : Context} :
      context[index]? = some (.bound sort) →
      Typed environment context function (.bound sort :: remaining) result →
      Typed environment context (.app1 function (.var index)) remaining result
  | appReg {function argument : SExpr} {sort result : Nat} {dependencies : Finset Nat}
      {remaining : Context} :
      Typed environment context function (.reg sort dependencies :: remaining) result →
      Typed environment context argument [] sort →
      Typed environment context (.app1 function argument) remaining result

def FitsBinder (environment : Env) (context : Context) (expression : SExpr) : Binder → Prop
  | .bound sort => ∃ index, expression = .var index ∧ context[index]? = some (.bound sort)
  | .reg sort _ => Typed environment context expression [] sort

def SortData.toKernel (info : SortData) : Kernel.SortInfo :=
  ⟨info.pure, info.strict, info.provable, info.free⟩

def SortData.ofKernel (info : Kernel.SortInfo) : SortData :=
  ⟨info.pure, info.strict, info.provable, info.free⟩

def Binder.toKernel : Binder → Kernel.Binder
  | .bound sort => .bound sort
  | .reg sort dependencies => .regular sort dependencies

def Binder.ofKernel : Kernel.Binder → Binder
  | .bound sort => .bound sort
  | .regular sort dependencies => .reg sort dependencies

def toContext (context : Context) : Kernel.Context := context.map Binder.toKernel
def ofContext (context : Kernel.Context) : Context := context.map Binder.ofKernel

def SExpr.toKernel : SExpr → Kernel.Preterm
  | .var index => .var index
  | .term index => .term index
  | .app1 function argument => .app function.toKernel argument.toKernel

def SExpr.ofKernel : Kernel.Preterm → SExpr
  | .var index => .var index
  | .term index => .term index
  | .app function argument => .app1 (ofKernel function) (ofKernel argument)

@[simp] theorem SortData.ofKernel_toKernel (info : SortData) :
    ofKernel info.toKernel = info := by cases info; rfl

@[simp] theorem SortData.toKernel_ofKernel (info : Kernel.SortInfo) :
    (ofKernel info).toKernel = info := by cases info; rfl

@[simp] theorem Binder.ofKernel_toKernel (binder : Binder) :
    ofKernel binder.toKernel = binder := by cases binder <;> rfl

@[simp] theorem Binder.toKernel_ofKernel (binder : Kernel.Binder) :
    (ofKernel binder).toKernel = binder := by cases binder <;> rfl

@[simp] theorem ofContext_toContext (context : Context) : ofContext (toContext context) = context := by
  simp [ofContext, toContext, List.map_map, Function.comp_def]

@[simp] theorem toContext_ofContext (context : Kernel.Context) : toContext (ofContext context) = context := by
  simp [ofContext, toContext, List.map_map, Function.comp_def]

theorem toContext_lookup {context : Context} {index : Nat} {binder : Binder}
    (lookup : context[index]? = some binder) :
    (toContext context)[index]? = some binder.toKernel := by
  rw [toContext, List.getElem?_map, lookup]
  rfl

theorem ofContext_lookup {context : Kernel.Context} {index : Nat} {binder : Kernel.Binder}
    (lookup : context[index]? = some binder) :
    (ofContext context)[index]? = some (Binder.ofKernel binder) := by
  rw [ofContext, List.getElem?_map, lookup]
  rfl

@[simp] theorem SExpr.ofKernel_toKernel (expression : SExpr) :
    ofKernel expression.toKernel = expression := by
  induction expression <;> simp_all [toKernel, ofKernel]

@[simp] theorem SExpr.toKernel_ofKernel (expression : Kernel.Preterm) :
    (ofKernel expression).toKernel = expression := by
  induction expression <;> simp_all [toKernel, ofKernel]

@[simp] theorem Binder.sort_toKernel (binder : Binder) : binder.toKernel.sort = binder.sort := by
  cases binder <;> rfl

@[simp] theorem Binder.sort_ofKernel (binder : Kernel.Binder) : (ofKernel binder).sort = binder.sort := by
  cases binder <;> rfl

def termDecl (arguments : Context) (result : DepType) : Kernel.TermDecl :=
  ⟨toContext arguments, result.1, result.2⟩

@[simp] theorem termDecl_ofKernel (declaration : Kernel.TermDecl) :
    termDecl (ofContext declaration.arguments) (declaration.resultSort, declaration.dependencies) =
      declaration := by cases declaration; simp [termDecl]

theorem termDecl_eq_iff (arguments : Context) (result : DepType) (declaration : Kernel.TermDecl) :
    termDecl arguments result = declaration ↔
      arguments = ofContext declaration.arguments ∧ result = (declaration.resultSort, declaration.dependencies) := by
  constructor
  · intro same
    subst declaration
    simp [termDecl]
  · rintro ⟨rfl, rfl⟩
    exact termDecl_ofKernel declaration

theorem getTerm_exists_iff (environment : Env) (index : Nat) (arguments : Context) (result : DepType) :
    (∃ body, GetTerm environment index arguments result body) ↔
      .term index arguments result ∈ environment ∨
        ∃ body, .defn index arguments result body ∈ environment := by
  constructor
  · rintro ⟨body, present⟩
    cases present with
    | term member => exact Or.inl member
    | defn member => exact Or.inr ⟨_, member⟩
  · rintro (member | ⟨body, member⟩)
    · exact ⟨none, .term member⟩
    · exact ⟨body, .defn member⟩

theorem getSort_append (environment : Env) (declaration : Decl) (index : Nat) (info : SortData) :
    getSort (environment ++ [declaration]) index info ↔
      getSort environment index info ∨ .sort index info = declaration := by
  simp [getSort]

theorem getTerm_append (environment : Env) (declaration : Decl) (index : Nat)
    (arguments : Context) (result : DepType) :
    (∃ body, GetTerm (environment ++ [declaration]) index arguments result body) ↔
      (∃ body, GetTerm environment index arguments result body) ∨
        (∃ body, GetTerm [declaration] index arguments result body) := by
  simp only [getTerm_exists_iff, List.mem_append]
  aesop

@[simp] theorem getTerm_single_sort (key : Nat) (info : SortData) (index : Nat)
    (arguments : Context) (result : DepType) :
    ¬ ∃ body, GetTerm [.sort key info] index arguments result body := by
  simp [getTerm_exists_iff]

@[simp] theorem getTerm_single_term (key index : Nat) (stored arguments : Context)
    (returned result : DepType) :
    (∃ body, GetTerm [.term key stored returned] index arguments result body) ↔
      index = key ∧ arguments = stored ∧ result = returned := by
  simp [getTerm_exists_iff]

@[simp] theorem getTerm_single_defn (key index : Nat) (stored arguments : Context)
    (returned result : DepType) (definition : Option (List Nat × SExpr)) :
    (∃ body, GetTerm [.defn key stored returned definition] index arguments result body) ↔
      index = key ∧ arguments = stored ∧ result = returned := by
  simp [getTerm_exists_iff]

@[simp] theorem getTerm_single_ax (stored : Context) (hypotheses : List SExpr) (conclusion : SExpr)
    (index : Nat) (arguments : Context) (result : DepType) :
    ¬ ∃ body, GetTerm [.ax stored hypotheses conclusion] index arguments result body := by
  simp [getTerm_exists_iff]

@[simp] theorem getTerm_single_thm (stored : Context) (hypotheses : List SExpr) (conclusion : SExpr)
    (index : Nat) (arguments : Context) (result : DepType) :
    ¬ ∃ body, GetTerm [.thm stored hypotheses conclusion] index arguments result body := by
  simp [getTerm_exists_iff]

theorem SortData.ofKernel_eq_iff (info : Kernel.SortInfo) (source : SortData) :
    ofKernel info = source ↔ info = source.toKernel := by
  constructor
  · intro same
    simpa using congrArg toKernel same
  · intro same
    simpa using congrArg ofKernel same

end Reference

/-- Equality of actual declaration observations, before any typing judgment. -/
structure EnvironmentRelated (environment : Reference.Env) (theory : Kernel.Theory) : Prop where
  sorts : ∀ index info, Reference.getSort environment index info ↔
    theory.sortSignature index = some info.toKernel
  terms : ∀ index arguments result, (∃ body, Reference.GetTerm environment index arguments result body) ↔
    theory.termSignature index = some (Reference.termDecl arguments result)

theorem typed_toKernel {environment : Reference.Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context remaining : Reference.Context}
    {expression : Reference.SExpr} {sort : Nat}
    (typed : Reference.Typed environment context expression remaining sort) :
    Kernel.Preterm.HasType theory.termSignature (Reference.toContext context) expression.toKernel
      (Reference.toContext remaining) sort := by
  induction typed with
  | var lookup =>
      simpa only [Reference.SExpr.toKernel, Reference.toContext, List.map_nil,
        Reference.Binder.sort_toKernel] using
        Kernel.Preterm.HasType.var (signature := theory.termSignature) (Reference.toContext_lookup lookup)
  | term present => exact .term ((related.terms _ _ _).mp ⟨_, present⟩)
  | appVar lookup _ ih =>
      exact .bound ih (Reference.toContext_lookup lookup)
  | appReg _ _ ihFunction ihArgument => exact .regular ihFunction ihArgument

theorem typed_ofKernel {environment : Reference.Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context remaining : Kernel.Context}
    {expression : Kernel.Preterm} {sort : Nat}
    (typed : Kernel.Preterm.HasType theory.termSignature context expression remaining sort) :
    Reference.Typed environment (Reference.ofContext context) (Reference.SExpr.ofKernel expression)
      (Reference.ofContext remaining) sort := by
  induction typed with
  | var lookup =>
      simpa only [Reference.SExpr.ofKernel, Reference.ofContext, List.map_nil,
        Reference.Binder.sort_ofKernel] using
        Reference.Typed.var (environment := environment) (Reference.ofContext_lookup lookup)
  | term lookup =>
      rename_i index declaration
      obtain ⟨body, present⟩ := (related.terms index (Reference.ofContext declaration.arguments)
        (declaration.resultSort, declaration.dependencies)).mpr (by simpa only [Reference.termDecl_ofKernel] using lookup)
      exact .term present
  | bound _ lookup ih =>
      exact .appVar (Reference.ofContext_lookup lookup) ih
  | regular _ _ ihFunction ihArgument => exact .appReg ihFunction ihArgument

theorem typed_iff {environment : Reference.Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (context remaining : Reference.Context)
    (expression : Reference.SExpr) (sort : Nat) :
    Reference.Typed environment context expression remaining sort ↔
      Kernel.Preterm.HasType theory.termSignature (Reference.toContext context) expression.toKernel
        (Reference.toContext remaining) sort := by
  exact ⟨typed_toKernel related, fun typed => by simpa using typed_ofKernel related typed⟩

theorem fitsBinder_ofKernel {environment : Reference.Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) {context : Kernel.Context}
    {expression : Kernel.Preterm} {binder : Kernel.Binder}
    (fits : Kernel.Preterm.FitsBinder theory.termSignature context expression binder) :
    Reference.FitsBinder environment (Reference.ofContext context)
      (Reference.SExpr.ofKernel expression) (Reference.Binder.ofKernel binder) := by
  cases fits with
  | bound lookup => exact ⟨_, rfl, Reference.ofContext_lookup lookup⟩
  | regular typed => exact typed_ofKernel related typed

theorem fitsBinder_iff {environment : Reference.Env} {theory : Kernel.Theory}
    (related : EnvironmentRelated environment theory) (context : Reference.Context)
    (expression : Reference.SExpr) (binder : Reference.Binder) :
    Reference.FitsBinder environment context expression binder ↔
      Kernel.Preterm.FitsBinder theory.termSignature (Reference.toContext context)
        expression.toKernel binder.toKernel := by
  constructor
  · intro fits
    cases binder with
    | bound sort =>
        obtain ⟨index, rfl, lookup⟩ := fits
        exact .bound (Reference.toContext_lookup lookup)
    | reg sort dependencies => exact .regular (typed_toKernel related fits)
  · intro fits
    simpa using fitsBinder_ofKernel related fits

/-- Project the stored logical payload, retaining the original declaration kind.
The old theorem declaration has no numeric theorem identifier or proof field;
this projection claims only sort/term observations, not theorem admission. -/
def projectAdmission : Kernel.Admission → Reference.Decl
  | .sort index info => .sort index (Reference.SortData.ofKernel info)
  | .term index declaration => .term index (Reference.ofContext declaration.arguments)
      (declaration.resultSort, declaration.dependencies)
  | .definition index declaration body => .defn index (Reference.ofContext declaration.arguments)
      (declaration.resultSort, declaration.dependencies)
      (some (body.dummies, Reference.SExpr.ofKernel body.expression))
  | .axiomDecl _ declaration => .ax (Reference.ofContext declaration.arguments)
      (declaration.hypotheses.map Reference.SExpr.ofKernel) (Reference.SExpr.ofKernel declaration.conclusion)
  | .theoremDecl _ declaration _ _ => .thm (Reference.ofContext declaration.arguments)
      (declaration.hypotheses.map Reference.SExpr.ofKernel) (Reference.SExpr.ofKernel declaration.conclusion)

def projectRun (admissions : List Kernel.Admission) : Reference.Env := admissions.map projectAdmission

private theorem lookup_insert_iff {α : Type} (entries : List (Nat × α)) (key index : Nat)
    (entry value : α) (fresh : entries.lookup key = none) :
    ((key, entry) :: entries).lookup index = some value ↔
      (index = key ∧ entry = value) ∨ entries.lookup index = some value := by
  by_cases same : index = key
  · subst index
    simp [fresh]
  · have unequal : (index == key) = false := by simp [same]
    simp [List.lookup_cons, unequal, same]

theorem empty_environment_related : EnvironmentRelated [] ({} : Kernel.Theory) := by
  constructor
  · intro index info
    simp [Reference.getSort, Kernel.Theory.sortSignature]
  · intro index arguments result
    simp [Reference.getTerm_exists_iff, Kernel.Theory.termSignature]

theorem step_environment_related {environment : Reference.Env} {before after : Kernel.Theory}
    {admission : Kernel.Admission} (related : EnvironmentRelated environment before)
    (checked : Kernel.Theory.Step before admission after) :
    EnvironmentRelated (environment ++ [projectAdmission admission]) after := by
  cases checked with
  | intro authorized =>
      cases authorized with
      | sort fresh =>
          constructor
          · intro index info
            rw [Reference.getSort_append]
            change Reference.getSort environment index info ∨
              Reference.Decl.sort index info = Reference.Decl.sort _ _ ↔
              ((_, _) :: before.sorts).lookup index = some info.toKernel
            rw [lookup_insert_iff _ _ _ _ _ fresh, related.sorts]
            simp only [Reference.Decl.sort.injEq]
            rw [← Reference.SortData.ofKernel_eq_iff]
            tauto
          · intro index arguments result
            rw [Reference.getTerm_append]
            simpa only [projectAdmission, Reference.getTerm_single_sort, or_false,
              Kernel.Admission.insert, Kernel.Theory.termSignature] using related.terms index arguments result
      | @term key declaration fresh _ =>
          constructor
          · intro index info
            rw [Reference.getSort_append]
            simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.sortSignature]
              using related.sorts index info
          · intro index arguments result
            rw [Reference.getTerm_append]
            change (∃ body, Reference.GetTerm environment index arguments result body) ∨
              (∃ body, Reference.GetTerm [Reference.Decl.term _ _ _] index arguments result body) ↔
              ((_, _) :: before.terms).lookup index = some (Reference.termDecl arguments result)
            rw [Reference.getTerm_single_term, lookup_insert_iff _ _ _ _ _ fresh, related.terms]
            rw [eq_comm (a := declaration) (b := Reference.termDecl arguments result), Reference.termDecl_eq_iff]
            tauto
      | @definition key declaration body fresh _ _ _ =>
          constructor
          · intro index info
            rw [Reference.getSort_append]
            simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.sortSignature]
              using related.sorts index info
          · intro index arguments result
            rw [Reference.getTerm_append]
            change (∃ body, Reference.GetTerm environment index arguments result body) ∨
              (∃ body, Reference.GetTerm [Reference.Decl.defn _ _ _ _] index arguments result body) ↔
              ((_, _) :: before.terms).lookup index = some (Reference.termDecl arguments result)
            rw [Reference.getTerm_single_defn, lookup_insert_iff _ _ _ _ _ fresh, related.terms]
            rw [eq_comm (a := declaration) (b := Reference.termDecl arguments result), Reference.termDecl_eq_iff]
            tauto
      | axiomDecl _ _ =>
          constructor
          · intro index info
            rw [Reference.getSort_append]
            simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.sortSignature]
              using related.sorts index info
          · intro index arguments result
            rw [Reference.getTerm_append]
            simpa only [projectAdmission, Reference.getTerm_single_ax, or_false,
              Kernel.Admission.insert, Kernel.Theory.termSignature] using related.terms index arguments result
      | theoremDecl _ _ _ _ =>
          constructor
          · intro index info
            rw [Reference.getSort_append]
            simpa [projectAdmission, Kernel.Admission.insert, Kernel.Theory.sortSignature]
              using related.sorts index info
          · intro index arguments result
            rw [Reference.getTerm_append]
            simpa only [projectAdmission, Reference.getTerm_single_thm, or_false,
              Kernel.Admission.insert, Kernel.Theory.termSignature] using related.terms index arguments result

theorem runs_environment_related {environment : Reference.Env} {before after : Kernel.Theory}
    {admissions : List Kernel.Admission} (related : EnvironmentRelated environment before)
    (checked : Kernel.Theory.Runs before admissions after) :
    EnvironmentRelated (environment ++ projectRun admissions) after := by
  induction checked generalizing environment with
  | nil theory => simpa [projectRun] using related
  | cons step _ ih =>
      simpa [projectRun, List.append_assoc] using ih (step_environment_related related step)

theorem checked_run_environment_related {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) :
    EnvironmentRelated (projectRun admissions) theory := by
  simpa using runs_environment_related empty_environment_related
    ((Kernel.Theory.run_eq_some_iff _ _ _).mp checked)

theorem checked_run_typing_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context remaining : Kernel.Context)
    (expression : Kernel.Preterm) (sort : Nat) :
    Reference.Typed (projectRun admissions) (Reference.ofContext context)
      (Reference.SExpr.ofKernel expression) (Reference.ofContext remaining) sort ↔
      Kernel.Preterm.HasType theory.termSignature context expression remaining sort := by
  simpa using typed_iff (checked_run_environment_related checked)
    (Reference.ofContext context) (Reference.ofContext remaining) (Reference.SExpr.ofKernel expression) sort

open Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- The actual authored typing entry is accepted exactly by the pinned common
typing rules on the concrete environment of a successful checked run. -/
theorem admitted_authored_typing_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context remaining : Kernel.Context)
    (expression : Kernel.Preterm) (sort : Nat) :
    Applies Presentation.ComputationalTyping.typingProgram computationalHost
      "mm0:infer" [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext context, Presentation.encode expression]
      (Presentation.ComputationalTyping.encodeType (some (remaining, sort))) ↔
      Reference.Typed (projectRun admissions) (Reference.ofContext context)
        (Reference.SExpr.ofKernel expression) (Reference.ofContext remaining) sort := by
  exact (Presentation.ComputationalTyping.theory_infer_accepts_iff _ _ _ _ _).trans
    (checked_run_typing_iff checked context remaining expression sort).symm

theorem checked_run_untyped_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) :
    (¬ ∃ remaining sort, Reference.Typed (projectRun admissions) (Reference.ofContext context)
      (Reference.SExpr.ofKernel expression) remaining sort) ↔
      ¬ ∃ remaining sort, Kernel.Preterm.HasType theory.termSignature context expression remaining sort := by
  have related := checked_run_environment_related checked
  constructor
  · rintro absent ⟨remaining, sort, typed⟩
    exact absent ⟨Reference.ofContext remaining, sort, typed_ofKernel related typed⟩
  · rintro absent ⟨remaining, sort, typed⟩
    exact absent ⟨Reference.toContext remaining, sort, by simpa using typed_toKernel related typed⟩

/-- Logical refusal is a completed `None` result, distinct from fuel exhaustion. -/
theorem admitted_authored_refusal_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) :
    Applies Presentation.ComputationalTyping.typingProgram computationalHost "mm0:infer"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext context, Presentation.encode expression] (.sym "None") ↔
      ¬ ∃ remaining sort, Reference.Typed (projectRun admissions) (Reference.ofContext context)
        (Reference.SExpr.ofKernel expression) remaining sort := by
  have refuses := Presentation.ComputationalTyping.infer_refuses_iff theory.terms context expression
  simp only [Presentation.ComputationalTyping.theory_signature] at refuses
  exact refuses.trans (checked_run_untyped_iff checked context expression).symm

namespace Controls

private def profile : Kernel.TermDecl := ⟨[.bound 0, .regular 1 {0}], 1, {0}⟩
private def claim : Kernel.TheoremDecl := ⟨[], [], .term 9⟩

/-- The fixture exercises every actual checked admission constructor. -/
private def history : List Kernel.Admission :=
  [.sort 0 {}, .sort 1 { provable := true }, .term 8 ⟨[], 1, ∅⟩,
    .term 7 profile, .definition 9 ⟨[], 1, ∅⟩ ⟨[], .term 8⟩,
    .axiomDecl 10 claim, .theoremDecl 11 claim [] (.theoremApp 10 [] [])]

private def theory : Kernel.Theory := (Kernel.Theory.run? {} history).getD {}
private def context : Kernel.Context := [.bound 0, .regular 1 {0}]
private def full : Kernel.Preterm := .app (.app (.term 7) (.var 0)) (.var 1)

theorem actual_run_succeeds : Kernel.Theory.run? {} history = some theory := by
  have success : (Kernel.Theory.run? {} history).isSome = true := by decide +kernel
  cases result : Kernel.Theory.run? {} history with
  | none => simp [result] at success
  | some final => simp [theory, result]

theorem all_admission_kinds_have_coherent_projection : EnvironmentRelated (projectRun history) theory :=
  checked_run_environment_related actual_run_succeeds

theorem partial_bound_application_preserved :
    Reference.Typed (projectRun history) (Reference.ofContext context)
      (Reference.SExpr.ofKernel (.app (.term 7) (.var 0))) (Reference.ofContext [.regular 1 {0}]) 1 := by
  apply (checked_run_typing_iff actual_run_succeeds _ _ _ _).mpr
  exact (Kernel.Preterm.infer_eq_some_iff _ _ _ _ _).mp (by decide +kernel)

theorem saturated_ordered_application_preserved :
    Applies Presentation.ComputationalTyping.typingProgram computationalHost "mm0:infer"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext context, Presentation.encode full]
      (Presentation.ComputationalTyping.encodeType (some ([], 1))) := by
  apply (Presentation.ComputationalTyping.theory_infer_accepts_iff _ _ _ _ _).mpr
  exact (Kernel.Preterm.infer_eq_some_iff _ _ _ _ _).mp (by decide +kernel)

theorem admitted_definition_head_preserved :
    Reference.Typed (projectRun history) [] (.term 9) [] 1 := by
  apply (checked_run_typing_iff actual_run_succeeds [] [] (.term 9) 1).mpr
  exact (Kernel.Preterm.infer_eq_some_iff _ _ _ _ _).mp (by decide +kernel)

theorem same_sort_regular_is_not_bound :
    ¬ ∃ remaining sort, Reference.Typed (projectRun history) (Reference.ofContext [.regular 0 ∅])
      (Reference.SExpr.ofKernel (.app (.term 7) (.var 0))) remaining sort := by
  apply (checked_run_untyped_iff actual_run_succeeds _ _).mpr
  exact (Kernel.Preterm.infer_none_iff _ _ _).mp (by decide +kernel)

theorem wrong_bound_sort_refuses :
    ¬ ∃ remaining sort, Reference.Typed (projectRun history) (Reference.ofContext [.bound 1])
      (Reference.SExpr.ofKernel (.app (.term 7) (.var 0))) remaining sort := by
  apply (checked_run_untyped_iff actual_run_succeeds _ _).mpr
  exact (Kernel.Preterm.infer_none_iff _ _ _).mp (by decide +kernel)

theorem reversed_arguments_refuse :
    Applies Presentation.ComputationalTyping.typingProgram computationalHost "mm0:infer"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalContext.encodeContext context,
        Presentation.encode (.app (.app (.term 7) (.var 1)) (.var 0))] (.sym "None") := by
  apply (admitted_authored_refusal_iff actual_run_succeeds _ _).mpr
  apply (checked_run_untyped_iff actual_run_succeeds _ _).mpr
  exact (Kernel.Preterm.infer_none_iff _ _ _).mp (by decide +kernel)

theorem surplus_argument_refuses :
    ¬ ∃ remaining sort, Reference.Typed (projectRun history) (Reference.ofContext context)
      (Reference.SExpr.ofKernel (.app full (.var 1))) remaining sort := by
  apply (checked_run_untyped_iff actual_run_succeeds _ _).mpr
  exact (Kernel.Preterm.infer_none_iff _ _ _).mp (by decide +kernel)

theorem wrong_claimed_result_refuses :
    ¬ Reference.Typed (projectRun history) (Reference.ofContext context)
      (Reference.SExpr.ofKernel full) [] 0 := by
  intro typed
  have accepted := ((checked_run_typing_iff actual_run_succeeds context [] full 0).mp typed).eval
  have result : Kernel.Preterm.infer theory.termSignature context full = some ([], 1) := by decide +kernel
  rw [result] at accepted
  cases accepted

theorem checked_redeclaration_refuses :
    (Kernel.Theory.run? {} (history ++ [.term 7 ⟨[], 0, ∅⟩])).isNone = true := by decide +kernel

private def duplicateEnvironment : Reference.Env := [.term 7 [] (0, ∅), .term 7 [] (1, ∅)]
private def firstKeyTheory : Kernel.Theory := { terms := [(7, ⟨[], 0, ∅⟩)] }

/-- Raw upstream membership alone permits incompatible declarations. -/
theorem raw_duplicate_has_second_type : Reference.Typed duplicateEnvironment [] (.term 7) [] 1 :=
  .term (result := (1, ∅)) (.term (by simp [duplicateEnvironment]))

theorem first_key_has_no_second_type : ¬ Kernel.Preterm.HasType firstKeyTheory.termSignature [] (.term 7) [] 1 := by
  intro typed
  have accepted := typed.eval
  simp [Kernel.Preterm.infer, Kernel.Theory.termSignature, firstKeyTheory] at accepted

theorem incompatible_duplicates_not_related : ¬ EnvironmentRelated duplicateEnvironment firstKeyTheory := by
  intro related
  have present : ∃ body, Reference.GetTerm duplicateEnvironment 7 [] (1, ∅) body :=
    ⟨none, .term (by simp [duplicateEnvironment])⟩
  have lookup := (related.terms _ _ _).mp present
  simp [Kernel.Theory.termSignature, firstKeyTheory, Reference.termDecl] at lookup

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3Typing
