import Mettapedia.Languages.MM0.Kernel.Proof

/-!
# MM0 declaration payload admission

This module checks declaration payloads against the preceding signatures.
Fresh identifiers, specification matching and sequential insertion belong to
the theory machine. In particular a well-formed theorem payload is not a
proof and does not make the theorem available.

Definition bodies follow the pinned C/Rust verifier profile: dummy sorts
are neither strict nor free, and every residual free variable is declared
in the return dependencies. The older formal sketches disagree on this
point; no exemption for undeclared free-sort variables is used here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace Preterm

def checkStatement (sorts : SortSignature) (signature : TermSignature)
    (context : Context) (expression : Preterm) : Bool :=
  match infer signature context expression with
  | some ([], sort) => (sorts sort).any (·.provable)
  | _ => false

theorem checkStatement_iff (sorts : SortSignature) (signature : TermSignature)
    (context : Context) (expression : Preterm) :
    checkStatement sorts signature context expression = true ↔
      IsStatement sorts signature context expression := by
  simp only [IsStatement, ← infer_eq_some_iff]
  cases typed : infer signature context expression with
  | none => simp [checkStatement, typed]
  | some type =>
      rcases type with ⟨remaining, sort⟩
      cases remaining with
      | cons binder remaining => simp [checkStatement, typed]
      | nil =>
          cases known : sorts sort with
          | none => simp [checkStatement, typed, known]
          | some info => simp [checkStatement, typed, known]

end Preterm

namespace TermDecl

structure Admissible (sorts : SortSignature) (declaration : TermDecl) : Prop where
  context : Context.WellFormed sorts declaration.arguments
  result : ∃ info, sorts declaration.resultSort = some info ∧ info.pure = false
  dependencies : ∀ index ∈ declaration.dependencies,
    ∃ sort, declaration.arguments[index]? = some (.bound sort)

def check (sorts : SortSignature) (declaration : TermDecl) : Bool :=
  Context.check sorts declaration.arguments &&
    (match sorts declaration.resultSort with
     | none => false
     | some info => !info.pure) &&
    decide (∀ index ∈ declaration.dependencies, Context.isBound declaration.arguments index = true)

theorem check_iff (sorts : SortSignature) (declaration : TermDecl) :
    check sorts declaration = true ↔ Admissible sorts declaration := by
  have result : (match sorts declaration.resultSort with
      | none => false | some info => !info.pure) = true ↔
      ∃ info, sorts declaration.resultSort = some info ∧ info.pure = false := by
    cases known : sorts declaration.resultSort <;> simp
  simp only [check, Bool.and_eq_true, Context.check_iff, result, decide_eq_true_eq,
    Context.isBound_iff]
  exact ⟨fun ⟨⟨context, result⟩, dependencies⟩ => ⟨context, result, dependencies⟩,
    fun admitted => ⟨⟨admitted.context, admitted.result⟩, admitted.dependencies⟩⟩

end TermDecl

namespace Definition

def dummySortAllowed (sorts : SortSignature) (sort : Nat) : Bool :=
  match sorts sort with
  | none => false
  | some info => !info.strict && !info.free

theorem dummySortAllowed_iff (sorts : SortSignature) (sort : Nat) :
    dummySortAllowed sorts sort = true ↔
      ∃ info, sorts sort = some info ∧ info.strict = false ∧ info.free = false := by
  cases known : sorts sort <;> simp [dummySortAllowed, known]

def checkDummySorts (sorts : SortSignature) (dummies : List Nat) : Bool :=
  dummies.all (dummySortAllowed sorts)

theorem checkDummySorts_iff (sorts : SortSignature) (dummies : List Nat) :
    checkDummySorts sorts dummies = true ↔
      ∀ sort ∈ dummies, ∃ info, sorts sort = some info ∧
        info.strict = false ∧ info.free = false := by
  simp [checkDummySorts, List.all_eq_true, dummySortAllowed_iff]

def Body.context (declaration : TermDecl) (body : Body) : Context :=
  declaration.arguments ++ body.dummies.map Binder.bound

structure AdmissibleBody (sorts : SortSignature) (signature : TermSignature)
    (declaration : TermDecl) (body : Body) : Prop where
  dummies : ∀ sort ∈ body.dummies, ∃ info, sorts sort = some info ∧
    info.strict = false ∧ info.free = false
  typed : Preterm.HasType signature (body.context declaration) body.expression [] declaration.resultSort
  free : ∃ freeSet, Preterm.FreeVars signature (body.context declaration) body.expression freeSet ∧
    freeSet ⊆ declaration.dependencies

def checkBody (sorts : SortSignature) (signature : TermSignature)
    (declaration : TermDecl) (body : Body) : Bool :=
  checkDummySorts sorts body.dummies &&
    decide (Preterm.infer signature (body.context declaration) body.expression =
      some ([], declaration.resultSort)) &&
    (match Preterm.freeVariables? signature (body.context declaration) body.expression with
     | none => false
     | some freeSet => decide (freeSet ⊆ declaration.dependencies))

theorem checkBody_iff (sorts : SortSignature) (signature : TermSignature)
    (declaration : TermDecl) (body : Body) :
    checkBody sorts signature declaration body = true ↔
      AdmissibleBody sorts signature declaration body := by
  have free : (match Preterm.freeVariables? signature (body.context declaration) body.expression with
      | none => false | some freeSet => decide (freeSet ⊆ declaration.dependencies)) = true ↔
      ∃ freeSet, Preterm.FreeVars signature (body.context declaration) body.expression freeSet ∧
        freeSet ⊆ declaration.dependencies := by
    simp only [← Preterm.freeVariables_eq_some_iff]
    cases computed : Preterm.freeVariables? signature (body.context declaration) body.expression <;> simp
  simp only [checkBody, Bool.and_eq_true, checkDummySorts_iff, decide_eq_true_eq,
    Preterm.infer_eq_some_iff, free]
  exact ⟨fun ⟨⟨dummies, typed⟩, free⟩ => ⟨dummies, typed, free⟩,
    fun admitted => ⟨⟨admitted.dummies, admitted.typed⟩, admitted.free⟩⟩

/-- An admitted payload provides the actual body-typing premise required by
unfolding; it does not assume the unfolding result. -/
theorem AdmissibleBody.unfold_total {sorts : SortSignature} {signature : TermSignature}
    {definitions : Signature} {target : Context} {symbol : Nat} {declaration : TermDecl} {body : Body}
    (admitted : AdmissibleBody sorts signature declaration body)
    (known : signature symbol = some declaration) (defined : definitions symbol = some body)
    {arguments : List Preterm} {images : List Nat}
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments declaration.arguments)
    (fresh : FreshDummies target arguments body.dummies images) :
    ∃ result, unfold? signature definitions target symbol arguments images = some result ∧
      Preterm.HasType signature target result [] declaration.resultSort :=
  unfold_typed_total known defined typed fresh admitted.typed

end Definition

namespace TheoremDecl

structure Admissible (sorts : SortSignature) (signature : TermSignature)
    (declaration : TheoremDecl) : Prop where
  context : Context.WellFormed sorts declaration.arguments
  hypotheses : ∀ expression ∈ declaration.hypotheses,
    Preterm.IsStatement sorts signature declaration.arguments expression
  conclusion : Preterm.IsStatement sorts signature declaration.arguments declaration.conclusion

def check (sorts : SortSignature) (signature : TermSignature) (declaration : TheoremDecl) : Bool :=
  Context.check sorts declaration.arguments &&
    declaration.hypotheses.all (Preterm.checkStatement sorts signature declaration.arguments) &&
    Preterm.checkStatement sorts signature declaration.arguments declaration.conclusion

theorem check_iff (sorts : SortSignature) (signature : TermSignature) (declaration : TheoremDecl) :
    check sorts signature declaration = true ↔ Admissible sorts signature declaration := by
  simp only [check, Bool.and_eq_true, Context.check_iff, List.all_eq_true,
    Preterm.checkStatement_iff]
  exact ⟨fun ⟨⟨context, hypotheses⟩, conclusion⟩ => ⟨context, hypotheses, conclusion⟩,
    fun admitted => ⟨⟨admitted.context, admitted.hypotheses⟩, admitted.conclusion⟩⟩

end TheoremDecl

end Mettapedia.Languages.MM0.Kernel
