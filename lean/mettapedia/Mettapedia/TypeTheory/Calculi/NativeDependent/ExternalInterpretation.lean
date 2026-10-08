import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModel

/-!
# Partial interpretation of authored external expressions

Evaluation traverses the independent raw syntax. Primitive arguments form
actual substitutions into semantic parameter telescopes; each logical
constructor checks its argument sections against the supplied dependent
annotations. Full-motive sum elimination uses the eliminator earned from
local sum laws.

The evaluator is mathematical and may fail on unadmitted syntax. Its
constructor equations do not by themselves establish soundness of all
generated judgment rules or classifying initiality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m a b

/-- Option composition across independent context/type/term universes. -/
def bindResult {α : Type a} {β : Type b} (result : Option α)
    (continuation : α → Option β) : Option β :=
  match result with
  | none => none
  | some value => continuation value

@[simp] theorem bindResult_some {α : Type a} {β : Type b} (value : α)
    (continuation : α → Option β) : bindResult (some value) continuation = continuation value := rfl

@[simp] theorem bindResult_none {α : Type a} {β : Type b}
    (continuation : α → Option β) : bindResult none continuation = none := rfl

theorem bindResult_eq_some_iff {α : Type a} {β : Type b} (result : Option α)
    (continuation : α → Option β) (value : β) :
    bindResult result continuation = some value ↔
      ∃ argument, result = some argument ∧ continuation argument = some value := by
  cases result with
  | none => simp [bindResult]
  | some argument => simp [bindResult]

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

/-- Check the actual section carried by an evaluated expression. -/
noncomputable def check? {Γ : C.toCwf.Ctx} (result : Option (Value C.toCwf Γ))
    (A : C.toCwf.Ty Γ) : Option (C.toCwf.Tm Γ A) :=
  bindResult result (fun value => value.atType? A)

@[simp] theorem check?_supplied {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ)
    (value : C.toCwf.Tm Γ A) : check? (some ⟨A, value⟩) A = some value := by
  simp [check?]

theorem check?_eq_some_iff {Γ : C.toCwf.Ctx} (result : Option (Value C.toCwf Γ))
    (A : C.toCwf.Ty Γ) (value : C.toCwf.Tm Γ A) :
    check? result A = some value ↔ result = some ⟨A, value⟩ := by
  cases result with
  | none => simp [check?]
  | some actual => simpa only [check?, bindResult_some, Option.some.injEq] using
      Value.atType?_eq_some_iff actual A value

noncomputable def lambda? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (body : Option (Value C.toCwf (C.toCwf.ext Γ A))) : Option (Value C.toCwf Γ) :=
  bindResult (check? body B) (fun value => some ⟨model.products.pi A B, model.products.lam value⟩)

noncomputable def application? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function argument : Option (Value C.toCwf Γ)) : Option (Value C.toCwf Γ) :=
  bindResult (check? function (model.products.pi A B)) (fun function =>
    bindResult (check? argument A) (fun argument =>
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf argument), model.products.app function argument⟩))

noncomputable def pair? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (first second : Option (Value C.toCwf Γ)) : Option (Value C.toCwf Γ) :=
  bindResult (check? first A) (fun first =>
    bindResult (check? second (C.toCwf.tySub B (selfExtend C.toCwf first))) (fun second =>
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair first second⟩))

noncomputable def first? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : Option (Value C.toCwf Γ)) : Option (Value C.toCwf Γ) :=
  bindResult (check? pair (model.sums.operations.sigma A B)) (fun pair =>
    some ⟨A, model.sums.operations.fst pair⟩)

noncomputable def second? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : Option (Value C.toCwf Γ)) : Option (Value C.toCwf Γ) :=
  bindResult (check? pair (model.sums.operations.sigma A B)) (fun pair =>
    some ⟨C.toCwf.tySub B (selfExtend C.toCwf (model.sums.operations.fst pair)),
      model.sums.operations.snd pair⟩)

noncomputable def sumEliminate? (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (C.toCwf.ext Γ (model.sums.operations.sigma A B)))
    (branch : Option (Value C.toCwf (C.toCwf.ext (C.toCwf.ext Γ A) B)))
    (pair : Option (Value C.toCwf Γ)) : Option (Value C.toCwf Γ) :=
  bindResult (check? branch (C.toCwf.tySub M (pack model.sums A B))) (fun branch =>
    bindResult (check? pair (model.sums.operations.sigma A B)) (fun pair =>
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate model.sums A B M branch) (selfExtend C.toCwf pair)⟩))

@[simp] theorem lambda?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (body : C.toCwf.Tm (C.toCwf.ext Γ A) B) :
    model.lambda? A B (some ⟨B, body⟩) =
      some ⟨model.products.pi A B, model.products.lam body⟩ := by
  simp [lambda?]

@[simp] theorem application?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (model.products.pi A B)) (argument : C.toCwf.Tm Γ A) :
    model.application? A B (some ⟨_, function⟩) (some ⟨A, argument⟩) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf argument), model.products.app function argument⟩ := by
  simp [application?]

@[simp] theorem pair?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (first : C.toCwf.Tm Γ A)
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    model.pair? A B (some ⟨A, first⟩) (some ⟨_, second⟩) =
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair first second⟩ := by
  simp [pair?]

@[simp] theorem first?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.first? A B (some ⟨_, pair⟩) = some ⟨A, model.sums.operations.fst pair⟩ := by
  simp [first?]

@[simp] theorem second?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.second? A B (some ⟨_, pair⟩) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf (model.sums.operations.fst pair)),
        model.sums.operations.snd pair⟩ := by
  simp [second?]

@[simp] theorem sumEliminate?_supplied (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (C.toCwf.ext Γ (model.sums.operations.sigma A B)))
    (branch : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B)
      (C.toCwf.tySub M (pack model.sums A B)))
    (pair : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.sumEliminate? A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩) =
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate model.sums A B M branch) (selfExtend C.toCwf pair)⟩ := by
  simp [sumEliminate?]

mutual

/-- Type evaluation visits all independently authored annotations and arguments. -/
noncomputable def evaluateTypeLifted (model : ModelData S C) : {n : Nat} →
    (Γ : Context C n) → TypeExpr S n → Option (ULift.{m} (C.toCwf.Ty Γ.1))
  | _, Γ, .family symbol arguments =>
      bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Γ (arguments index))) (fun arguments =>
          some ⟨model.familyAt symbol arguments⟩)
  | _, Γ, .pi domain body =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          some ⟨model.products.pi A B⟩))
  | _, Γ, .sigma domain body =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          some ⟨model.sums.operations.sigma A B⟩))

/-- Terms become actual typed sections of the supplied model. -/
noncomputable def evaluateTerm (model : ModelData S C) : {n : Nat} →
    (Γ : Context C n) → TermExpr S n → Option (Value C.toCwf Γ.1)
  | _, Γ, .var index => some (Γ.2.lookup index)
  | _, Γ, .primitive symbol arguments =>
      bindResult ((model.termParameters symbol).2.assemble?
        (fun index => model.evaluateTerm Γ (arguments index))) (fun arguments =>
          some (model.primitiveAt symbol arguments))
  | _, Γ, .lam domain body term =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          model.lambda? A B (model.evaluateTerm (Γ.snoc A) term)))
  | _, Γ, .app domain body function argument =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          model.application? A B (model.evaluateTerm Γ function) (model.evaluateTerm Γ argument)))
  | _, Γ, .pair domain body first second =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          model.pair? A B (model.evaluateTerm Γ first) (model.evaluateTerm Γ second)))
  | _, Γ, .fst domain body pair =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          model.first? A B (model.evaluateTerm Γ pair)))
  | _, Γ, .snd domain body pair =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          model.second? A B (model.evaluateTerm Γ pair)))
  | _, Γ, .sigmaElim domain body motive branch pair =>
      bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
        let A := liftedA.down
        bindResult (model.evaluateTypeLifted (Γ.snoc A) body) (fun liftedB =>
          let B := liftedB.down
          bindResult (model.evaluateTypeLifted (Γ.snoc (model.sums.operations.sigma A B)) motive) (fun liftedM =>
            let M := liftedM.down
            model.sumEliminate? A B M (model.evaluateTerm ((Γ.snoc A).snoc B) branch)
              (model.evaluateTerm Γ pair))))

end

/-- The universe lift is only an implementation of mutual recursion across
independent model type and term universes. -/
noncomputable def evaluateType (model : ModelData S C) {n : Nat} (Γ : Context C n)
    (type : TypeExpr S n) : Option (C.toCwf.Ty Γ.1) :=
  (model.evaluateTypeLifted Γ type).map ULift.down

/-- Lifted and ordinary type readouts carry exactly the same meaning. -/
theorem evaluateType_eq_some_iff (model : ModelData S C) {n : Nat}
    (Γ : Context C n) (type : TypeExpr S n) (A : C.toCwf.Ty Γ.1) :
    model.evaluateType Γ type = some A ↔
      model.evaluateTypeLifted Γ type = some (ULift.up A) := by
  unfold evaluateType
  cases result : model.evaluateTypeLifted Γ type with
  | none => simp
  | some actual => cases actual; simp

/-- Inversion of the two independently evaluated dependent annotations. -/
theorem dependentAnnotations_eq_some_iff {Result : Type a} (model : ModelData S C)
    {n : Nat} (Γ : Context C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (continuation : (A : C.toCwf.Ty Γ.1) → C.toCwf.Ty (C.toCwf.ext Γ.1 A) → Option Result)
    (value : Result) :
    bindResult (model.evaluateTypeLifted Γ domain) (fun liftedA =>
      bindResult (model.evaluateTypeLifted (Γ.snoc liftedA.down) body)
        (fun liftedB => continuation liftedA.down liftedB.down)) = some value ↔
      ∃ A B, model.evaluateType Γ domain = some A ∧
        model.evaluateType (Γ.snoc A) body = some B ∧ continuation A B = some value := by
  constructor
  · intro evaluated
    rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨liftedA, first, rest⟩
    rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨liftedB, second, last⟩
    refine ⟨liftedA.down, liftedB.down, ?_, ?_, last⟩
    · exact (model.evaluateType_eq_some_iff _ _ _).mpr first
    · exact (model.evaluateType_eq_some_iff _ _ _).mpr second
  · rintro ⟨A, B, first, second, last⟩
    apply (bindResult_eq_some_iff _ _ _).mpr
    refine ⟨ULift.up A, (model.evaluateType_eq_some_iff _ _ _).mp first, ?_⟩
    apply (bindResult_eq_some_iff _ _ _).mpr
    exact ⟨ULift.up B, (model.evaluateType_eq_some_iff _ _ _).mp second, last⟩

noncomputable def evaluateContext (model : ModelData S C) :
    {n : Nat} → ContextExpr S n → Option (Context C n)
  | _, .nil => some (Context.nil C)
  | _, .snoc previous type =>
      bindResult (model.evaluateContext previous) (fun Γ =>
        bindResult (model.evaluateType Γ type) (fun A => some (Γ.snoc A)))

noncomputable def evaluateSubstitution (model : ModelData S C) {n k : Nat}
    (Γ : Context C n) (Δ : Context C k) (substitution : Fin k → TermExpr S n) :
    Option (C.toCwf.Sub Γ.1 Δ.1) :=
  Δ.2.assemble? (fun index => model.evaluateTerm Γ (substitution index))

/-- Successful substitution evaluation has exactly its authored term readouts. -/
theorem evaluateSubstitution_eq_some_iff (model : ModelData S C) {n k : Nat}
    (Γ : Context C n) (Δ : Context C k) (substitution : Fin k → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 Δ.1) : model.evaluateSubstitution Γ Δ substitution = some σ ↔
    ∀ index, model.evaluateTerm Γ (substitution index) = some (Δ.2.components σ index) :=
  Telescope.assemble?_eq_some_iff _ _ _

@[simp] theorem evaluateSubstitution_identity (model : ModelData S C) {n : Nat}
    (Γ : Context C n) : model.evaluateSubstitution Γ Γ TermExpr.var = some (C.toCwf.idS Γ.1) := by
  apply (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro index
  simp only [evaluateTerm, Telescope.components, Value.substitute_identity]

/-- A raw expression's checked readout fixes its section, independently of
which proof of the semantic annotation equality supplied its cast. -/
theorem checked_readout_unique {Γ : C.toCwf.Ctx} {result : Option (Value C.toCwf Γ)}
    {A B : C.toCwf.Ty Γ} {first : C.toCwf.Tm Γ A} {second : C.toCwf.Tm Γ B}
    (firstChecked : check? result A = some first) (secondChecked : check? result B = some second) :
    A = B ∧ HEq first second := by
  have values : (⟨A, first⟩ : Value C.toCwf Γ) = ⟨B, second⟩ :=
    Option.some.inj (((check?_eq_some_iff _ _ _).mp firstChecked).symm.trans
      ((check?_eq_some_iff _ _ _).mp secondChecked))
  exact ⟨congrArg Sigma.fst values, sigma_second_heq values⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
