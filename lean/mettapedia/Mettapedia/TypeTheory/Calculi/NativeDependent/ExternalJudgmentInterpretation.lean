import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgments
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Concrete semantic judgments for the external presentation

A semantic judgment describes successful evaluation of its authored context,
type, term or substitution. Equations require both independently evaluated
sides to yield the same actual model datum. Primitive declaration agreement
is local to its parameter header and result; source soundness is not a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

/-- The supplied primitive families and sections have these actual authored
declaration headers. This contains no whole-judgment interpretation law. -/
structure SignatureRealization (model : ModelData S C) (D : Signature S) : Prop where
  typeHeader : ∀ symbol, model.evaluateContext (D.typeParameters symbol) =
    some (model.typeParameters symbol)
  termHeader : ∀ symbol, model.evaluateContext (D.termParameters symbol) =
    some (model.termParameters symbol)
  termResult : ∀ symbol, model.evaluateType (model.termParameters symbol) (D.termResult symbol) =
    some (model.termType symbol)

def Interprets (model : ModelData S C) : Judgment S → Prop
  | .context context => ∃ Γ, model.evaluateContext context = some Γ
  | .type context type => ∃ Γ A, model.evaluateContext context = some Γ ∧
      model.evaluateType Γ type = some A
  | .term context term type => ∃ Γ A, ∃ (value : C.toCwf.Tm Γ.1 A),
      model.evaluateContext context = some Γ ∧ model.evaluateType Γ type = some A ∧
        model.evaluateTerm Γ term = some ⟨A, value⟩
  | .substitution source target substitution => ∃ Γ Δ, ∃ (arrow : C.toCwf.Sub Γ.1 Δ.1),
      model.evaluateContext source = some Γ ∧ model.evaluateContext target = some Δ ∧
        model.evaluateSubstitution Γ Δ substitution = some arrow
  | .contextEq first second => ∃ Γ, model.evaluateContext first = some Γ ∧
      model.evaluateContext second = some Γ
  | .typeEq context first second => ∃ Γ A, model.evaluateContext context = some Γ ∧
      model.evaluateType Γ first = some A ∧ model.evaluateType Γ second = some A
  | .termEq context first second type => ∃ Γ A, ∃ (value : C.toCwf.Tm Γ.1 A),
      model.evaluateContext context = some Γ ∧ model.evaluateType Γ type = some A ∧
        model.evaluateTerm Γ first = some ⟨A, value⟩ ∧
          model.evaluateTerm Γ second = some ⟨A, value⟩
  | .substitutionEq source target first second => ∃ Γ Δ, ∃ (arrow : C.toCwf.Sub Γ.1 Δ.1),
      model.evaluateContext source = some Γ ∧ model.evaluateContext target = some Δ ∧
        model.evaluateSubstitution Γ Δ first = some arrow ∧
          model.evaluateSubstitution Γ Δ second = some arrow

namespace Interprets

variable {model : ModelData S C} {n k : Nat}

theorem dependentTypes {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body)) :
    ∃ Γ A, ∃ (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A)),
      model.evaluateContext context = some Γ ∧ model.evaluateType Γ domain = some A ∧
        model.evaluateType (Γ.snoc A) body = some B := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases bodyInterpreted with ⟨actual, B, actualRead, bodyRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead))
  exact ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩

theorem dependentTypeEquations {context : ContextExpr S n}
    {firstDomain secondDomain : TypeExpr S n} {firstBody secondBody : TypeExpr S (n + 1)}
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (bodiesInterpreted : Interprets model (.typeEq (.snoc context firstDomain) firstBody secondBody)) :
    ∃ Γ A, ∃ (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A)),
      model.evaluateContext context = some Γ ∧
        model.evaluateType Γ firstDomain = some A ∧ model.evaluateType Γ secondDomain = some A ∧
          model.evaluateType (Γ.snoc A) firstBody = some B ∧ model.evaluateType (Γ.snoc A) secondBody = some B := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases bodiesInterpreted with ⟨actual, B, actualRead, firstBodyRead, secondBodyRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  exact ⟨Γ, A, B, contextRead, firstDomainRead, secondDomainRead, firstBodyRead, secondBodyRead⟩

theorem typeAt {context : ContextExpr S n} {type : TypeExpr S n}
    (interpreted : Interprets model (.type context type)) (Γ : Context C n)
    (contextRead : model.evaluateContext context = some Γ) :
    ∃ A, model.evaluateType Γ type = some A := by
  rcases interpreted with ⟨actual, A, actualRead, typeRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  exact ⟨A, typeRead⟩

theorem termAt {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (interpreted : Interprets model (.term context term type)) (Γ : Context C n)
    (A : C.toCwf.Ty Γ.1) (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    ∃ value : C.toCwf.Tm Γ.1 A, model.evaluateTerm Γ term = some ⟨A, value⟩ := by
  rcases interpreted with ⟨actual, B, value, actualRead, actualTypeRead, termRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  cases Option.some.inj (actualTypeRead.symm.trans typeRead)
  exact ⟨value, termRead⟩

theorem substitutionAt {source : ContextExpr S n} {target : ContextExpr S k}
    {substitution : Substitution S k n}
    (interpreted : Interprets model (.substitution source target substitution))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    ∃ arrow, model.evaluateSubstitution Γ Δ substitution = some arrow := by
  rcases interpreted with ⟨actual, actualTarget, arrow, actualRead, actualTargetRead, termRead⟩
  cases Option.some.inj (actualRead.symm.trans sourceRead)
  cases Option.some.inj (actualTargetRead.symm.trans targetRead)
  exact ⟨arrow, termRead⟩

theorem contextEqAt {first second : ContextExpr S n}
    (interpreted : Interprets model (.contextEq first second)) (Γ : Context C n)
    (firstRead : model.evaluateContext first = some Γ) :
    model.evaluateContext second = some Γ := by
  rcases interpreted with ⟨actual, actualRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans firstRead)
  exact secondRead

theorem typeEqAt {context : ContextExpr S n} {first second : TypeExpr S n}
    (interpreted : Interprets model (.typeEq context first second)) (Γ : Context C n)
    (A : C.toCwf.Ty Γ.1) (contextRead : model.evaluateContext context = some Γ)
    (firstRead : model.evaluateType Γ first = some A) :
    model.evaluateType Γ second = some A := by
  rcases interpreted with ⟨actual, B, actualRead, firstTypeRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  cases Option.some.inj (firstTypeRead.symm.trans firstRead)
  exact secondRead

theorem termEqAt {context : ContextExpr S n} {first second : TermExpr S n} {type : TypeExpr S n}
    (interpreted : Interprets model (.termEq context first second type)) (Γ : Context C n)
    (A : C.toCwf.Ty Γ.1) (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    ∃ value : C.toCwf.Tm Γ.1 A, model.evaluateTerm Γ first = some ⟨A, value⟩ ∧
      model.evaluateTerm Γ second = some ⟨A, value⟩ := by
  rcases interpreted with ⟨actual, B, value, actualRead, actualTypeRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  cases Option.some.inj (actualTypeRead.symm.trans typeRead)
  exact ⟨value, firstRead, secondRead⟩

theorem substitutionEqAt {source : ContextExpr S n} {target : ContextExpr S k}
    {first second : Substitution S k n}
    (interpreted : Interprets model (.substitutionEq source target first second))
    (Γ : Context C n) (Δ : Context C k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    ∃ arrow, model.evaluateSubstitution Γ Δ first = some arrow ∧
      model.evaluateSubstitution Γ Δ second = some arrow := by
  rcases interpreted with ⟨actual, actualTarget, arrow, actualRead, actualTargetRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans sourceRead)
  cases Option.some.inj (actualTargetRead.symm.trans targetRead)
  exact ⟨arrow, firstRead, secondRead⟩

end Interprets

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
