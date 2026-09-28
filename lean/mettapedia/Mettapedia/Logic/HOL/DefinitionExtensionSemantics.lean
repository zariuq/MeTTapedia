import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.ImpredicativeConnectives

/-!
# A definitional extension of a Henkin model

A fresh typed constant can be interpreted by a closed term of the old
signature. The extension retains the old carriers, admissible domains, and
the meanings of every old term. Its new constant has the body's denotation
by construction, using the established closed-term substitution reduct.

This is a semantic model of a definition, not an assumption that an arbitrary
interpretation of a fresh symbol happens to respect it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Extend an indexed HOL constant signature by one new symbol at `target`. -/
inductive DefinedConst (Const : Ty Base → Type v) (target : Ty Base) :
    Ty Base → Type (max u v) where
  | old {type : Ty Base} : Const type → DefinedConst Const target type
  | defined : DefinedConst Const target target

namespace DefinedConst

/-- Eliminate the fresh symbol by its closed defining body. -/
def expansion {target : Ty Base} (body : ClosedTerm Const target) :
    ∀ {type : Ty Base}, DefinedConst Const target type → ClosedTerm Const type
  | _, .old symbol => .const symbol
  | _, .defined => body

/-- The old syntax is embedded without changing its variables or formers. -/
def embed {target : Ty Base} {gamma : Ctx Base} {type : Ty Base}
    (term : Term Const gamma type) : Term (DefinedConst Const target) gamma type :=
  mapConst DefinedConst.old term

/-- Expanding a term from the old signature recovers it exactly. -/
theorem expansion_embed {target : Ty Base} (body : ClosedTerm Const target)
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type) :
    substConst (expansion body) (embed (target := target) term) = term := by
  induction term with
  | const symbol => simp [embed, expansion, substConst]
  | _ => simp_all [embed, mapConst, substConst]

/-- Derived logical connectives commute with embedding an old signature into
its definitional extension. -/
theorem expand_embed {target : Ty Base}
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type) :
    ImpredicativeConnectives.expand (embed (target := target) term) =
      embed (target := target) (ImpredicativeConnectives.expand term) := by
  induction term <;>
    simp_all [embed, mapConst, ImpredicativeConnectives.expand,
      ImpredicativeConnectives.truth, ImpredicativeConnectives.falsity,
      ImpredicativeConnectives.conjunction, ImpredicativeConnectives.disjunction,
      ImpredicativeConnectives.existential]

end DefinedConst

namespace HenkinModel

/-- A genuine model of a definitional extension; no new closure hypothesis is
needed because the defining body was already a typed closed source term. -/
def definitionExtension (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    HenkinModel.{u, max u v, w} Base (DefinedConst Const target) :=
  constantSubstitutionReduct (DefinedConst.expansion body) M

/-- Old constant meanings survive the definitional extension. -/
@[simp] theorem definitionExtension_old (M : HenkinModel.{u, v, w} Base Const)
    {target type : Ty Base} (body : ClosedTerm Const target) (symbol : Const type) :
    (M.definitionExtension body).constDen (DefinedConst.old symbol) =
      M.constDen symbol := rfl

/-- The fresh constant denotes the defining closed term. -/
@[simp] theorem definitionExtension_defined (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    (M.definitionExtension body).constDen DefinedConst.defined =
      M.denote body (fun index => nomatch index) := rfl

/-- Conservative denotation for every old term, including open terms and
derived HOL connectives, at the same valuation. -/
theorem definitionExtension_embed (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target)
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type)
    (valuation : M.Valuation gamma) :
    (M.definitionExtension body).denote (DefinedConst.embed (target := target) term)
      valuation = M.denote term valuation := by
  change (constantSubstitutionReduct (DefinedConst.expansion body) M).denote
    (DefinedConst.embed (target := target) term) valuation = M.denote term valuation
  exact (denote_substConst (DefinedConst.expansion body) M
    (DefinedConst.embed (target := target) term) valuation).symm.trans
      (congrArg (fun t => M.denote t valuation) (DefinedConst.expansion_embed body term))

/-- Every old sentence keeps its truth value. Thus old theorem and axiom
validity is not silently strengthened or weakened by adding the definition. -/
theorem definitionExtension_models_embed (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target)
    (formula : ClosedFormula Const) :
    (M.definitionExtension body).models (DefinedConst.embed (target := target) formula) ↔
      M.models formula :=
  Iff.of_eq (congrArg ULift.down
    (M.definitionExtension_embed body formula (fun index => nomatch index)))

/-- Freshness and typing alone do not force an arbitrary interpretation of a
new symbol to respect a proposed definition. Interpreting it as false cannot
validate the proposal that its body is true. -/
theorem unrelated_extension_disagrees (M : HenkinModel.{u, v, w} Base Const) :
    (M.definitionExtension (.bot : ClosedTerm Const .prop)).constDen
        (DefinedConst.defined : DefinedConst Const .prop .prop) ≠
      M.denote (.top : ClosedTerm Const .prop) (fun index => nomatch index) := by
  intro equal
  have contradiction : False = True := by
    exact congrArg ULift.down equal
  exact (contradiction.symm ▸ True.intro)

end HenkinModel

#print axioms DefinedConst.expansion_embed
#print axioms DefinedConst.expand_embed
#print axioms HenkinModel.definitionExtension
#print axioms HenkinModel.definitionExtension_embed
#print axioms HenkinModel.definitionExtension_models_embed
#print axioms HenkinModel.unrelated_extension_disagrees

end Mettapedia.Logic.HOL
