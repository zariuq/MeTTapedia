import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeRepresentation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationAdmissionReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.Telescopes
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList

/-!
# HOL definitions as dependent declarations

A closed typed source term supplies the exact value of a native declaration,
including unapplied function values. Source abstraction is native abstraction;
there is no arity expansion into a different clause program. Formation and body
typing follow from the existing total HOL representation and earn source-prefix
admission in the existing dependent judgment system.

A declared source lambda applied to a represented argument, including one
from an open source context, takes one delta and one beta step to the
representation of source instantiation. Its source and result are typed.
Source axioms and the host logical signature remain
explicit parameters; admission does not validate their truth or consistency.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionAdmission

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface HOLImpredicativeRepresentation
open Mettapedia.Logic

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def entry (signature : LogicalSignature Base Const) {type : HOL.Ty Base}
    (body : HOL.Term Const [] type) : Entry Tower.Head :=
  ⟨typeAt signature.types 0 type, some (translate signature body)⟩

def declarations (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type) : List (DeclName × Entry Tower.Head) :=
  [(name, entry signature body)]

abbrev rules (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type) : Rules Tower.Head :=
  extendRules signature.rules (Signature.ofList (declarations signature name body))

/-- The translation earns formation and body typing; only name freshness is
additional to the law-bearing source logical signature. -/
theorem admitted (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none) :
    DeclarationAdmissionReplay.Admitted signature.rules [] (declarations signature name body) := by
  apply DeclarationAdmissionReplay.Admitted.cons (levelHead := .sort Tower.zero)
  · simp [extendRules, combinedType, Signature.ofList, Signature.empty, Signature.typeOf?, fresh]
  · exact .sort _
  · exact (typeAt_formed signature type (.nil : Tower.Ctx 0)).includeSignature (Signature.ofList [])
  · intro value selected
    have same : translate signature body = value := Option.some.inj selected
    subst value
    exact (translate_typed signature body).includeSignature (Signature.ofList [])
  · exact .nil _

theorem admitted_iff_fresh (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type) :
    DeclarationAdmissionReplay.Admitted signature.rules [] (declarations signature name body) ↔
      signature.rules.constantType name = none := by
  constructor
  · intro checked
    cases checked with
    | cons fresh _ _ _ _ =>
        cases selected : signature.rules.constantType name with
        | none => rfl
        | some type => simp [extendRules, combinedType, selected] at fresh
  · exact admitted signature name body

theorem constant_typed (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none)
    {n : Nat} (context : Tower.Ctx n) :
    Typing (rules signature name body) context (.const name)
      (liftClosed (typeAt signature.types 0 type)) := by
  apply Typing.const (type := typeAt signature.types 0 type)
  · apply combinedType_of_signature signature.rules _ fresh
    simp [declarations, entry, Signature.typeOf?, Signature.ofList, Signature.insert]
  · exact (typeAt_formed signature type (.nil : Tower.Ctx 0)).includeSignature _
  · exact .sort Tower.zero

/-- The selected source definition unfolds as a value before application. -/
theorem delta (signature : LogicalSignature Base Const) (name : DeclName)
    {type : HOL.Ty Base} (body : HOL.Term Const [] type) {n : Nat} :
    Step (rules signature name body).headEq (.const name : Tower.Tm n)
      (liftClosed (translate signature body)) (rules signature name body).computation := by
  apply Step.root
  apply RootStep.delta
  simp [declarations, entry, Signature.valueOf?, Signature.ofList, Signature.insert]

theorem application_typed (signature : LogicalSignature Base Const) (name : DeclName)
    {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
    (body : HOL.Term Const [domain] codomain) (argument : HOL.Term Const Γ domain)
    (fresh : signature.rules.constantType name = none) :
    Typing (rules signature name (.lam body)) (context signature.types Γ)
      (.app (.const name) (translate signature argument))
      (typeAt signature.types Γ.length codomain) := by
  have function := constant_typed signature name (.lam body) fresh (context signature.types Γ)
  simp only [liftClosed, typeAt_rename] at function
  have typed : Typing (rules signature name (.lam body)) (context signature.types Γ)
      (.const name) (.pi (typeAt signature.types Γ.length domain)
        (typeAt signature.types (Γ.length + 1) codomain)) := by
    simpa only [typeAt] using function
  simpa only [inst0, typeAt_subst] using
    Typing.appElim typed ((translate_typed signature argument).includeSignature
      (Signature.ofList (declarations signature name (.lam body))))

/-- The two actual target steps return the computed translation of source
substitution, not an independently selected term of the same type. -/
theorem application_steps (signature : LogicalSignature Base Const) (name : DeclName)
    {domain codomain : HOL.Ty Base} (body : HOL.Term Const [domain] codomain)
    (argument : HOL.Term Const [] domain) :
    ConversionCoherence.StepStar (rules signature name (.lam body))
      (.app (.const name) (translate signature argument))
      (translate signature (HOL.instantiate argument body)) := by
  rw [translate_instantiate]
  have unfolds := delta signature name (.lam body) (n := 0)
  have source : Step (rules signature name (.lam body)).headEq
      (.const name : Tower.Tm 0) (.lam (translate signature body))
      (rules signature name (.lam body)).computation := by
    simpa only [TelescopeAbstraction.liftClosed_zero, translate_lam] using unfolds
  exact .tail (.tail .refl (.congAppFun source)) (.betaPi _ _)

/-- Calls from an open source context first lift the closed declaration under
that context. The returned closure keeps its ambient variables through the
source's capture-avoiding instantiation. -/
theorem application_open_steps (signature : LogicalSignature Base Const) (name : DeclName)
    {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
    (body : HOL.Term Const [domain] codomain) (argument : HOL.Term Const Γ domain) :
    ConversionCoherence.StepStar (rules signature name (.lam body))
      (.app (.const name) (translate signature argument))
      (translate signature (HOL.instantiate argument
        (HOL.rename (HOL.Rename.lift (Γ := []) (Δ := Γ) (fun index => nomatch index)) body))) := by
  rw [translate_instantiate]
  have renamed := translate_rename signature
    (HOL.Rename.lift (Γ := []) (Δ := Γ) (fun index => nomatch index))
    (liftRen (Fin.elim0 : Ren 0 Γ.length)) (t := body) (by
      intro type index
      cases index with
      | vz => rfl
      | vs earlier => cases earlier)
  rw [renamed]
  have unfolds := delta signature name (.lam body) (n := Γ.length)
  have source : Step (rules signature name (.lam body)).headEq
      (.const name : Tower.Tm Γ.length)
      (.lam (Presentation.rename (liftRen Fin.elim0) (translate signature body)))
      (rules signature name (.lam body)).computation := by
    simpa only [translate_lam, liftClosed, Presentation.rename] using unfolds
  exact .tail (.tail .refl (.congAppFun source)) (.betaPi _ _)

theorem open_result_typed (signature : LogicalSignature Base Const) (name : DeclName)
    {Γ : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
    (body : HOL.Term Const [domain] codomain) (argument : HOL.Term Const Γ domain) :
    Typing (rules signature name (.lam body)) (context signature.types Γ)
      (translate signature (HOL.instantiate argument
        (HOL.rename (HOL.Rename.lift (Γ := []) (Δ := Γ) (fun index => nomatch index)) body)))
      (typeAt signature.types Γ.length codomain) :=
  (translate_typed signature _).includeSignature _

theorem result_typed (signature : LogicalSignature Base Const) (name : DeclName)
    {domain codomain : HOL.Ty Base} (body : HOL.Term Const [domain] codomain)
    (argument : HOL.Term Const [] domain) :
    Typing (rules signature name (.lam body)) .nil
      (translate signature (HOL.instantiate argument body)) (typeAt signature.types 0 codomain) :=
  (translate_typed signature (HOL.instantiate argument body)).includeSignature _

namespace Controls

open HOL.UniformListInduction

def name : DeclName := `HOLDefinitionAdmission.keep

/-- A source function returns a closure retaining the older binder. -/
def body : HOL.Term Symbol [.prop] (.arr .prop .prop) := .lam (.var (.vs .vz))

theorem fresh : FormationSensitiveHOLUniformList.signature.rules.constantType name = none := by
  decide +kernel

theorem source_admitted : DeclarationAdmissionReplay.Admitted
    FormationSensitiveHOLUniformList.signature.rules []
    (declarations FormationSensitiveHOLUniformList.signature name (.lam body)) :=
  admitted _ name (.lam body) fresh

theorem source_application_typed : Typing
    (rules FormationSensitiveHOLUniformList.signature name (.lam body)) .nil
    (.app (.const name) (translate FormationSensitiveHOLUniformList.signature (.top : HOL.Formula Symbol [])))
    (typeAt FormationSensitiveHOLUniformList.signature.types 0 (.arr .prop .prop)) :=
  application_typed _ name (Γ := []) body .top fresh

theorem source_application_runs : ConversionCoherence.StepStar
    (rules FormationSensitiveHOLUniformList.signature name (.lam body))
    (.app (.const name) (translate FormationSensitiveHOLUniformList.signature (.top : HOL.Formula Symbol [])))
    (translate FormationSensitiveHOLUniformList.signature (HOL.instantiate .top body)) :=
  application_steps _ name body .top

theorem returned_closure_avoids_capture :
    translate FormationSensitiveHOLUniformList.signature (HOL.instantiate .top body) ≠
      (.lam (.var 0) : Tower.Tm 0) := by decide +kernel

/-- The returned function retains the caller's variable instead of capturing
it as its own argument. This exercises the open-context execution law. -/
theorem open_argument_runs : ConversionCoherence.StepStar
    (rules FormationSensitiveHOLUniformList.signature name (.lam body))
    (.app (.const name) (.var 0) : Tower.Tm 1) (.lam (.var 1)) := by
  simpa [body, HOL.rename, HOL.Rename.lift, HOL.instantiate, HOL.subst,
    HOL.Subst.single, HOL.Subst.lift, HOL.weaken, HOL.Rename.weaken, variableIndex] using
    application_open_steps FormationSensitiveHOLUniformList.signature name body
      (.var (.vz : HOL.Var [.prop] .prop))

theorem replacing_proposition_carrier_rejected :
    ¬ DeclarationAdmissionReplay.Admitted FormationSensitiveHOLUniformList.signature.rules []
      (declarations FormationSensitiveHOLUniformList.signature `HOLUniformList.prop (.lam body)) := by
  rw [admitted_iff_fresh]
  decide +kernel

end Controls

#print axioms admitted
#print axioms admitted_iff_fresh
#print axioms constant_typed
#print axioms delta
#print axioms application_typed
#print axioms application_steps
#print axioms application_open_steps
#print axioms open_result_typed
#print axioms result_typed
#print axioms Controls.source_admitted
#print axioms Controls.source_application_typed
#print axioms Controls.source_application_runs
#print axioms Controls.returned_closure_avoids_capture
#print axioms Controls.open_argument_runs
#print axioms Controls.replacing_proposition_carrier_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionAdmission
