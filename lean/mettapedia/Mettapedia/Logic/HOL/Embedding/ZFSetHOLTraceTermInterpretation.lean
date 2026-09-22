import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation

/-!
# Original HOL terms in the uniform trace representation

This interpreter recursively traverses the original HOL syntax and uses
actual trace lambda/application at every arrow type. Quantifiers range over
the recursively trace-coded carriers. Structural comparison with the existing
graph interpreter reuses its established Henkin and substitution theorems.
Concrete set constants are built from the same lifted set operations; no
second set model or assumed source-adequacy field is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation

open ZFSetHOLTraceTypeInterpretation ZFSetDependentProducts ZFSetUniverseLift
open ZFSetUniverseClosure ZFSetLiftedUniverseClosure ZFSetHenkinInterpretation
open ZFSetUniverseInterpretation
open ZFSetHOLTypeInterpretation (truth holds holds_truth)
open ZFSetHOLTermInterpretation (RawValuation)

universe u v

abbrev Valuation (Γ : Ctx Unit) := ∀ {A}, Var Γ A → Value.{u} A

noncomputable def graphValuation {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) :
    ZFSetHOLTermInterpretation.Valuation.{u} Γ := fun {_} boundVar => graphEquiv _ (ρ boundVar)

noncomputable def decodeValuation {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) :
    RawValuation.{u} Γ := fun {_} boundVar => decode _ (ρ boundVar)

theorem graphValuation_decode {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) :
    (ZFSetHOLTermInterpretation.decodeValuation (graphValuation ρ) : RawValuation Γ) =
      (decodeValuation ρ : RawValuation Γ) := by
  funext A boundVar
  exact graphEquiv_decode A (ρ boundVar)

def extend {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ)
    (x : Value A) : Valuation (A :: Γ)
  | _, .vz => x
  | _, .vs boundVar => ρ boundVar

theorem graphValuation_extend {Γ : Ctx Unit} {A : Ty Unit}
    (ρ : Valuation.{u} Γ) (x : Value A) :
    (graphValuation (extend ρ x) : ZFSetHOLTermInterpretation.Valuation (A :: Γ)) =
      (ZFSetHOLTermInterpretation.extend (graphValuation ρ) (graphEquiv A x) :
        ZFSetHOLTermInterpretation.Valuation (A :: Γ)) := by
  funext B boundVar
  cases boundVar <;> rfl

noncomputable def interpret {Const : Ty Unit → Type v}
    (constants : {A : Ty Unit} → Const A → Value.{u} A) :
    {Γ : Ctx Unit} → {A : Ty Unit} → Term Const Γ A → Valuation Γ → Value A
  | _, _, .var boundVar, ρ => ρ boundVar
  | _, _, .const c, _ => constants c
  | _, _, .app f x, ρ => app (interpret constants f ρ) (interpret constants x ρ)
  | _, _, .lam body, ρ => lam (fun x => interpret constants body (extend ρ x))
  | _, _, .top, _ => truth True
  | _, _, .bot, _ => truth False
  | _, _, .and p q, ρ => truth (holds (interpret constants p ρ) ∧ holds (interpret constants q ρ))
  | _, _, .or p q, ρ => truth (holds (interpret constants p ρ) ∨ holds (interpret constants q ρ))
  | _, _, .imp p q, ρ => truth (holds (interpret constants p ρ) → holds (interpret constants q ρ))
  | _, _, .not p, ρ => truth (¬ holds (interpret constants p ρ))
  | _, _, .eq x y, ρ => truth (interpret constants x ρ = interpret constants y ρ)
  | _, _, .all p, ρ => truth (∀ x, holds (interpret constants p (extend ρ x)))
  | _, _, .ex p, ρ => truth (∃ x, holds (interpret constants p (extend ρ x)))

/-- This comparison is proved for independently evaluated syntax. Its
constant premise is discharged below for the actual set signatures. -/
theorem graph_interpret {Const : Ty Unit → Type v}
    (constants : {A : Ty Unit} → Const A → Value.{u} A)
    (graphConstants : {A : Ty Unit} → Const A → ZFSetHOLTypeInterpretation.Value.{u} A)
    (constant_law : ∀ {A} (c : Const A), graphEquiv A (constants c) = graphConstants c)
    {Γ : Ctx Unit} {A : Ty Unit} (term : Term Const Γ A) (ρ : Valuation Γ) :
    graphEquiv A (interpret constants term ρ) =
      ZFSetHOLTermInterpretation.interpret graphConstants term (graphValuation ρ) := by
  induction term with
  | var => rfl
  | const c => exact constant_law c
  | app f x ihf ihx =>
      rw [interpret, graphEquiv_app, ihf, ihx]
      rfl
  | lam body ih =>
      rw [interpret, graphEquiv_lam, ZFSetHOLTermInterpretation.interpret]
      congr 1
      funext x
      rw [ih, graphValuation_extend, Equiv.apply_symm_apply]
  | top => exact graphEquiv_prop _
  | bot => exact graphEquiv_prop _
  | and p q ihp ihq =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      have hp := (graphEquiv_prop _).symm.trans (ihp ρ)
      have hq := (graphEquiv_prop _).symm.trans (ihq ρ)
      rw [hp, hq]
  | or p q ihp ihq =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      have hp := (graphEquiv_prop _).symm.trans (ihp ρ)
      have hq := (graphEquiv_prop _).symm.trans (ihq ρ)
      rw [hp, hq]
  | imp p q ihp ihq =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      have hp := (graphEquiv_prop _).symm.trans (ihp ρ)
      have hq := (graphEquiv_prop _).symm.trans (ihq ρ)
      rw [hp, hq]
  | not p ih =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      rw [(graphEquiv_prop _).symm.trans (ih ρ)]
  | eq x y ihx ihy =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      congr 1
      apply propext
      exact ((graphEquiv _).injective.eq_iff).symm.trans
        (iff_of_eq (congrArg₂ Eq (ihx ρ) (ihy ρ)))
  | @all A Γ p ih =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      congr 1
      apply propext
      constructor
      · intro hp x
        have value := hp ((graphEquiv A).symm x)
        have equal := (graphEquiv_prop _).symm.trans (ih (extend ρ ((graphEquiv A).symm x)))
        rw [graphValuation_extend, Equiv.apply_symm_apply] at equal
        exact equal ▸ value
      · intro hp x
        have equal := (graphEquiv_prop _).symm.trans (ih (extend ρ x))
        rw [graphValuation_extend] at equal
        exact equal.symm ▸ hp (graphEquiv A x)
  | @ex A Γ p ih =>
      rw [interpret, graphEquiv_prop, ZFSetHOLTermInterpretation.interpret]
      congr 1
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨graphEquiv A x, ?_⟩
        have equal := (graphEquiv_prop _).symm.trans (ih (extend ρ x))
        rw [graphValuation_extend] at equal
        exact equal ▸ hx
      · rintro ⟨x, hx⟩
        refine ⟨(graphEquiv A).symm x, ?_⟩
        have equal := (graphEquiv_prop _).symm.trans (ih (extend ρ ((graphEquiv A).symm x)))
        rw [graphValuation_extend, Equiv.apply_symm_apply] at equal
        exact equal.symm ▸ hx

/-! ## Reusing the same set operations, with trace-coded higher-order inputs -/

noncomputable def separateValue (a : Value.{u} set) (p : Value predicate) : Value set :=
  carrierSeparation a (fun x => holds (app p (encode (lowerValue x))))

noncomputable def constants : {A : Ty Unit} → Symbol A → Value.{u} A
  | _, .member => lam (fun x => lam (fun a => truth (x.1 ∈ a.1)))
  | _, .empty => carrierEmpty
  | _, .union => lam carrierUnion
  | _, .power => lam carrierPower
  | _, .separate => lam (fun a => lam (separateValue a))
  | _, .replace => lam (fun a => lam (fun f => carrierReplacement a (app f)))

theorem graphEquiv_symm_base (x : ZFSetHOLTypeInterpretation.Value.{u} set) :
    (graphEquiv set).symm x = x := by
  apply (graphEquiv set).injective
  rw [Equiv.apply_symm_apply, graphEquiv_base]

theorem graph_separateValue (a : Value.{u} set) (p : Value predicate) :
    graphEquiv set (separateValue a p) =
      ZFSetHOLTermInterpretation.separateValue (graphEquiv set a) (graphEquiv predicate p) := by
  rw [graphEquiv_base, graphEquiv_base]
  unfold separateValue ZFSetHOLTermInterpretation.separateValue
  congr 1
  funext x
  have equal := graphEquiv_app (A := set) (B := .prop) p (encode (lowerValue x))
  rw [graphEquiv_prop, graphEquiv_base] at equal
  exact congrArg holds equal

theorem graph_constants {A : Ty Unit} (c : Symbol A) :
    graphEquiv A (constants.{u} c) = ZFSetHOLTermInterpretation.constants c := by
  cases c with
  | member =>
      rw [constants, graphEquiv_lam, ZFSetHOLTermInterpretation.constants]
      congr 1
      funext x
      rw [graphEquiv_lam]
      congr 1
      funext a
      rw [graphEquiv_prop, graphEquiv_symm_base, graphEquiv_symm_base]
  | empty => exact graphEquiv_base _
  | union =>
      rw [constants, graphEquiv_lam, ZFSetHOLTermInterpretation.constants]
      congr 1
      funext a
      rw [graphEquiv_base, graphEquiv_symm_base]
  | power =>
      rw [constants, graphEquiv_lam, ZFSetHOLTermInterpretation.constants]
      congr 1
      funext a
      rw [graphEquiv_base, graphEquiv_symm_base]
  | separate =>
      rw [constants, graphEquiv_lam, ZFSetHOLTermInterpretation.constants]
      congr 1
      funext a
      rw [graphEquiv_lam]
      congr 1
      funext p
      rw [graph_separateValue, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  | replace =>
      rw [constants, graphEquiv_lam, ZFSetHOLTermInterpretation.constants]
      congr 1
      funext a
      rw [graphEquiv_lam]
      congr 1
      funext f
      rw [graphEquiv_base, graphEquiv_symm_base]
      congr 1
      funext x
      have equal := graphEquiv_app (A := set) (B := set) ((graphEquiv mapping).symm f) x
      rw [graphEquiv_base, graphEquiv_base, Equiv.apply_symm_apply] at equal
      exact equal

noncomputable def universeConstants (h : CofinalInaccessibles.{u}) :
    {A : Ty Unit} → UniverseSymbol A → Value.{u} A
  | _, .core c => constants c
  | _, .universe => lam (carrierUniverse h)

theorem graph_universeConstants (h : CofinalInaccessibles.{u})
    {A : Ty Unit} (c : UniverseSymbol A) :
    graphEquiv A (universeConstants h c) = ZFSetHOLTermInterpretation.universeConstants h c := by
  cases c with
  | core c => exact graph_constants c
  | «universe» =>
      rw [universeConstants, graphEquiv_lam, ZFSetHOLTermInterpretation.universeConstants]
      congr 1
      funext a
      rw [graphEquiv_base, graphEquiv_symm_base]

theorem core_term_agreement {Γ : Ctx Unit} {A : Ty Unit}
    (term : Expr Γ A) (ρ : Valuation.{u} Γ) :
    decode A (interpret constants term ρ) = model.denote term (decodeValuation ρ) := by
  rw [← graphEquiv_decode, graph_interpret constants ZFSetHOLTermInterpretation.constants
    graph_constants, ZFSetHOLTermInterpretation.core_term_agreement, graphValuation_decode]

theorem universe_term_agreement (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (term : UniverseExpr Γ A) (ρ : Valuation Γ) :
    decode A (interpret (universeConstants h) term ρ) =
      (universeModel h).denote term (decodeValuation ρ) := by
  rw [← graphEquiv_decode,
    graph_interpret (universeConstants h) (ZFSetHOLTermInterpretation.universeConstants h)
      (graph_universeConstants h),
    ZFSetHOLTermInterpretation.universe_term_agreement, graphValuation_decode]

/-! ## Original simultaneous substitutions and lifted binders -/

theorem graphValuation_injective {Γ : Ctx Unit} :
    Function.Injective (@graphValuation.{u} Γ) := by
  intro ρ ν equal
  funext A boundVar
  apply (graphEquiv A).injective
  exact congrArg (fun ξ : ZFSetHOLTermInterpretation.Valuation Γ => ξ boundVar) equal

noncomputable def substValuation {Const : Ty Unit → Type v}
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    {Γ Δ : Ctx Unit} (θ : Subst Const Γ Δ) (ρ : Valuation Δ) : Valuation Γ :=
  fun {_} boundVar => interpret symbols (θ boundVar) ρ

theorem graph_substValuation {Const : Ty Unit → Type v}
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    (graphSymbols : {A : Ty Unit} → Const A → ZFSetHOLTypeInterpretation.Value.{u} A)
    (constant_law : ∀ {A} (c : Const A), graphEquiv A (symbols c) = graphSymbols c)
    {Γ Δ : Ctx Unit} (θ : Subst Const Γ Δ) (ρ : Valuation Δ) :
    (graphValuation (substValuation symbols θ ρ) : ZFSetHOLTermInterpretation.Valuation Γ) =
      (ZFSetHOLTermInterpretation.substValuation graphSymbols θ (graphValuation ρ) :
        ZFSetHOLTermInterpretation.Valuation Γ) := by
  funext A boundVar
  exact graph_interpret symbols graphSymbols constant_law (θ boundVar) ρ

/-- Substitution for arbitrary interpreted constants, derived through the
independently proved graph comparison and existing semantic substitution. -/
theorem interpret_substitution {Const : Ty Unit → Type v}
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    {Γ Δ : Ctx Unit} {A : Ty Unit} (term : Term Const Γ A)
    (θ : Subst Const Γ Δ) (ρ : Valuation Δ) :
    interpret symbols (HOL.subst θ term) ρ =
      interpret symbols term (substValuation symbols θ ρ) := by
  let graphSymbols : {A : Ty Unit} → Const A → ZFSetHOLTypeInterpretation.Value.{u} A :=
    fun {_} c => graphEquiv _ (symbols c)
  have comparison : ∀ {A} (c : Const A), graphEquiv A (symbols c) = graphSymbols c :=
    fun _ => rfl
  have denotation : ∀ {A} (c : Const A),
      ZFSetHOLTypeInterpretation.decode A (graphSymbols c) = decode A (symbols c) :=
    fun c => graphEquiv_decode _ (symbols c)
  apply (graphEquiv A).injective
  rw [graph_interpret symbols graphSymbols comparison,
    graph_interpret symbols graphSymbols comparison,
    graph_substValuation symbols graphSymbols comparison]
  exact ZFSetHOLTermInterpretation.interpret_substitution
    (fun c => decode _ (symbols c)) graphSymbols denotation term θ (graphValuation ρ)

theorem core_substitution {Γ Δ : Ctx Unit} {A : Ty Unit}
    (term : Expr Γ A) (θ : Subst Symbol Γ Δ) (ρ : Valuation.{u} Δ) :
    interpret constants (HOL.subst θ term) ρ =
      interpret constants term (substValuation constants θ ρ) :=
  interpret_substitution constants term θ ρ

theorem universe_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (term : UniverseExpr Γ A)
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    interpret (universeConstants h) (HOL.subst θ term) ρ =
      interpret (universeConstants h) term (substValuation (universeConstants h) θ ρ) :=
  interpret_substitution (universeConstants h) term θ ρ

theorem universe_substValuation_lift (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ) (x : Value A) :
    (substValuation (universeConstants h) (Subst.lift θ) (extend ρ x) : Valuation (A :: Γ)) =
      (extend (substValuation (universeConstants h) θ ρ) x : Valuation (A :: Γ)) := by
  apply graphValuation_injective
  have first := graph_substValuation (universeConstants h)
    (ZFSetHOLTermInterpretation.universeConstants h) (graph_universeConstants h)
    (Subst.lift θ) (extend ρ x)
  have second := congrArg (fun ν : ZFSetHOLTermInterpretation.Valuation (A :: Δ) =>
    (ZFSetHOLTermInterpretation.substValuation
      (ZFSetHOLTermInterpretation.universeConstants h) (Subst.lift θ) ν :
        ZFSetHOLTermInterpretation.Valuation (A :: Γ))) (graphValuation_extend ρ x)
  have third := ZFSetHOLTermInterpretation.universe_substValuation_lift h θ
    (graphValuation ρ) (graphEquiv A x)
  have fourth := congrArg (fun ν : ZFSetHOLTermInterpretation.Valuation Γ =>
    (ZFSetHOLTermInterpretation.extend ν (graphEquiv A x) :
      ZFSetHOLTermInterpretation.Valuation (A :: Γ)))
    (graph_substValuation (universeConstants h) (ZFSetHOLTermInterpretation.universeConstants h)
      (graph_universeConstants h) θ ρ)
  exact first.trans (second.trans (third.trans (fourth.symm.trans
    (graphValuation_extend (substValuation (universeConstants h) θ ρ) x).symm)))

/-! ## Original higher-order statements and a changed-function control -/

def emptyValuation : Valuation.{u} [] := fun {_} boundVar => nomatch boundVar

theorem coded_function_eta : holds (interpret constants.{u}
    ZFSetHOLTermInterpretation.applicationEta emptyValuation) := by
  simp only [ZFSetHOLTermInterpretation.applicationEta, interpret, extend, holds_truth]
  exact lam_eta

theorem not_all_functions_identity : ¬ holds (interpret constants.{u}
    ZFSetHOLTermInterpretation.allFunctionsIdentity emptyValuation) := by
  intro claimed
  have equal := (graphEquiv_prop _).symm.trans
    (graph_interpret constants ZFSetHOLTermInterpretation.constants graph_constants
      ZFSetHOLTermInterpretation.allFunctionsIdentity emptyValuation)
  have empty : (graphValuation emptyValuation : ZFSetHOLTermInterpretation.Valuation []) =
      (ZFSetHOLTermInterpretation.emptyValuation : ZFSetHOLTermInterpretation.Valuation []) := by
    funext A boundVar
    nomatch boundVar
  rw [empty] at equal
  exact ZFSetHOLTermInterpretation.not_all_functions_identity (equal ▸ claimed)

def powerApplication : Expr [] set := .app (.const .power) (.const .empty)

theorem power_application : interpret constants.{u} powerApplication emptyValuation =
    carrierPower carrierEmpty := by
  simp only [powerApplication, interpret, constants, app_lam]

theorem power_application_not_empty : interpret constants.{u} powerApplication emptyValuation ≠
    carrierEmpty := by
  rw [power_application]
  intro equal
  have decoded := congrArg carrierEquiv equal
  rw [decode_power, decode_empty] at decoded
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [decoded] at member
  exact ZFSet.notMem_empty _ member

def functionParameter : Expr [mapping, set] set :=
  .app (.var .vz) (.var (.vs .vz))

def substitutePower : Subst Symbol [mapping, set] [set]
  | _, .vz => .const .power
  | _, .vs .vz => .var .vz

theorem function_parameter_substitution (ρ : Valuation.{u} [set]) :
    interpret constants (HOL.subst substitutePower functionParameter) ρ =
      carrierPower (ρ .vz) := by
  change app (A := set) (B := set) (lam carrierPower) (ρ .vz) = _
  exact app_lam (A := set) (B := set) carrierPower (ρ .vz)

theorem function_parameter_substitution_square (ρ : Valuation.{u} [set]) :
    graphEquiv set
      (interpret constants functionParameter (substValuation constants substitutePower ρ)) =
      ZFSetHOLTermInterpretation.interpret ZFSetHOLTermInterpretation.constants
        (HOL.subst substitutePower functionParameter) (graphValuation ρ) := by
  rw [← core_substitution]
  exact graph_interpret constants ZFSetHOLTermInterpretation.constants graph_constants _ ρ

#print axioms graph_interpret
#print axioms graph_constants
#print axioms graph_universeConstants
#print axioms core_term_agreement
#print axioms universe_term_agreement
#print axioms graph_substValuation
#print axioms interpret_substitution
#print axioms core_substitution
#print axioms universe_substitution
#print axioms universe_substValuation_lift
#print axioms coded_function_eta
#print axioms not_all_functions_identity
#print axioms power_application
#print axioms power_application_not_empty
#print axioms function_parameter_substitution
#print axioms function_parameter_substitution_square

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation
