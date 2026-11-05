import Mettapedia.Logic.HOL.FunctionExtensionalityEtaExpansion

/-!
# Controls for eta-licensed function-extensionality expansion

A beta-only pointwise proof compares an arbitrary function with its eta
expansion. The derived equation explicitly uses eta and fails the existing
eta/function-extensionality-free qualification. A natural-number model gives
the function a genuinely nonconstant interpretation; a different successor
function also refutes omitting the pointwise premise. No intensional model or
eta-free admissibility theorem is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FunctionExtensionalityEtaExpansionControls
universe u v

section Generic
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {Δ : List (Formula Const Γ)} {domain codomain : Ty Base}

def etaExpansion (function : Term Const Γ (domain ⇒ codomain)) : Term Const Γ (domain ⇒ codomain) :=
  .lam (.app (weaken function) (.var .vz))

def pointwise (first second : Term Const Γ (domain ⇒ codomain)) : Formula Const Γ :=
  .all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))

def pointwiseEta (function : Term Const Γ (domain ⇒ codomain)) :
    ProofSyntax Const Δ (pointwise function (etaExpansion function)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.eqSymm
  let body : Term Const (domain :: Γ) codomain := .app (weaken function) (.var .vz)
  apply ProofSyntax.castIndices rfl ?_
    (.beta (.var .vz) (rename (Rename.lift Rename.weaken) body))
  exact congrArg (fun result => Term.eq (.app (weaken (.lam body)) (.var .vz)) result)
    (ContextualTrinity.instantiate_vz_rename_lift_weaken body)

theorem pointwiseEta_free (function : Term Const Γ (domain ⇒ codomain)) :
    (pointwiseEta (Δ := Δ) function).FunctionExtensionalityFree := by
  simp only [pointwiseEta,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]

def derived (function : Term Const Γ (domain ⇒ codomain)) :
    ProofSyntax Const Δ (.eq function (etaExpansion function)) :=
  ProofSyntax.funExtViaEta (pointwiseEta function)

theorem derived_not_free (function : Term Const Γ (domain ⇒ codomain)) :
    ¬ (derived (Δ := Δ) function).FunctionExtensionalityFree :=
  ProofSyntax.funExtViaEta_not_free _

def direct (function : Term Const Γ (domain ⇒ codomain)) :
    ProofSyntax Const Δ (.eq function (etaExpansion function)) := .funExt (pointwiseEta function)

theorem direct_uses_one_rule (function : Term Const Γ (domain ⇒ codomain)) :
    (direct (Δ := Δ) function).primitiveFunExtUses = 1 := by
  simp only [direct,ProofSyntax.primitiveFunExtUses,pointwiseEta,
    ProofSyntax.primitiveFunExtUses_castIndices,Nat.zero_add]

theorem expanded_uses_no_direct_rule (function : Term Const Γ (domain ⇒ codomain)) :
    ((direct (Δ := Δ) function).expandFunExt).primitiveFunExtUses = 0 :=
  ProofSyntax.expandFunExt_primitiveUses _

theorem expansion_changes_the_actual_tree (function : Term Const Γ (domain ⇒ codomain)) :
    (direct (Δ := Δ) function).expandFunExt ≠ direct function := by
  intro same
  have count := congrArg ProofSyntax.primitiveFunExtUses same
  rw [expanded_uses_no_direct_rule,direct_uses_one_rule] at count
  cases count

end Generic

abbrev N : Ty Unit := .base ()
inductive Const : Ty Unit → Type where
  | zero : Const N
  | successor : Const (N ⇒ N)

def carrier (_ : Unit) : Type 1 := ULift.{1} Nat
def meaning : {type : Ty Unit} → Const type → Ty.denote.{0,0} carrier type
  | _,.zero => ULift.up 0
  | _,.successor => fun n => ULift.up (n.down+1)
def model : HenkinModel.{0,0,0} Unit Const := .standard carrier meaning
def emptyValues : model.Valuation [] := fun index => nomatch index
def function : Term Const [N ⇒ N] (N ⇒ N) := .var .vz
def values : model.Valuation [N ⇒ N] := model.extend (σ := N ⇒ N) emptyValues (fun n => ULift.up (n.down+1))
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

theorem function_is_nonconstant :
    model.denote function values (ULift.up 0) ≠ model.denote function values (ULift.up 1) := by
  intro same
  have impossible : (1 : Nat) = 2 := congrArg ULift.down same
  cases impossible

theorem nonconstant_derived_equation_holds :
    (model.denote (.eq function (etaExpansion function)) values).down :=
  Soundness.extDerivation_sound (derived (Δ := []) function).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (by intro formula impossible; cases impossible)

def identity : ClosedTerm Const (N ⇒ N) := .lam (.var .vz)
def successor : ClosedTerm Const (N ⇒ N) := .const .successor

theorem unequal_functions_refused : ¬ (model.denote (.eq identity successor) emptyValues).down := by
  intro same
  have impossible := model.eqv_arr_apply same (model.base_mem () (ULift.up 0))
  change (ULift.up 0 : ULift.{1} Nat) = ULift.up 1 at impossible
  have wrong : (0 : Nat) = 1 := congrArg ULift.down impossible
  cases wrong

theorem missing_pointwise_premise_refused :
    ¬ Nonempty (ProofSyntax Const [] (pointwise identity successor)) := by
  rintro ⟨proof⟩
  exact unequal_functions_refused (Soundness.extDerivation_sound (ProofSyntax.funExtViaEta proof).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (by intro formula impossible; cases impossible))

#print axioms pointwiseEta_free
#print axioms derived_not_free
#print axioms expansion_changes_the_actual_tree
#print axioms function_is_nonconstant
#print axioms missing_pointwise_premise_refused

end Mettapedia.Logic.HOL.FunctionExtensionalityEtaExpansionControls
