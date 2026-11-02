import Mettapedia.Languages.HOLLight.CachedSourceExpansion

/-!
# Typed tables for cached defining equations

A row retains a complete source symbol and a closed body at its actual type.
The table constructs each equation proof from its ordered hypothesis position.
Matching compares source roles, declaration provenance and type annotations;
an unmatched symbol remains literal. Repeated keys select the first row, while
every row and its hypothesis occurrence remain in the authored table.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceDefinitionTable

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation CachedSourceExpansion

abbrev Key := Sigma Symbol

theorem reverseSymbol_injective {first second : Key}
    (same : reverseSymbol first.2 = reverseSymbol second.2) : first = second := by
  rcases first with ⟨firstType, first⟩
  rcases second with ⟨secondType, second⟩
  cases first with
  | constant first annotation firstTyped =>
      cases second with
      | «variable» => cases same
      | constant second otherAnnotation secondTyped =>
          cases same
          cases firstTyped
          cases secondTyped
          rfl
  | «variable» first firstTyped =>
      cases second with
      | constant => cases same
      | «variable» second secondTyped =>
          cases same
          cases firstTyped
          cases secondTyped
          rfl

def sameKey (first second : Key) : Bool :=
  DBTerm.same (reverseSymbol first.2) (reverseSymbol second.2)

@[simp] theorem sameKey_iff (first second : Key) : sameKey first second = true ↔ first = second := by
  constructor
  · intro equal
    exact reverseSymbol_injective ((DBTerm.same_eq_true_iff _ _).mp equal)
  · rintro rfl
    exact (DBTerm.same_eq_true_iff _ _).mpr rfl

structure Binding where
  key : Key
  body : HOL.ClosedTerm Symbol key.1

def Binding.equation (binding : Binding) : Formula := .eq (.const binding.key.2) binding.body

/-- Instantiate the actual row, including its symbol annotation and every
type occurrence in its body. Lookup after a noninjective type map has its
separate first-row policy; no lookup-naturality assumption is made here. -/
def Binding.typeInstance (binding : Binding) (substitution : TypeSubst) : Binding where
  key := ⟨HOL.Ty.substitute substitution.baseInstance binding.key.1,
    substitution.symbolInstance binding.key.2⟩
  body := HOL.mapTypes substitution.baseInstance substitution.symbolInstance binding.body

theorem Binding.typeInstance_equation (binding : Binding) (substitution : TypeSubst) :
    (binding.typeInstance substitution).equation =
      HOL.mapTypes substitution.baseInstance substitution.symbolInstance binding.equation := rfl

def theory (bindings : List Binding) : List Formula := bindings.map Binding.equation

structure Image (assumptions : List Formula) (key : Key) where
  body : HOL.ClosedTerm Symbol key.1
  proof : HOL.ProofSyntax Symbol assumptions (.eq (.const key.2) body)
  free : proof.FunctionExtensionalityFree

def Image.literal (assumptions : List Formula) (key : Key) : Image assumptions key :=
  ⟨.const key.2, .eqRefl _, True.intro⟩

def Image.castKey {assumptions : List Formula} {first second : Key} (same : first = second)
    (image : Image assumptions first) : Image assumptions second := same ▸ image

def image : (bindings : List Binding) → (key : Key) → Image (theory bindings) key
  | [], key => .literal _ key
  | binding :: rest, key =>
      if matched : sameKey binding.key key = true then
        Image.castKey ((sameKey_iff _ _).mp matched)
          ⟨binding.body, .hyp ⟨0, by simp [theory]⟩, by trivial⟩
      else
        let previous := image rest key
        ⟨previous.body, previous.proof.prepend binding.equation,
          by simpa only [HOL.ProofSyntax.prepend, HOL.ProofSyntax.functionExtensionalityFree_mono]
            using previous.free⟩

def replacement (bindings : List Binding) {type : HOL.Ty AtomicTy} (symbol : Symbol type) :
    HOL.ClosedTerm Symbol type := (image bindings ⟨type, symbol⟩).body

@[simp] theorem image_here_body (binding : Binding) (rest : List Binding) :
    (image (binding :: rest) binding.key).body = binding.body := by
  simp [image, Image.castKey]

theorem image_tail_body (binding : Binding) (rest : List Binding) (key : Key)
    (different : binding.key ≠ key) :
    (image (binding :: rest) key).body = (image rest key).body := by
  simp [image, different]

theorem image_missing (bindings : List Binding) (key : Key)
    (absent : ∀ binding ∈ bindings, binding.key ≠ key) :
    (image bindings key).body = .const key.2 := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rw [image_tail_body binding rest key (absent binding List.mem_cons_self)]
      exact ih (fun row member => absent row (List.mem_cons_of_mem _ member))

def replacements (bindings : List Binding) {type : HOL.Ty AtomicTy} (symbol : Symbol type) :
    Option (HOL.ClosedTerm Symbol type) := some (replacement bindings symbol)

def equations (bindings : List Binding) {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (body : HOL.ClosedTerm Symbol type) (present : replacements bindings symbol = some body) :
    HOL.ProofSyntax Symbol (theory bindings) (.eq (.const symbol) body) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (HOL.Term.eq (.const symbol)) (Option.some.inj present))
    (image bindings ⟨type, symbol⟩).proof

theorem equations_free (bindings : List Binding) {type : HOL.Ty AtomicTy} (symbol : Symbol type)
    (body : HOL.ClosedTerm Symbol type) (present : replacements bindings symbol = some body) :
    (equations bindings symbol body present).FunctionExtensionalityFree := by
  unfold equations
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (image bindings ⟨type, symbol⟩).free

def applyTerm (bindings : List Binding) {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol Γ type) : HOL.Term Symbol Γ type :=
  HOL.substConst (replacement bindings) term

theorem applyTerm_rename (bindings : List Binding) {Γ Ξ : HOL.Ctx AtomicTy}
    (renameVariables : HOL.Rename AtomicTy Γ Ξ) {type : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ type) :
    applyTerm bindings (HOL.rename renameVariables term) = HOL.rename renameVariables (applyTerm bindings term) :=
  HOL.substConst_rename (replacement bindings) renameVariables term

/-- The substitution environment is transformed too: its entries may contain
the very constants being expanded. -/
theorem applyTerm_subst (bindings : List Binding) {Γ Ξ : HOL.Ctx AtomicTy}
    (substitution : HOL.Subst Symbol Γ Ξ) {type : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ type) :
    applyTerm bindings (HOL.subst substitution term) =
      HOL.subst (fun index => applyTerm bindings (substitution index)) (applyTerm bindings term) :=
  (HOL.substConst_subst (replacement bindings) substitution term).symm

/-- The complete transported theorem is built by the existing checked task,
using only the individual authored row equations as assumptions. -/
def task (bindings : List Binding) (source : Formula) : Task where
  source := source
  target := applyTerm bindings source
  theory := theory bindings
  replacements := replacements bindings
  equations := equations bindings
  equationsFree := equations_free bindings
  expanded := HOL.substConst?_some (replacement bindings) source

namespace SyntaxControls

def symbolName : Name := .global "__definition_table_symbol"
def sourceConstant : Const := .mk symbolName .undefined
def constantKey : Key := ⟨.prop, .constant sourceConstant Ty.bool Ty.toHOL_bool⟩
def variableKey : Key := ⟨.prop, .variable ⟨symbolName, Ty.bool⟩ Ty.toHOL_bool⟩
def functionKey : Key := ⟨.arr .prop .prop,
  .constant sourceConstant (.function Ty.bool Ty.bool) (by simp only [Ty.toHOL_function, Ty.toHOL_bool])⟩

def truthBody : HOL.ClosedTerm Symbol .prop :=
  .eq (.lam (.var (.vz : HOL.Var [.prop] .prop))) (.lam (.var .vz))

def row : Binding := ⟨constantKey, truthBody⟩

def source : Formula := .all (.eq (.const constantKey.2) (.var .vz))
def target : Formula := .all (.eq (HOL.weaken truthBody) (.var .vz))

theorem beneath_binder : applyTerm [row] source = target := by
  change (.all (.eq (HOL.weaken (image [row] constantKey).body) (.var .vz)) : Formula) = target
  exact congrArg (fun body : HOL.ClosedTerm Symbol .prop =>
    (.all (.eq (HOL.weaken body) (.var .vz)) : Formula)) (image_here_body row [])

theorem role_distinct : sameKey constantKey variableKey = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have same := (sameKey_iff constantKey variableKey).mp accepted
  cases same

theorem annotation_distinct : sameKey constantKey functionKey = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have same := congrArg Sigma.fst ((sameKey_iff constantKey functionKey).mp accepted)
  cases same

theorem free_symbol_retained :
    applyTerm [row] (.const variableKey.2 : HOL.ClosedTerm Symbol .prop) = .const variableKey.2 := by
  change (image [row] variableKey).body = .const variableKey.2
  apply image_missing
  intro binding member
  have bindingSame : binding = row := List.mem_singleton.mp member
  subst binding
  intro same
  have accepted := (sameKey_iff row.key variableKey).mpr same
  rw [show sameKey row.key variableKey = false from role_distinct] at accepted
  cases accepted

/-- A repeated key keeps the first authored row and both hypothesis positions. -/
theorem duplicate_first (otherBody : HOL.ClosedTerm Symbol .prop) :
    (image [row, ⟨constantKey, otherBody⟩] constantKey).body = truthBody :=
  image_here_body row _

end SyntaxControls

#print axioms reverseSymbol_injective
#print axioms sameKey_iff
#print axioms equations_free
#print axioms task
#print axioms Binding.typeInstance_equation
#print axioms image_missing
#print axioms applyTerm_rename
#print axioms applyTerm_subst
#print axioms SyntaxControls.beneath_binder
#print axioms SyntaxControls.role_distinct
#print axioms SyntaxControls.annotation_distinct
#print axioms SyntaxControls.free_symbol_retained

end Mettapedia.Languages.HOLLight.CachedSourceDefinitionTable
