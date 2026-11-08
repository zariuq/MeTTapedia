import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission

/-!
# An executable inert source-dependency gate

The source dependencies of type inference and retained type outputs have
different requirements. Type variables are permitted here. Every external
resource leaf is rejected, and this conservative slice also rejects symbols
licensed for type normalization, wherever they occur. Consequently a
substitution cannot move a licensed symbol into a callable head position.

The normalization traversal below has the source head-dispatch conditions:
expressions shorter than two are inert; other expressions normalize their
children; a symbolic head is dispatched only at arity at least two and with
the type-pure license. The dispatched implementation is arbitrary. Admission
proves that it is never called, rather than assuming it is world-independent.

The constant restriction is preserved by the existing total unifier, actual
atom substitution and renaming. This certifies the source operations used by
declaration/subtype inference. Mapping every native operation and effective
imported row to these source operations remains a separate correspondence
obligation. Computed arithmetic type expressions are intentionally outside
this conservative slice.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InertTypeDependencies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Logic.LP.UnificationRestriction (Respect)
open TypeDependencyAdmission
open RetainedTypePayloads (ExternalView observe observeList)

mutual
def checkAtom (active : String → Bool) : Atom → Bool
  | .symbol name => !active name
  | .var _ => true
  | .grounded (.int _) => true
  | .grounded (.bool _) => true
  | .grounded (.string _) => true
  | .grounded (.custom _ _) => false
  | .expression children => checkList active children
def checkList (active : String → Bool) : List Atom → Bool
  | [] => true
  | atom :: atoms => checkAtom active atom && checkList active atoms
end

theorem checkList_iff (active : String → Bool) (atoms : List Atom) :
    checkList active atoms = true ↔ ∀ atom ∈ atoms, checkAtom active atom = true := by
  induction atoms with
  | nil => simp [checkList]
  | cons atom atoms ih => simp [checkList, ih]

mutual
theorem checkAtom_resourceFree (active : String → Bool) : ∀ atom,
    checkAtom active atom = true → resourceFree atom = true
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded value, safe => by cases value <;> simp_all [checkAtom, resourceFree]
  | .expression children, safe => checkList_resourceFree active children safe
theorem checkList_resourceFree (active : String → Bool) : ∀ atoms,
    checkList active atoms = true → resourceFreeList atoms = true
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [checkList, Bool.and_eq_true] at safe
      exact Bool.and_eq_true_iff.mpr
        ⟨checkAtom_resourceFree active atom safe.1, checkList_resourceFree active atoms safe.2⟩
end

mutual
theorem rename_closed (active : String → Bool) (rename : String → String) : ∀ atom,
    checkAtom active (renameAtom rename atom) = checkAtom active atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression children => renameList_closed active rename children
theorem renameList_closed (active : String → Bool) (rename : String → String) : ∀ atoms,
    checkList active (renameAtomList rename atoms) = checkList active atoms
  | [] => rfl
  | atom :: atoms => by
      rw [renameAtomList, checkList, rename_closed, renameList_closed, checkList]
end

mutual
theorem substitute_closed (active : String → Bool) (state : String → Atom)
    (stateSafe : ∀ name, checkAtom active (state name) = true) : ∀ atom,
    checkAtom active atom = true → checkAtom active (substA state atom) = true
  | .symbol _, safe => safe
  | .var name, _ => stateSafe name
  | .grounded _, safe => safe
  | .expression children, safe => substituteList_closed active state stateSafe children safe
theorem substituteList_closed (active : String → Bool) (state : String → Atom)
    (stateSafe : ∀ name, checkAtom active (state name) = true) : ∀ atoms,
    checkList active atoms = true → checkList active (substL state atoms) = true
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [checkList, Bool.and_eq_true] at safe
      exact Bool.and_eq_true_iff.mpr
        ⟨substitute_closed active state stateSafe atom safe.1,
          substituteList_closed active state stateSafe atoms safe.2⟩
end

def leafAllowed (active : String → Bool) : UnifyAtoms.Leaf → Prop
  | .sym name => active name = false
  | .gnd (.custom _ _) => False
  | .gnd _ => True

instance (active : String → Bool) : DecidablePred (leafAllowed active) := fun leaf => by
  cases leaf with
  | sym _ => unfold leafAllowed; infer_instance
  | gnd value => cases value <;> simp [leafAllowed] <;> infer_instance

theorem encode_allowed (active : String → Bool) (atom : Atom)
    (safe : checkAtom active atom = true) : Respect (leafAllowed active) (UnifyAtoms.encode atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms => checkList active atoms = true →
      ∀ atom ∈ atoms, Respect (leafAllowed active) (UnifyAtoms.encode atom)) with
  | symbol _ => simpa [checkAtom, UnifyAtoms.encode, Respect, leafAllowed] using safe
  | var _ => simp [UnifyAtoms.encode, Respect]
  | grounded value => cases value <;> simp_all [checkAtom, UnifyAtoms.encode, Respect, leafAllowed]
  | expression children ih =>
      rw [UnifyAtoms.encode_expression]
      exact fun index => ih safe _ (List.get_mem _ _)
  | nil _ _ member => cases member
  | cons atom atoms first rest safe child member =>
      simp only [checkList, Bool.and_eq_true] at safe
      rcases List.mem_cons.mp member with rfl | later
      · exact first safe.1
      · exact rest safe.2 child later

theorem decode_allowed (active : String → Bool) : ∀ term : Mettapedia.Logic.LP.Term UnifyAtoms.sig,
    Respect (leafAllowed active) term → checkAtom active (UnifyAtoms.decode term) = true
  | .var _, _ => rfl
  | .const (.sym name), safe => by simpa [Respect, leafAllowed, UnifyAtoms.decode, checkAtom] using safe
  | .const (.gnd value), safe => by cases value <;> simp_all [Respect, leafAllowed, UnifyAtoms.decode, checkAtom]
  | .app arity children, safe => by
      change checkList active (List.ofFn fun index : Fin arity => UnifyAtoms.decode (children index)) = true
      apply (checkList_iff _ _).mpr
      intro atom member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact decode_allowed active (children index) (safe index)

theorem unify_closed (active : String → Bool) {left right : Atom}
    {theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig}
    (matched : UnifyAtoms.unify left right = some theta)
    (leftSafe : checkAtom active left = true) (rightSafe : checkAtom active right = true) :
    ∀ name, checkAtom active (UnifyAtoms.readBack theta name) = true := by
  have each := Mettapedia.Logic.LP.UnificationRestriction.unifyTotal_respects
    (σ := UnifyAtoms.sig) (leafAllowed active) (.gnd (.int 0)) (by trivial)
    [(UnifyAtoms.encode left, UnifyAtoms.encode right)] theta matched
    (by intro equation member
        have same := List.mem_singleton.mp member
        subst equation
        exact ⟨encode_allowed active left leftSafe, encode_allowed active right rightSafe⟩)
  exact fun name => decode_allowed active (theta name) (each name)

def normalizeHead (active : String → Bool) (dispatch : String → List Atom → Option Atom) : Atom → Atom
  | atom@(.expression (.symbol head :: first :: second :: rest)) =>
      if active head then (dispatch head (first :: second :: rest)).getD atom else atom
  | atom => atom

mutual
def normalize (active : String → Bool) (dispatch : String → List Atom → Option Atom) : Atom → Atom
  | atom@(.expression children) =>
      if children.length < 2 then atom
      else normalizeHead active dispatch (.expression (normalizeList active dispatch children))
  | atom => atom
def normalizeList (active : String → Bool) (dispatch : String → List Atom → Option Atom) : List Atom → List Atom
  | [] => []
  | atom :: atoms => normalize active dispatch atom :: normalizeList active dispatch atoms
end

theorem normalizeHead_inert (active : String → Bool) (dispatch : String → List Atom → Option Atom)
    (atom : Atom) (safe : checkAtom active atom = true) : normalizeHead active dispatch atom = atom := by
  unfold normalizeHead
  split
  · simp only [checkAtom, checkList, Bool.and_eq_true, Bool.not_eq_true'] at safe
    simp [safe.1]
  · rfl

mutual
theorem normalize_inert (active : String → Bool) (dispatch : String → List Atom → Option Atom) :
    ∀ atom, checkAtom active atom = true → normalize active dispatch atom = atom
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded _, _ => rfl
  | .expression children, safe => by
      rw [normalize]
      split
      · rfl
      · rw [normalizeList_inert active dispatch children safe]
        exact normalizeHead_inert active dispatch _ safe
theorem normalizeList_inert (active : String → Bool) (dispatch : String → List Atom → Option Atom) :
    ∀ atoms, checkList active atoms = true → normalizeList active dispatch atoms = atoms
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [checkList, Bool.and_eq_true] at safe
      rw [normalizeList, normalize_inert active dispatch atom safe.1,
        normalizeList_inert active dispatch atoms safe.2]
end

/-- Even two entirely different external implementations of licensed
operations cannot change admitted type normalization. -/
theorem normalize_world (active : String → Bool)
    (first second : String → List Atom → Option Atom) (atom : Atom)
    (safe : checkAtom active atom = true) :
    normalize active first atom = normalize active second atom := by
  rw [normalize_inert active first atom safe, normalize_inert active second atom safe]

namespace Controls

def comparisonActive (name : String) : Bool := name == "=="

theorem schematic_list_is_inert :
    checkAtom comparisonActive (.expression [.symbol "List", .var "element"]) = true := by decide

/-- A licensed symbol is rejected even when it is currently in a data
position: unification could later place that symbol at an expression head. -/
theorem licensed_symbol_hidden_in_data_is_not_inert :
    checkAtom comparisonActive (.expression [.symbol "Holder", .symbol "=="]) = false := by decide

theorem resource_free_is_not_inert :
    resourceFree (.expression [.symbol "==", .grounded (.int 1), .grounded (.int 1)]) = true ∧
    checkAtom comparisonActive (.expression [.symbol "==", .grounded (.int 1), .grounded (.int 1)]) = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InertTypeDependencies
