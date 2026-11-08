import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemand
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedVersions
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-!
# Resource-free source dependencies of type inference

Input dependencies may contain type variables; retained output states may
not. This checker therefore differs from `RetainedTypePayloads.admitted`.
It checks the source rows and inputs before lookup, freshening, substitution
or unification. Groundness of the final range cannot establish this property.

The source packet is the complete effective declaration/subtype input,
including imported and intrinsic declarations supplied by its owner. Its
global check is conservative: unrelated rows in that packet are checked too.
The native capture of that complete packet remains a source-index obligation;
this module never identifies a partial local row list with an import closure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open RetainedTypePayloads (ExternalView observe observeList)

mutual
def resourceFree : Atom → Bool
  | .symbol _ => true
  | .var _ => true
  | .grounded (.int _) => true
  | .grounded (.bool _) => true
  | .grounded (.string _) => true
  | .grounded (.custom _ _) => false
  | .expression children => resourceFreeList children
def resourceFreeList : List Atom → Bool
  | [] => true
  | atom :: atoms => resourceFree atom && resourceFreeList atoms
end

theorem resourceFreeList_iff (atoms : List Atom) :
    resourceFreeList atoms = true ↔ ∀ atom ∈ atoms, resourceFree atom = true := by
  induction atoms with
  | nil => simp [resourceFreeList]
  | cons atom atoms ih => simp [resourceFreeList, ih]

mutual
theorem observe_resourceFree (external : ExternalView) : ∀ atom,
    resourceFree atom = true → observe external atom = atom
  | .symbol _, _ => rfl
  | .var _, _ => rfl
  | .grounded value, safe => by cases value <;> simp_all [resourceFree, observe]
  | .expression children, safe => by rw [observe, observeList_resourceFree external children safe]
theorem observeList_resourceFree (external : ExternalView) : ∀ atoms,
    resourceFreeList atoms = true → observeList external atoms = atoms
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      rw [observeList, observe_resourceFree external atom safe.1,
        observeList_resourceFree external atoms safe.2]
end

mutual
theorem rename_resourceFree (rename : String → String) : ∀ atom,
    resourceFree (renameAtom rename atom) = resourceFree atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression children => renameList_resourceFree rename children
theorem renameList_resourceFree (rename : String → String) : ∀ atoms,
    resourceFreeList (renameAtomList rename atoms) = resourceFreeList atoms
  | [] => rfl
  | atom :: atoms => by
      rw [renameAtomList, resourceFreeList, rename_resourceFree, renameList_resourceFree, resourceFreeList]
end

mutual
theorem substitute_resourceFree (substitution : String → Atom)
    (valuesSafe : ∀ name, resourceFree (substitution name) = true) :
    ∀ atom, resourceFree atom = true → resourceFree (substA substitution atom) = true
  | .symbol _, _ => rfl
  | .var name, _ => valuesSafe name
  | .grounded _, safe => safe
  | .expression children, safe => substituteList_resourceFree substitution valuesSafe children safe
theorem substituteList_resourceFree (substitution : String → Atom)
    (valuesSafe : ∀ name, resourceFree (substitution name) = true) :
    ∀ atoms, resourceFreeList atoms = true → resourceFreeList (substL substitution atoms) = true
  | [], _ => rfl
  | atom :: atoms, safe => by
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      exact Bool.and_eq_true_iff.mpr
        ⟨substitute_resourceFree substitution valuesSafe atom safe.1,
          substituteList_resourceFree substitution valuesSafe atoms safe.2⟩
end

open Mettapedia.Logic.LP.UnificationRestriction (Respect)

def permittedLeaf : UnifyAtoms.Leaf → Prop
  | .sym _ => True
  | .gnd (.custom _ _) => False
  | .gnd _ => True

instance : DecidablePred permittedLeaf := fun leaf => by
  cases leaf with
  | sym _ => exact isTrue trivial
  | gnd value => cases value <;> simp [permittedLeaf] <;> infer_instance

theorem encode_respects (atom : Atom) (safe : resourceFree atom = true) :
    Respect permittedLeaf (UnifyAtoms.encode atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    resourceFreeList atoms = true → ∀ atom ∈ atoms, Respect permittedLeaf (UnifyAtoms.encode atom)) with
  | symbol _ => simp [UnifyAtoms.encode, Respect, permittedLeaf]
  | var _ => simp [UnifyAtoms.encode, Respect]
  | grounded value => cases value <;> simp_all [resourceFree, UnifyAtoms.encode, Respect, permittedLeaf]
  | expression children ih =>
      rw [UnifyAtoms.encode_expression]
      exact fun index => ih safe _ (List.get_mem _ _)
  | nil _ _ member => cases member
  | cons atom atoms first rest safe child member =>
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      rcases List.mem_cons.mp member with rfl | later
      · exact first safe.1
      · exact rest safe.2 child later

theorem decode_resourceFree : ∀ term : Mettapedia.Logic.LP.Term UnifyAtoms.sig,
    Respect permittedLeaf term → resourceFree (UnifyAtoms.decode term) = true
  | .var _, _ => rfl
  | .const (.sym _), _ => rfl
  | .const (.gnd value), safe => by cases value <;> simp_all [permittedLeaf, Respect, UnifyAtoms.decode, resourceFree]
  | .app arity children, safe => by
      change resourceFreeList (List.ofFn fun index : Fin arity => UnifyAtoms.decode (children index)) = true
      apply (resourceFreeList_iff _).mpr
      intro atom member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact decode_resourceFree (children index) (safe index)

/-- The actual total first-order unifier cannot introduce resource-valued
constants absent from both operands, including in images of other variables. -/
theorem unify_resourceFree {left right : Atom} {theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig}
    (matched : UnifyAtoms.unify left right = some theta)
    (leftSafe : resourceFree left = true) (rightSafe : resourceFree right = true) :
    ∀ name, resourceFree (UnifyAtoms.readBack theta name) = true := by
  have each := Mettapedia.Logic.LP.UnificationRestriction.unifyTotal_respects
    (σ := UnifyAtoms.sig) permittedLeaf (UnifyAtoms.Leaf.sym "") (by trivial)
    [(UnifyAtoms.encode left, UnifyAtoms.encode right)] theta matched
    (by intro equation member
        have same := List.mem_singleton.mp member
        subst equation
        exact ⟨encode_respects left leftSafe, encode_respects right rightSafe⟩)
  intro name
  exact decode_resourceFree (theta name) (each name)

/-- Matching a subtype row then reading its upper expression is closed under
the resource-free grammar; the rule may contain type variables on both sides. -/
theorem subtype_instance_resourceFree {lower upper input : Atom}
    {theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig}
    (lowerSafe : resourceFree lower = true) (upperSafe : resourceFree upper = true)
    (inputSafe : resourceFree input = true) (matched : UnifyAtoms.unify lower input = some theta) :
    resourceFree (substA (UnifyAtoms.readBack theta) upper) = true :=
  substitute_resourceFree _ (unify_resourceFree matched lowerSafe inputSafe) upper upperSafe

structure SourcePacket where
  rows : List Atom
  intrinsicRows : List Atom
  input : Atom

def check (packet : SourcePacket) : Bool :=
  resourceFreeList packet.rows && resourceFreeList packet.intrinsicRows && resourceFree packet.input

/-- Every imported/overlay row must be included by the packet producer.
The checker is deliberately global within that captured source packet. -/
theorem check_source_rows {packet : SourcePacket} (accepted : check packet = true) :
    (∀ row ∈ packet.rows, resourceFree row = true) ∧
    (∀ row ∈ packet.intrinsicRows, resourceFree row = true) ∧ resourceFree packet.input = true := by
  simpa [check, resourceFreeList_iff, and_assoc] using accepted

def observedSpace (external : ExternalView) (rows : List Atom) : Space :=
  ⟨observeList external rows⟩

theorem annotation_resourceFree {rows : List Atom} (safe : resourceFreeList rows = true)
    (subject : Atom) {type_ : Atom} (member : type_ ∈ getAnnotatedTypes ⟨rows⟩ subject) :
    resourceFree type_ = true := by
  unfold getAnnotatedTypes at member
  obtain ⟨row, occurs, selected⟩ := List.mem_filterMap.mp member
  have rowSafe := (resourceFreeList_iff _).mp safe row occurs
  split at selected <;> simp_all [resourceFree, resourceFreeList]

/-- The actual annotation reader agrees under every external world once the
complete source packet passes. This includes rows on subjects other than the
queried head: they are not silently omitted from scope admission. -/
theorem annotation_world_independent (first second : ExternalView) {packet : SourcePacket}
    (accepted : check packet = true) :
    getAnnotatedTypes (observedSpace first packet.rows) (observe first packet.input) =
      getAnnotatedTypes (observedSpace second packet.rows) (observe second packet.input) := by
  have data := check_source_rows accepted
  simp [observedSpace, observeList_resourceFree first _ ((resourceFreeList_iff _).mpr data.1),
    observeList_resourceFree second _ ((resourceFreeList_iff _).mpr data.1),
    observe_resourceFree first _ data.2.2, observe_resourceFree second _ data.2.2]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission
