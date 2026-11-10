import Mettapedia.GSLT.LanguageDef.ABTHeadMapping
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSubstitution
import Mettapedia.GSLT.LanguageDef.ScopedABTApplication

/-! # Structural head transport on the common binding trees

Changing constructor identities retains every object index and field depth.
It commutes with capture-avoiding substitution and contextual grafting. An
injective head map therefore changes representation without identifying
distinct binding trees.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

variable {A B C : Type}

mutual
  def traverseHeads? (read : A → Option B) : Term A → Option (Term B)
    | .idx index => some (.idx index)
    | .node head fields => do return .node (← read head) (← traverseFieldHeads? read fields)

  def traverseFieldHeads? (read : A → Option B) : Fields A → Option (Fields B)
    | .nil => some .nil
    | .cons depth term rest => do
        return .cons depth (← traverseHeads? read term) (← traverseFieldHeads? read rest)
end

mutual
  theorem traverse_mapHeads (write : A → B) (read : B → Option A)
      (roundtrip : ∀ head, read (write head) = some head) (term : Term A) :
      traverseHeads? read (mapHeads write term) = some term := by
    cases term with
    | idx => rfl
    | node head fields =>
        simp only [mapHeads, traverseHeads?, roundtrip, traverse_mapFieldHeads write read roundtrip fields]
        rfl

  theorem traverse_mapFieldHeads (write : A → B) (read : B → Option A)
      (roundtrip : ∀ head, read (write head) = some head) (fields : Fields A) :
      traverseFieldHeads? read (mapFieldHeads write fields) = some fields := by
    cases fields with
    | nil => rfl
    | cons depth term rest =>
        simp only [mapFieldHeads, traverseFieldHeads?, traverse_mapHeads write read roundtrip term,
          traverse_mapFieldHeads write read roundtrip rest]
        rfl
end

mutual
  theorem conforms_mapHeads (change : A → B) (source : A → List Nat) (target : B → List Nat)
      (agrees : ∀ head, target (change head) = source head) (term : Term A) :
      Term.conforms target (mapHeads change term) = Term.conforms source term := by
    cases term with
    | idx => rfl
    | node head fields =>
        simp only [mapHeads, Term.conforms, agrees,
          conforms_mapFieldHeads change source target agrees (source head) fields]

  theorem conforms_mapFieldHeads (change : A → B) (source : A → List Nat) (target : B → List Nat)
      (agrees : ∀ head, target (change head) = source head) (expected : List Nat) (fields : Fields A) :
      Term.Fields.conforms target expected (mapFieldHeads change fields) =
        Term.Fields.conforms source expected fields := by
    cases fields with
    | nil => cases expected <;> rfl
    | cons depth term rest =>
        cases expected with
        | nil => rfl
        | cons wanted remaining =>
            simp only [mapFieldHeads, Term.Fields.conforms, conforms_mapHeads change source target agrees term,
              conforms_mapFieldHeads change source target agrees remaining rest]
end

mutual
  theorem mapHeads_comp (first : A → B) (second : B → C) (term : Term A) :
      mapHeads second (mapHeads first term) = mapHeads (second ∘ first) term := by
    cases term with
    | idx => rfl
    | node head fields => simp only [mapHeads, mapFieldHeads_comp first second fields]; rfl

  theorem mapFieldHeads_comp (first : A → B) (second : B → C) (fields : Fields A) :
      mapFieldHeads second (mapFieldHeads first fields) = mapFieldHeads (second ∘ first) fields := by
    cases fields with
    | nil => rfl
    | cons depth term rest =>
        simp only [mapFieldHeads, mapHeads_comp first second term, mapFieldHeads_comp first second rest]
end

mutual
  theorem mapHeads_lift (change : A → B) (cutoff amount : Nat) (term : Term A) :
      mapHeads change (Term.lift cutoff amount term) = Term.lift cutoff amount (mapHeads change term) := by
    cases term with
    | idx index => simp only [Term.lift, mapHeads]; split <;> rfl
    | node head fields =>
        simp only [Term.lift, mapHeads, mapFieldHeads_lift change cutoff amount fields]

  theorem mapFieldHeads_lift (change : A → B) (cutoff amount : Nat) (fields : Fields A) :
      mapFieldHeads change (Term.Fields.lift cutoff amount fields) =
        Term.Fields.lift cutoff amount (mapFieldHeads change fields) := by
    cases fields with
    | nil => rfl
    | cons depth term rest =>
        simp only [Term.Fields.lift, mapFieldHeads,
          mapHeads_lift change (cutoff + depth) amount term, mapFieldHeads_lift change cutoff amount rest]
end

theorem mapHeads_underBinders (change : A → B) (depth : Nat) (assignment : Nat → Term A) :
    (fun index => mapHeads change (underBinders depth assignment index)) =
      underBinders depth (fun index => mapHeads change (assignment index)) := by
  funext index
  simp only [underBinders_eq]
  split
  · rfl
  · exact mapHeads_lift change 0 depth (assignment (index - depth))

mutual
  theorem mapHeads_substitute (change : A → B) (assignment : Nat → Term A) (term : Term A) :
      mapHeads change (Term.substituteMany assignment term) =
        Term.substituteMany (fun index => mapHeads change (assignment index)) (mapHeads change term) := by
    cases term with
    | idx index => simp only [Term.substituteMany_idx, mapHeads]
    | node head fields =>
        simp only [substitute_node, mapHeads, mapFieldHeads_substitute change assignment fields]

  theorem mapFieldHeads_substitute (change : A → B) (assignment : Nat → Term A) (fields : Fields A) :
      mapFieldHeads change (substituteFields assignment fields) =
        substituteFields (fun index => mapHeads change (assignment index)) (mapFieldHeads change fields) := by
    cases fields with
    | nil => simp only [substitute_fields_nil, mapFieldHeads]
    | cons depth term rest =>
        simp only [substitute_fields_cons, mapFieldHeads,
          mapHeads_substitute change (underBinders depth assignment) term,
          mapHeads_underBinders, mapFieldHeads_substitute change assignment rest]
end

theorem mapHeads_argumentAt (change : A → B) (arguments : List (Term A)) (index : Nat) :
    mapHeads change (ScopedApplication.argumentAt arguments index) =
      ScopedApplication.argumentAt (arguments.map (mapHeads change)) index := by
  unfold ScopedApplication.argumentAt
  cases found : arguments[index]? <;> simp [List.getElem?_map, found, mapHeads]

theorem graft_mapHeads (change : A → B) (arity : Nat) (arguments : List (Term A)) (body : Term A) :
    ScopedApplication.graft arity (arguments.map (mapHeads change)) (mapHeads change body) =
      (ScopedApplication.graft arity arguments body).map (mapHeads change) := by
  simp only [ScopedApplication.graft, List.length_map, mapHeads_scope]
  split
  · simp only [Option.map_some, mapHeads_substitute]
    congr 1
    apply congrArg (fun assignment => Term.substituteMany assignment (mapHeads change body))
    funext index
    exact (mapHeads_argumentAt change arguments index).symm
  · rfl

#print axioms mapHeads_injective
#print axioms mapHeads_substitute
#print axioms graft_mapHeads

end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
