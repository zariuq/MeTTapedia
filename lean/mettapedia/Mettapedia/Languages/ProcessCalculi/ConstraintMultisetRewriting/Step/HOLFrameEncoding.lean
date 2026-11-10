import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames
import Mettapedia.Logic.HOL.IndexedCarrier

/-! # Indexed frame data in inhabited HOL carrier types

Terms and morphisms are tagged by their actual frame indices. The invalid
sentinel supplies the raw carrier's inhabitant without filling any valid
fibre. Operations are total on raw carriers and agree with the indexed
operations on valid data. This constructs model data; interpretation of the
loaded HOL defining terms is a separate connection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameEncoding

open Mettapedia.Logic.HOL

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

abbrev Objects (Obj : Type uO) := Option Obj
abbrev Terms (Tm : Obj → Type uT) := IndexedCarrier.Raw Tm
abbrev Morphisms (Hom : Obj → Obj → Type uH) := IndexedCarrier.Raw (fun pair : Obj × Obj => Hom pair.1 pair.2)

def encodeTerm {a : Obj} (term : Tm a) : Terms Tm := IndexedCarrier.encode Tm term
def encodeHom {a b : Obj} (map : Hom a b) : Morphisms Hom := IndexedCarrier.encode _ (index := (a, b)) map

def objects : Objects Obj → Prop
  | none => False
  | some _ => True

def terms : Objects Obj → Terms Tm → Prop
  | none, _ => False
  | some a, raw => IndexedCarrier.Valid Tm a raw

def hom : Objects Obj → Objects Obj → Morphisms Hom → Prop
  | some a, some b, raw => IndexedCarrier.Valid (fun pair : Obj × Obj => Hom pair.1 pair.2) (a, b) raw
  | _, _, _ => False

variable (X : Frames Tm Hom)

noncomputable def act (map : Morphisms Hom) (term : Terms Tm) : Terms Tm :=
  match map with
  | none => none
  | some ⟨(a, _b), value⟩ => (IndexedCarrier.decode Tm a term).bind (fun input => encodeTerm (X.act value input))

def identity : Objects Obj → Morphisms Hom
  | none => none
  | some a => encodeHom (X.id a)

noncomputable def comp (second first : Morphisms Hom) : Morphisms Hom := by
  classical
  exact match first, second with
    | some ⟨(a, b), first⟩, some ⟨(c, d), second⟩ =>
        if same : b = c then
          let compatible : Hom b d := same.symm ▸ second
          encodeHom (X.comp compatible first)
        else none
    | _, _ => none

def equal : Objects Obj → Terms Tm → Terms Tm → Prop
  | none, _, _ => False
  | some a, first, second => ∃ (x y : Tm a), first = encodeTerm x ∧ second = encodeTerm y ∧ X.E x y

@[simp] theorem act_encoded {a b : Obj} (map : Hom a b) (term : Tm a) :
    act X (encodeHom map) (encodeTerm term) = encodeTerm (X.act map term) := by
  simp [act, encodeHom, encodeTerm, IndexedCarrier.encode, IndexedCarrier.decode]

@[simp] theorem identity_encoded (a : Obj) : identity X (some a) = encodeHom (X.id a) := rfl

@[simp] theorem comp_encoded {a b c : Obj} (second : Hom b c) (first : Hom a b) :
    comp X (encodeHom second) (encodeHom first) = encodeHom (X.comp second first) := by
  simp [comp, encodeHom, IndexedCarrier.encode]

theorem terms_encoded {a : Obj} (term : Tm a) : terms (some a) (encodeTerm term) := ⟨term, rfl⟩
theorem hom_encoded {a b : Obj} (map : Hom a b) : hom (some a) (some b) (encodeHom map) := ⟨map, rfl⟩

theorem equal_encoded {a : Obj} (first second : Tm a) :
    equal X (some a) (encodeTerm first) (encodeTerm second) ↔ X.E first second := by
  constructor
  · rintro ⟨x, y, firstEq, secondEq, related⟩
    have hx := IndexedCarrier.encode_injective Tm a firstEq
    have hy := IndexedCarrier.encode_injective Tm a secondEq
    simpa only [hx, hy] using related
  · intro related
    exact ⟨first, second, rfl, rfl, related⟩

theorem act_identity {a : Obj} (term : Tm a) :
    act X (identity X (some a)) (encodeTerm term) = encodeTerm term := by
  rw [identity_encoded, act_encoded, X.act_id]

theorem act_composition {a b c : Obj} (second : Hom b c) (first : Hom a b) (term : Tm a) :
    act X (comp X (encodeHom second) (encodeHom first)) (encodeTerm term) =
      act X (encodeHom second) (act X (encodeHom first) (encodeTerm term)) := by
  rw [comp_encoded, act_encoded, act_encoded, act_encoded, X.act_comp]

theorem action_preserves {a b : Obj} (map : Hom a b) {first second : Tm a}
    (related : equal X (some a) (encodeTerm first) (encodeTerm second)) :
    equal X (some b) (act X (encodeHom map) (encodeTerm first))
      (act X (encodeHom map) (encodeTerm second)) := by
  rw [act_encoded, act_encoded, equal_encoded]
  exact X.preserves map ((equal_encoded X first second).mp related)

/-- A finite store is represented by membership, not by an assumption that
every HOL predicate is an executable finite store. -/
def store {a : Obj} (equations : EquationStore (Tm a)) : Terms Tm → Terms Tm → Prop :=
  fun first second => ∃ equation ∈ equations, first = encodeTerm equation.1 ∧ second = encodeTerm equation.2

def models (a b : Objects Obj) (map : Morphisms Hom) (equations : Terms Tm → Terms Tm → Prop) : Prop :=
  hom a b map ∧ ∀ first second, equations first second → equal X b (act X map first) (act X map second)

theorem store_typed {a : Obj} (equations : EquationStore (Tm a)) {first second : Terms Tm}
    (member : store equations first second) : terms (some a) first ∧ terms (some a) second := by
  obtain ⟨equation, _, rfl, rfl⟩ := member
  exact ⟨terms_encoded _, terms_encoded _⟩

theorem models_encoded {a b : Obj} (map : Hom a b) (equations : EquationStore (Tm a)) :
    models X (some a) (some b) (encodeHom map) (store equations) ↔ X.Models map equations := by
  constructor
  · rintro ⟨_, modeled⟩ equation member
    have related := modeled (encodeTerm equation.1) (encodeTerm equation.2) ⟨equation, member, rfl, rfl⟩
    rw [act_encoded, act_encoded, equal_encoded] at related
    exact related
  · intro modeled
    refine ⟨hom_encoded map, ?_⟩
    rintro first second ⟨equation, member, rfl, rfl⟩
    rw [act_encoded, act_encoded, equal_encoded]
    exact modeled equation member

def solvable (a : Objects Obj) (equations : Terms Tm → Terms Tm → Prop) : Prop :=
  ∃ (b : Objects Obj) (map : Morphisms Hom), models X a b map equations

theorem solvable_encoded {a : Obj} (equations : EquationStore (Tm a)) :
    solvable X (some a) (store equations) ↔ X.Solvable equations := by
  constructor
  · rintro ⟨target, raw, valid, solves⟩
    cases target with
    | none => cases valid
    | some target =>
        obtain ⟨map, same⟩ := valid
        change raw = encodeHom map at same
        subst raw
        exact ⟨target, map, (models_encoded X map equations).mp ⟨hom_encoded map, solves⟩⟩
  · rintro ⟨target, map, solves⟩
    exact ⟨some target, encodeHom map, (models_encoded X map equations).mpr solves⟩

theorem empty_fibre_stays_empty (a : Obj) [IsEmpty (Tm a)] (raw : Terms Tm) :
    ¬terms (some a) raw := IndexedCarrier.empty_fibre_invalid Tm a raw

theorem invalid_object_has_no_hom (raw : Objects Obj) (map : Morphisms Hom) :
    ¬hom raw none map := by cases raw <;> simp [hom]

theorem terms_object {a : Objects Obj} {raw : Terms Tm} (valid : terms a raw) : objects a := by
  cases a with
  | none => exact valid
  | some _ => trivial

theorem hom_objects {a b : Objects Obj} {raw : Morphisms Hom} (valid : hom a b raw) :
    objects a ∧ objects b := by
  cases a <;> cases b <;> simp_all [hom, objects]

theorem identity_valid {a : Objects Obj} (valid : objects a) : hom a a (identity X a) := by
  cases a with
  | none => exact valid
  | some a => exact hom_encoded (X.id a)

theorem act_valid {a b : Objects Obj} {map : Morphisms Hom} {term : Terms Tm}
    (mapValid : hom a b map) (termValid : terms a term) : terms b (act X map term) := by
  cases a with
  | none => cases termValid
  | some a =>
      cases b with
      | none => cases mapValid
      | some b =>
          obtain ⟨typedMap, rfl⟩ := mapValid
          obtain ⟨typedTerm, rfl⟩ := termValid
          change terms (some b) (act X (encodeHom (a := a) (b := b) typedMap) (encodeTerm typedTerm))
          rw [act_encoded]
          exact terms_encoded _

theorem comp_valid {a b c : Objects Obj} {first second : Morphisms Hom}
    (firstValid : hom a b first) (secondValid : hom b c second) : hom a c (comp X second first) := by
  cases a <;> cases b <;> cases c
  all_goals try exact False.elim firstValid
  all_goals try exact False.elim secondValid
  obtain ⟨typedFirst, rfl⟩ := firstValid
  obtain ⟨typedSecond, rfl⟩ := secondValid
  change hom _ _ (comp X (encodeHom typedSecond) (encodeHom typedFirst))
  rw [comp_encoded]
  exact hom_encoded _

theorem act_identity_valid {a : Objects Obj} {raw : Terms Tm} (valid : terms a raw) :
    act X (identity X a) raw = raw := by
  cases a with
  | none => cases valid
  | some a =>
      obtain ⟨term, rfl⟩ := valid
      exact act_identity X term

theorem act_composition_valid {a b c : Objects Obj} {first second : Morphisms Hom} {raw : Terms Tm}
    (firstValid : hom a b first) (secondValid : hom b c second) (termValid : terms a raw) :
    act X (comp X second first) raw = act X second (act X first raw) := by
  cases a <;> cases b <;> cases c
  all_goals try exact False.elim firstValid
  all_goals try exact False.elim secondValid
  obtain ⟨typedFirst, rfl⟩ := firstValid
  obtain ⟨typedSecond, rfl⟩ := secondValid
  obtain ⟨term, rfl⟩ := termValid
  exact act_composition X typedSecond typedFirst term

theorem equal_reflexive_valid {a : Objects Obj} {raw : Terms Tm} (valid : terms a raw) :
    equal X a raw raw := by
  cases a with
  | none => cases valid
  | some a =>
      obtain ⟨term, rfl⟩ := valid
      exact ⟨term, term, rfl, rfl, (X.equivalence a).refl term⟩

theorem equal_symmetric {a : Objects Obj} {first second : Terms Tm}
    (related : equal X a first second) : equal X a second first := by
  cases a with
  | none => cases related
  | some a =>
      obtain ⟨x, y, rfl, rfl, relation⟩ := related
      exact ⟨y, x, rfl, rfl, (X.equivalence a).symm relation⟩

theorem equal_transitive {a : Objects Obj} {first middle last : Terms Tm}
    (earlier : equal X a first middle) (later : equal X a middle last) : equal X a first last := by
  cases a with
  | none => cases earlier
  | some a =>
      obtain ⟨x, y, rfl, rfl, xy⟩ := earlier
      obtain ⟨y', z, same, rfl, yz⟩ := later
      have sameValue := IndexedCarrier.encode_injective Tm a same
      subst y'
      exact ⟨x, z, rfl, rfl, (X.equivalence a).trans xy yz⟩

theorem action_preserves_valid {a b : Objects Obj} {map : Morphisms Hom} {first second : Terms Tm}
    (mapValid : hom a b map) (related : equal X a first second) :
    equal X b (act X map first) (act X map second) := by
  cases a <;> cases b
  all_goals try exact False.elim mapValid
  obtain ⟨typedMap, rfl⟩ := mapValid
  obtain ⟨x, y, rfl, rfl, relation⟩ := related
  exact action_preserves X typedMap ((equal_encoded X x y).mpr relation)

theorem morphism_identity_retained (a b : Obj) :
    Function.Injective (encodeHom (Hom := Hom) (a := a) (b := b)) :=
  IndexedCarrier.encode_injective (fun pair : Obj × Obj => Hom pair.1 pair.2) (a, b)

def guard {a : Obj} (holds : (b : Obj) → Hom a b → Prop) : Objects Obj → Morphisms Hom → Prop
  | none, _ => False
  | some b, raw => ∃ map : Hom a b, raw = encodeHom map ∧ holds b map

theorem guard_encoded {a b : Obj} (holds : (target : Obj) → Hom a target → Prop) (map : Hom a b) :
    guard holds (some b) (encodeHom map) ↔ holds b map := by
  constructor
  · rintro ⟨typed, same, valid⟩
    have equalMap := IndexedCarrier.encode_injective (fun pair : Obj × Obj => Hom pair.1 pair.2) (a, b) same
    simpa only [equalMap] using valid
  · intro valid
    exact ⟨map, rfl, valid⟩

def entails (a : Objects Obj) (equations : Terms Tm → Terms Tm → Prop)
    (holds : Objects Obj → Morphisms Hom → Prop) : Prop :=
  ∀ b map, models X a b map equations → holds b map

theorem entails_encoded {a : Obj} (equations : EquationStore (Tm a))
    (holds : (b : Obj) → Hom a b → Prop) :
    entails X (some a) (store equations) (guard holds) ↔ X.Entails equations holds := by
  constructor
  · intro all target map solves
    exact (guard_encoded holds map).mp
      (all (some target) (encodeHom map) ((models_encoded X map equations).mpr solves))
  · rintro all target raw ⟨valid, solves⟩
    cases target with
    | none => cases valid
    | some target =>
        obtain ⟨map, same⟩ := valid
        change raw = encodeHom map at same
        subst raw
        exact (guard_encoded holds map).mpr
          (all target map ((models_encoded X map equations).mp ⟨hom_encoded map, solves⟩))

def mapStore (map : Morphisms Hom) (equations : Terms Tm → Terms Tm → Prop) : Terms Tm → Terms Tm → Prop :=
  fun first second => ∃ x y, equations x y ∧ first = act X map x ∧ second = act X map y

theorem mapped_store_encoded {a b : Obj} (map : Hom a b) (equations : EquationStore (Tm a)) :
    mapStore X (encodeHom map) (store equations) = store (X.applyStore map equations) := by
  funext first second
  apply propext
  constructor
  · rintro ⟨x, y, ⟨equation, member, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨(X.act map equation.1, X.act map equation.2), List.mem_map.mpr ⟨equation, member, rfl⟩,
      act_encoded X map equation.1, act_encoded X map equation.2⟩
  · rintro ⟨equation, member, rfl, rfl⟩
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact ⟨encodeTerm source.1, encodeTerm source.2, ⟨source, present, rfl, rfl⟩,
      (act_encoded X map source.1).symm, (act_encoded X map source.2).symm⟩

#print axioms models_encoded
#print axioms solvable_encoded
#print axioms empty_fibre_stays_empty
#print axioms entails_encoded
#print axioms mapped_store_encoded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameEncoding
