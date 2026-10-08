import Mettapedia.TypeTheory.ContextualModelTelescopes
import Mettapedia.TypeTheory.PresheafNativeStableRefinement

/-!
# Mixed semantic scopes for native predicates

Data binders extend by their actual native type. A predicate assumption
restricts the current presheaf to its satisfying subfunctor and preserves
the number of data variables. Every existing variable is reindexed along
the inclusion. Ordered argument checking traverses both kinds of binder;
it checks dependent sections and factors through the actual assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open DisplayedPresheafCwf NativeLocalTheoryTransformation NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

abbrev NativeModel (C : Type u) [Category.{u} C] := nativeLocalModel C

abbrev NativeValue (P : Cᵒᵖ ⥤ Type u) := Value (NativeModel C).toCwf P

/-- Factor an actual map through a satisfying subobject. -/
def assumptionMap {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ P)
    (satisfies : ∀ world value, substitution.app world value ∈ predicate.obj world) :
    Q ⟶ predicate.toFunctor where
  app world := TypeCat.ofHom fun value => ⟨substitution.app world value, satisfies world value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact substitution.naturality_apply arrow value

theorem assumptionMap_inclusion {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ P)
    (satisfies : ∀ world value, substitution.app world value ∈ predicate.obj world) :
    assumptionMap predicate substitution satisfies ≫ predicate.ι = substitution := by
  ext world value
  rfl

theorem assumptionMap_eta {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ predicate.toFunctor) :
    assumptionMap predicate (substitution ≫ predicate.ι)
      (fun world value => (substitution.app world value).property) = substitution := by
  ext world value
  rfl

/-- Checking assumptions is separate from checking the ordered data values. -/
noncomputable def assumptionMap? {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ P) : Option (Q ⟶ predicate.toFunctor) := by
  classical
  exact if satisfies : ∀ world value, substitution.app world value ∈ predicate.obj world then
    some (assumptionMap predicate substitution satisfies) else none

theorem assumptionMap?_eq_some_iff {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ P) (restricted : Q ⟶ predicate.toFunctor) :
    assumptionMap? predicate substitution = some restricted ↔
      restricted ≫ predicate.ι = substitution := by
  classical
  by_cases satisfies : ∀ world value, substitution.app world value ∈ predicate.obj world
  · rw [assumptionMap?, dif_pos satisfies, Option.some.injEq]
    constructor
    · intro equal
      exact equal ▸ assumptionMap_inclusion predicate substitution satisfies
    · intro equal
      ext world value
      apply Subtype.ext
      exact (ConcreteCategory.congr_hom (NatTrans.congr_app equal world) value).symm
  · rw [assumptionMap?, dif_neg satisfies]
    constructor
    · intro impossible
      cases impossible
    · intro equal
      apply False.elim
      apply satisfies
      intro world value
      have readout := ConcreteCategory.congr_hom (NatTrans.congr_app equal world) value
      exact readout ▸ (restricted.app world value).property

theorem assumptionMap?_supplied {P Q : Cᵒᵖ ⥤ Type u} (predicate : Subfunctor P)
    (substitution : Q ⟶ predicate.toFunctor) :
    assumptionMap? predicate (substitution ≫ predicate.ι) = some substitution :=
  (assumptionMap?_eq_some_iff _ _ _).2 rfl

/-- The index counts only data variables; assumption binders carry their
actual satisfying subobject without introducing a data variable. -/
inductive ScopeData (C : Type u) [Category.{u} C] :
    Nat → (Cᵒᵖ ⥤ Type u) → Type (u + 1) where
  | nil : ScopeData C 0 (NativeModel C).empty
  | snoc {n : Nat} {P : Cᵒᵖ ⥤ Type u} (previous : ScopeData C n P)
      (type : NativeType P) : ScopeData C (n + 1) ((NativeModel C).toCwf.ext P type)
  | assume {n : Nat} {P : Cᵒᵖ ⥤ Type u} (previous : ScopeData C n P)
      (predicate : Subfunctor P) : ScopeData C n predicate.toFunctor

abbrev Scope (C : Type u) [Category.{u} C] (n : Nat) :=
  Σ P : Cᵒᵖ ⥤ Type u, ScopeData C n P

namespace Scope

abbrev nil (C : Type u) [Category.{u} C] : Scope C 0 := ⟨(NativeModel C).empty, .nil⟩

abbrev snoc {n : Nat} (scope : Scope C n) (type : NativeType scope.1) : Scope C (n + 1) :=
  ⟨(NativeModel C).toCwf.ext scope.1 type, .snoc scope.2 type⟩

abbrev assume {n : Nat} (scope : Scope C n) (predicate : Subfunctor scope.1) : Scope C n :=
  ⟨predicate.toFunctor, .assume scope.2 predicate⟩

end Scope

namespace ScopeData

variable {n : Nat} {P Q R : Cᵒᵖ ⥤ Type u}

/-- Assumption restriction reindexes every previously introduced section. -/
def lookup : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} → ScopeData C n P → Fin n → NativeValue P
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .snoc previous type, index =>
      Fin.cases ⟨(NativeModel C).toCwf.tySub type ((NativeModel C).toCwf.wk type),
        (NativeModel C).toCwf.vz type⟩
        (fun older => (lookup previous older).substitute ((NativeModel C).toCwf.wk type)) index
  | _, _, .assume previous predicate, index =>
      (lookup previous index).substitute predicate.ι

@[simp] theorem lookup_zero (previous : ScopeData C n P) (type : NativeType P) :
    lookup (.snoc previous type) 0 =
      ⟨(NativeModel C).toCwf.tySub type ((NativeModel C).toCwf.wk type),
        (NativeModel C).toCwf.vz type⟩ := rfl

@[simp] theorem lookup_succ (previous : ScopeData C n P) (type : NativeType P)
    (index : Fin n) : lookup (.snoc previous type) index.succ =
      (lookup previous index).substitute ((NativeModel C).toCwf.wk type) := rfl

@[simp] theorem lookup_assume (previous : ScopeData C n P) (predicate : Subfunctor P)
    (index : Fin n) : lookup (.assume previous predicate) index =
      (lookup previous index).substitute predicate.ι := rfl

def components (scope : ScopeData C n P) (substitution : Q ⟶ P) : Fin n → NativeValue Q :=
  fun index => (scope.lookup index).substitute substitution

theorem components_composition (scope : ScopeData C n P) (substitution : Q ⟶ P)
    (earlier : R ⟶ Q) (index : Fin n) :
    components scope (earlier ≫ substitution) index =
      (components scope substitution index).substitute earlier :=
  Value.substitute_composition (K := (NativeModel C).toCwf) _ substitution earlier

@[simp] theorem components_succ (previous : ScopeData C n P) (type : NativeType P)
    (substitution : Q ⟶ (NativeModel C).toCwf.ext P type) (index : Fin n) :
    components (.snoc previous type) substitution index.succ =
      components previous (substitution ≫ (NativeModel C).toCwf.wk type) index :=
  (Value.substitute_composition _ _ _).symm

@[simp] theorem components_assume (previous : ScopeData C n P) (predicate : Subfunctor P)
    (substitution : Q ⟶ predicate.toFunctor) (index : Fin n) :
    components (.assume previous predicate) substitution index =
      components previous (substitution ≫ predicate.ι) index :=
  (Value.substitute_composition _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem components_pair_zero (previous : ScopeData C n P) (type : NativeType P)
    (substitution : Q ⟶ P)
    (term : (NativeModel C).toCwf.Tm Q ((NativeModel C).toCwf.tySub type substitution)) :
    components (.snoc previous type) ((NativeModel C).toCwf.pair substitution type term) 0 =
      ⟨(NativeModel C).toCwf.tySub type substitution, term⟩ := by
  apply Sigma.ext
  · change (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub type
        ((NativeModel C).toCwf.wk type)) ((NativeModel C).toCwf.pair substitution type term) = _
    rw [← (NativeModel C).toCwf.tySub_comp, (NativeModel C).toCwf.wk_pair]
  · exact (heq_of_eq ((NativeModel C).toCwf.vz_pair substitution type term)).trans (cast_heq _ _)

set_option backward.isDefEq.respectTransparency false in
theorem components_pair_succ (previous : ScopeData C n P) (type : NativeType P)
    (substitution : Q ⟶ P)
    (term : (NativeModel C).toCwf.Tm Q ((NativeModel C).toCwf.tySub type substitution))
    (index : Fin n) :
    components (.snoc previous type) ((NativeModel C).toCwf.pair substitution type term) index.succ =
      components previous substitution index := by
  rw [components_succ]
  exact congrArg (fun arrow => components previous arrow index)
    ((NativeModel C).toCwf.wk_pair substitution type term)

/-- The actual predicate assumption is checked even though it has no data
position. Successful data checks alone do not discard this obligation. -/
noncomputable def assemble? : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} → ScopeData C n P →
    (Fin n → Option (NativeValue Q)) → Option (Q ⟶ P)
  | _, _, .nil, _ => some ((NativeModel C).toEmpty Q)
  | _, _, .snoc previous type, supplied =>
      match assemble? previous (fun index => supplied index.succ) with
      | none => none
      | some older =>
          match supplied 0 with
          | none => none
          | some value =>
              match value.atType? ((NativeModel C).toCwf.tySub type older) with
              | none => none
              | some term => some ((NativeModel C).toCwf.pair older type term)
  | _, _, .assume previous predicate, supplied =>
      match assemble? previous supplied with
      | none => none
      | some older => assumptionMap? predicate older

set_option backward.isDefEq.respectTransparency false in
theorem assemble?_components : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    (scope : ScopeData C n P) → (substitution : Q ⟶ P) →
    assemble? scope (fun index => some (components scope substitution index)) = some substitution
  | _, _, .nil, substitution => by
      exact congrArg some ((NativeModel C).toEmpty_unique Q substitution).symm
  | _, _, .snoc previous type, substitution => by
      have earlier := assemble?_components previous (substitution ≫ (NativeModel C).toCwf.wk type)
      have inputs :
          (fun index => some (components (.snoc previous type) substitution index.succ)) =
            (fun index => some (components previous
              (substitution ≫ (NativeModel C).toCwf.wk type) index)) := by
        funext index
        rw [components_succ]
      rw [assemble?, inputs, earlier]
      simp only [components, lookup_zero, Value.substitute]
      have equal : (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub type
          ((NativeModel C).toCwf.wk type)) substitution =
        (NativeModel C).toCwf.tySub type (substitution ≫ (NativeModel C).toCwf.wk type) :=
        ((NativeModel C).toCwf.tySub_comp _ _ _).symm
      rw [Value.atType?_cast _ _ equal]
      exact congrArg some ((NativeModel C).toCwf.pair_eta type substitution)
  | _, _, .assume previous predicate, substitution => by
      have inputs :
          (fun index => some (components (.assume previous predicate) substitution index)) =
            (fun index => some (components previous (substitution ≫ predicate.ι) index)) := by
        funext index
        rw [components_assume]
      rw [assemble?, inputs, assemble?_components previous (substitution ≫ predicate.ι)]
      exact assumptionMap?_supplied predicate substitution

set_option backward.isDefEq.respectTransparency false in
theorem assemble?_sound : {n : Nat} → {P : Cᵒᵖ ⥤ Type u} →
    (scope : ScopeData C n P) → (supplied : Fin n → Option (NativeValue Q)) →
    (substitution : Q ⟶ P) → assemble? scope supplied = some substitution →
    ∀ index, supplied index = some (components scope substitution index)
  | _, _, .nil, _, _, _, index => Fin.elim0 index
  | _, _, .snoc previous type, supplied, substitution, assembled, index => by
      cases earlier : assemble? previous (fun index => supplied index.succ) with
      | none => simp [assemble?, earlier] at assembled
      | some older =>
          cases newest : supplied 0 with
          | none => simp [assemble?, earlier, newest] at assembled
          | some value =>
              cases checked : value.atType? ((NativeModel C).toCwf.tySub type older) with
              | none => simp [assemble?, earlier, newest, checked] at assembled
              | some term =>
                  have same : (NativeModel C).toCwf.pair older type term = substitution := by
                    have sameSome : some ((NativeModel C).toCwf.pair older type term) =
                        some substitution := by
                      simpa only [assemble?, earlier, newest, checked] using assembled
                    exact Option.some.inj sameSome
                  subst substitution
                  cases index using Fin.cases with
                  | zero =>
                      rw [components_pair_zero, newest]
                      exact congrArg some ((Value.atType?_eq_some_iff _ _ _).1 checked)
                  | succ olderIndex =>
                      rw [components_pair_succ]
                      exact assemble?_sound previous _ older earlier olderIndex
  | _, _, .assume previous predicate, supplied, substitution, assembled, index => by
      cases earlier : assemble? previous supplied with
      | none => simp [assemble?, earlier] at assembled
      | some older =>
          have restricted : assumptionMap? predicate older = some substitution := by
            simpa only [assemble?, earlier] using assembled
          have projection := (assumptionMap?_eq_some_iff _ _ _).1 restricted
          rw [components_assume, projection]
          exact assemble?_sound previous supplied older earlier index

theorem assemble?_eq_some_iff (scope : ScopeData C n P)
    (supplied : Fin n → Option (NativeValue Q)) (substitution : Q ⟶ P) :
    assemble? scope supplied = some substitution ↔
      ∀ index, supplied index = some (components scope substitution index) := by
  constructor
  · exact assemble?_sound scope supplied substitution
  · intro all
    rw [funext all]
    exact assemble?_components scope substitution

theorem assemble?_substitution (scope : ScopeData C n P)
    (supplied : Fin n → Option (NativeValue Q)) (substitution : Q ⟶ P)
    (assembled : assemble? scope supplied = some substitution) (earlier : R ⟶ Q) :
    assemble? scope (fun index => (supplied index).map (fun value => value.substitute earlier)) =
      some (earlier ≫ substitution) := by
  apply (assemble?_eq_some_iff _ _ _).2
  intro index
  rw [assemble?_sound scope supplied substitution assembled index, Option.map_some,
    components_composition]

theorem components_injective (scope : ScopeData C n P) :
    Function.Injective (components (Q := Q) scope) := by
  intro first second equal
  have checked := congrArg (fun supplied => assemble? scope (fun index => some (supplied index))) equal
  rw [assemble?_components, assemble?_components] at checked
  exact Option.some.inj checked

end ScopeData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
