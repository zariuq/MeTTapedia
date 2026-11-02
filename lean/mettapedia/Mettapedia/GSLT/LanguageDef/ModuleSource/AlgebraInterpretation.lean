import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtraction
import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTyping
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch

/-!
# Reading binary source equations in a collection-fold model

The interpretation below covers first-order constructor equations. It refuses
binders, explicit substitution and collection patterns; it is the source-side
interpretation of a binary operation before its collection replacement.
Its equations quantify over variable assignments independently of the
syntactic recognizers used by admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u
variable {A : Type u}

def read? (operations : String → List A → A) (assignment : String → A) : Pattern → Option A
  | .fvar name => some (assignment name)
  | .apply label arguments =>
      (arguments.mapM (read? operations assignment)).map (operations label)
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

def EquationHolds (operations : String → List A → A) (left right : Pattern) : Prop :=
  ∀ assignment, ∃ value,
    read? operations assignment left = some value ∧ read? operations assignment right = some value

theorem EquationHolds.symm {operations : String → List A → A} {left right : Pattern}
    (holds : EquationHolds operations left right) : EquationHolds operations right left := by
  intro assignment
  obtain ⟨value, first, second⟩ := holds assignment
  exact ⟨value, second, first⟩

theorem EquationHolds.equal {operations : String → List A → A} {left right : Pattern}
    (holds : EquationHolds operations left right) (assignment : String → A) :
    read? operations assignment left = read? operations assignment right := by
  obtain ⟨value, first, second⟩ := holds assignment
  exact first.trans second.symm

theorem binary_associativity_shape {op : String} {left right : Pattern}
    (checked : statesBinaryAssociative op left right = true) :
    ∃ x y z, [x, y, z].Nodup ∧
      left = .apply op [.apply op [.fvar x, .fvar y], .fvar z] ∧
      right = .apply op [.fvar x, .apply op [.fvar y, .fvar z]] := by
  unfold statesBinaryAssociative at checked
  split at checked
  next a b x y z c x' d y' z' =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
    obtain ⟨⟨⟨⟨⟨⟨⟨aEq, bEq⟩, cEq⟩, dEq⟩, xEq⟩, yEq⟩, zEq⟩, distinct⟩ := checked
    subst a; subst b; subst c; subst d; subst x'; subst y'; subst z'
    exact ⟨x, y, z, distinct, rfl, rfl⟩
  next => contradiction

theorem binary_associativity_sound (operations : String → List A → A)
    {op : String} {left right : Pattern}
    (checked : statesBinaryAssociative op left right = true)
    (holds : EquationHolds operations left right) :
    ∀ first second third : A,
      operations op [operations op [first, second], third] =
        operations op [first, operations op [second, third]] := by
  obtain ⟨x, y, z, distinct, rfl, rfl⟩ := binary_associativity_shape checked
  intro first second third
  have xy : x ≠ y := by simpa using (List.pairwise_cons.mp distinct).1 y (by simp)
  have xz : x ≠ z := by simpa using (List.pairwise_cons.mp distinct).1 z (by simp)
  have yz : y ≠ z := by
    exact (List.pairwise_cons.mp (List.pairwise_cons.mp distinct).2).1 z (by simp)
  let assignment : String → A := fun name => if name = x then first else if name = y then second else third
  have result := holds.equal assignment
  simpa [read?, assignment, Ne.symm xy, Ne.symm xz, Ne.symm yz] using result

theorem binary_unit_shape {op unit : String} {left right : Pattern} {onLeft : Bool}
    (checked : binaryUnit op left right = some (unit, onLeft)) :
    ∃ name, right = .fvar name ∧
      left = .apply op (if onLeft then [.apply unit [], .fvar name]
        else [.fvar name, .apply unit []]) := by
  unfold binaryUnit at checked
  split at checked
  next head name actual name' =>
    split at checked
    next condition =>
      have parts : head = op ∧ name = name' := by simpa using condition
      cases Option.some.inj checked
      rcases parts with ⟨rfl, rfl⟩
      exact ⟨_, rfl, rfl⟩
    next => cases checked
  next head actual name name' =>
    split at checked
    next condition =>
      have parts : head = op ∧ name = name' := by simpa using condition
      cases Option.some.inj checked
      rcases parts with ⟨rfl, rfl⟩
      exact ⟨_, rfl, rfl⟩
    next => cases checked
  next => cases checked

theorem binary_unit_sound (operations : String → List A → A)
    {op unit : String} {left right : Pattern} {onLeft : Bool}
    (checked : binaryUnit op left right = some (unit, onLeft))
    (holds : EquationHolds operations left right) (value : A) :
    operations op (if onLeft then [operations unit [], value]
      else [value, operations unit []]) = value := by
  obtain ⟨name, rfl, rfl⟩ := binary_unit_shape checked
  have result := holds.equal (fun _ => value)
  cases onLeft <;> simpa [read?] using result

theorem binary_commutativity_sound (operations : String → List A → A)
    {op : String} {left right : Pattern}
    (checked : statesCommutative op left right = true)
    (holds : EquationHolds operations left right) :
    ∀ first second : A, operations op [first, second] = operations op [second, first] := by
  unfold statesCommutative at checked
  split at checked
  next a x y b y' x' =>
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at checked
    obtain ⟨⟨⟨⟨aEq, bEq⟩, different⟩, xEq⟩, yEq⟩ := checked
    subst a; subst b; subst x'; subst y'
    intro first second
    have result := holds.equal (fun name => if name = x then first else second)
    simpa [read?, Ne.symm different] using result
  next => contradiction

theorem binary_idempotence_sound (operations : String → List A → A)
    {op : String} {left right : Pattern}
    (checked : statesIdempotent op left right = true)
    (holds : EquationHolds operations left right) :
    ∀ element : A, operations op [element, element] = element := by
  unfold statesIdempotent at checked
  split at checked
  next head name name' name'' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := checked
    intro element
    simpa [read?] using holds.equal (fun _ => element)
  next => contradiction

/-- Satisfaction is of actual premise-free source rows, before extraction.
The first-order interpretation supplies no claims about scoped equations. -/
def SourceEquationsHold (operations : String → List A → A) (value : Value) : Prop :=
  ∀ item ∈ value.entries, ∀ row, item.body = .equation row → row.premises = [] →
    EquationHolds operations row.left row.right

theorem recognized_equation {operations : String → List A → A} {value : Value}
    (holds : SourceEquationsHold operations value)
    {law : String → Pattern → Pattern → Bool} {op : String}
    (checked : holdsOf value law op = true) :
    ∃ left right, law op left right = true ∧ EquationHolds operations left right := by
  obtain ⟨item, member, checked⟩ := List.any_eq_true.mp checked
  cases body : item.body <;> simp only [body] at checked
  all_goals try contradiction
  rename_i row
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at checked
  have semantic := holds item member row body checked.1
  rcases checked.2 with forward | backward
  · exact ⟨row.left, row.right, forward, semantic⟩
  · exact ⟨row.right, row.left, backward, semantic.symm⟩

theorem binaryUnits_sound {operations : String → List A → A} {value : Value} {op : String}
    (holds : SourceEquationsHold operations value)
    {unit : String} {onLeft : Bool} (member : (unit, onLeft) ∈ binaryUnits value op)
    (element : A) :
    operations op (if onLeft then [operations unit [], element]
      else [element, operations unit []]) = element := by
  obtain ⟨item, itemMember, member⟩ := List.mem_flatMap.mp member
  cases body : item.body <;> simp only [body] at member
  all_goals try contradiction
  rename_i row
  split at member
  next unconditional =>
    have semantic := holds item itemMember row body (List.isEmpty_iff.mp unconditional)
    rcases List.mem_append.mp member with forward | backward
    · exact binary_unit_sound operations (by simpa using forward) semantic element
    · exact binary_unit_sound operations (by simpa using backward) semantic.symm element
  next => contradiction

/-- The computed basis supplies an actual monoid in every model of the
selected source equations. No monoid laws are assumed by this theorem. -/
theorem binaryFoldReady_model {operations : String → List A → A} {value : Value} {op : String}
    (holds : SourceEquationsHold operations value) (checked : binaryFoldReady value op = true) :
    ∃ unit : String, ∃ algebra : Monoid A,
      algebra.one = operations unit [] ∧
      ∀ first second, algebra.mul first second = operations op [first, second] := by
  simp only [binaryFoldReady, Bool.and_eq_true] at checked
  obtain ⟨left, right, assocSyntax, assocMeaning⟩ := recognized_equation holds checked.1
  have associative := binary_associativity_sound operations assocSyntax assocMeaning
  obtain ⟨⟨unit, side⟩, unitMember, other⟩ := List.any_eq_true.mp checked.2
  have localUnit := binaryUnits_sound holds unitMember
  have laws : (∀ element, operations op [operations unit [], element] = element) ∧
      (∀ element, operations op [element, operations unit []] = element) := by
    obtain ⟨⟨otherUnit, otherSide⟩, otherMember, accepted⟩ := List.any_eq_true.mp other
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at accepted
    rcases accepted with ⟨same, different⟩ | commutative
    · subst otherUnit
      have oppositeUnit := binaryUnits_sound holds otherMember
      cases side <;> cases otherSide <;> simp_all
    · obtain ⟨commLeft, commRight, commSyntax, commMeaning⟩ := recognized_equation holds commutative
      have commutes := binary_commutativity_sound operations commSyntax commMeaning
      cases side
      · exact ⟨fun element => (commutes _ _).trans (localUnit element), localUnit⟩
      · exact ⟨localUnit, fun element => (commutes _ _).trans (localUnit element)⟩
  let algebra : Monoid A :=
    { one := operations unit [], mul := fun first second => operations op [first, second],
      mul_assoc := associative, one_mul := laws.1, mul_one := laws.2 }
  exact ⟨unit, algebra, rfl, fun _ _ => rfl⟩

/-- Source equations construct the whole variadic interpretation, including
the quotient laws for the selected collection kind. No fold or quotient
preservation law is provided as an assumption. -/
theorem collection_fold_model {operations : String → List A → A}
    {value : Value} {op : String} (kind : CollType)
    (holds : SourceEquationsHold operations value)
    (ready : binaryFoldReady value op = true)
    (commutative : kind ≠ .vec → holdsOf value statesCommutative op = true)
    (idempotent : kind = .hashSet → holdsOf value statesIdempotent op = true) :
    ∃ unit : String, ∃ fold : Mettapedia.Algebra.CollectionFold.Model A,
      fold.fold [] = operations unit [] ∧
      (∀ first second, fold.fold [first, second] = operations op [first, second]) ∧
      (kind ≠ .vec → fold.PermutationInvariant) ∧
      (kind = .hashSet → fold.MembershipInvariant) := by
  obtain ⟨unit, algebra, empty, binary⟩ := binaryFoldReady_model holds ready
  let _ := algebra
  let fold := Mettapedia.Algebra.CollectionFold.ofMonoid (A := A)
  have onBinary (first second : A) :
      fold.fold [first, second] = operations op [first, second] := by
    exact (Mettapedia.Algebra.CollectionFold.ofMonoid_binary first second).trans (binary first second)
  have onPermutation (unordered : kind ≠ .vec) : fold.PermutationInvariant := by
    apply fold.permutationInvariant_iff.mpr
    obtain ⟨left, right, checked, interpreted⟩ := recognized_equation holds (commutative unordered)
    intro first second
    rw [onBinary, onBinary]
    exact binary_commutativity_sound operations checked interpreted first second
  refine ⟨unit, fold, empty, onBinary, onPermutation, ?_⟩
  intro isSet
  apply fold.membershipInvariant_iff.mpr
  refine ⟨onPermutation (by simp [isSet]), ?_⟩
  obtain ⟨left, right, checked, interpreted⟩ := recognized_equation holds (idempotent isSet)
  intro element
  rw [onBinary]
  exact binary_idempotence_sound operations checked interpreted element

theorem checkFaithful_collection_basis {value : Value} {old new : GrammarRule}
    {name : String} {kind : CollType} {element : TypeExpr}
    (source : collectionParameterKind old = none)
    (target : new.params = [.simple name (.collection kind element)])
    (accepted : checkFaithful value old new = .ok ()) :
    old.params.length = 2 ∧ binaryFoldReady value old.label = true ∧
      (kind ≠ .vec → holdsOf value statesCommutative old.label = true) ∧
      (kind = .hashSet → holdsOf value statesIdempotent old.label = true) := by
  have targetKind : collectionParameterKind new = some kind := by
    simp [collectionParameterKind, target]
  unfold checkFaithful at accepted
  simp only [source, targetKind, target, Option.isSome_some, Option.isNone_none,
    Bool.and_self, ↓reduceIte] at accepted
  split_ifs at accepted <;>
    simp_all [bind, Except.bind, pure, Except.pure, Bool.and_eq_true, Bool.or_eq_true]
  all_goals cases kind <;> simp_all

/-- The actual replacement admission, interpreted in a source equation
model, constructs the lawful finite fold with exactly its collection policy. -/
theorem admitted_collection_fold_model {operations : String → List A → A}
    {value : Value} {old new : GrammarRule} {name : String} {kind : CollType} {element : TypeExpr}
    (source : collectionParameterKind old = none)
    (target : new.params = [.simple name (.collection kind element)])
    (accepted : checkFaithful value old new = .ok ())
    (holds : SourceEquationsHold operations value) :
    ∃ unit : String, ∃ fold : Mettapedia.Algebra.CollectionFold.Model A,
      fold.fold [] = operations unit [] ∧
      (∀ first second, fold.fold [first, second] = operations old.label [first, second]) ∧
      (kind ≠ .vec → fold.PermutationInvariant) ∧
      (kind = .hashSet → fold.MembershipInvariant) := by
  obtain ⟨_, ready, commutative, idempotent⟩ := checkFaithful_collection_basis source target accepted
  exact collection_fold_model kind holds ready commutative idempotent

/-- Successful execution of the actual replacement operation earns the
fold interpretation of its selected binary declaration. The source model
supplies its equations; no target monoid, fold or quotient law is assumed.
Transport of arbitrary enclosing equations through core lowering remains a
separate obligation. -/
theorem replacement_collection_fold_model {operations : String → List A → A}
    {value result : Value} {replacement : Replacement} {item : Item} {old : GrammarRule}
    {name : String} {kind : CollType} {element : TypeExpr}
    (accepted : replaceRow value replacement = .ok result)
    (selected : value.entries.find? (·.label == (.term, replacement.old)) = some item)
    (body : item.body = .term old) (source : collectionParameterKind old = none)
    (target : replacement.rule.params = [.simple name (.collection kind element)])
    (holds : SourceEquationsHold operations value) :
    ∃ unit : String, ∃ fold : Mettapedia.Algebra.CollectionFold.Model A,
      fold.fold [] = operations unit [] ∧
      (∀ first second, fold.fold [first, second] = operations old.label [first, second]) ∧
      (kind ≠ .vec → fold.PermutationInvariant) ∧
      (kind = .hashSet → fold.MembershipInvariant) := by
  obtain ⟨actualItem, actualRule, _, found, actualBody, _, _, faithful⟩ :=
    replaceRow_typing_readout value replacement accepted
  have sameItem : actualItem = item := Option.some.inj (found.symm.trans selected)
  subst actualItem
  have sameRule : actualRule = old := Decl.term.inj (actualBody.symm.trans body)
  subst actualRule
  exact admitted_collection_fold_model source target faithful holds


/-! ## The actual source-equation quotient as a separating model -/

namespace SourceQuotient
open Mettapedia.OSLF.MeTTaIL.ContextualStep Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.EquationSemantics

abbrev Carrier (base : BasePremiseEvaluator) (language : LanguageDef) :=
  Quotient (equationSetoid base language)

def classOf (base : BasePremiseEvaluator) (language : LanguageDef) (pattern : Pattern) :
    Carrier base language := Quotient.mk _ pattern

/-- Constructor congruence makes representative selection independent of the
chosen representatives. The carrier is the actual source equation quotient. -/
noncomputable def operations (base : BasePremiseEvaluator) (language : LanguageDef)
    (label : String) (arguments : List (Carrier base language)) : Carrier base language :=
  classOf base language (.apply label (arguments.map Quotient.out))

theorem operations_classOf (base : BasePremiseEvaluator) (language : LanguageDef)
    (label : String) (arguments : List Pattern) :
    operations base language label (arguments.map (classOf base language)) =
      classOf base language (.apply label arguments) := by
  apply Quotient.sound
  apply equationEquiv_apply_of_forall₂
  simp only [List.map_map, Function.comp_def]
  change List.Forall₂ (EquationEquiv base language)
    (arguments.map fun pattern => Quotient.out (classOf base language pattern)) arguments
  induction arguments with
  | nil => exact .nil
  | cons pattern arguments ih =>
      exact .cons (Quotient.exact (Quotient.out_eq (classOf base language pattern))) ih

private theorem lookup_table (names : List String) (values : String → Pattern)
    (key : String) (member : key ∈ names) :
    Bindings.lookup (names.map fun identifier => (identifier, values identifier)) key =
      some (values key) := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
      by_cases same : first = key
      · subst first
        simp [Bindings.lookup]
      · have later : key ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have test : (first == key) = false := by simp [same]
        simpa only [List.map_cons, Bindings.lookup, List.find?_cons, test] using ih later

mutual
  /-- Reading a first-order schema in the quotient returns its actual
  substitution instance, for any finite environment covering its variables. -/
  theorem read_instance (base : BasePremiseEvaluator) (language : LanguageDef)
      (assignment : String → Carrier base language) (environment : Bindings)
      {schema : Pattern} (shape : FirstOrder schema)
      (consistent : ∀ identifier ∈ schema.freeFvarNames,
        classOf base language (applyBindings environment (.fvar identifier)) = assignment identifier) :
      read? (operations base language) assignment schema =
        some (classOf base language (applyBindings environment schema)) := by
    cases shape with
    | metavariable identifier =>
        simpa only [read?] using
          congrArg some (consistent identifier (by simp [Pattern.freeFvarNames])).symm
    | constructor label arguments children =>
        have mapped := read_arguments base language assignment environment children
          (by simpa only [Pattern.freeFvarNames] using consistent)
        simpa only [read?, mapped, Option.map_some, applyBindings, List.map_map, Function.comp_def] using
          congrArg some (operations_classOf base language label
            (arguments.map (applyBindings environment)))
  termination_by sizeOf schema

  theorem read_arguments (base : BasePremiseEvaluator) (language : LanguageDef)
      (assignment : String → Carrier base language) (environment : Bindings)
      {schemas : List Pattern} (shapes : ∀ schema ∈ schemas, FirstOrder schema)
      (consistent : ∀ identifier ∈ schemas.flatMap Pattern.freeFvarNames,
        classOf base language (applyBindings environment (.fvar identifier)) = assignment identifier) :
      schemas.mapM (read? (operations base language) assignment) =
        some (schemas.map fun schema => classOf base language (applyBindings environment schema)) := by
    cases schemas with
    | nil => rfl
    | cons schema schemas =>
        have first := read_instance base language assignment environment (shapes schema (by simp))
          (fun identifier member => consistent identifier (by simp [member]))
        have rest := read_arguments base language assignment environment
          (fun child member => shapes child (List.mem_cons_of_mem _ member))
          (fun identifier member => consistent identifier (by simp [member]))
        simp only [List.mapM_cons, first, rest, List.map_cons]
        rfl
  termination_by sizeOf schemas
end

private theorem empty_instance {schema : Pattern} (shape : FirstOrder schema) :
    applyBindings [] schema = schema := by
  induction schema using Pattern.inductionOn with
  | hfvar => simp only [applyBindings, List.find?_nil]
  | happly label arguments ih =>
      cases shape with
      | constructor _ _ children =>
          simp only [applyBindings]
          apply congrArg (Pattern.apply label)
          exact (List.map_congr_left (fun child member => ih child member (children child member))).trans
            (List.map_id arguments)
  | hbvar | hlambda | hmultiLambda | hsubst | hcollection => cases shape

theorem read_classOf (base : BasePremiseEvaluator) (language : LanguageDef)
    {schema : Pattern} (shape : FirstOrder schema) :
    read? (operations base language) (fun identifier => classOf base language (.fvar identifier)) schema =
      some (classOf base language schema) := by
  simpa only [empty_instance shape] using
    read_instance base language (fun identifier => classOf base language (.fvar identifier)) [] shape
      (by intro identifier _; simp only [applyBindings, List.find?_nil])

theorem binderFreeList_of_forall : ∀ (patterns : List Pattern), (∀ pattern ∈ patterns, binderFree pattern = true) →
    binderFreeList patterns = true
  | [], _ => rfl
  | pattern :: patterns, all => by
    simp only [binderFreeList, all pattern List.mem_cons_self,
      binderFreeList_of_forall patterns (fun other member => all other (List.mem_cons_of_mem _ member)), Bool.and_self]

/-- **A first-order pattern holds no binder.** -/
theorem binderFree_of_firstOrder {pattern : Pattern} (shape : FirstOrder pattern) : binderFree pattern = true := by
  induction shape with
  | metavariable => rfl
  | constructor label arguments children holds =>
    simp only [binderFree]
    exact binderFreeList_of_forall arguments holds

/-- An actual premise-free first-order equation holds in its own quotient.
The right-side variable condition is essential for ordinary matching to
read the same finite substitution on both sides. -/
theorem equation_holds (base : BasePremiseEvaluator) {language : LanguageDef} {row : Equation}
    (member : row ∈ language.equations) (unconditional : row.premises = [])
    (leftShape : FirstOrder row.left) (rightShape : FirstOrder row.right)
    (closed : ∀ identifier ∈ row.right.freeFvarNames, identifier ∈ row.left.freeFvarNames) :
    EquationHolds (operations base language) row.left row.right := by
  intro assignment
  let environment : Bindings := row.left.freeFvarNames.map fun identifier =>
    (identifier, Quotient.out (assignment identifier))
  have defined : Defined environment row.left.freeFvarNames := by
    intro identifier member
    exact ⟨_, lookup_table row.left.freeFvarNames (fun identifier => Quotient.out (assignment identifier)) identifier member⟩
  obtain ⟨bindings, matched, compatible, _, names⟩ := match_instance environment leftShape defined
  have rightRead := compatible_readout rightShape compatible
    (fun identifier occurs => (names identifier).mpr (closed identifier occurs))
  have step : EquationInstance base language
      (applyBindings environment row.left) (applyBindings environment row.right) := by
    have raw : readsRaw row = true := by
      simp [readsRaw, binderFree_of_firstOrder leftShape, binderFree_of_firstOrder rightShape]
    refine ⟨0, .forward member raw (matchRel_complete matched) ?_ rightRead⟩
    simpa only [unconditional] using (PremisesAt.nil bindings : PremisesAt base language 0 bindings [] bindings)
  have equivalent : EquationEquiv base language
      (applyBindings environment row.left) (applyBindings environment row.right) :=
    .rel _ _ (.inContext .hole (.inl step))
  have consistent : ∀ identifier ∈ row.left.freeFvarNames,
      classOf base language (applyBindings environment (.fvar identifier)) = assignment identifier := by
    intro identifier occurs
    rw [apply_variable,
      show Bindings.lookup environment identifier = some (Quotient.out (assignment identifier)) from
        lookup_table _ (fun identifier => Quotient.out (assignment identifier)) identifier occurs,
      Option.getD_some]
    exact Quotient.out_eq _
  refine ⟨classOf base language (applyBindings environment row.left),
    read_instance base language assignment environment leftShape consistent, ?_⟩
  rw [read_instance base language assignment environment rightShape
    (fun identifier occurs => consistent identifier (closed identifier occurs))]
  exact congrArg some (Quotient.sound equivalent).symm

/-- Flattened source rows, not a supplied semantic oracle, license the
quotient model used by binary collection replacement. -/
theorem sourceEquationsHold (base : BasePremiseEvaluator) (sourceName : String) (value : Value)
    (rows : ∀ row ∈ (flattenRaw sourceName value).equations, row.premises = [] →
      FirstOrder row.left ∧ FirstOrder row.right ∧
        ∀ identifier ∈ row.right.freeFvarNames, identifier ∈ row.left.freeFvarNames) :
    SourceEquationsHold (operations base (flattenRaw sourceName value)) value := by
  intro item member row body unconditional
  have declared : row ∈ (flattenRaw sourceName value).equations :=
    List.mem_filterMap.mpr ⟨item, member, by simp [body]⟩
  obtain ⟨leftShape, rightShape, closed⟩ := rows row declared unconditional
  exact equation_holds base declared unconditional leftShape rightShape closed

#print axioms operations_classOf
#print axioms read_instance
#print axioms read_classOf
#print axioms equation_holds
#print axioms sourceEquationsHold
end SourceQuotient

end Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation
