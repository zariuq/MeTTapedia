import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface
import Mettapedia.Logic.HOL.UniformListInduction
import Mettapedia.Logic.HOL.UniformListInductionChart

/-!
# Uniform HOL list induction in a formed native declaration interface

The actual list signature, equations, predicate-quantified induction principle
and map-length conclusion are represented in the existing scoped native
syntax. Four distinct declared carriers retain proposition, element, sequence
and count types. A single polymorphic equality declaration covers all the
source's simple types, including function types.

Formation and both binding operations are justified by the general logical
interface. The object-HOL derivation remains a derivation of the source
formula; no equation identifies HOL truth with native inhabitation, and no
interpretation of arbitrary target terms or selected mathematical host is
claimed. All declarations here are opaque.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLUniformList

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic
open HOL.UniformListInduction

def baseName : BaseSort → DeclName
  | .element => `HOLUniformList.element
  | .sequence => `HOLUniformList.sequence
  | .count => `HOLUniformList.count

def types : TypeInterpretation BaseSort where
  proposition := .const `HOLUniformList.prop
  base := fun sort => .const (baseName sort)

def universalType : Tower.Tm 0 :=
  .pi (sortTm Tower.zero)
    (.pi (.pi (.var 0) (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop))

def symbolName : {type : HOL.Ty BaseSort} → Symbol type → DeclName
  | _, .nil => `HOLUniformList.nil
  | _, .cons => `HOLUniformList.cons
  | _, .map => `HOLUniformList.map
  | _, .length => `HOLUniformList.length
  | _, .zero => `HOLUniformList.zero
  | _, .succ => `HOLUniformList.succ

/-- The source's abstract list operations are retained as six ordinary
declarations. No implementation or logical axiom is installed by this table. -/
def declarations : Signature Tower.Head := Signature.ofList
  [(`HOLUniformList.prop, ⟨sortTm Tower.zero, none⟩),
   (`HOLUniformList.element, ⟨sortTm Tower.zero, none⟩),
   (`HOLUniformList.sequence, ⟨sortTm Tower.zero, none⟩),
   (`HOLUniformList.count, ⟨sortTm Tower.zero, none⟩),
   (`HOLUniformList.implication, ⟨typeAt types 0 (.arr .prop (.arr .prop .prop)), none⟩),
   (`HOLUniformList.universal, ⟨universalType, none⟩),
   (`HOLUniformList.equality, ⟨equalityDeclarationType types.proposition, none⟩),
   (`HOLUniformList.nil, ⟨typeAt types 0 sequence, none⟩),
   (`HOLUniformList.cons, ⟨typeAt types 0 (.arr element (.arr sequence sequence)), none⟩),
   (`HOLUniformList.map, ⟨typeAt types 0 (.arr mapping (.arr sequence sequence)), none⟩),
   (`HOLUniformList.length, ⟨typeAt types 0 (.arr sequence count), none⟩),
   (`HOLUniformList.zero, ⟨typeAt types 0 count, none⟩),
   (`HOLUniformList.succ, ⟨typeAt types 0 (.arr count count), none⟩)]

def rules : Rules Tower.Head := extendRules Tower.rules declarations

private theorem proposition_lookup :
    rules.constantType `HOLUniformList.prop = some (sortTm Tower.zero) := by decide

private theorem base_lookup (sort : BaseSort) :
    rules.constantType (baseName sort) = some (sortTm Tower.zero) := by
  cases sort <;> decide

private theorem implication_lookup : rules.constantType `HOLUniformList.implication =
    some (typeAt types 0 (.arr .prop (.arr .prop .prop))) := by decide

private theorem universal_lookup :
    rules.constantType `HOLUniformList.universal = some universalType := by decide

private theorem equality_lookup :
    rules.constantType `HOLUniformList.equality =
      some (equalityDeclarationType types.proposition) := by decide

private theorem symbol_lookup {type : HOL.Ty BaseSort} (symbol : Symbol type) :
    rules.constantType (symbolName symbol) = some (typeAt types 0 type) := by
  cases symbol <;> decide

theorem proposition_formed {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  .const proposition_lookup (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem base_formed (sort : BaseSort) :
    Typing rules .nil (types.base sort) (sortTm Tower.zero) :=
  .const (base_lookup sort) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem simple_type_formed (type : HOL.Ty BaseSort) {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (typeAt types n type) (sortTm Tower.zero) :=
  typeAt_formed_of_atoms declarations types (proposition_formed .nil) base_formed type gamma

private theorem pi_zero {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing rules gamma a (sortTm Tower.zero))
    (codomain : Typing rules (.snoc gamma a) b (sortTm Tower.zero)) :
    Typing rules gamma (.pi a b) (sortTm Tower.zero) := by
  apply Typing.cumul (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, LevelTower.zero]

theorem universal_type_formed : Typing rules .nil universalType
    (sortTm (.max (.succ Tower.zero) Tower.zero)) := by
  refine Typing.piForm (R := rules) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    ?_ (.sort Tower.zero) (.sorts (.succ Tower.zero) Tower.zero)
  exact pi_zero (pi_zero (.var 0) (proposition_formed _)) (proposition_formed _)

def universal (type : HOL.Ty BaseSort) : Tower.Tm 0 :=
  .app (.const `HOLUniformList.universal) (typeAt types 0 type)

theorem universal_typed (type : HOL.Ty BaseSort) :
    Typing rules .nil (universal type) (typeAt types 0 (.arr (.arr type .prop) .prop)) := by
  have symbol : Typing rules .nil (.const `HOLUniformList.universal) universalType :=
    .const universal_lookup universal_type_formed (.sort (.max (.succ Tower.zero) Tower.zero))
  have applied := Typing.appElim symbol (simple_type_formed type .nil)
  simpa only [universal, universalType, typeAt, types, liftClosed, Presentation.rename,
    inst0, Presentation.subst, subst0, consSub, liftSub, Fin.cases_zero] using applied

def equality (type : HOL.Ty BaseSort) : Tower.Tm 0 :=
  .app (.const `HOLUniformList.equality) (typeAt types 0 type)

theorem equality_typed (type : HOL.Ty BaseSort) :
    Typing rules .nil (equality type) (typeAt types 0 (.arr type (.arr type .prop))) := by
  have symbol : Typing rules .nil (.const `HOLUniformList.equality)
      (equalityDeclarationType types.proposition) :=
    .const equality_lookup
      (equalityDeclarationType_formed declarations types.proposition (proposition_formed .nil))
      (.sort (.max (.succ Tower.zero) Tower.zero))
  have applied := Typing.appElim symbol (simple_type_formed type .nil)
  simpa only [equality, equalityDeclarationType, typeAt, types, liftClosed, Presentation.rename,
    inst0, Presentation.subst, subst0, consSub, liftSub, Fin.cases_zero, Fin.cases_succ,
    typeAt_rename] using applied

def signature : LogicalSignature BaseSort Symbol where
  declarations := declarations
  types := types
  proposition_formed := proposition_formed .nil
  base_formed := base_formed
  constant := fun symbol => .const (symbolName symbol)
  constant_typed := by
    intro type symbol
    simpa only [rules, liftClosed, typeAt_rename] using
      Typing.const (Γ := .nil) (symbol_lookup symbol)
        (simple_type_formed type .nil) (.sort Tower.zero)
  implication := .const `HOLUniformList.implication
  implication_typed := .const implication_lookup
    (simple_type_formed (.arr .prop (.arr .prop .prop)) .nil) (.sort Tower.zero)
  universal := universal
  universal_typed := universal_typed
  equality := equality
  equality_typed := equality_typed

/-! ## Independently displayed target formulas -/

def rawAll {n : Nat} (type : HOL.Ty BaseSort) (body : Tower.Tm (n + 1)) : Tower.Tm n :=
  .app (liftClosed (universal type)) (.lam body)

def rawEq {n : Nat} (type : HOL.Ty BaseSort) (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed (equality type)) left) right

def rawImp {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const `HOLUniformList.implication) left) right

def rawNil {n : Nat} : Tower.Tm n := .const `HOLUniformList.nil

def rawCons {n : Nat} (element sequence : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const `HOLUniformList.cons) element) sequence

def rawMap {n : Nat} (function sequence : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const `HOLUniformList.map) function) sequence

def rawLength {n : Nat} (sequence : Tower.Tm n) : Tower.Tm n :=
  .app (.const `HOLUniformList.length) sequence

def rawSucc {n : Nat} (count : Tower.Tm n) : Tower.Tm n :=
  .app (.const `HOLUniformList.succ) count

def rawMapNil {n : Nat} : Tower.Tm n :=
  rawAll mapping (rawEq sequence (rawMap (.var 0) rawNil) rawNil)

def rawMapCons {n : Nat} : Tower.Tm n :=
  rawAll mapping (rawAll element (rawAll sequence
    (rawEq sequence
      (rawMap (.var (Fin.succ (Fin.succ 0))) (rawCons (.var (Fin.succ 0)) (.var 0)))
      (rawCons (.app (.var (Fin.succ (Fin.succ 0))) (.var (Fin.succ 0)))
        (rawMap (.var (Fin.succ (Fin.succ 0))) (.var 0))))))

def rawLengthNil {n : Nat} : Tower.Tm n :=
  rawEq count (rawLength rawNil) (.const `HOLUniformList.zero)

def rawLengthCons {n : Nat} : Tower.Tm n :=
  rawAll element (rawAll sequence (rawEq count
    (rawLength (rawCons (.var (Fin.succ 0)) (.var 0))) (rawSucc (rawLength (.var 0)))))

def rawInductionStep {n : Nat} (predicate : Tower.Tm n) : Tower.Tm n :=
  rawAll element (rawAll sequence (rawImp
    (.app (Presentation.rename wk (Presentation.rename wk predicate)) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk predicate))
      (rawCons (.var (Fin.succ 0)) (.var 0)))))

def rawInductionPrinciple {n : Nat} : Tower.Tm n :=
  rawAll predicate (rawImp (.app (.var 0) rawNil)
    (rawImp (rawInductionStep (.var 0))
      (rawAll sequence (.app (.var (Fin.succ 0)) (.var 0)))))

def rawPreservesLength {n : Nat} (function sequence : Tower.Tm n) : Tower.Tm n :=
  rawEq count (rawLength (rawMap function sequence)) (rawLength sequence)

def rawMapLength {n : Nat} : Tower.Tm n :=
  rawAll mapping (rawAll sequence (rawPreservesLength (.var (Fin.succ 0)) (.var 0)))

def rawEquations {n : Nat} : List (Tower.Tm n) :=
  [rawMapNil, rawMapCons, rawLengthNil, rawLengthCons]

def rawTheory {n : Nat} : List (Tower.Tm n) :=
  rawInductionPrinciple :: rawEquations

theorem mapNil_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (mapNil (Γ := gamma)) = some rawMapNil := rfl

theorem mapCons_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (mapCons (Γ := gamma)) = some rawMapCons := rfl

theorem lengthNil_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (lengthNil (Γ := gamma)) = some rawLengthNil := rfl

theorem lengthCons_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (lengthCons (Γ := gamma)) = some rawLengthCons := rfl

theorem inductionPrinciple_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (inductionPrinciple (Γ := gamma)) = some rawInductionPrinciple := rfl

theorem mapLength_represented (gamma : HOL.Ctx BaseSort) :
    represent signature (mapLength (Γ := gamma)) = some rawMapLength := rfl

theorem equations_represented (gamma : HOL.Ctx BaseSort) :
    (equations (Γ := gamma)).map (represent signature) = (rawEquations (n := gamma.length)).map some :=
  rfl

theorem theory_represented (gamma : HOL.Ctx BaseSort) :
    (theory (Γ := gamma)).map (represent signature) = (rawTheory (n := gamma.length)).map some :=
  rfl

theorem mapLength_formed (gamma : HOL.Ctx BaseSort) :
    Judgment rules (context types gamma) rawMapLength (.const `HOLUniformList.prop) :=
  represent_judgment signature _ (mapLength_represented gamma)

theorem theory_formed (gamma : HOL.Ctx BaseSort) :
    ∀ formula ∈ rawTheory (n := gamma.length),
      Judgment rules (context types gamma) formula (.const `HOLUniformList.prop) := by
  intro formula member
  simp only [rawTheory, rawEquations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact represent_judgment signature _ (inductionPrinciple_represented gamma)
  · exact represent_judgment signature _ (mapNil_represented gamma)
  · exact represent_judgment signature _ (mapCons_represented gamma)
  · exact represent_judgment signature _ (lengthNil_represented gamma)
  · exact represent_judgment signature _ (lengthCons_represented gamma)

/-- The original proof and its represented formula share the same source
syntax. The native judgment forms the proposition; it does not prove it. -/
theorem source_derivation_and_representation (gamma : HOL.Ctx BaseSort) :
    HOL.ExtDerivation Symbol (theory (Γ := gamma)) mapLength ∧
      represent signature (mapLength (Γ := gamma)) = some rawMapLength ∧
      Judgment rules (context types gamma) rawMapLength (.const `HOLUniformList.prop) :=
  ⟨mapLength_derivation, mapLength_represented gamma, mapLength_formed gamma⟩

/-- The specialized equational certificates reconstruct the same source
theorem whose formula is represented by the native declaration interface.
The two proof judgments remain separate: this is not native inhabitation of
the represented proposition. -/
theorem chart_derivation_and_representation (gamma : HOL.Ctx BaseSort) :
    HOL.ExtDerivation Symbol (theory (Γ := gamma)) mapLength ∧
      represent signature (mapLength (Γ := gamma)) = some rawMapLength ∧
      Judgment rules (context types gamma) rawMapLength (.const `HOLUniformList.prop) :=
  ⟨HOL.UniformListInductionChart.mapLength_via_chart gamma,
    mapLength_represented gamma, mapLength_formed gamma⟩

/-! ## Actual binding operations and negative controls -/

def mappingIdentity : Expr [] mapping := .lam (.var .vz)

def rawMappingIdentity : Tower.Tm 0 := .lam (.var 0)

def rawLengthPredicate : Tower.Tm 1 :=
  .lam (rawPreservesLength (.var (Fin.succ 0)) (.var 0))

theorem mappingIdentity_represented :
    represent signature mappingIdentity = some rawMappingIdentity := rfl

theorem lengthPredicate_represented :
    represent signature (lengthPredicate (.var .vz : Expr [mapping] mapping)) =
      some rawLengthPredicate := rfl

/-- Weakening shifts the free mapping variable beneath the sequence binder,
using the same renaming operation as the generic scoped syntax. -/
theorem lengthPredicate_renaming :
    represent signature (HOL.weaken (σ := element)
      (lengthPredicate (.var .vz : Expr [mapping] mapping))) =
      some (Presentation.rename wk rawLengthPredicate) := by
  have renamed := represent_rename signature (HOL.Rename.weaken (σ := element))
    wk (fun _ => rfl) (lengthPredicate (.var .vz : Expr [mapping] mapping))
  simpa only [HOL.weaken, lengthPredicate_represented, Option.map_some] using renamed

theorem lengthPredicate_renaming_formed :
    Judgment rules (context types [element, mapping])
      (Presentation.rename wk rawLengthPredicate) (typeAt types 2 predicate) :=
  represent_judgment signature _ lengthPredicate_renaming

private theorem substitution_components {type : HOL.Ty BaseSort}
    (index : HOL.Var [mapping] type) :
    represent signature (HOL.Subst.single mappingIdentity index) =
      some (subst0 rawMappingIdentity (variableIndex index)) := by
  cases index with
  | vz => exact mappingIdentity_represented
  | vs previous => nomatch previous

/-- A function-valued substitution passes beneath the list binder and through
the newly supported equality constructor using the general substitution law. -/
theorem lengthPredicate_substitution :
    represent signature (HOL.instantiate mappingIdentity
      (lengthPredicate (.var .vz : Expr [mapping] mapping))) =
      some (inst0 rawMappingIdentity rawLengthPredicate) := by
  have substituted := represent_subst signature (HOL.Subst.single mappingIdentity)
    (subst0 rawMappingIdentity) substitution_components
    (lengthPredicate (.var .vz : Expr [mapping] mapping))
  simpa only [lengthPredicate_represented, Option.map_some, HOL.instantiate, inst0] using substituted

theorem lengthPredicate_substitution_formed :
    Judgment rules .nil (inst0 rawMappingIdentity rawLengthPredicate)
      (typeAt types 0 predicate) :=
  represent_judgment signature _ lengthPredicate_substitution

/-- Supporting equality does not silently enable unsupported operands. -/
theorem unsupported_operand_rejected :
    represent signature (HOL.Term.eq .bot .bot : HOL.ClosedFormula Symbol) = none := rfl

/-- An undeclared operator cannot supply the independently required equality
typing field, at any source type. -/
theorem missing_equality_not_typed (type : HOL.Ty BaseSort) :
    ¬ Typing rules .nil (.const `HOLUniformList.missingEquality)
      (typeAt types 0 (.arr type (.arr type .prop))) := by
  intro typed
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  have absent : rules.constantType `HOLUniformList.missingEquality = none := by decide
  rw [absent] at lookup
  cases lookup

/-- Source type names retain distinct native representations. -/
theorem carrier_codes_distinct :
    ([(types.proposition : Tower.Tm 0), types.base .element,
      types.base .sequence, types.base .count]).Nodup := by decide

#print axioms equality_typed
#print axioms mapLength_formed
#print axioms theory_formed
#print axioms source_derivation_and_representation
#print axioms chart_derivation_and_representation
#print axioms lengthPredicate_renaming
#print axioms lengthPredicate_renaming_formed
#print axioms lengthPredicate_substitution
#print axioms lengthPredicate_substitution_formed
#print axioms unsupported_operand_rejected
#print axioms missing_equality_not_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLUniformList
