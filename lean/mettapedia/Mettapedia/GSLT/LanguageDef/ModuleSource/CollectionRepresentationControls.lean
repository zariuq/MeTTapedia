import Lean.Elab.Tactic.CbvSimproc
import Lean.Meta.StringLitProof
import Lean.Meta.Sym.LitValues
import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentation
import Mettapedia.GSLT.LanguageDef.ModuleSource.FixedArityCollectionControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionInterpretation
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProfile
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.BagEquationDecision
import Mettapedia.Languages.ProcessCalculi.OrientedRho.Module

/-! # Independent operations over the same collection carrier

The two monoid operations have different units and a natural-number model
that distinguishes them. Their named collection replacements retain all
source equations. Anonymous bags cannot acquire their result sort.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.OSLF.MeTTaIL.Syntax
#module_file "../../../../../../metta/gslt/module/CollectionIndependentMonoids.module"
#module_file "../../../../../../metta/gslt/module/CollectionNamedSets.module"

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls

open Mettapedia.OSLF.MeTTaIL
open WellSorted

def language : LanguageDef := CollectionIndependentMonoids.language.toOption.getD (LanguageDef.empty "")
def core : LanguageDef := (language.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard CollectionIndependentMonoids.language.isOk
#guard language.toCore.isOk
#guard language.equations.length == 8
#guard language.terms.filterMap (fun row => if row.collectionRepresentation == .wrapped then some row.label else none) == ["Sum", "Product"]
#guard core.rewrites.map (fun row => row.left == row.right) == [false]
#guard (CoreReduction.bareLabels core).isEmpty

def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "One" []
def payload : Pattern := .collection .hashBag [zero, one] none
def resultSort : TypeExpr := .base "Number"

def queries : List (String × Pattern × Bool) :=
  [("sum", .apply "Sum" [payload], true),
   ("product", .apply "Product" [payload], true),
   ("anonymous-bag", payload, false),
   ("wrong-kind", .apply "Sum" [.collection .hashSet [zero, one] none], false),
   ("wrong-wrapper", .apply "Other" [payload], false),
   ("wrong-arity", .apply "Sum" [zero, one], false)]

#guard queries.all fun (_, term, expected) =>
  checkHasType core (fun _ => none) [] term resultSort == expected

namespace NamedSets

def language : LanguageDef := CollectionNamedSets.language.toOption.getD (LanguageDef.empty "")
def core : LanguageDef := (language.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")
def nodes : List Pattern := [.apply "A" [], .apply "B" []]
def resultSort : TypeExpr := .base "Graph"
def queries : List (String × Pattern × Bool) :=
  [("reach", .apply "Reach" [.collection .hashSet nodes none], true),
   ("seen", .apply "Seen" [.collection .hashSet nodes none], true),
   ("anonymous-set", .collection .hashSet nodes none, false),
   ("bag-in-set-wrapper", .apply "Reach" [.collection .hashBag nodes none], false)]

#guard CollectionNamedSets.language.isOk
#guard language.toCore.isOk
#guard (CoreReduction.bareLabels core).isEmpty
#guard core.rewrites.map (·.left) == [.apply "Reach" [.collection .hashSet nodes none]]
#guard core.rewrites.map (·.right) == [.apply "Seen" [.collection .hashSet nodes none]]
#guard queries.all fun (_, term, expected) =>
  checkHasType core (fun _ => none) [] term resultSort == expected

end NamedSets

namespace IndependentMonoids
open Mettapedia.GSLT.LanguageDef.ModuleSource
open AlgebraInterpretation

def original : Value :=
  ((applyTheory CollectionIndependentMonoids.library CollectionIndependentMonoids.module ["Operations"] []).toOption.map
    Prod.snd).getD { entries := [] }

def v (label : String) : Pattern := .fvar label

def op (label : String) (first second : Pattern) : Pattern := .apply label [first,second]

def unit (label : String) : Pattern := .apply label []

def laws (label neutral : String) : List (Pattern × Pattern) :=
  [(op label (op label (v "x") (v "y")) (v "z"), op label (v "x") (op label (v "y") (v "z"))),
   (op label (v "x") (v "y"), op label (v "y") (v "x")),
   (op label (v "x") (unit neutral), v "x"),
   (op label (unit neutral) (v "x"), v "x")]

theorem inventory :
    (flattenRaw "" original).equations.map (fun row => (row.left,row.right)) =
      laws "Add" "Zero" ++ laws "Mul" "One" := by decide

def numeric : String → List Nat → Nat
  | "Add", [first,second] => first + second
  | "Mul", [first,second] => first * second
  | "One", [] => 1
  | _, _ => 0

theorem actual_source_numeric_model : SourceEquationsHold numeric original := by
  intro item member row body _
  have declared : row ∈ (flattenRaw "" original).equations :=
    List.mem_filterMap.mpr ⟨item, member, by simp [body]⟩
  have pair := List.mem_map_of_mem (f := fun row : Equation => (row.left,row.right)) declared
  rw [inventory] at pair
  simp only [laws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at pair
  rcases pair with ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ |
      ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ <;>
    rw [left,right] <;>
    simp [EquationHolds, read?, numeric, op, unit, v] <;> intro assignment <;> ac_rfl

end IndependentMonoids

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource
open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics BagNormalForm
open BagNormalForm.WithAuthoredEquations
set_option maxHeartbeats 200000
open Mettapedia.OSLF.MeTTaIL.Match

@[local cbv_eval] private theorem origin_eq_fields (first second : Origin) :
    (first = second) = (first.inst = second.inst ∧ first.name = second.name) := by
  cases first
  cases second
  simp
@[local cbv_eval] private theorem label_eq_fields (first second : Label) :
    (first = second) = (first.1 = second.1 ∧ first.2 = second.2) := by
  cases first
  cases second
  simp



open Lean Meta in
local cbv_simproc cbv_eval sourceStringDecidable (String.decEq _ _) := fun e => do
  let_expr String.decEq first second := e | return .rfl
  let some firstValue := Sym.getStringValue? first | return .rfl
  let some secondValue := Sym.getStringValue? second | return .rfl
  let literalProof ← if firstValue == secondValue then mkEqRefl first
    else mkStringLitNeProof firstValue secondValue
  let decidableConstructor := if firstValue == secondValue then ``Decidable.isTrue else ``Decidable.isFalse
  let result ← mkAppM decidableConstructor #[literalProof]
  let result ← Sym.share result
  let proof ← mkAppM ``Subsingleton.elim #[e,result]
  return .step result proof

@[local cbv_eval] private theorem constructor_refs_nullary (label : String) :
    Pattern.constructorRefs (.apply label []) = [(label,0)] := by
  simp only [Pattern.constructorRefs,Pattern.constructorRefsList]
  rfl

attribute [local cbv_opaque] String.decEq



/-- Select the actual parallel-monoid theory from the existing module file. -/
def arguments : List Expr :=
  [.apply ["u","CommutativeMonoid"] [.apply ["u","Monoid"] [.apply ["u","EmptySet"] []]]]
def selected : Except Error (String × Value) :=
  applyTheory _root_.OrientedRho.library _root_.OrientedRho.module ["ParMonoid"] arguments
def authored : LanguageDef :=
  (selected.map (fun pair => flatten pair.1 pair.2)).toOption.getD (LanguageDef.empty "")
def core : LanguageDef := (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")
def carrier : GrammarRule := core.terms[1]?.getD {label := "missing",category := "Proc",params := [],syntaxPattern := []}
def comparison : LanguageDef := {core with «equations» := []}
def proc : TypeExpr := .base "Proc"
def zero : Pattern := .apply "PZero" []

theorem selected_accepted : selected.isOk = true := by cbv
theorem core_accepted : authored.toCore.isOk = true := by cbv
theorem binary_origin_retained :
    (selected.toOption.map (fun pair => pair.2.binaryCollections)) = some [⟨1,"Mult"⟩] := by cbv
theorem actual_rows_retained : core.equations.length = 2 := by cbv

theorem actual_equation_shapes : core.equations.map (fun row => (row.left,row.right,row.premises)) =
    [(.collection .hashBag [.fvar "x",zero] none,.fvar "x",[]),
     (.collection .hashBag [zero,.fvar "x"] none,.fvar "x",[])] := by cbv

theorem actual_bare_theory : BareBagTheory comparison carrier (some "PZero") :=
  (bagTheory_of_check (by cbv)).asBare (by cbv)

theorem actual_rows : ∀ row ∈ core.equations,
    row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
      ∀ bindings, normalForm (some "PZero") (applyBindings bindings row.left) =
        normalForm (some "PZero") (applyBindings bindings row.right) := by
  intro row member
  have shape : (row.left,row.right,row.premises) ∈
      [(.collection .hashBag [.fvar "x",zero] none,.fvar "x",[]),
       (.collection .hashBag [zero,.fvar "x"] none,.fvar "x",[])] := by
    rw [← actual_equation_shapes]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at shape
  rcases shape with first | second
  · obtain ⟨left,rest⟩ := Prod.mk.inj first
    obtain ⟨right,empty⟩ := Prod.mk.inj rest
    refine ⟨empty,?_,?_,?_⟩
    · rw [left]
      exact .inr ⟨[.fvar "x",zero],rfl,by
        intro element member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> rfl⟩
    · rw [right]; exact .inl rfl
    · intro bindings
      rw [left,right]
      simpa only [applyBindings,List.map_cons,List.map_nil,List.append_nil,List.cons_append,List.nil_append,zero] using
        (normalForm_insert_unit "PZero" [applyBindings bindings (.fvar "x")] []).trans
          (normalForm_singleton "PZero" _)
  · obtain ⟨left,rest⟩ := Prod.mk.inj second
    obtain ⟨right,empty⟩ := Prod.mk.inj rest
    refine ⟨empty,?_,?_,?_⟩
    · rw [left]
      exact .inr ⟨[zero,.fvar "x"],rfl,by
        intro element member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> rfl⟩
    · rw [right]; exact .inl rfl
    · intro bindings
      rw [left,right]
      simpa only [applyBindings,List.map_cons,List.map_nil,List.append_nil,List.cons_append,List.nil_append,zero] using
        (normalForm_insert_unit "PZero" [] [applyBindings bindings (.fvar "x")]).trans
          (normalForm_singleton "PZero" _)

/-- The actual source relation and existing coherence interface share one
normalizer, on the admissible source fibre only. -/
theorem actual_source_normalizer (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) :
    Complete.Coherence.Normalizer
      (fun (first second : {pattern // Admissible core free bound proc pattern}) =>
        EquationContextStep base core first.1 second.1)
      (normalizeSource actual_bare_theory base free bound proc rfl) :=
  sourceNormalizer actual_bare_theory actual_rows base free bound proc rfl

theorem actual_source_equivalence (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) (left right : {pattern // Admissible core free bound proc pattern}) :
    Relation.EqvGen
      (fun (first second : {pattern // Admissible core free bound proc pattern}) =>
        EquationContextStep base core first.1 second.1) left right ↔
      normalForm (some "PZero") left.1 = normalForm (some "PZero") right.1 :=
  source_fibre_equiv_iff_normalForm_eq actual_bare_theory actual_rows base free bound proc rfl left right

/-- The actual raw source equivalence agrees at admissible endpoints,
including chains which leave the object fibre between those endpoints. -/
theorem actual_raw_source_equivalence (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) (left right : {pattern // Admissible core free bound proc pattern}) :
    EquationEquiv base core left.1 right.1 ↔
      normalForm (some "PZero") left.1 = normalForm (some "PZero") right.1 :=
  source_equationEquiv_iff_normalForm_eq actual_bare_theory actual_rows base left.2 right.2 rfl

def free : FreeTypeContext := fun _ => some proc
def first : Pattern := .collection .hashBag
  [zero,.collection .hashBag [.fvar "b",.fvar "a"] none,zero] none
def second : Pattern := .collection .hashBag [.fvar "a",.fvar "b"] none

theorem first_admissible : Admissible core free [] proc first :=
  ⟨checkHasType_sound (by cbv),by cbv,by cbv⟩
theorem second_admissible : Admissible core free [] proc second :=
  ⟨checkHasType_sound (by cbv),by cbv,by cbv⟩
theorem nested_unit_permutation_agreement :
    Relation.EqvGen
      (fun (left right : {pattern // Admissible core free [] proc pattern}) =>
        EquationContextStep defaultBasePremises core left.1 right.1)
      ⟨first,first_admissible⟩ ⟨second,second_admissible⟩ :=
  (actual_source_equivalence defaultBasePremises free [] _ _).mpr (by cbv)

theorem nested_unit_permutation_raw_equivalence :
    EquationEquiv defaultBasePremises core first second :=
  (actual_raw_source_equivalence defaultBasePremises free []
    ⟨first,first_admissible⟩ ⟨second,second_admissible⟩).mpr (by cbv)

theorem empty_and_singleton_collapse :
    normalForm (some "PZero") (.collection .hashBag [] none) = zero ∧
      normalForm (some "PZero") (.collection .hashBag [.fvar "a"] none) = .fvar "a" := by cbv

theorem wrong_unit_profile_refused : bagTheoryCheck comparison carrier (some "WrongUnit") = false := by cbv

theorem cross_constructor_profile_refused :
    bagTheoryCheck comparison {carrier with label := "OtherBag"} (some "PZero") = false := by cbv

theorem wrong_unit_separates_actual_row :
    normalForm (some "WrongUnit") (.collection .hashBag [.fvar "a",zero] none) ≠
      normalForm (some "WrongUnit") (.fvar "a") := by cbv; decide

/-- The raw matcher may ignore an authored subject's open tail. This does not
license an unrestricted raw normalizer or alter the matcher. -/
def openTail : Pattern := .collection .hashBag [.fvar "a",zero] (some "tail")
def rightUnit : Equation := core.equations.headD
  {«name» := "missing",typeContext := [],«premises» := [],left := .fvar "x",right := .fvar "x"}

theorem right_unit_member : rightUnit ∈ core.equations := by
  have split : core.equations = rightUnit :: core.equations.drop 1 := by cbv
  rw [split]
  exact List.mem_cons_self

theorem raw_tail_unit_instance (base : BasePremiseEvaluator) :
    EquationInstance base core openTail (.fvar "a") := by
  refine ⟨0,EquationInstanceAt.forward (equation := rightUnit)
    (initialBindings := [("x",.fvar "a")]) (finalBindings := [("x",.fvar "a")])
    right_unit_member (by cbv) ?_ ?_ ?_⟩
  · cbv
    exact .head []
  · rw [(actual_rows rightUnit right_unit_member).1]
    exact .nil _
  · cbv

theorem raw_tail_is_not_object : isObjectPattern openTail = false := by cbv

theorem raw_tail_normal_forms_separate :
    normalForm (some "PZero") openTail ≠ normalForm (some "PZero") (.fvar "a") := by cbv; decide

theorem no_unrestricted_source_normalizer (base : BasePremiseEvaluator) :
    ¬ Complete.Coherence.Normalizer (EquationContextStep base core) (normalForm (some "PZero")) := by
  intro claimed
  exact raw_tail_normal_forms_separate
    (claimed.canonical openTail (.fvar "a") (.inContext .hole (.inl (raw_tail_unit_instance base))))


namespace BinarySource
open ReplacementTransport BinaryCollectionLowering
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

/-- The actual imported commutative monoid before the ParMonoid exports and
replacements. Subsequent stages use the blocks parsed from that theory. -/
def imported : Except Error (String × Value) :=
  applyTheory _root_.OrientedRho.library _root_.OrientedRho.module ["u","CommutativeMonoid"]
    [.apply ["u","Monoid"] [.apply ["u","EmptySet"] []]]
def blocks : List Block :=
  match (_root_.OrientedRho.module.theories[0]?).map Theory.body with
  | some (Expr.extend _ parsedBlocks) => parsedBlocks
  | _ => []
def replacements : List Replacement :=
  match blocks[1]? with | some (Block.replacements rows) => rows | _ => []
def unitReplacement : Replacement :=
  replacements[0]?.getD {old := "missing",rule := {label := "missing",category := "Proc",params := [],syntaxPattern := []}}
def replacement : Replacement :=
  replacements[1]?.getD {old := "missing",rule := {label := "missing",category := "Proc",params := [],syntaxPattern := []}}
def before : Value :=
  ((imported.bind fun pair => do
    let exported ← applyBlock 3 pair.2 (blocks[0]?.getD (.types []))
    replaceRow exported unitReplacement).toOption).getD {entries := []}
def after : Value := (replaceRow before replacement).toOption.getD {entries := []}
def source : LanguageDef := flattenRaw "OrientedRho.ParMonoid" before
def target : LanguageDef := flattenRaw "OrientedRho.ParMonoid" after
def sourceItem : Item :=
  (before.entries.find? (·.label == (.term,replacement.old))).getD
    ⟨⟨0,"missing"⟩,(.term,"missing"),.sort "missing"⟩
def sourceRule : GrammarRule :=
  match sourceItem.body with
  | .term rule => rule
  | _ => {label := "missing",category := "Proc",params := [],syntaxPattern := []}

theorem imported_accepted : imported.isOk = true := by cbv
theorem replacement_accepted : replaceRow before replacement = .ok after := by cbv
theorem selected_item : before.entries.find? (·.label == (.term,replacement.old)) = some sourceItem := by cbv
theorem selected_rule : sourceItem.body = .term sourceRule := by cbv
theorem actual_replacement : replacement.old = "Plus" ∧ replacement.rule.label = "PPar" ∧
    replacement.rule.params = [.simple "ps" (.collection .hashBag proc)] := by cbv

theorem final_raw_agreement : target =
    flattenRaw "OrientedRho.ParMonoid" (selected.toOption.getD ("",{entries := []})).2 := by cbv

theorem origins_retained : after.entries.map (·.origin) = before.entries.map (·.origin) := by cbv
theorem binary_origin : after.binaryCollections = [⟨1,"Mult"⟩] := by cbv

theorem source_rows_eligible : ∀ row ∈ source.equations, row.premises = [] →
    FirstOrder row.left ∧ FirstOrder row.right ∧
      ∀ identifier ∈ row.right.freeFvarNames, identifier ∈ row.left.freeFvarNames := by
  have finite : source.equations.all (fun row => checkFirstOrder row.left && checkFirstOrder row.right &&
      row.right.freeFvarNames.all (fun identifier => decide (identifier ∈ row.left.freeFvarNames))) = true := by cbv
  intro row member _
  have checked := List.all_eq_true.mp finite row member
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  exact ⟨checkFirstOrder_sound checked.1.1,checkFirstOrder_sound checked.1.2,checked.2⟩

theorem source_coherent : TermLabelsCoherent before :=
  (checkTermLabelsCoherent_iff before).mp (by cbv)
theorem source_valid : ModuleAlgebra.Valid before.entries.toFinset :=
  (ModuleAlgebra.orderedCheck_isSome_iff before.entries).mp (by cbv)

theorem reflection (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right)
    (equal : normalForm (some "PZero") (translated target sourceRule replacement.rule .hashBag left) =
      normalForm (some "PZero") (translated target sourceRule replacement.rule .hashBag right)) :
    EquationEquiv base source left right := by
  exact BinaryCollectionInterpretation.replacement_reflects_bagNormalForm
    replacement_accepted selected_item selected_rule source_coherent source_valid
    "OrientedRho.ParMonoid" "OrientedRho.ParMonoid" (by cbv) (by cbv) actual_replacement.2.2
    (by cbv) (by cbv) base source_rows_eligible "PZero" false (by cbv; exact .head _) (by cbv)
    free bound leftTyped rightTyped leftShape rightShape equal

theorem wrong_unit_not_declared : ("Wrong",false) ∉ binaryUnits before sourceRule.label := by
  have table : binaryUnits before sourceRule.label = [("PZero",false),("PZero",true)] := by cbv
  rw [table]
  simp

theorem cross_constructor_freshness_refused :
    BinaryCollectionInterpretation.checkFreshLabel source sourceRule
      {replacement.rule with label := "PZero"} = false := by cbv


theorem actual_core_lowering_table : CoreReduction.bareLabels target = CoreReduction.bareLabels core := by cbv

/-- The actual selected module's final core table is the very table used in
reflection, after the original binary constructor is packed. -/
theorem reflection_into_actual_core (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right)
    (equal : normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag left) =
      normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag right)) :
    EquationEquiv base source left right := by
  apply reflection base free bound leftTyped rightTyped leftShape rightShape
  simpa only [translated,actual_core_lowering_table] using equal

def nestedBinary : Pattern := .apply "Plus" [zero,.apply "Plus" [.fvar "b",.fvar "a"]]
def flatBinary : Pattern := .apply "Plus" [.fvar "a",.fvar "b"]

theorem unit_collapse_reflected (base : BasePremiseEvaluator) :
    EquationEquiv base source (.apply "Plus" [zero,.fvar "a"]) (.fvar "a") :=
  reflection_into_actual_core (type := proc) base free [] (checkHasType_sound (by cbv)) (checkHasType_sound (by cbv))
    (checkFirstOrder_sound (by cbv)) (checkFirstOrder_sound (by cbv)) (by cbv)

theorem nested_unit_permutation_reflected (base : BasePremiseEvaluator) :
    EquationEquiv base source nestedBinary flatBinary :=
  reflection_into_actual_core (type := proc) base free [] (checkHasType_sound (by cbv)) (checkHasType_sound (by cbv))
    (checkFirstOrder_sound (by cbv)) (checkFirstOrder_sound (by cbv)) (by cbv)


open BinaryCollectionInterpretation

theorem source_rule_label : sourceRule.label = "Plus" := by cbv

theorem source_equation_shapes : source.equations.map (fun row => (row.left,row.right,row.premises)) =
    [(.apply "Plus" [.apply "Plus" [.fvar "x",.fvar "y"],.fvar "z"],
      .apply "Plus" [.fvar "x",.apply "Plus" [.fvar "y",.fvar "z"]],[]),
     (.apply "Plus" [.fvar "x",zero],.fvar "x",[]),
     (.apply "Plus" [zero,.fvar "x"],.fvar "x",[]),
     (.apply "Plus" [.fvar "x",.fvar "y"],.apply "Plus" [.fvar "y",.fvar "x"],[])] := by cbv

theorem source_plain : PlainEquations source := by
  have finite : source.equations.all (fun row => row.premises.isEmpty) = true := by cbv
  have declarations : source.equations.all (fun row => row.bindings.isNone) = true := by cbv
  intro row member
  have unconditional := List.isEmpty_iff.mp (List.all_eq_true.mp finite row member)
  have eligible := source_rows_eligible row member unconditional
  exact ⟨unconditional,eligible.1.isMatchCorrect,eligible.2.1.isMatchCorrect,
    readsRaw_of_none (Option.isNone_iff_eq_none.mp (List.all_eq_true.mp declarations row member))⟩

theorem source_rows_projected : ∀ row ∈ source.equations, ∀ bindings : Match.Bindings,
    normalForm (some "PZero") (projectBinary sourceRule.label (applyBindings bindings row.left)) =
      normalForm (some "PZero") (projectBinary sourceRule.label (applyBindings bindings row.right)) := by
  intro row member bindings
  rw [source_rule_label]
  have shape : (row.left,row.right,row.premises) ∈
      [(.apply "Plus" [.apply "Plus" [.fvar "x",.fvar "y"],.fvar "z"],
        .apply "Plus" [.fvar "x",.apply "Plus" [.fvar "y",.fvar "z"]],[]),
       (.apply "Plus" [.fvar "x",zero],.fvar "x",[]),
       (.apply "Plus" [zero,.fvar "x"],.fvar "x",[]),
       (.apply "Plus" [.fvar "x",.fvar "y"],.apply "Plus" [.fvar "y",.fvar "x"],[])] := by
    rw [← source_equation_shapes]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at shape
  rcases shape with associative | rightUnit | leftUnit | commutative
  · obtain ⟨left,rest⟩ := Prod.mk.inj associative
    obtain ⟨right,_⟩ := Prod.mk.inj rest
    rw [left,right]
    simpa only [applyBindings,List.map_cons,List.map_nil] using
      projectBinary_associativity "Plus" "PZero" (applyBindings bindings (.fvar "x"))
        (applyBindings bindings (.fvar "y")) (applyBindings bindings (.fvar "z"))
  · obtain ⟨left,rest⟩ := Prod.mk.inj rightUnit
    obtain ⟨right,_⟩ := Prod.mk.inj rest
    rw [left,right]
    simpa only [applyBindings,List.map_cons,List.map_nil,zero,Bool.false_eq_true,↓reduceIte] using
      projectBinary_unit "Plus" "PZero" (by decide) (applyBindings bindings (.fvar "x")) false
  · obtain ⟨left,rest⟩ := Prod.mk.inj leftUnit
    obtain ⟨right,_⟩ := Prod.mk.inj rest
    rw [left,right]
    simpa only [applyBindings,List.map_cons,List.map_nil,zero,↓reduceIte] using
      projectBinary_unit "Plus" "PZero" (by decide) (applyBindings bindings (.fvar "x")) true
  · obtain ⟨left,rest⟩ := Prod.mk.inj commutative
    obtain ⟨right,_⟩ := Prod.mk.inj rest
    rw [left,right]
    simpa only [applyBindings,List.map_cons,List.map_nil] using
      projectBinary_commutativity "Plus" "PZero" (applyBindings bindings (.fvar "x"))
        (applyBindings bindings (.fvar "y"))

/-- Original raw source equivalence preserves the actual compiled
observation at typed first-order endpoints. Intermediates need not be typed. -/
theorem preservation_into_actual_core (base : BasePremiseEvaluator) (free : FreeTypeContext)
    (bound : List TypeExpr) {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right)
    (equivalent : EquationEquiv base source left right) :
    normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag left) =
      normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag right) := by
  have represented : Representation source core sourceRule replacement.rule .hashBag :=
    (checkRepresentation_iff _ _ _ _ _).mp (by cbv)
  have bare : replacement.rule.collectionRepresentation = .bare := by cbv
  rw [translated_eq_projectBinary represented bare leftTyped leftShape,
    translated_eq_projectBinary represented bare rightTyped rightShape]
  exact projectBinary_equationEquiv sourceRule.label "PZero" base source source_plain
    (by cbv) (by cbv) (by cbv) source_rows_projected equivalent

theorem original_equationEquiv_iff_actual_core_normalForm_eq
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right) :
    EquationEquiv base source left right ↔
      normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag left) =
        normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag right) :=
  ⟨preservation_into_actual_core base free bound leftTyped rightTyped leftShape rightShape,
    reflection_into_actual_core base free bound leftTyped rightTyped leftShape rightShape⟩

/-- Raw target-wrapper spelling is not an authored source constructor.
Shape-sensitive unwrapping therefore cannot be assumed compositional there. -/
def foreignWrappedBefore : Pattern := .apply "PPar" [.apply "Plus" [zero,.fvar "a"]]
def foreignWrappedAfter : Pattern := .apply "PPar" [.fvar "a"]

theorem foreign_wrapper_source_equivalent (base : BasePremiseEvaluator) :
    EquationEquiv base source foreignWrappedBefore foreignWrappedAfter :=
  equationEquiv_fill (.apply "PPar" [] .hole []) (unit_collapse_reflected base)

theorem foreign_wrapper_observations_separate :
    normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag foreignWrappedBefore) ≠
      normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag foreignWrappedAfter) := by cbv; decide

theorem foreign_wrapper_source_typing_refused :
    checkHasType source free [] foreignWrappedBefore proc = false ∧
      checkHasType source free [] foreignWrappedAfter proc = false := by cbv

theorem no_unrestricted_raw_lowering_preservation (base : BasePremiseEvaluator) :
    ¬ (∀ left right, EquationEquiv base source left right →
      normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag left) =
        normalForm (some "PZero") (translated core sourceRule replacement.rule .hashBag right)) := by
  intro claimed
  exact foreign_wrapper_observations_separate (claimed _ _ (foreign_wrapper_source_equivalent base))


/-- This declaration is read from the actual original source table. -/
def sourceUnitRule : GrammarRule := source.terms[0]?.getD
  {label := "missing",category := "Proc",params := [],syntaxPattern := []}

theorem source_terms : source.terms = [sourceUnitRule,sourceRule] := by cbv
theorem source_unit_label : sourceUnitRule.label = "PZero" := by cbv
theorem source_unit_in_core : sourceUnitRule ∈ core.terms := by cbv; exact .head _
theorem selected_core_declaration : renameUnitReferences sourceRule.label carrier.label carrier ∈ core.terms := by
  cbv
  exact .tail _ (.head _)
theorem unit_references_unchanged :
    renameUnitReferences sourceRule.label carrier.label sourceUnitRule = sourceUnitRule := by cbv

/-- Actual final declarations, including the extracted algebra metadata,
license the existing whole-pattern packing typing theorem. -/
theorem actual_core_signature : Signature source core sourceRule carrier := by
  refine ⟨?_,?_,selected_core_declaration,?_⟩
  · rw [source_terms]
    exact .tail _ (.head _)
  · intro rule member label
    rw [source_terms] at member
    rcases List.mem_cons.mp member with same | later
    · subst rule
      have impossible : ("PZero" : String) = "Plus" := by
        simpa only [source_unit_label,source_rule_label] using label
      exact ((by decide : ("PZero" : String) ≠ "Plus") impossible).elim
    · exact List.mem_singleton.mp later
  · intro rule member different
    rw [source_terms] at member
    rcases List.mem_cons.mp member with same | later
    · subst rule
      rw [unit_references_unchanged]
      exact source_unit_in_core
    · have same := List.mem_singleton.mp later
      subst rule
      exact (different rfl).elim

theorem actual_core_representation : Representation source core sourceRule carrier .hashBag :=
  (checkRepresentation_iff _ _ _ _ _).mp (by cbv)

theorem core_carrier_replacement_label : carrier.label = replacement.rule.label := by cbv

/-- Target typing, object shape and canonical metadata all follow from the
actual source typing and selected first-order syntax. -/
theorem lowered_admissible (free : FreeTypeContext) (bound : List TypeExpr)
    {pattern : Pattern} {type : TypeExpr} (typed : HasType source free bound pattern type)
    (firstOrder : FirstOrder pattern) :
    Admissible core free bound type (translated core sourceRule replacement.rule .hashBag pattern) := by
  have certified := translated_admissible («name» := "ps") (sort := "Proc")
    actual_core_signature actual_core_representation (by cbv) (by cbv) (by cbv) (by cbv) typed firstOrder
  simpa only [translated,core_carrier_replacement_label] using certified

/-- Exact correspondence with the actual retained target equation relation,
not merely equality of an external observation. Both relations are the
existing unrestricted raw EquationEquiv at their eligible endpoints. -/
theorem original_equationEquiv_iff_actual_core_equationEquiv
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    {left right : Pattern}
    (leftTyped : HasType source free bound left proc) (rightTyped : HasType source free bound right proc)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right) :
    EquationEquiv base source left right ↔
      EquationEquiv base core (translated core sourceRule replacement.rule .hashBag left)
        (translated core sourceRule replacement.rule .hashBag right) := by
  have first := lowered_admissible free bound leftTyped leftShape
  have second := lowered_admissible free bound rightTyped rightShape
  exact (original_equationEquiv_iff_actual_core_normalForm_eq base free bound
      leftTyped rightTyped leftShape rightShape).trans
    (actual_raw_source_equivalence base free bound ⟨_,first⟩ ⟨_,second⟩).symm

theorem lowered_unit_equation (base : BasePremiseEvaluator) :
    EquationEquiv base core
      (translated core sourceRule replacement.rule .hashBag (.apply "Plus" [zero,.fvar "a"]))
      (translated core sourceRule replacement.rule .hashBag (.fvar "a")) :=
  (original_equationEquiv_iff_actual_core_equationEquiv base free []
    (checkHasType_sound (by cbv)) (checkHasType_sound (by cbv))
    (checkFirstOrder_sound (by cbv)) (checkFirstOrder_sound (by cbv))).mp (unit_collapse_reflected base)

theorem lowered_nested_unit_permutation_equation (base : BasePremiseEvaluator) :
    EquationEquiv base core
      (translated core sourceRule replacement.rule .hashBag nestedBinary)
      (translated core sourceRule replacement.rule .hashBag flatBinary) :=
  (original_equationEquiv_iff_actual_core_equationEquiv base free []
    (checkHasType_sound (by cbv)) (checkHasType_sound (by cbv))
    (checkFirstOrder_sound (by cbv)) (checkFirstOrder_sound (by cbv))).mp (nested_unit_permutation_reflected base)

end BinarySource
#print axioms BinarySource.source_terms
#print axioms BinarySource.source_unit_label
#print axioms BinarySource.source_unit_in_core
#print axioms BinarySource.selected_core_declaration
#print axioms BinarySource.unit_references_unchanged
#print axioms BinarySource.actual_core_signature
#print axioms BinarySource.actual_core_representation
#print axioms BinarySource.core_carrier_replacement_label
#print axioms BinarySource.lowered_admissible
#print axioms BinarySource.original_equationEquiv_iff_actual_core_equationEquiv
#print axioms BinarySource.lowered_unit_equation
#print axioms BinarySource.lowered_nested_unit_permutation_equation
#print axioms BinarySource.source_rule_label
#print axioms BinarySource.source_equation_shapes
#print axioms BinarySource.source_plain
#print axioms BinarySource.source_rows_projected
#print axioms BinarySource.preservation_into_actual_core
#print axioms BinarySource.original_equationEquiv_iff_actual_core_normalForm_eq
#print axioms BinarySource.foreign_wrapper_source_equivalent
#print axioms BinarySource.foreign_wrapper_observations_separate
#print axioms BinarySource.foreign_wrapper_source_typing_refused
#print axioms BinarySource.no_unrestricted_raw_lowering_preservation
#print axioms BinarySource.actual_core_lowering_table
#print axioms BinarySource.reflection_into_actual_core
#print axioms BinarySource.unit_collapse_reflected
#print axioms BinarySource.nested_unit_permutation_reflected
#print axioms BinarySource.imported_accepted
#print axioms BinarySource.replacement_accepted
#print axioms BinarySource.selected_item
#print axioms BinarySource.selected_rule
#print axioms BinarySource.actual_replacement
#print axioms BinarySource.final_raw_agreement
#print axioms BinarySource.origins_retained
#print axioms BinarySource.binary_origin
#print axioms BinarySource.source_rows_eligible
#print axioms BinarySource.source_coherent
#print axioms BinarySource.source_valid
#print axioms BinarySource.reflection
#print axioms BinarySource.wrong_unit_not_declared
#print axioms BinarySource.cross_constructor_freshness_refused

#print axioms origin_eq_fields
#print axioms label_eq_fields
#print axioms constructor_refs_nullary
#print axioms selected_accepted
#print axioms core_accepted
#print axioms binary_origin_retained
#print axioms actual_rows_retained
#print axioms actual_equation_shapes
#print axioms actual_bare_theory
#print axioms actual_rows
#print axioms actual_source_normalizer
#print axioms actual_source_equivalence
#print axioms actual_raw_source_equivalence
#print axioms first_admissible
#print axioms second_admissible
#print axioms nested_unit_permutation_agreement
#print axioms nested_unit_permutation_raw_equivalence
#print axioms empty_and_singleton_collapse
#print axioms wrong_unit_profile_refused
#print axioms cross_constructor_profile_refused
#print axioms wrong_unit_separates_actual_row
#print axioms right_unit_member
#print axioms raw_tail_unit_instance
#print axioms raw_tail_is_not_object
#print axioms raw_tail_normal_forms_separate
#print axioms no_unrestricted_source_normalizer

namespace FocusView

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics BagNormalForm
open BagNormalForm.WithAuthoredEquations BagNormalForm.WithAuthoredEquations.AlgebraFocus

theorem carrier_category : carrier.category = "Proc" := by cbv

theorem scalar_admissible : Admissible core free [] proc (.fvar "a") :=
  ⟨.fvar rfl, rfl, rfl⟩

theorem scalar_equivalent_to_matching_view :
    EquationEquiv defaultBasePremises core (.fvar "a")
      (.collection .hashBag [.fvar "a"] none) := by
  have result := normalized_view_equivalent actual_bare_theory defaultBasePremises
    (by simpa only [carrier_category, proc] using scalar_admissible)
  simpa [normalForm, view, bagContents, splice] using result

theorem scalar_itself_has_no_collection_match {bindings : Bindings} :
    ¬ MatchRel (.collection .hashBag [.fvar "selected"] (some "rest")) (.fvar "a") bindings := by
  intro matched
  cases matched

theorem scalar_view_has_exact_collection_rest :
    MatchRel (.collection .hashBag [.fvar "selected"] (some "rest"))
      (view "PZero" (.fvar "a"))
      [("rest",.collection .hashBag [] none),("selected",.fvar "a")] := by
  exact match_view_single_rest (index := 0)
    (headBindings := [("selected",.fvar "a")]) (by decide) .fvar rfl

theorem scalar_residual_is_typed_collection_data :
    Admissible core free [] (.collection .hashBag proc) (.collection .hashBag [] none) := by
  have result := residual_admissible actual_bare_theory
    (by simpa only [carrier_category, proc] using scalar_admissible) 0
  simpa [carrier_category, proc, bagContents, splice] using result

theorem unit_equivalent_to_empty_matching_view :
    EquationEquiv defaultBasePremises core zero (.collection .hashBag [] none) := by
  have good : Admissible core free [] proc zero :=
    ⟨checkHasType_sound (by cbv),rfl,rfl⟩
  have result := normalized_view_equivalent actual_bare_theory defaultBasePremises
    (by simpa only [carrier_category, proc] using good)
  simpa [zero, normalForm, view, bagContents, splice] using result

theorem unit_view_has_no_selected_component (index : Nat) :
    (bagContents "PZero" [normalForm (some "PZero") zero])[index]? = none := by
  simp [zero, normalForm, bagContents, splice]

theorem nested_component_has_original_typed_zipper :
    ∃ (original : Pattern) (context : OneHoleContext),
      Admissible core free [] proc original ∧ context.fill original = first ∧
      normalForm (some "PZero") original = .fvar "a" ∧
      ∀ replacement, HasType core free [] replacement proc →
        HasType core free [] (context.fill replacement) proc := by
  have result := component_source_origin actual_bare_theory first
    (by simpa only [carrier_category, proc] using first_admissible)
    (component := .fvar "a") (by cbv; exact .head _)
  simpa only [carrier_category, proc] using result

theorem duplicate_source_zippers_are_distinct :
    let firstOrigin : OneHoleContext := .collection .hashBag [] .hole [.fvar "a"] none
    let secondOrigin : OneHoleContext := .collection .hashBag [.fvar "a"] .hole [] none
    firstOrigin.fill (.fvar "a") = .collection .hashBag [.fvar "a",.fvar "a"] none ∧
      secondOrigin.fill (.fvar "a") = .collection .hashBag [.fvar "a",.fvar "a"] none ∧
      firstOrigin ≠ secondOrigin := by decide

/-- A residual is data at its declared collection type. Applying the global
base-algebra normal form to that data would remove its required carrier. -/
theorem singleton_residual_boundary_separates :
    Admissible core free [] (.collection .hashBag proc) (.collection .hashBag [.fvar "b"] none) ∧
      normalForm (some "PZero") (.collection .hashBag [.fvar "b"] none) = .fvar "b" ∧
      ¬ HasType core free [] (.fvar "b") (.collection .hashBag proc) := by
  refine ⟨⟨.collection (.cons (.fvar rfl) (.nil _ _)),rfl,rfl⟩,by cbv,?_⟩
  intro typed
  cases typed with
  | fvar found => cases found

theorem wrong_kind_cannot_supply_base_focus :
    ¬ HasType core free [] (.collection .hashSet [.fvar "a"] none) proc := by
  intro typed
  have checked := checkHasType_complete_of_object typed rfl
  have refused : checkHasType core free [] (.collection .hashSet [.fvar "a"] none) proc = false := by cbv
  rw [refused] at checked
  contradiction

/-- The unit has equivalent nonempty representatives. A schema allowed to
consume it is therefore outside completeness of the empty component view. -/
theorem unit_redex_not_covered_by_empty_view :
    EquationEquiv defaultBasePremises core zero (.collection .hashBag [zero] none) ∧
      MatchRel (.collection .hashBag [.fvar "selected"] (some "rest"))
        (.collection .hashBag [zero] none)
        [("rest",.collection .hashBag [] none),("selected",zero)] ∧
      ¬ ∃ bindings, MatchRel (.collection .hashBag [.fvar "selected"] (some "rest"))
        (view "PZero" zero) bindings := by
  refine ⟨?_,?_,?_⟩
  · exact ((actual_raw_source_equivalence defaultBasePremises free []
      ⟨.collection .hashBag [zero] none,checkHasType_sound (by cbv),rfl,rfl⟩
      ⟨zero,checkHasType_sound (by cbv),rfl,rfl⟩).mpr (by cbv)).symm
  · exact .collection (by decide) (.cons 0 (by simp) .fvar .nilRest rfl)
  · rintro ⟨bindings, matched⟩
    have empty : view "PZero" zero = .collection .hashBag [] none := by cbv
    rw [empty] at matched
    cases matched with
    | collection _ bagMatch => cases bagMatch with
      | cons index within _ _ _ => simp at within

/-- Equal tokens yield two ordinary positional allocations. Their equality
as values does not authorize deleting an occurrence. -/
theorem duplicate_literal_allocations_retained :
    (matchPattern (.collection .hashBag [.fvar "selected"] (some "rest"))
      (.collection .hashBag [.fvar "a",.fvar "a"] none)).length = 2 := by cbv

#print axioms carrier_category
#print axioms scalar_admissible
#print axioms scalar_equivalent_to_matching_view
#print axioms scalar_itself_has_no_collection_match
#print axioms scalar_view_has_exact_collection_rest
#print axioms scalar_residual_is_typed_collection_data
#print axioms unit_equivalent_to_empty_matching_view
#print axioms unit_view_has_no_selected_component
#print axioms nested_component_has_original_typed_zipper
#print axioms duplicate_source_zippers_are_distinct
#print axioms singleton_residual_boundary_separates
#print axioms wrong_kind_cannot_supply_base_focus
#print axioms unit_redex_not_covered_by_empty_view
#print axioms duplicate_literal_allocations_retained

end FocusView


open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics BagNormalForm
open BagNormalForm.WithAuthoredEquations BagNormalForm.WithAuthoredEquations.AlgebraFocus

/-- The actual retained unit rows satisfy the source hub's finite scope checks. -/
theorem actual_reference_rows_aligned : ReferenceStep.EquationsAligned core := by
  intro row member
  have shapes : (row.left,row.right,row.premises) ∈
      [(.collection .hashBag [.fvar "x",zero] none,.fvar "x",[]),
       (.collection .hashBag [zero,.fvar "x"] none,.fvar "x",[])] := by
    rw [← actual_equation_shapes]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at shapes
  rcases shapes with shape | shape
  all_goals
    obtain ⟨leftEq,tailEq⟩ := Prod.mk.inj shape
    obtain ⟨rightEq,premiseEq⟩ := Prod.mk.inj tailEq
    simp only [ReferenceStep.equationAligned,leftEq,rightEq,premiseEq,List.all_nil]
    simp [ReferenceStep.notDeeper,ReferenceStep.notDeeperList,ReferenceStep.captureSitesOf,
      captureDepth,captureDepthList,zero,ReferenceStep.readsRaw,EquationSemantics.readsRaw,leftEq,rightEq,
      Match.binderFree,Match.binderFreeList]

theorem actual_reference_rows_unconditional : ReferenceStep.UnconditionalEquations core :=
  fun row member => (actual_rows row member).1

/-- The already certified actual .module normalizer serves the original
reference hub on its genuine typed fibre, with both authored rows retained. -/
theorem actual_reference_normalizer (relEnv : Engine.RelationEnv) (freeTypes : FreeTypeContext)
    (boundTypes : List TypeExpr) :
    Complete.Coherence.Normalizer
      (fun (left right : {pattern // Admissible core freeTypes boundTypes proc pattern}) =>
        ReferenceStep.EquationStep relEnv core left.1 right.1)
      (normalizeSource actual_bare_theory (engineBasePremises relEnv) freeTypes boundTypes proc rfl) :=
  reference_sourceNormalizer (language := core) (bag := carrier) (unit := some "PZero")
    actual_bare_theory actual_rows actual_reference_rows_aligned relEnv freeTypes boundTypes proc rfl

theorem actual_reference_equivalence (relEnv : Engine.RelationEnv) (freeTypes : FreeTypeContext)
    (boundTypes : List TypeExpr) (left right : {pattern // Admissible core freeTypes boundTypes proc pattern}) :
    ReferenceStep.Equivalent relEnv core left.1 right.1 ↔
      normalForm (some "PZero") left.1 = normalForm (some "PZero") right.1 :=
  reference_equivalent_iff_normalForm_eq (language := core) (bag := carrier) (unit := some "PZero")
    (free := freeTypes) (bound := boundTypes) (type := proc)
    actual_bare_theory actual_rows actual_reference_rows_aligned relEnv left.2 right.2 rfl

theorem nested_unit_permutation_reference_equivalence (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv core first second :=
  (actual_reference_equivalence relEnv free [] ⟨first,first_admissible⟩ ⟨second,second_admissible⟩).mpr (by cbv)

namespace BinarySource

open BinaryCollectionLowering BinaryCollectionInterpretation GeneralFirstOrderProjection

theorem source_reference_rows_aligned : ReferenceStep.EquationsAligned source := by
  intro row member
  have shapes : (row.left,row.right,row.premises) ∈
      [(.apply "Plus" [.apply "Plus" [.fvar "x",.fvar "y"],.fvar "z"],
        .apply "Plus" [.fvar "x",.apply "Plus" [.fvar "y",.fvar "z"]],[]),
       (.apply "Plus" [.fvar "x",zero],.fvar "x",[]),
       (.apply "Plus" [zero,.fvar "x"],.fvar "x",[]),
       (.apply "Plus" [.fvar "x",.fvar "y"],.apply "Plus" [.fvar "y",.fvar "x"],[])] := by
    rw [← source_equation_shapes]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at shapes
  rcases shapes with shape | shape | shape | shape
  all_goals
    obtain ⟨leftEq,tailEq⟩ := Prod.mk.inj shape
    obtain ⟨rightEq,premiseEq⟩ := Prod.mk.inj tailEq
    simp only [ReferenceStep.equationAligned,leftEq,rightEq,premiseEq,List.all_nil]
    simp [ReferenceStep.notDeeper,ReferenceStep.notDeeperList,ReferenceStep.captureSitesOf,
      captureDepth,captureDepthList,zero,ReferenceStep.readsRaw,EquationSemantics.readsRaw,leftEq,rightEq,
      Match.binderFree,Match.binderFreeList]

theorem source_reference_rows_unconditional : ReferenceStep.UnconditionalEquations source :=
  fun row member => (source_plain row member).1

/-- Actual constructor replacement, algebra extraction and core lowering
preserve and reflect the original reference equation theory at the typed
first-order source endpoints. Both endpoint typing and the lowering are real
operations; no semantic preservation premise is supplied by the caller. -/
theorem original_reference_equivalence_iff_actual_core
    (relEnv : Engine.RelationEnv) (freeTypes : FreeTypeContext) (boundTypes : List TypeExpr)
    {left right : Pattern}
    (leftTyped : HasType source freeTypes boundTypes left proc)
    (rightTyped : HasType source freeTypes boundTypes right proc)
    (leftShape : FirstOrder left) (rightShape : FirstOrder right) :
    ReferenceStep.Equivalent relEnv source left right ↔
      ReferenceStep.Equivalent relEnv core (translated core sourceRule replacement.rule .hashBag left)
        (translated core sourceRule replacement.rule .hashBag right) :=
  (ReferenceStep.equivalent_iff_unconditional (relEnv := relEnv) (language := source)
    source_reference_rows_unconditional source_reference_rows_aligned).symm.trans
    ((original_equationEquiv_iff_actual_core_equationEquiv (engineBasePremises relEnv)
      freeTypes boundTypes leftTyped rightTyped leftShape rightShape).trans
      (ReferenceStep.equivalent_iff_unconditional (relEnv := relEnv) (language := core)
        actual_reference_rows_unconditional actual_reference_rows_aligned))

#print axioms source_reference_rows_aligned
#print axioms source_reference_rows_unconditional
#print axioms original_reference_equivalence_iff_actual_core

end BinarySource

/-- The selected normalized component retains its actual source
path through the nested carrier; sorting has not invented a child index. -/
def selectedAOccurrence : SourceOccurrence :=
  {original := .fvar "a",address := [1,1],
    context := .collection .hashBag [zero]
      (.collection .hashBag [.fvar "b"] .hole [] none) [zero] none,
    value := .fvar "a"}

theorem selected_a_occurrence :
    (normalizedOccurrences "PZero" first)[0]? = some selectedAOccurrence := by cbv

def selectedBindings : Bindings :=
  [("rest",.collection .hashBag [.fvar "b"] none),("selected",.fvar "a")]

/-- A match through the actual declared algebra has an ordinary source
presentation and the physical source occurrence which supplies its component.
The rest stays collection data. -/
theorem selected_reference_source_match (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
        (.collection .hashBag [.fvar "selected"] (some "rest")) first selectedBindings ∧
      Admissible core free [] proc selectedAOccurrence.original ∧
      selectedAOccurrence.context.fill selectedAOccurrence.original = first ∧
      ReferenceStep.Equivalent relEnv core selectedAOccurrence.original selectedAOccurrence.value ∧
      contextAddress selectedAOccurrence.context = selectedAOccurrence.address := by
  have result := tagged_reference_presentation (language := core) (bag := carrier) (unitLabel := "PZero")
    (free := free) (bound := []) (source := first)
    actual_bare_theory actual_reference_rows_unconditional actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using first_admissible)
    (schema := .fvar "selected") (restName := "rest") (bindings := selectedBindings)
    (headBindings := [("selected",.fvar "a")]) selected_a_occurrence .fvar (by cbv)
  simpa only [FocusView.carrier_category,proc] using result

/-- Unit administration and two equal live occurrences have separate actual
source addresses in this .module instance. -/
def duplicateTaggedSource : Pattern :=
  .collection .hashBag [zero,.collection .hashBag [.fvar "a",.fvar "a"] none] none

theorem duplicate_tagged_source_typed : Admissible core free [] proc duplicateTaggedSource :=
  ⟨checkHasType_sound (by cbv),rfl,rfl⟩

theorem duplicate_tagged_source_account :
    (normalizedOccurrences "PZero" duplicateTaggedSource).map SourceOccurrence.address = [[1,0],[1,1]] ∧
      (unitOccurrences "PZero" duplicateTaggedSource).map SourceOccurrence.address = [[0]] ∧
      (normalizedOccurrences "PZero" duplicateTaggedSource).length = 2 := by cbv

/-- The empty matching view still omits genuine unit-sensitive source
redexes. The reference-hub bridge retains this negative instead of licensing
completeness or manufacturing a physical occurrence for the virtual unit. -/
theorem unit_reference_view_incomplete :
    ReferenceStep.Equivalent Engine.RelationEnv.empty core zero (.collection .hashBag [zero] none) ∧
      ¬ ∃ bindings,MatchSpec.MatchRel (.collection .hashBag [.fvar "selected"] (some "rest"))
        (view "PZero" zero) bindings := by
  have separator := FocusView.unit_redex_not_covered_by_empty_view
  exact ⟨(ReferenceStep.equivalent_iff_unconditional actual_reference_rows_unconditional
    actual_reference_rows_aligned).mp separator.1,separator.2.2⟩

#print axioms actual_reference_rows_aligned
#print axioms actual_reference_rows_unconditional
#print axioms actual_reference_normalizer
#print axioms actual_reference_equivalence
#print axioms nested_unit_permutation_reference_equivalence
#print axioms selected_a_occurrence
#print axioms selected_reference_source_match
#print axioms duplicate_tagged_source_typed
#print axioms duplicate_tagged_source_account
#print axioms unit_reference_view_incomplete



namespace UnitSelection

/-- This actual source has no physical token or unit occurrence. -/
def emptySource : Pattern := .collection .hashBag [] none

theorem empty_source_admissible : Admissible core free [] proc emptySource :=
  ⟨checkHasType_sound (by cbv),rfl,rfl⟩

def schema : Pattern := .collection .hashBag [.fvar "selected"] (some "rest")
def emptyBindings : Bindings := [("rest",emptySource),("selected",zero)]

/-- The previously missing unit-sensitive match now has a genuine reference
presentation, while its source occurrence account remains empty. -/
theorem virtual_unit_from_empty_source (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core) schema emptySource emptyBindings ∧
      Admissible core free [] (.collection .hashBag proc) emptySource ∧
      sourceOccurrences "PZero" emptySource = [] ∧ normalizedOccurrences "PZero" emptySource = [] := by
  have recovered := zero_component_reference_presentation
    (language := core) (bag := carrier) (unitLabel := "PZero") (free := free) (bound := [])
    (source := emptySource) actual_bare_theory actual_reference_rows_unconditional
    actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using empty_source_admissible)
    (schema := .fvar "selected") (restName := "rest") (headBindings := [("selected",zero)])
    (bindings := emptyBindings) .fvar (by cbv)
  exact ⟨recovered.1,⟨.collection (.nil _ _),rfl,rfl⟩,by cbv,by cbv⟩

def duplicateBindings : Bindings :=
  [("rest",.collection .hashBag [.fvar "a",.fvar "a"] none),("selected",zero)]

/-- A virtual unit consumes zero physical components: both equal live
occurrences and the original source-unit administration keep their addresses. -/
theorem virtual_unit_keeps_duplicate_account (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
        schema duplicateTaggedSource duplicateBindings ∧
      (normalizedOccurrences "PZero" duplicateTaggedSource).map SourceOccurrence.address = [[1,0],[1,1]] ∧
      (unitOccurrences "PZero" duplicateTaggedSource).map SourceOccurrence.address = [[0]] := by
  have recovered := zero_component_reference_presentation
    (language := core) (bag := carrier) (unitLabel := "PZero") (free := free) (bound := [])
    (source := duplicateTaggedSource) actual_bare_theory actual_reference_rows_unconditional
    actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using duplicate_tagged_source_typed)
    (schema := .fvar "selected") (restName := "rest") (headBindings := [("selected",zero)])
    (bindings := duplicateBindings) .fvar (by cbv)
  exact ⟨recovered.1,duplicate_tagged_source_account.1,duplicate_tagged_source_account.2.1⟩

theorem wrong_unit_does_not_match_expansion :
    matchPattern (.collection .hashBag [.apply "WrongUnit" []] (some "rest"))
      (unitExpansion "PZero" (normalForm (some "PZero") emptySource)) = [] := by decide +kernel

/-- A grouped presentation is allowed by the actual declared singleton and
flattening laws, even though the component-only view does not enumerate it. -/
def groupedSource : Pattern := .collection .hashBag [second] none

def groupedBindings : Bindings := [("rest",emptySource),("selected",second)]

theorem grouped_source_admissible : Admissible core free [] proc groupedSource :=
  ⟨checkHasType_sound (by cbv),rfl,rfl⟩

theorem grouped_reference_equivalence (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv core second groupedSource :=
  (actual_reference_equivalence relEnv free [] ⟨second,second_admissible⟩
    ⟨groupedSource,grouped_source_admissible⟩).mpr (by cbv)

theorem grouped_source_match (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core) schema second groupedBindings :=
  ⟨groupedSource,grouped_reference_equivalence relEnv,by decide +kernel⟩

theorem grouped_capture_not_in_component_view :
    groupedBindings ∉ matchPattern schema (view "PZero" (normalForm (some "PZero") second)) := by
  cbv
  intro member
  rcases List.mem_cons.mp member with impossible | remaining
  · cases impossible
  · cases List.mem_singleton.mp remaining

/-- The selected raw child is proper in its expanded representative, but
has exactly the original source value. A strict canonical source-size bound
therefore does not follow from raw structural descent through this quotient. -/
theorem grouped_child_has_no_strict_canonical_bound :
    groupedBindings ∈ matchPattern schema groupedSource ∧
      sizeOf second < sizeOf groupedSource ∧
      groupedBindings.lookup "selected" = some second ∧
      ¬ sizeOf (CanonicalBags.canon ((groupedBindings.lookup "selected").getD zero)) <
        sizeOf (CanonicalBags.canon second) := by
  refine ⟨?_,by decide +kernel,rfl,?_⟩
  · cbv
    exact .head _
  · change ¬ sizeOf (CanonicalBags.canon second) < sizeOf (CanonicalBags.canon second)
    exact Nat.lt_irrefl _

#print axioms empty_source_admissible
#print axioms virtual_unit_from_empty_source
#print axioms virtual_unit_keeps_duplicate_account
#print axioms wrong_unit_does_not_match_expansion
#print axioms grouped_source_admissible
#print axioms grouped_reference_equivalence
#print axioms grouped_source_match
#print axioms grouped_capture_not_in_component_view
#print axioms grouped_child_has_no_strict_canonical_bound

end UnitSelection

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource.GroupedSelection

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec PatternTreeSize
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics BagNormalForm
open BagNormalForm.WithAuthoredEquations BagNormalForm.WithAuthoredEquations.AlgebraFocus

def tags : List SourceOccurrence := normalizedOccurrences "PZero" first

theorem whole_group_allocation : ([tags],[]) ∈ groupedOccurrences 1 tags := by
  apply (mem_groupedOccurrences 1).mpr
  exact ⟨rfl,by simp⟩

theorem whole_group_has_actual_origins :
    (tags.map SourceOccurrence.value) = [.fvar "a",.fvar "b"] ∧
      (tags.map SourceOccurrence.address) = [[1,1],[1,0]] ∧
      (unitOccurrences "PZero" first).map SourceOccurrence.address = [[0],[2]] := by cbv

/-- Whole-group selection, missing from the individual-component view, is
an actual ordinary match at a finite source-equivalent presentation. -/
theorem whole_group_reference_match (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
      UnitSelection.schema first UnitSelection.groupedBindings := by
  have result := grouped_reference_presentation actual_bare_theory
    actual_reference_rows_unconditional actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using first_admissible)
    whole_group_allocation (single_group_capture_match "PZero" "selected" "rest" (by decide) tags [])
  have shownBindings :
      [("rest",Pattern.collection .hashBag (([] : List SourceOccurrence).map SourceOccurrence.value) none),
       ("selected",collapse "PZero" (tags.map SourceOccurrence.value))] =
        UnitSelection.groupedBindings := by cbv
  rw [shownBindings] at result
  exact result

/-- Two virtual unit slots are allowed without consuming or copying a
physical token. The live component row remains the residual's data. -/
theorem two_empty_groups_allocation : ([[],[]],tags) ∈ groupedOccurrences 2 tags := by
  apply (mem_groupedOccurrences 2).mpr
  exact ⟨rfl,by simp⟩

theorem two_virtual_units_reference_match (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
      (.collection .hashBag [zero,zero] (some "rest")) first [("rest",second)] := by
  apply grouped_reference_presentation actual_bare_theory actual_reference_rows_unconditional
    actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using first_admissible) two_empty_groups_allocation
  have shown : groupedView "PZero" [[],[]] tags =
      .collection .hashBag [zero,zero,.fvar "a",.fvar "b"] none := by cbv
  rw [shown]
  exact matchPattern_sound (by cbv; exact .head _)

theorem virtual_units_leave_physical_account :
    (([[],[]] : List (List SourceOccurrence)).flatten ++ tags ++ unitOccurrences "PZero" first).Perm
      (sourceOccurrences "PZero" first) :=
  grouped_occurrence_account two_empty_groups_allocation

/-- An empty group and a whole nested group can be matched together; this
uses literal unit and nested-collection schemas in the ordinary matcher. -/
theorem unit_and_group_reference_match (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
      (.collection .hashBag [zero,.collection .hashBag [.fvar "left",.fvar "right"] none] (some "rest"))
      first [("left",.fvar "a"),("right",.fvar "b"),("rest",.collection .hashBag [] none)] := by
  have allocation : ([[],tags],[]) ∈ groupedOccurrences 2 tags :=
    (mem_groupedOccurrences 2).mpr ⟨rfl,by simp⟩
  apply grouped_reference_presentation actual_bare_theory actual_reference_rows_unconditional
    actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using first_admissible) allocation
  have shown : groupedView "PZero" [[],tags] [] = .collection .hashBag [zero,second] none := by cbv
  rw [shown]
  exact matchPattern_sound (by cbv; exact .head _)

def duplicateTags : List SourceOccurrence := normalizedOccurrences "PZero" duplicateTaggedSource

/-- Two equal-valued tokens can go to different groups without identifying
their original positions. -/
theorem equal_values_distinct_groups :
    ([duplicateTags.take 1,duplicateTags.drop 1],[]) ∈ groupedOccurrences 2 duplicateTags ∧
      (duplicateTags.take 1).map SourceOccurrence.value = (duplicateTags.drop 1).map SourceOccurrence.value ∧
      (duplicateTags.take 1).map SourceOccurrence.address ≠ (duplicateTags.drop 1).map SourceOccurrence.address := by
  refine ⟨(mem_groupedOccurrences 2).mpr ⟨by cbv,?_⟩,by cbv,by cbv; decide +kernel⟩
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.take_append_drop]
  exact .refl _

/-- Using one equal-valued physical occurrence twice is not an allocation
of the two different source occurrences. -/
theorem repeated_origin_refused :
    (duplicateTags.take 1 ++ duplicateTags.take 1,[]) ∉ occurrenceSplits duplicateTags := by
  rw [mem_occurrenceSplits]
  intro account
  have addresses := account.map SourceOccurrence.address
  have refused : ¬ ((duplicateTags.take 1 ++ duplicateTags.take 1 ++ []).map SourceOccurrence.address).Perm
      (duplicateTags.map SourceOccurrence.address) := by cbv; decide +kernel
  exact refused addresses

/-- The general converse is instantiated on the actual module's raw
singleton presentation and ordinary source match, rather than assumed. -/
theorem actual_grouped_source_covered (relEnv : Engine.RelationEnv) :
    ∃ selected residual originalSelected originalResidual,
      (selected,residual) ∈ occurrenceSplits (normalizedOccurrences "PZero" second) ∧
      UnitSelection.groupedBindings.lookup "selected" = some originalSelected ∧
      UnitSelection.groupedBindings.lookup "rest" = some originalResidual ∧
      ReferenceStep.Equivalent relEnv core originalSelected (collapse "PZero" (selected.map SourceOccurrence.value)) ∧
      ReferenceStep.Equivalent relEnv core originalResidual
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
        UnitSelection.schema second
        [("rest",.collection .hashBag (residual.map SourceOccurrence.value) none),
         ("selected",collapse "PZero" (selected.map SourceOccurrence.value))] ∧
      Admissible core free [] (.collection .hashBag proc)
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      nodes (collapse "PZero" (selected.map SourceOccurrence.value)) ≤ nodes (normalForm (some "PZero") second) := by
  have result := source_capture_covered (bindings := UnitSelection.groupedBindings)
    actual_bare_theory actual_rows actual_reference_rows_aligned relEnv
    (by simpa only [FocusView.carrier_category,proc] using second_admissible)
    (by simpa only [FocusView.carrier_category,proc,UnitSelection.groupedSource] using UnitSelection.grouped_source_admissible)
    (UnitSelection.grouped_reference_equivalence relEnv) (selectedName := "selected") (restName := "rest")
    (by decide) (.cons 0 (by decide) .fvar .nilRest (by cbv))
  simpa only [FocusView.carrier_category,proc,UnitSelection.schema] using result

/-- Positive consumption and a nonempty residual earn strict descent. -/
theorem strict_group_progress :
    nodes (collapse "PZero" ((tags.take 1).map SourceOccurrence.value)) <
      nodes (normalForm (some "PZero") first) := by
  apply split_group_nodes_lt (selected := tags.take 1) (residual := tags.drop 1)
  · apply mem_occurrenceSplits.mpr
    rw [List.take_append_drop]
    exact .refl _
  · cbv; simp
  · cbv; simp

/-- The general non-strict bound is sharp for the actual authored
singleton/flattening theory. -/
theorem whole_group_bound_is_not_strict :
    nodes (collapse "PZero" (tags.map SourceOccurrence.value)) = nodes (normalForm (some "PZero") first) ∧
      ¬ nodes (collapse "PZero" (tags.map SourceOccurrence.value)) < nodes (normalForm (some "PZero") first) := by
  have same : collapse "PZero" (tags.map SourceOccurrence.value) = normalForm (some "PZero") first := by
    rw [tags,normalizedOccurrences_values,collapse_contents (rootNormal_normalForm "PZero" first)]
  rw [same]
  exact ⟨rfl,Nat.lt_irrefl _⟩

theorem wrong_unit_still_refused :
    matchPattern (.collection .hashBag [.apply "WrongUnit" []] (some "rest"))
      (groupedView "PZero" [[],[]] tags) = [] := by cbv

/-- The residual of an empty selection remains collection data even when
there are no physical source components. -/
theorem empty_group_residual_keeps_data :
    Admissible core free [] (.collection .hashBag proc) UnitSelection.emptySource ∧
      groupedView "PZero" [[]] [] = .collection .hashBag [zero] none ∧
      normalizedOccurrences "PZero" UnitSelection.emptySource = [] := by
  exact ⟨⟨.collection (.nil _ _),rfl,rfl⟩,rfl,by cbv⟩

/-- Recorded sizes are enumeration costs, not logical derivation counts. -/
theorem finite_allocation_sizes :
    (occurrenceSplits ([] : List Nat)).length = 1 ∧
      (occurrenceSplits [0]).length = 2 ∧
      (occurrenceSplits [0,1]).length = 6 ∧
      (occurrenceSplits [0,1,2]).length = 24 ∧
      (groupedOccurrences 2 [0,1]).length = 22 := by cbv

#print axioms whole_group_allocation
#print axioms whole_group_has_actual_origins
#print axioms whole_group_reference_match
#print axioms two_empty_groups_allocation
#print axioms two_virtual_units_reference_match
#print axioms virtual_units_leave_physical_account
#print axioms unit_and_group_reference_match
#print axioms equal_values_distinct_groups
#print axioms repeated_origin_refused
#print axioms actual_grouped_source_covered
#print axioms strict_group_progress
#print axioms whole_group_bound_is_not_strict
#print axioms wrong_unit_still_refused
#print axioms empty_group_residual_keeps_data
#print axioms finite_allocation_sizes

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource.GroupedSelection

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource.GroupedSelection

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec PatternTreeSize
open Mettapedia.GSLT.LanguageDef WellSorted EquationSemantics BagNormalForm
open BagNormalForm.WithAuthoredEquations BagNormalForm.WithAuthoredEquations.AlgebraFocus

def rawCaptureBindings : Bindings :=
  [("rest",.collection .hashBag [] none),("selected",openTail)]

/-- The unrestricted original source can match an open-tail capture from a
canonical scalar. Raw typing alone therefore does not imply the finite
admissible grouping theorem's normal-form bound. -/
theorem raw_presented_capture_breaks_normal_bound (relEnv : Engine.RelationEnv) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv core)
      UnitSelection.schema (.fvar "a") rawCaptureBindings ∧
      HasType core free [] (.collection .hashBag [openTail] none) proc ∧
      isObjectPattern (.collection .hashBag [openTail] none) = false ∧
      rawCaptureBindings.lookup "selected" = some openTail ∧
      nodes (normalForm (some "PZero") (.fvar "a")) < nodes (normalForm (some "PZero") openTail) := by
  have zeroGood : Admissible core free [] (.base carrier.category) zero :=
    declared_unit_admissible (language := core) actual_bare_theory (engineBasePremises relEnv) free []
  have atomTyped : HasType core free [] (.fvar "a") (.base carrier.category) :=
    .fvar (by rw [FocusView.carrier_category]; rfl)
  obtain ⟨parameterName,carrierShape⟩ := actual_bare_theory.bareShape
  have rawTyped : HasType core free [] openTail (.base carrier.category) :=
    .collectionConstructor actual_bare_theory.bagAuthored carrierShape
      (.cons atomTyped (.cons zeroGood.typed (.nil _ _)))
  have outerTyped : HasType core free [] (.collection .hashBag [openTail] none)
      (.base carrier.category) :=
    .collectionConstructor actual_bare_theory.bagAuthored carrierShape (.cons rawTyped (.nil _ _))
  have comparedAlgebra := actual_bare_theory.bagAlgebraRule
  have actualAlgebra : AlgebraRule core carrier .hashBag { flatten := true,unit := some "PZero" } :=
    ⟨comparedAlgebra.authored,comparedAlgebra.declared,comparedAlgebra.selfSorted,comparedAlgebra.unitAuthored⟩
  have singletonEquivalent : EquationEquiv (engineBasePremises relEnv) core
      (.collection .hashBag [openTail] none) openTail :=
    .rel _ _ (.inContext .hole (.inr (.singleton actualAlgebra rfl ⟨free,[],outerTyped⟩)))
  have rawEquivalent : EquationEquiv (engineBasePremises relEnv) core openTail (.fvar "a") :=
    .rel _ _ (.inContext .hole (.inl (raw_tail_unit_instance (engineBasePremises relEnv))))
  have equivalent := (ReferenceStep.equivalent_iff_unconditional actual_reference_rows_unconditional
    actual_reference_rows_aligned).mp (.trans _ _ _ rawEquivalent.symm singletonEquivalent.symm)
  refine ⟨⟨.collection .hashBag [openTail] none,equivalent,?_⟩,?_,?_,rfl,?_⟩
  · exact matchRel_complete (.collection (by decide) (.cons 0 (by decide) .fvar .nilRest (by cbv)))
  · simpa only [FocusView.carrier_category,proc] using outerTyped
  · cbv
  · cbv

#print axioms raw_presented_capture_breaks_normal_bound

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls.ParMonoidSource.GroupedSelection
