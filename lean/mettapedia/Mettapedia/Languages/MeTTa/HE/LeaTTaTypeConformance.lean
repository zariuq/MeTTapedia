import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaSpecSoundness
import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeImage
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.TypeSoundness
import Std.Data.HashMap.Lemmas

/-!
# LeaTTa conformance to the named spec type refinements

The published spec type layer and its named R1/R2 refinements use native HE
atoms throughout.  Existing matcher and merge seals state their observational
theory using LeaTTa-valued valuations.  This downstream module first connects
those two model languages, then uses the connection to state the reachable
type-binding invariant consumed by reduced-type and application inference.

The total decoding map below is only a semantic bridge.  Its extra cases make
the function total on LeaTTa's larger grounded runtime domain; translated HE
atoms round-trip exactly.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open LeaTTaBridge
open LeaTTaSpecConformance
open Spec.Type
open Spec.Type.Conformance
open Spec.Type.RuntimeRefinement

/-! ## Native/LeaTTa model-language bridge -/

/-- Total decoding of LeaTTa grounded payloads into the spec atom language.
Runtime-only constructors are retained as explicitly tagged custom
payloads; no conformance claim is made for their operational behavior. -/
def fromLeaTTaGround : Metta.Ground → GroundedValue
  | .int value => .int value
  | .float _ => .custom "%LeaFloat%" ""
  | .str value => .string value
  | .bool value => .bool value
  | .unit => .custom "%LeaUnit%" ""
  | .error message => .custom "%LeaError%" message
  | .external typeName payload => .custom typeName payload
  | .bindings relations => .custom "%LeaBindings%" (reprStr relations)

mutual

/-- Total structural decoding from LeaTTa atoms to native HE atoms. -/
def fromLeaTTaAtom : Metta.Atom → Atom
  | .sym name => .symbol name
  | .var name => .var name
  | .gnd value => .grounded (fromLeaTTaGround value)
  | .expr atoms => .expression (fromLeaTTaAtoms atoms)

/-- List companion of `fromLeaTTaAtom`. -/
def fromLeaTTaAtoms : List Metta.Atom → List Atom
  | [] => []
  | atom :: atoms => fromLeaTTaAtom atom :: fromLeaTTaAtoms atoms

end

@[simp] theorem fromLeaTTaGround_toLeaTTaGround (value : GroundedValue) :
    fromLeaTTaGround (toLeaTTaGround value) = value := by
  cases value <;> rfl

@[simp] theorem toLeaTTaAtoms_eq_map (atoms : List Atom) :
    toLeaTTaAtoms atoms = atoms.map toLeaTTaAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [toLeaTTaAtoms, ih]

@[simp] theorem fromLeaTTaAtoms_eq_map (atoms : List Metta.Atom) :
    fromLeaTTaAtoms atoms = atoms.map fromLeaTTaAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [fromLeaTTaAtoms, ih]

mutual

@[simp] theorem fromLeaTTaAtom_toLeaTTaAtom (atom : Atom) :
    fromLeaTTaAtom (toLeaTTaAtom atom) = atom := by
  cases atom with
  | symbol | var | grounded =>
      simp [toLeaTTaAtom, fromLeaTTaAtom]
  | expression atoms =>
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_toLeaTTaAtoms atoms)
termination_by 2 * sizeOf atom

@[simp] theorem fromLeaTTaAtoms_toLeaTTaAtoms (atoms : List Atom) :
    fromLeaTTaAtoms (toLeaTTaAtoms atoms) = atoms := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_toLeaTTaAtom atom)
        (fromLeaTTaAtoms_toLeaTTaAtoms atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

mutual

/-- Translating a native valuation after applying it is the same as applying
its pointwise translation in the LeaTTa model language. -/
theorem toLeaTTaAtom_applyTypeValuation
    (valuation : String → Atom) (atom : Atom) :
    toLeaTTaAtom (applyTypeValuation valuation atom) =
      applyClassSolution (fun name => toLeaTTaAtom (valuation name))
        (toLeaTTaAtom atom) := by
  cases atom with
  | symbol | var | grounded =>
      simp [applyTypeValuation, toLeaTTaAtom, applyClassSolution]
  | expression atoms =>
      rw [applyTypeValuation, toLeaTTaAtom, toLeaTTaAtom,
        applyClassSolution]
      exact congrArg Metta.Atom.expr
        (toLeaTTaAtoms_applyTypeValuation valuation atoms)
termination_by 2 * sizeOf atom

/-- List companion of `toLeaTTaAtom_applyTypeValuation`. -/
theorem toLeaTTaAtoms_applyTypeValuation
    (valuation : String → Atom) (atoms : List Atom) :
    toLeaTTaAtoms (atoms.map (applyTypeValuation valuation)) =
      (toLeaTTaAtoms atoms).map
        (applyClassSolution (fun name => toLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (toLeaTTaAtom_applyTypeValuation valuation atom)
        (toLeaTTaAtoms_applyTypeValuation valuation atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

mutual

/-- Structural Boolean equality is exact on the native translation image.
Translated grounded payloads contain no host floats, so the non-reflexive NaN
corner of LeaTTa's larger runtime atom domain is absent. -/
theorem toLeaTTaAtom_beq_eq_true_iff (left right : Atom) :
    Metta.Atom.beq (toLeaTTaAtom left) (toLeaTTaAtom right) = true ↔
      left = right := by
  cases left with
  | symbol leftName =>
      cases right <;>
        simp [toLeaTTaAtom, Metta.Atom.beq]
  | var leftName =>
      cases right <;>
        simp [toLeaTTaAtom, Metta.Atom.beq]
  | grounded leftValue =>
      cases right with
      | symbol | var | expression =>
          simp [toLeaTTaAtom, Metta.Atom.beq]
      | grounded rightValue =>
          simp only [toLeaTTaAtom, Metta.Atom.beq,
            Atom.grounded.injEq]
          cases leftValue <;> cases rightValue <;>
            simp [toLeaTTaGround, Metta.Ground.beq]
  | expression leftAtoms =>
      cases right with
      | symbol | var | grounded =>
          simp [toLeaTTaAtom, Metta.Atom.beq]
      | expression rightAtoms =>
          simpa [toLeaTTaAtom, Metta.Atom.beq] using
            (toLeaTTaAtoms_beqList_eq_true_iff leftAtoms rightAtoms)
termination_by 2 * (sizeOf left + sizeOf right)

/-- List companion of `toLeaTTaAtom_beq_eq_true_iff`. -/
theorem toLeaTTaAtoms_beqList_eq_true_iff
    (left right : List Atom) :
    Metta.Atom.beqList (toLeaTTaAtoms left) (toLeaTTaAtoms right) = true ↔
      left = right := by
  cases left with
  | nil =>
      cases right <;> simp [toLeaTTaAtoms, Metta.Atom.beqList]
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [toLeaTTaAtoms, Metta.Atom.beqList]
      | cons rightHead rightTail =>
          simp only [toLeaTTaAtoms, Metta.Atom.beqList,
            Bool.and_eq_true, List.cons.injEq]
          rw [toLeaTTaAtom_beq_eq_true_iff,
            toLeaTTaAtoms_beqList_eq_true_iff]
termination_by 2 * (sizeOf left + sizeOf right) + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Exact image provenance supplies the inverse round trip needed at the
native/runtime representation boundary. -/
theorem toLeaTTaAtom_fromLeaTTaAtom_of_heImage
    {leaAtom : Metta.Atom} (image : LeaAtomHEImage leaAtom) :
    toLeaTTaAtom (fromLeaTTaAtom leaAtom) = leaAtom := by
  obtain ⟨atom, rfl⟩ := image
  simp

/-- List companion of `toLeaTTaAtom_fromLeaTTaAtom_of_heImage`. -/
theorem toLeaTTaAtoms_fromLeaTTaAtoms_of_heImage
    {leaAtoms : List Metta.Atom} (image : LeaAtomsHEImage leaAtoms) :
    toLeaTTaAtoms (fromLeaTTaAtoms leaAtoms) = leaAtoms := by
  obtain ⟨atoms, rfl⟩ := image
  simp

/-- Image provenance for a nonempty expression exposes exact round trips for
its head and tail independently. -/
theorem heImage_expression_roundtrip_parts
    {head : Metta.Atom} {tail : List Metta.Atom}
    (image : LeaAtomHEImage (.expr (head :: tail))) :
    toLeaTTaAtom (fromLeaTTaAtom head) = head ∧
      toLeaTTaAtoms (fromLeaTTaAtoms tail) = tail := by
  have roundtrip := toLeaTTaAtom_fromLeaTTaAtom_of_heImage image
  simpa [fromLeaTTaAtom, toLeaTTaAtom,
    fromLeaTTaAtoms, toLeaTTaAtoms] using
      Metta.Atom.expr.inj roundtrip


mutual

/-- Decoding commutes with semantic substitution for every LeaTTa atom, not
only atoms known to lie in the native translation image. -/
theorem fromLeaTTaAtom_applyClassSolution_any
    (valuation : String → Metta.Atom) (atom : Metta.Atom) :
    fromLeaTTaAtom (applyClassSolution valuation atom) =
      applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))
        (fromLeaTTaAtom atom) := by
  cases atom with
  | sym | var | gnd =>
      simp [applyClassSolution, fromLeaTTaAtom, applyTypeValuation]
  | expr atoms =>
      simp only [applyClassSolution, fromLeaTTaAtom,
        applyTypeValuation.eq_def]
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_applyClassSolution_any valuation atoms)

/-- List companion of `fromLeaTTaAtom_applyClassSolution_any`. -/
theorem fromLeaTTaAtoms_applyClassSolution_any
    (valuation : String → Metta.Atom) (atoms : List Metta.Atom) :
    fromLeaTTaAtoms (atoms.map (applyClassSolution valuation)) =
      (fromLeaTTaAtoms atoms).map
        (applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_applyClassSolution_any valuation atom)
        (fromLeaTTaAtoms_applyClassSolution_any valuation atoms)

end


mutual

/-- Decoding a substituted translated atom is the same as applying the
pointwise decoded valuation natively.  The LeaTTa valuation itself need not
lie in the image of the translation. -/
theorem fromLeaTTaAtom_applyClassSolution
    (valuation : String → Metta.Atom) (atom : Atom) :
    fromLeaTTaAtom
        (applyClassSolution valuation (toLeaTTaAtom atom)) =
      applyTypeValuation (fun name => fromLeaTTaAtom (valuation name)) atom := by
  cases atom with
  | symbol | var | grounded =>
      simp [applyTypeValuation, toLeaTTaAtom, applyClassSolution,
        fromLeaTTaAtom]
  | expression atoms =>
      rw [toLeaTTaAtom, applyClassSolution, fromLeaTTaAtom,
        applyTypeValuation]
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_applyClassSolution valuation atoms)
termination_by 2 * sizeOf atom

/-- List companion of `fromLeaTTaAtom_applyClassSolution`. -/
theorem fromLeaTTaAtoms_applyClassSolution
    (valuation : String → Metta.Atom) (atoms : List Atom) :
    fromLeaTTaAtoms
        ((toLeaTTaAtoms atoms).map (applyClassSolution valuation)) =
      atoms.map
        (applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_applyClassSolution valuation atom)
        (fromLeaTTaAtoms_applyClassSolution valuation atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end


/-- Native satisfaction maps into the established LeaTTa-valued observation
language by translating a valuation pointwise. -/
theorem heBindingSatisfied_of_specTypeBindingSatisfied
    {valuation : String → Atom} {bindings : Bindings}
    (hsatisfied : TypeBindingSatisfied valuation bindings) :
    HEBindingSatisfied (fun name => toLeaTTaAtom (valuation name))
      bindings := by
  constructor
  · intro name value hmem
    have h := hsatisfied.1 name value hmem
    exact (congrArg toLeaTTaAtom h).trans
      (toLeaTTaAtom_applyTypeValuation valuation value)
  · intro left right hmem
    exact congrArg toLeaTTaAtom (hsatisfied.2 left right hmem)

/-- Every model in the established LeaTTa-valued observation language
decodes to an honest native model of the same spec binding record. -/
theorem specTypeBindingSatisfied_of_heBindingSatisfied
    {valuation : String → Metta.Atom} {bindings : Bindings}
    (hsatisfied : HEBindingSatisfied valuation bindings) :
    TypeBindingSatisfied
      (fun name => fromLeaTTaAtom (valuation name)) bindings := by
  constructor
  · intro name value hmem
    have h := hsatisfied.1 name value hmem
    have := congrArg fromLeaTTaAtom h
    simpa [fromLeaTTaAtom_applyClassSolution] using this
  · intro left right hmem
    exact congrArg fromLeaTTaAtom (hsatisfied.2 left right hmem)

/-- For a pointwise translated native valuation, the established observation
language and native type-binding satisfaction coincide exactly. -/
theorem specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    (valuation : String → Atom) (bindings : Bindings) :
    TypeBindingSatisfied valuation bindings ↔
      HEBindingSatisfied
        (fun name => toLeaTTaAtom (valuation name)) bindings := by
  constructor
  · exact heBindingSatisfied_of_specTypeBindingSatisfied
  · intro hsatisfied
    constructor
    · intro name value hmem
      apply toLeaTTaAtom_injective
      rw [toLeaTTaAtom_applyTypeValuation]
      exact hsatisfied.1 name value hmem
    · intro left right hmem
      apply toLeaTTaAtom_injective
      exact hsatisfied.2 left right hmem

/-- Away from expressions and R2's explicit `%Undefined%` wildcard, reduced
type consistency is ordinary equality after applying the native valuation. -/
theorem reducedTypeConsistent_iff_applyTypeValuation_eq_of_leaf
    (valuation : String → Atom) (left right : Atom)
    (hnotBothExpressions : ∀ lefts rights,
      left = .expression lefts → right = .expression rights → False)
    (hleftUndefined : left ≠ Atom.undefinedType)
    (hrightUndefined : right ≠ Atom.undefinedType) :
    ReducedTypeConsistent valuation left right ↔
      applyTypeValuation valuation left =
        applyTypeValuation valuation right := by
  cases left <;> cases right
  all_goals
    simp [Atom.undefinedType] at hnotBothExpressions hleftUndefined hrightUndefined
  all_goals unfold ReducedTypeConsistent applyTypeValuation
  all_goals first | rfl | simp_all

/-! ## Reachable type-binding bridge -/

/-- The direct symbol annotation selected by the published spec lookup. -/
private def directSymbolAnnotationType? (name : String) : Atom → Option Atom
  | .expression [.symbol ":", annotated, type] =>
      if annotated == .symbol name then some type else none
  | _ => none

private theorem getAnnotatedTypes_symbol_eq_filterMap
    (atoms : List Atom) (name : String) :
    getAnnotatedTypes (Space.ofList atoms) (.symbol name) =
      atoms.filterMap (directSymbolAnnotationType? name) := by
  rfl

/-- The executable symbol-type indexing step, named only so its fold invariant
can be stated independently of `MinEnv.ofAtomsGT`'s other indexes. -/
private def leaSymbolTypeIndexStep
    (types : Std.HashMap String (List Metta.Atom)) (atom : Metta.Atom) :
    Std.HashMap String (List Metta.Atom) :=
  match atom with
  | .expr [.sym ":", .sym symbol, type] =>
      types.insert symbol (types.getD symbol [] ++ [type])
  | _ => types

/-- Folding translated annotations preserves their published order in every
symbol bucket, on top of any pre-existing accumulator bucket. -/
private theorem leaSymbolTypeIndexFold_getD
    (atoms : List Atom) (initial : Std.HashMap String (List Metta.Atom))
    (name : String) :
    ((toLeaTTaAtoms atoms).foldl leaSymbolTypeIndexStep initial).getD name [] =
      initial.getD name [] ++
        toLeaTTaAtoms (atoms.filterMap (directSymbolAnnotationType? name)) := by
  induction atoms generalizing initial with
  | nil => simp [toLeaTTaAtoms]
  | cons atom atoms ih =>
      rw [toLeaTTaAtoms, List.foldl_cons, ih]
      cases atom with
      | symbol | var | grounded =>
          simp [leaSymbolTypeIndexStep, directSymbolAnnotationType?,
            toLeaTTaAtom]
      | expression children =>
          rcases children with _ | ⟨first, children⟩
          · simp [leaSymbolTypeIndexStep, directSymbolAnnotationType?,
              toLeaTTaAtom]
          rcases children with _ | ⟨annotated, children⟩
          · simp [leaSymbolTypeIndexStep, directSymbolAnnotationType?,
              toLeaTTaAtom]
          rcases children with _ | ⟨type, children⟩
          · simp [leaSymbolTypeIndexStep, directSymbolAnnotationType?,
              toLeaTTaAtom]
          rcases children with _ | ⟨extra, children⟩
          · cases first with
            | symbol firstName =>
                by_cases hcolon : firstName = ":"
                · subst firstName
                  cases annotated with
                  | symbol annotatedName =>
                      by_cases hname : annotatedName = name
                      · subst annotatedName
                        simp [leaSymbolTypeIndexStep,
                          directSymbolAnnotationType?, toLeaTTaAtom,
                          List.append_assoc]
                      · simp [leaSymbolTypeIndexStep,
                          directSymbolAnnotationType?, toLeaTTaAtom,
                          Std.HashMap.getD_insert, hname]
                  | var | grounded | expression =>
                      simp [leaSymbolTypeIndexStep,
                        directSymbolAnnotationType?, toLeaTTaAtom]
                · simp [leaSymbolTypeIndexStep,
                    directSymbolAnnotationType?, toLeaTTaAtom, hcolon]
            | var | grounded | expression =>
                simp [leaSymbolTypeIndexStep,
                  directSymbolAnnotationType?, toLeaTTaAtom]
          · simp [leaSymbolTypeIndexStep, directSymbolAnnotationType?,
              toLeaTTaAtom]

/-- The expression annotation retained by LeaTTa's linear expression index. -/
private def leaExpressionAnnotation?
    (atom : Metta.Atom) : Option (Metta.Atom × Metta.Atom) :=
  match atom with
  | .expr [.sym ":", .expr expression, type] =>
      some (.expr expression, type)
  | _ => none

/-- The direct expression annotation selected by the published lookup. -/
private def directExpressionAnnotationType?
    (target : Atom) : Atom → Option Atom
  | .expression [.symbol ":", annotated, type] =>
      if annotated == target then some type else none
  | _ => none

private theorem getAnnotatedTypes_expression_eq_filterMap
    (atoms : List Atom) (head : Atom) (tail : List Atom) :
    getAnnotatedTypes (Space.ofList atoms) (.expression (head :: tail)) =
      atoms.filterMap
        (directExpressionAnnotationType? (.expression (head :: tail))) := by
  rfl

/-- Querying LeaTTa's translated expression index is exactly ordered direct
annotation lookup in the published spec space. -/
private theorem leaExpressionTypeIndexQuery
    (atoms : List Atom) (head : Atom) (tail : List Atom) :
    (((toLeaTTaAtoms atoms).filterMap leaExpressionAnnotation?).filter
        (fun entry =>
          entry.1 == toLeaTTaAtom (.expression (head :: tail)))).map (·.2) =
      toLeaTTaAtoms
        (atoms.filterMap
          (directExpressionAnnotationType?
            (.expression (head :: tail)))) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rw [toLeaTTaAtoms]
      cases atom with
      | symbol | var | grounded =>
          simpa [leaExpressionAnnotation?,
            directExpressionAnnotationType?, toLeaTTaAtom] using ih
      | expression children =>
          rcases children with _ | ⟨first, children⟩
          · simpa [leaExpressionAnnotation?,
              directExpressionAnnotationType?, toLeaTTaAtom] using ih
          rcases children with _ | ⟨annotated, children⟩
          · simpa [leaExpressionAnnotation?,
              directExpressionAnnotationType?, toLeaTTaAtom] using ih
          rcases children with _ | ⟨type, children⟩
          · simpa [leaExpressionAnnotation?,
              directExpressionAnnotationType?, toLeaTTaAtom] using ih
          rcases children with _ | ⟨extra, children⟩
          · cases first with
            | symbol firstName =>
                by_cases hcolon : firstName = ":"
                · subst firstName
                  cases annotated with
                  | expression annotatedChildren =>
                      by_cases heq : annotatedChildren = head :: tail
                      · subst annotatedChildren
                        have htranslated :
                            Metta.Atom.beq
                              (toLeaTTaAtom (.expression (head :: tail)))
                              (toLeaTTaAtom (.expression (head :: tail))) =
                                true :=
                          (toLeaTTaAtom_beq_eq_true_iff _ _).2 rfl
                        have hfilter :
                            ((.expr
                                (toLeaTTaAtom head ::
                                  tail.map toLeaTTaAtom) : Metta.Atom) ==
                              (.expr
                                (toLeaTTaAtom head ::
                                  tail.map toLeaTTaAtom))) = true := by
                          change Metta.Atom.beq _ _ = true
                          simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using
                            htranslated
                        simp [leaExpressionAnnotation?,
                          directExpressionAnnotationType?, toLeaTTaAtom]
                        simp only [List.filter_cons, hfilter, if_true,
                          List.map_cons]
                        simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map,
                          leaExpressionAnnotation?,
                          directExpressionAnnotationType?] using
                            congrArg (List.cons (toLeaTTaAtom type)) ih
                      · have hatomNe :
                            Atom.expression annotatedChildren ≠
                              Atom.expression (head :: tail) := by
                          intro hatom
                          exact heq (Atom.expression.inj hatom)
                        have hnative :
                            (Atom.expression annotatedChildren ==
                              Atom.expression (head :: tail)) = false := by
                          apply Bool.eq_false_iff.mpr
                          intro htrue
                          exact hatomNe (beq_iff_eq.mp htrue)
                        have htranslated :
                            Metta.Atom.beq
                              (toLeaTTaAtom
                                (.expression annotatedChildren))
                              (toLeaTTaAtom
                                (.expression (head :: tail))) = false := by
                          apply Bool.eq_false_iff.mpr
                          intro htrue
                          exact hatomNe
                            ((toLeaTTaAtom_beq_eq_true_iff _ _).mp htrue)
                        have hfilter :
                            ((.expr
                                (annotatedChildren.map toLeaTTaAtom) :
                                  Metta.Atom) ==
                              (.expr
                                (toLeaTTaAtom head ::
                                  tail.map toLeaTTaAtom))) = false := by
                          change Metta.Atom.beq _ _ = false
                          simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using
                            htranslated
                        simp [leaExpressionAnnotation?,
                          directExpressionAnnotationType?, toLeaTTaAtom,
                          hatomNe]
                        simp only [List.filter_cons, hfilter,
                          Bool.false_eq_true, if_false]
                        simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map,
                          leaExpressionAnnotation?,
                          directExpressionAnnotationType?, hatomNe] using ih
                  | symbol | var | grounded =>
                      simpa [leaExpressionAnnotation?,
                        directExpressionAnnotationType?, toLeaTTaAtom] using ih
                · simpa [leaExpressionAnnotation?,
                    directExpressionAnnotationType?, toLeaTTaAtom,
                    hcolon] using ih
            | var | grounded | expression =>
                simpa [leaExpressionAnnotation?,
                  directExpressionAnnotationType?, toLeaTTaAtom] using ih
          · simpa [leaExpressionAnnotation?,
              directExpressionAnnotationType?, toLeaTTaAtom] using ih

/-- The two type indexes observed by `getTypes` contain exactly the direct
published annotations of the corresponding spec space.  This relation keeps
index construction separate from recursive type inference; a later theorem
establishes it for `MinEnv.ofAtomsGT`. -/
structure TypeEnvironmentRel
    (space : Space) (env : Metta.Minimal.MinEnv) : Prop where
  symbolTypes : ∀ name,
    env.types.getD name [] =
      toLeaTTaAtoms (getAnnotatedTypes space (.symbol name))
  expressionTypes : ∀ head tail,
    (env.exprTypes.filter (fun entry =>
      entry.1 == toLeaTTaAtom (.expression (head :: tail)))).map (·.2) =
      toLeaTTaAtoms
        (getAnnotatedTypes space (.expression (head :: tail)))

/-- Filtering a proof-carrying list and erasing the proofs is the ordinary
filter on the underlying list. -/
private theorem unattach_filter_attachWith
    {α : Type} {property : α → Prop} (entries : List α)
    (all : ∀ entry ∈ entries, property entry) (predicate : α → Bool) :
    ((entries.attachWith property all).filter
      (fun entry => predicate entry.1)).unattach =
      entries.filter predicate := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      by_cases hhead : predicate head = true
      · simp only [List.attachWith, List.pmap, List.filter,
          List.unattach, hhead]
        apply congrArg (List.cons head)
        exact ih (fun entry hentry =>
          all entry (List.mem_cons_of_mem _ hentry))
      · simp only [List.attachWith, List.pmap, List.filter,
          List.unattach, hhead]
        exact ih (fun entry hentry =>
          all entry (List.mem_cons_of_mem _ hentry))

/-- Specialization of `unattach_filter_attachWith` to `List.attach`. -/
private theorem unattach_filter_attach
    {α : Type} (entries : List α) (predicate : α → Bool) :
    (entries.attach.filter (fun entry => predicate entry.1)).unattach =
      entries.filter predicate := by
  exact unattach_filter_attachWith entries (fun _ h => h) predicate

/-- Building LeaTTa's minimal environment from the structural translation of
a spec space establishes the exact ordered annotation-index relation. -/
theorem typeEnvironmentRel_ofAtomsGT
    (space : Space) (groundingTable : Metta.GroundingTable) :
    TypeEnvironmentRel space
      (Metta.Minimal.MinEnv.ofAtomsGT
        (toLeaTTaAtoms space.atoms) groundingTable) := by
  cases space with
  | mk atoms =>
      constructor
      · intro name
        change
          ((toLeaTTaAtoms atoms).foldl leaSymbolTypeIndexStep
              Std.HashMap.emptyWithCapacity).getD name [] =
            toLeaTTaAtoms
              (getAnnotatedTypes (Space.ofList atoms) (.symbol name))
        rw [leaSymbolTypeIndexFold_getD,
          Std.HashMap.getD_emptyWithCapacity]
        simp only [List.nil_append]
        rw [getAnnotatedTypes_symbol_eq_filterMap]
      · intro head tail
        change
          (((toLeaTTaAtoms atoms).filterMap
              leaExpressionAnnotation?).filter
              (fun entry =>
                entry.1 ==
                  toLeaTTaAtom (.expression (head :: tail)))).map (·.2) =
            toLeaTTaAtoms
              (getAnnotatedTypes (Space.ofList atoms)
                (.expression (head :: tail)))
        rw [leaExpressionTypeIndexQuery,
          getAnnotatedTypes_expression_eq_filterMap]

/-! ## Runtime type lookup, nonrecursive branches -/

/-- Repaired LeaTTa's intrinsic grounded lookup agrees with the published
spec grounded-type relation, including custom values' carried type tag. -/
theorem getTypes_grounded_runtimeEvidence
    (space : Space) (env : Metta.Minimal.MinEnv) (value : GroundedValue)
    {leaType : Metta.Atom}
    (hmem : leaType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom (.grounded value))) :
    RuntimeTypeEvidenceRel space (.grounded value)
      (fromLeaTTaAtom leaType) := by
  cases value with
  | int | bool | string =>
      simp [Metta.Minimal.getTypes, toLeaTTaAtom,
        toLeaTTaGround] at hmem
      subst leaType
      apply RuntimeTypeEvidenceRel.published
      apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
      simp [getAtomTypes, getGroundedType, fromLeaTTaAtom,
        Atom.undefinedType]
  | custom typeName payload =>
      simp [Metta.Minimal.getTypes, toLeaTTaAtom,
        toLeaTTaGround] at hmem
      subst leaType
      apply RuntimeTypeEvidenceRel.published
      apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
      by_cases hundefined : typeName = "%Undefined%"
      · subst typeName
        simp [getAtomTypes, getGroundedType, fromLeaTTaAtom,
          Atom.undefinedType]
      · simp [getAtomTypes, getGroundedType, fromLeaTTaAtom,
          Atom.undefinedType, hundefined]

/-- Variables receive exactly the published gradual `%Undefined%` type. -/
theorem getTypes_variable_runtimeEvidence
    (space : Space) (env : Metta.Minimal.MinEnv) (name : String)
    {leaType : Metta.Atom}
    (hmem : leaType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom (.var name))) :
    RuntimeTypeEvidenceRel space (.var name) (fromLeaTTaAtom leaType) := by
  simp [Metta.Minimal.getTypes, toLeaTTaAtom] at hmem
  subst leaType
  apply RuntimeTypeEvidenceRel.published
  apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
  simp [getAtomTypes, fromLeaTTaAtom, Atom.undefinedType]

/-- The empty expression receives exactly the published gradual fallback. -/
theorem getTypes_emptyExpression_runtimeEvidence
    (space : Space) (env : Metta.Minimal.MinEnv) {leaType : Metta.Atom}
    (hmem : leaType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom (.expression []))) :
    RuntimeTypeEvidenceRel space (.expression [])
      (fromLeaTTaAtom leaType) := by
  simp [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaAtoms] at hmem
  subst leaType
  apply RuntimeTypeEvidenceRel.published
  apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
  simp [getAtomTypes, fromLeaTTaAtom, Atom.undefinedType]

/-- The unrestricted R3 branch is exactly LeaTTa's `StateValue` lookup rule;
the recursive content-type evidence is exposed as an explicit premise. -/
theorem getTypes_stateValue_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv} (value : Atom)
    (contentEvidence : ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom value) →
        RuntimeTypeEvidenceRel space value (fromLeaTTaAtom leaType))
    {leaType : Metta.Atom}
    (hmem : leaType ∈ Metta.Minimal.getTypes env
      (toLeaTTaAtom
        (.expression [.symbol "StateValue", value]))) :
    RuntimeTypeEvidenceRel space
      (.expression [.symbol "StateValue", value])
      (fromLeaTTaAtom leaType) := by
  obtain ⟨contentType, rest, htypes⟩ := List.exists_cons_of_ne_nil
    (Metta.getTypes_ne_nil env (toLeaTTaAtom value))
  have hcontent : contentType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom value) := by
    rw [htypes]
    simp
  have hevidence := contentEvidence hcontent
  simp [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaAtoms,
    htypes] at hmem
  subst leaType
  simpa [fromLeaTTaAtom, fromLeaTTaAtoms] using
    (RuntimeTypeEvidenceRel.stateValue
      (R3StateValueTypeRel.mk hevidence))

/-- Totality turns pointwise soundness for every computed type into soundness
for the particular head type selected by LeaTTa's R1 inference. -/
theorem getTypes_head_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv} {atom : Atom}
    (evidence : ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom atom) →
        RuntimeTypeEvidenceRel space atom (fromLeaTTaAtom leaType)) :
    RuntimeTypeEvidenceRel space atom
      (fromLeaTTaAtom
        (((Metta.Minimal.getTypes env (toLeaTTaAtom atom)).head?).getD
          (.sym "%Undefined%"))) := by
  obtain ⟨head, tail, htypes⟩ := List.exists_cons_of_ne_nil
    (Metta.getTypes_ne_nil env (toLeaTTaAtom atom))
  have hhead : head ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom atom) := by
    rw [htypes]
    simp
  simpa [htypes] using evidence hhead

/-- Pointwise recursive soundness supplies the R1 evidence list for the head
type selected at every application argument. -/
theorem getTypes_argumentHeads_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv} (arguments : List Atom)
    (evidence : ∀ argument ∈ arguments, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        RuntimeTypeEvidenceRel space argument
          (fromLeaTTaAtom leaType)) :
    List.Forall₂ (RuntimeTypeEvidenceRel space) arguments
      (fromLeaTTaAtoms
        (arguments.map fun argument =>
          ((Metta.Minimal.getTypes env
            (toLeaTTaAtom argument)).head?).getD
              (.sym "%Undefined%"))) := by
  induction arguments with
  | nil => exact .nil
  | cons argument arguments ih =>
      rw [List.map_cons, fromLeaTTaAtoms]
      apply List.Forall₂.cons
      · apply getTypes_head_runtimeEvidence
        intro leaType hmem
        exact evidence argument (by simp) hmem
      · apply ih
        intro child hchild leaType hmem
        exact evidence child (by simp [hchild]) hmem

/-- Pointwise round trips for every computed type give the exact round trip
for the head type selected by application inference. -/
theorem getTypes_head_roundtrip
    {env : Metta.Minimal.MinEnv} {atom : Atom}
    (roundtrip : ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom atom) →
        toLeaTTaAtom (fromLeaTTaAtom leaType) = leaType) :
    toLeaTTaAtom
        (fromLeaTTaAtom
          (((Metta.Minimal.getTypes env (toLeaTTaAtom atom)).head?).getD
            (.sym "%Undefined%"))) =
      ((Metta.Minimal.getTypes env (toLeaTTaAtom atom)).head?).getD
        (.sym "%Undefined%") := by
  obtain ⟨head, tail, htypes⟩ := List.exists_cons_of_ne_nil
    (Metta.getTypes_ne_nil env (toLeaTTaAtom atom))
  have hhead : head ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom atom) := by
    rw [htypes]
    simp
  simpa [htypes] using roundtrip hhead

/-- Pointwise image preservation for computed types gives image provenance
for the head type selected by application inference. -/
theorem getTypes_head_heImage
    {env : Metta.Minimal.MinEnv} {atom : Metta.Atom}
    (image : ∀ {leaType}, leaType ∈ Metta.Minimal.getTypes env atom →
      LeaAtomHEImage leaType) :
    LeaAtomHEImage
      (((Metta.Minimal.getTypes env atom).head?).getD
        (.sym "%Undefined%")) := by
  obtain ⟨head, tail, htypes⟩ := List.exists_cons_of_ne_nil
    (Metta.getTypes_ne_nil env atom)
  apply image
  rw [htypes]
  simp

/-- List companion of `getTypes_head_roundtrip` for the actual argument-type
list selected by application inference. -/
theorem getTypes_argumentHeads_roundtrip
    {env : Metta.Minimal.MinEnv} (arguments : List Atom)
    (roundtrip : ∀ argument ∈ arguments, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        toLeaTTaAtom (fromLeaTTaAtom leaType) = leaType) :
    toLeaTTaAtoms
        (fromLeaTTaAtoms
          (arguments.map fun argument =>
            ((Metta.Minimal.getTypes env
              (toLeaTTaAtom argument)).head?).getD
                (.sym "%Undefined%"))) =
      arguments.map fun argument =>
        ((Metta.Minimal.getTypes env
          (toLeaTTaAtom argument)).head?).getD
            (.sym "%Undefined%") := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [List.map_cons, fromLeaTTaAtoms, toLeaTTaAtoms]
      apply congrArg₂ List.cons
      · apply getTypes_head_roundtrip
        intro leaType hmem
        exact roundtrip argument (by simp) hmem
      · apply ih
        intro child hchild leaType hmem
        exact roundtrip child (by simp [hchild]) hmem

/-- List companion of `getTypes_head_heImage` for application arguments. -/
theorem getTypes_argumentHeads_heImage
    {env : Metta.Minimal.MinEnv} (arguments : List Metta.Atom)
    (image : ∀ argument ∈ arguments, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env argument →
        LeaAtomHEImage leaType) :
    LeaAtomsHEImage
      (arguments.map fun argument =>
        ((Metta.Minimal.getTypes env argument).head?).getD
          (.sym "%Undefined%")) := by
  apply leaAtomsHEImage_of_forall
  intro selected hselected
  obtain ⟨argument, hargument, rfl⟩ := List.mem_map.mp hselected
  apply getTypes_head_heImage
  intro leaType hmem
  exact image argument hargument hmem

/-- Every indexed symbol type is published-core type evidence. -/
theorem TypeEnvironmentRel.symbolPublished
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {name : String} {leaType : Metta.Atom}
    (hmem : leaType ∈ env.types.getD name []) :
    TypeOfRel space (.symbol name) (fromLeaTTaAtom leaType) := by
  have htranslated : leaType ∈
      toLeaTTaAtoms (getAnnotatedTypes space (.symbol name)) := by
    simpa [index.symbolTypes name] using hmem
  rw [toLeaTTaAtoms_eq_map] at htranslated
  obtain ⟨type, htype, rfl⟩ := List.mem_map.mp htranslated
  rw [fromLeaTTaAtom_toLeaTTaAtom]
  apply (typeOfRel_iff_mem_getAtomTypes space (.symbol name) type).mpr
  have hnonempty : getAnnotatedTypes space (.symbol name) ≠ [] := by
    intro hempty
    simp [hempty] at htype
  simpa [getAtomTypes, hnonempty] using htype

/-- Every value stored in the symbol annotation index lies in the exact
native translation image. -/
theorem TypeEnvironmentRel.symbolHEImage
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {name : String} {leaType : Metta.Atom}
    (hmem : leaType ∈ env.types.getD name []) :
    LeaAtomHEImage leaType := by
  have htranslated : leaType ∈
      toLeaTTaAtoms (getAnnotatedTypes space (.symbol name)) := by
    simpa [index.symbolTypes name] using hmem
  rw [toLeaTTaAtoms_eq_map] at htranslated
  obtain ⟨type, _, rfl⟩ := List.mem_map.mp htranslated
  exact leaAtomHEImage_toLeaTTaAtom type

/-- Every indexed nonempty-expression type is published-core type evidence. -/
theorem TypeEnvironmentRel.expressionPublished
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {head : Atom} {tail : List Atom} {leaType : Metta.Atom}
    (hmem : leaType ∈
      (env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail)))).map (·.2)) :
    TypeOfRel space (.expression (head :: tail))
      (fromLeaTTaAtom leaType) := by
  have htranslated : leaType ∈
      toLeaTTaAtoms
        (getAnnotatedTypes space (.expression (head :: tail))) := by
    simpa [index.expressionTypes head tail] using hmem
  rw [toLeaTTaAtoms_eq_map] at htranslated
  obtain ⟨type, htype, rfl⟩ := List.mem_map.mp htranslated
  rw [fromLeaTTaAtom_toLeaTTaAtom]
  apply (typeOfRel_iff_mem_getAtomTypes space
    (.expression (head :: tail)) type).mpr
  have hnonempty :
      getAnnotatedTypes space (.expression (head :: tail)) ≠ [] := by
    intro hempty
    simp [hempty] at htype
  simpa [getAtomTypes, hnonempty] using htype

/-- Every value stored in the direct-expression annotation index lies in the
exact native translation image. -/
theorem TypeEnvironmentRel.expressionHEImage
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {head : Atom} {tail : List Atom} {leaType : Metta.Atom}
    (hmem : leaType ∈
      (env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail)))).map (·.2)) :
    LeaAtomHEImage leaType := by
  have htranslated : leaType ∈
      toLeaTTaAtoms
        (getAnnotatedTypes space (.expression (head :: tail))) := by
    simpa [index.expressionTypes head tail] using hmem
  rw [toLeaTTaAtoms_eq_map] at htranslated
  obtain ⟨type, _, rfl⟩ := List.mem_map.mp htranslated
  exact leaAtomHEImage_toLeaTTaAtom type

/-- Symbol lookup is exactly the ordered published annotation list, with the
same `%Undefined%` fallback when its index bucket is empty. -/
theorem getTypes_symbol_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (name : String)
    {leaType : Metta.Atom}
    (hmem : leaType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom (.symbol name))) :
    RuntimeTypeEvidenceRel space (.symbol name)
      (fromLeaTTaAtom leaType) := by
  cases hbucket : env.types.getD name [] with
  | nil =>
      have hannotations :
          getAnnotatedTypes space (.symbol name) = [] := by
        have htranslated := index.symbolTypes name
        rw [hbucket] at htranslated
        have hdecoded := congrArg fromLeaTTaAtoms htranslated
        simpa using hdecoded.symm
      simp [Metta.Minimal.getTypes, toLeaTTaAtom, hbucket] at hmem
      subst leaType
      apply RuntimeTypeEvidenceRel.published
      apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
      simp [getAtomTypes, hannotations, fromLeaTTaAtom,
        Atom.undefinedType]
  | cons first rest =>
      apply RuntimeTypeEvidenceRel.published
      apply index.symbolPublished
      simpa [Metta.Minimal.getTypes, toLeaTTaAtom, hbucket] using hmem

/-- When a direct expression annotation is present, LeaTTa returns that
published-core evidence before considering R1 inference. -/
theorem getTypes_directExpression_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (head : Atom) (tail : List Atom)
    {leaType : Metta.Atom}
    (hnotState : ∀ leaValue,
      toLeaTTaAtom head = .sym "StateValue" →
      toLeaTTaAtoms tail = [leaValue] → False)
    (hdirect :
      (env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail)))) ≠ [])
    (hmem : leaType ∈
      Metta.Minimal.getTypes env
        (toLeaTTaAtom (.expression (head :: tail)))) :
    RuntimeTypeEvidenceRel space (.expression (head :: tail))
      (fromLeaTTaAtom leaType) := by
  obtain ⟨first, rest, hquery⟩ := List.exists_cons_of_ne_nil hdirect
  have hquery' :
      env.exprTypes.filter (fun entry =>
        entry.1 == .expr
          (toLeaTTaAtom head :: tail.map toLeaTTaAtom)) = first :: rest := by
    simpa [toLeaTTaAtom, toLeaTTaAtoms_eq_map] using hquery
  apply RuntimeTypeEvidenceRel.published
  apply index.expressionPublished
  rw [hquery]
  change leaType ∈ Metta.Minimal.getTypes env
    (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) at hmem
  rw [Metta.Minimal.getTypes.eq_10 env
    (toLeaTTaAtom head) (toLeaTTaAtoms tail) hnotState] at hmem
  simpa [hquery'] using hmem

/-- Homomorphic valuation of a runtime atom depends only on its finite
variable support. -/
theorem applyClassSolution_congr_on_atom_vars
    {left right : String → Metta.Atom} (atom : Metta.Atom)
    (agrees : ∀ name, name ∈ atom.vars → left name = right name) :
    applyClassSolution left atom = applyClassSolution right atom := by
  induction atom with
  | sym name => simp [applyClassSolution]
  | var name =>
      simpa [applyClassSolution] using
        agrees name (by simp [Metta.Atom.vars])
  | gnd value => simp [applyClassSolution]
  | expr atoms inductionHypothesis =>
      simp only [applyClassSolution, Metta.Atom.expr.injEq]
      apply List.map_congr_left
      intro child childMember
      exact inductionHypothesis child childMember fun name member =>
        agrees name (by
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, childMember, rfl⟩, member⟩)

/-- Satisfaction of a runtime binding theory depends only on the names that
occur in its binding list. -/
theorem leaBindingSatisfied_congr_on_binding_vars
    {left right : String → Metta.Atom} {bindings : Metta.Bindings}
    (agrees : ∀ name, name ∈ bindings.vars → left name = right name) :
    LeaBindingSatisfied left bindings ↔
      LeaBindingSatisfied right bindings := by
  have forward : ∀ {first second : String → Metta.Atom},
      (∀ name, name ∈ bindings.vars → first name = second name) →
      LeaBindingSatisfied first bindings →
        LeaBindingSatisfied second bindings := by
    intro first second pointwise satisfied
    constructor
    · intro name value member
      have nameMember : name ∈ bindings.vars := by
        simp only [Metta.Bindings.vars, List.mem_eraseDups,
          List.mem_flatMap]
        exact ⟨.val name value, member, by simp⟩
      have valueAgreement :
          applyClassSolution first value = applyClassSolution second value :=
        applyClassSolution_congr_on_atom_vars value fun candidate
            candidateMember =>
          pointwise candidate (by
            simp only [Metta.Bindings.vars, List.mem_eraseDups,
              List.mem_flatMap]
            exact ⟨.val name value, member, by simp [candidateMember]⟩)
      calc
        second name = first name := (pointwise name nameMember).symm
        _ = applyClassSolution first value := satisfied.1 name value member
        _ = applyClassSolution second value := valueAgreement
    · intro firstName secondName member
      have firstMember : firstName ∈ bindings.vars := by
        simp only [Metta.Bindings.vars, List.mem_eraseDups,
          List.mem_flatMap]
        exact ⟨.eq firstName secondName, member, by simp⟩
      have secondMember : secondName ∈ bindings.vars := by
        simp only [Metta.Bindings.vars, List.mem_eraseDups,
          List.mem_flatMap]
        exact ⟨.eq firstName secondName, member, by simp⟩
      calc
        second firstName = first firstName :=
          (pointwise firstName firstMember).symm
        _ = first secondName := satisfied.2 firstName secondName member
        _ = second secondName := pointwise secondName secondMember
  constructor
  · exact forward agrees
  · exact forward (fun name member => (agrees name member).symm)

/-- A reachable type-binding state pairs one native spec presentation with
one repaired-LeaTTa presentation of the same complete solution theory.  The
LeaTTa runtime invariant supplies the inhabited canonical model needed by the
next type match. -/
structure TypeBindingState (spec : Bindings) (lea : Metta.Bindings) : Prop where
  theory : LeaBindingSolutionTheoryEquiv spec lea
  specAssignmentsNonVariable : HEAssignmentsNonVariable spec
  runtime : LeaRuntimeBindingInvariant lea

/-- List companion used internally by the reduced-type conformance induction.
It carries exactly the conjunction of incoming binding theory and pointwise R2
consistency. -/
private structure R2ReducedTypeListMatchRel
    (left right : List Atom) (incoming output : Bindings) : Prop where
  satisfiable : ∃ valuation, TypeBindingSatisfied valuation output
  solutions : ∀ valuation,
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation incoming ∧
        ReducedTypeListConsistent valuation left right

/-- Every reachable type-binding state has a native spec model. -/
theorem TypeBindingState.specSatisfiable
    {spec : Bindings} {lea : Metta.Bindings}
    (state : TypeBindingState spec lea) :
    ∃ valuation, TypeBindingSatisfied valuation spec := by
  let leaValuation := leaClassSolution lea
  have hlea : LeaBindingSatisfied leaValuation lea :=
    state.runtime.canonical.1
  have hspec : HEBindingSatisfied leaValuation spec :=
    (state.theory leaValuation).mpr hlea
  exact ⟨fun name => fromLeaTTaAtom (leaValuation name),
    specTypeBindingSatisfied_of_heBindingSatisfied hspec⟩

/-- The native side of a reachable type-binding state has the runtime
binding list as a semantic support: changing a valuation away from
`lea.vars` cannot change satisfaction of the native binding theory. -/
theorem TypeBindingState.specSatisfied_congr_on_runtimeVars
    {spec : Bindings} {lea : Metta.Bindings}
    (state : TypeBindingState spec lea)
    {left right : String → Atom}
    (agrees : ∀ name, name ∈ lea.vars → left name = right name) :
    TypeBindingSatisfied left spec ↔
      TypeBindingSatisfied right spec := by
  let leftRuntime : String → Metta.Atom :=
    fun name => toLeaTTaAtom (left name)
  let rightRuntime : String → Metta.Atom :=
    fun name => toLeaTTaAtom (right name)
  have runtimeAgrees : ∀ name, name ∈ lea.vars →
      leftRuntime name = rightRuntime name := by
    intro name member
    exact congrArg toLeaTTaAtom (agrees name member)
  calc
    TypeBindingSatisfied left spec ↔
        HEBindingSatisfied leftRuntime spec :=
      specTypeBindingSatisfied_iff_heBindingSatisfied_translated left spec
    _ ↔ LeaBindingSatisfied leftRuntime lea := state.theory leftRuntime
    _ ↔ LeaBindingSatisfied rightRuntime lea :=
      leaBindingSatisfied_congr_on_binding_vars runtimeAgrees
    _ ↔ HEBindingSatisfied rightRuntime spec :=
      (state.theory rightRuntime).symm
    _ ↔ TypeBindingSatisfied right spec :=
      (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        right spec).symm

/-- Instantiating a declared return type with a reachable LeaTTa binding
presentation produces exactly the observational return-type witness required
by R1.  The comparison quantifies over every model of the shared binding
theory; it does not identify binding presentations. -/
theorem TypeBindingState.returnObserved
    {spec : Bindings} {lea : Metta.Bindings}
    (state : TypeBindingState spec lea) (declared : Atom) :
    R1ReturnTypeObserved spec declared
      (fromLeaTTaAtom (Metta.instantiate lea (toLeaTTaAtom declared))) := by
  constructor
  · exact state.specSatisfiable
  · intro valuation hspec
    let leaValuation : String → Metta.Atom :=
      fun name => toLeaTTaAtom (valuation name)
    have hhe : HEBindingSatisfied leaValuation spec :=
      (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        valuation spec).mp hspec
    have hlea : LeaBindingSatisfied leaValuation lea :=
      (state.theory leaValuation).mp hhe
    have hinert := instantiate_semantically_inert hlea
      (toLeaTTaAtom declared)
    have hdecoded := congrArg fromLeaTTaAtom hinert
    rw [fromLeaTTaAtom_applyClassSolution_any,
      fromLeaTTaAtom_applyClassSolution_any] at hdecoded
    simpa [leaValuation] using hdecoded.symm

/-- Empty spec and LeaTTa binding presentations establish the base state. -/
theorem typeBindingState_empty :
    TypeBindingState Bindings.empty Metta.Bindings.empty := by
  constructor
  · intro valuation
    simp [HEBindingSatisfied, LeaBindingSatisfied, Bindings.empty,
      Metta.Bindings.empty]
  · simp [HEAssignmentsNonVariable, Bindings.empty]
  · exact leaRuntimeBindingInvariant_empty

/-- Extend one reachable type-binding state by one repaired matcher output and
one successful, loop-filtered LeaTTa merge.  The corresponding spec match and
merge are reconstructed from the shared solution theory; no executable HE
matcher or merger participates. -/
theorem TypeBindingState.mergeMatchOutput
    {specIncoming : Bindings}
    {leaIncoming matched leaOutput : Metta.Bindings}
    {expected actual : Atom}
    (state : TypeBindingState specIncoming leaIncoming)
    (hmatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom expected) (toLeaTTaAtom actual))
    (hmerge : leaOutput ∈ Metta.Bindings.merge leaIncoming matched)
    (hloop : leaOutput.hasLoop = false) :
    ∃ specMatched specOutput,
      Spec.Match.Merge.MatchRel
          Spec.Match.Merge.equalityGroundedSemantic
          actual expected specMatched ∧
        Spec.Match.Merge.MergeRel
          Spec.Match.Merge.equalityGroundedSemantic
          specIncoming specMatched specOutput ∧
        TypeBindingState specOutput leaOutput := by
  obtain ⟨specMatched, hspecMatch, hmatchedTheory⟩ :=
    leaMatch_observational_sound hmatch
  have hmatchedNoFloat : LeaBindingsNoFloat matched :=
    leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat expected)
      (toLeaTTaAtom_noFloat actual) hmatch
  have houtputRuntime : LeaRuntimeBindingInvariant leaOutput :=
    state.runtime.merge_matchOutput
      (toLeaTTaAtom_noFloat expected)
      (toLeaTTaAtom_noFloat actual) hmatch hmerge hloop
  let valuation := leaClassSolution leaOutput
  have houtputSatisfied : LeaBindingSatisfied valuation leaOutput :=
    houtputRuntime.canonical.1
  have hinputsSatisfied :
      LeaBindingSatisfied valuation leaIncoming ∧
        LeaBindingSatisfied valuation matched :=
    (leaMerge_solution_iff valuation state.runtime.noFloat
      hmatchedNoFloat hmerge).mp houtputSatisfied
  have hspecIncoming : HEBindingSatisfied valuation specIncoming :=
    (state.theory valuation).mpr hinputsSatisfied.1
  have hspecMatched : HEBindingSatisfied valuation specMatched :=
    (hmatchedTheory valuation).mpr hinputsSatisfied.2
  obtain ⟨specOutput, hspecMerge, _hspecOutput,
      hspecOutputNonVariable⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution
      hspecIncoming state.specAssignmentsNonVariable
      hspecMatched
      (LeaTTaSpecConformance.specMatch_assignmentsNonVariable hspecMatch)
  refine ⟨specMatched, specOutput, hspecMatch, hspecMerge, ?_⟩
  refine ⟨?_, hspecOutputNonVariable, houtputRuntime⟩
  intro otherValuation
  rw [Spec.Match.SolutionTheory.mergeRel_solution_iff hspecMerge,
    state.theory otherValuation, hmatchedTheory otherValuation,
    leaMerge_solution_iff otherValuation state.runtime.noFloat
      hmatchedNoFloat hmerge]

private theorem toLeaTTaAtom_beq_undefined_eq_false
    (atom : Atom) (hneq : atom ≠ Atom.undefinedType) :
    (toLeaTTaAtom atom == Metta.Atom.sym "%Undefined%") = false := by
  cases atom with
  | symbol name =>
      simp [Atom.undefinedType] at hneq
      change (name == "%Undefined%") = false
      simp [hneq]
  | var | grounded | expression =>
      rfl

private theorem toLeaTTaAtom_beq_atomType_eq_false
    (atom : Atom) (hneq : atom ≠ Atom.atomType) :
    (toLeaTTaAtom atom == Metta.Atom.sym "Atom") = false := by
  cases atom with
  | symbol name =>
      simp [Atom.atomType] at hneq
      change (name == "Atom") = false
      simp [hneq]
  | var | grounded | expression =>
      rfl

/-- Operational decomposition of one successful repaired reduced-type leaf.
The repair's pre-selection filter exposes loop-freedom together with the
matcher and merge witnesses used to reconstruct the spec step. -/
private theorem matchReduced_leaf_success
    {left right : Atom} {leaIncoming leaOutput : Metta.Bindings}
    (hnotBothExpressions : ∀ lefts rights,
      left = .expression lefts → right = .expression rights → False)
    (hleftUndefined : left ≠ Atom.undefinedType)
    (hrightUndefined : right ≠ Atom.undefinedType)
    (hsuccess : Metta.Minimal.matchReduced leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput) :
    ∃ matched,
      matched ∈ Metta.matchAtoms
          (toLeaTTaAtom left) (toLeaTTaAtom right) ∧
        leaOutput ∈ Metta.Bindings.merge leaIncoming matched ∧
        leaOutput.hasLoop = false := by
  have hleftBeq := toLeaTTaAtom_beq_undefined_eq_false left hleftUndefined
  have hrightBeq := toLeaTTaAtom_beq_undefined_eq_false right hrightUndefined
  rw [Metta.Minimal.matchReduced, hleftBeq, hrightBeq] at hsuccess
  · cases left <;> cases right
    all_goals
      simp [Atom.undefinedType] at hnotBothExpressions hleftUndefined hrightUndefined
    all_goals
      try simp only [Bool.false_or, Bool.false_eq_true, if_false] at hsuccess
      obtain ⟨tail, hfiltered⟩ := List.head?_eq_some_iff.mp hsuccess
      have hmemFilter : leaOutput ∈ leaOutput :: tail := by simp
      rw [← hfiltered] at hmemFilter
      have hparts := List.mem_filter.mp hmemFilter
      obtain ⟨matched, hmatch, hmerge⟩ :=
        List.mem_flatMap.mp hparts.1
      refine ⟨matched, hmatch, hmerge, ?_⟩
      simpa using hparts.2
  · intro expectedAtoms actualAtoms hleftExpression hrightExpression
    cases left <;> simp [toLeaTTaAtom] at hleftExpression
    cases right <;> simp [toLeaTTaAtom] at hrightExpression
    exact hnotBothExpressions _ _ rfl rfl

/-- One repaired non-expression reduced-type step realizes the observational
R2 relation and preserves the complete reachable binding-state invariant. -/
private theorem matchReduced_leaf_r2_sound
    {left right : Atom}
    {specIncoming : Bindings} {leaIncoming leaOutput : Metta.Bindings}
    (state : TypeBindingState specIncoming leaIncoming)
    (hnotBothExpressions : ∀ lefts rights,
      left = .expression lefts → right = .expression rights → False)
    (hleftUndefined : left ≠ Atom.undefinedType)
    (hrightUndefined : right ≠ Atom.undefinedType)
    (hsuccess : Metta.Minimal.matchReduced leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput) :
    ∃ specOutput,
      R2ReducedTypeMatchRel left right specIncoming specOutput ∧
        TypeBindingState specOutput leaOutput := by
  obtain ⟨matched, hmatch, hmerge, hloop⟩ :=
    matchReduced_leaf_success hnotBothExpressions hleftUndefined
      hrightUndefined hsuccess
  obtain ⟨specMatched, specOutput, hspecMatch, hspecMerge,
      outputState⟩ := state.mergeMatchOutput hmatch hmerge hloop
  refine ⟨specOutput, ?_, outputState⟩
  constructor
  · exact outputState.specSatisfiable
  · intro valuation
    let translated : String → Metta.Atom :=
      fun name => toLeaTTaAtom (valuation name)
    constructor
    · intro houtput
      have houtputHE : HEBindingSatisfied translated specOutput :=
        (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
          valuation specOutput).mp houtput
      have hparts :=
        (Spec.Match.SolutionTheory.mergeRel_solution_iff
          hspecMerge translated).mp houtputHE
      have hincoming : TypeBindingSatisfied valuation specIncoming :=
        (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
          valuation specIncoming).mpr hparts.1
      have hequation :=
        (Spec.Match.SolutionTheory.matchRel_solution_iff
          hspecMatch translated).mp hparts.2
      have hequationNative :
          applyTypeValuation valuation right =
            applyTypeValuation valuation left := by
        apply toLeaTTaAtom_injective
        rw [toLeaTTaAtom_applyTypeValuation,
          toLeaTTaAtom_applyTypeValuation]
        exact hequation
      exact ⟨hincoming,
        (reducedTypeConsistent_iff_applyTypeValuation_eq_of_leaf
          valuation left right hnotBothExpressions hleftUndefined
          hrightUndefined).mpr hequationNative.symm⟩
    · rintro ⟨hincoming, hconsistent⟩
      have hincomingHE : HEBindingSatisfied translated specIncoming :=
        (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
          valuation specIncoming).mp hincoming
      have hequationNative :
          applyTypeValuation valuation left =
            applyTypeValuation valuation right :=
        (reducedTypeConsistent_iff_applyTypeValuation_eq_of_leaf
          valuation left right hnotBothExpressions hleftUndefined
          hrightUndefined).mp hconsistent
      have hequation :
          applyClassSolution translated (toLeaTTaAtom right) =
            applyClassSolution translated (toLeaTTaAtom left) := by
        rw [← toLeaTTaAtom_applyTypeValuation,
          ← toLeaTTaAtom_applyTypeValuation]
        exact congrArg toLeaTTaAtom hequationNative.symm
      have hmatchedHE : HEBindingSatisfied translated specMatched :=
        (Spec.Match.SolutionTheory.matchRel_solution_iff
          hspecMatch translated).mpr hequation
      have houtputHE : HEBindingSatisfied translated specOutput :=
        (Spec.Match.SolutionTheory.mergeRel_solution_iff
          hspecMerge translated).mpr ⟨hincomingHE, hmatchedHE⟩
      exact
        (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
          valuation specOutput).mpr houtputHE

private theorem reducedTypeConsistent_right_undefined
    (valuation : String → Atom) (left : Atom) :
    ReducedTypeConsistent valuation left Atom.undefinedType := by
  by_cases hleft : left = Atom.undefinedType
  · subst left
    change ReducedTypeConsistent valuation
      (.symbol "%Undefined%") (.symbol "%Undefined%")
    rw [ReducedTypeConsistent.eq_1]
    trivial
  · change ReducedTypeConsistent valuation left (.symbol "%Undefined%")
    rw [ReducedTypeConsistent.eq_2 valuation left hleft]
    trivial

mutual

/-- Every successful repaired LeaTTa reduced-type match realizes the named R2
spec relation and preserves the complete reachable binding-state invariant. -/
theorem matchReduced_r2_sound
    {left right : Atom}
    {specIncoming : Bindings} {leaIncoming leaOutput : Metta.Bindings}
    (state : TypeBindingState specIncoming leaIncoming)
    (hsuccess : Metta.Minimal.matchReduced leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput) :
    ∃ specOutput,
      R2ReducedTypeMatchRel left right specIncoming specOutput ∧
        TypeBindingState specOutput leaOutput := by
  by_cases hleftUndefined : left = Atom.undefinedType
  · subst left
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" == Metta.Atom.sym "%Undefined%") =
          true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchReduced, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      change TypeBindingSatisfied valuation specIncoming ↔
        TypeBindingSatisfied valuation specIncoming ∧ True
      tauto
  by_cases hrightUndefined : right = Atom.undefinedType
  · subst right
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" == Metta.Atom.sym "%Undefined%") =
          true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchReduced, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      have hconsistent :
          ReducedTypeConsistent valuation left Atom.undefinedType :=
        reducedTypeConsistent_right_undefined valuation left
      constructor
      · intro hincoming
        exact ⟨hincoming, hconsistent⟩
      · exact fun hparts => hparts.1
  by_cases hexpressions : ∃ lefts rights,
      left = .expression lefts ∧ right = .expression rights
  · obtain ⟨lefts, rights, rfl, rfl⟩ := hexpressions
    have hleftBeq :
        (Metta.Atom.expr (toLeaTTaAtoms lefts) ==
          Metta.Atom.sym "%Undefined%") = false := rfl
    have hrightBeq :
        (Metta.Atom.expr (toLeaTTaAtoms rights) ==
          Metta.Atom.sym "%Undefined%") = false := rfl
    have hlistSuccess :
        Metta.Minimal.matchReducedList leaIncoming
            (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) =
          some leaOutput := by
      simp only [toLeaTTaAtom] at hsuccess
      rw [Metta.Minimal.matchReduced.eq_1, hleftBeq, hrightBeq] at hsuccess
      exact hsuccess
    obtain ⟨specOutput, hlistRel, outputState⟩ :=
      matchReducedList_r2_sound state hlistSuccess
    refine ⟨specOutput, ?_, outputState⟩
    constructor
    · exact hlistRel.satisfiable
    · intro valuation
      simpa [ReducedTypeConsistent] using hlistRel.solutions valuation
  · have hnotBothExpressions : ∀ lefts rights,
        left = .expression lefts → right = .expression rights → False := by
      intro lefts rights hleft hright
      exact hexpressions ⟨lefts, rights, hleft, hright⟩
    exact matchReduced_leaf_r2_sound state hnotBothExpressions
      hleftUndefined hrightUndefined hsuccess
termination_by 2 * (sizeOf left + sizeOf right)

/-- Pointwise companion of `matchReduced_r2_sound`; each successful child
extends the state consumed by the next child. -/
private theorem matchReducedList_r2_sound
    {left right : List Atom}
    {specIncoming : Bindings} {leaIncoming leaOutput : Metta.Bindings}
    (state : TypeBindingState specIncoming leaIncoming)
    (hsuccess : Metta.Minimal.matchReducedList leaIncoming
      (toLeaTTaAtoms left) (toLeaTTaAtoms right) = some leaOutput) :
    ∃ specOutput,
      R2ReducedTypeListMatchRel left right specIncoming specOutput ∧
        TypeBindingState specOutput leaOutput := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have hsame : leaIncoming = leaOutput := by
            simpa [Metta.Minimal.matchReducedList] using hsuccess
          subst leaOutput
          refine ⟨specIncoming, ?_, state⟩
          constructor
          · exact state.specSatisfiable
          · intro valuation
            simp [ReducedTypeListConsistent]
      | cons rightHead rightTail =>
          simp [toLeaTTaAtoms, Metta.Minimal.matchReducedList] at hsuccess
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp [toLeaTTaAtoms, Metta.Minimal.matchReducedList] at hsuccess
      | cons rightHead rightTail =>
          cases hnext : Metta.Minimal.matchReduced leaIncoming
              (toLeaTTaAtom leftHead) (toLeaTTaAtom rightHead) with
          | none =>
              simp [toLeaTTaAtoms, Metta.Minimal.matchReducedList,
                hnext] at hsuccess
          | some leaNext =>
              have htailSuccess :
                  Metta.Minimal.matchReducedList leaNext
                      (toLeaTTaAtoms leftTail) (toLeaTTaAtoms rightTail) =
                    some leaOutput := by
                simpa [toLeaTTaAtoms, Metta.Minimal.matchReducedList,
                  hnext] using hsuccess
              obtain ⟨specNext, hheadRel, nextState⟩ :=
                matchReduced_r2_sound state hnext
              obtain ⟨specOutput, htailRel, outputState⟩ :=
                matchReducedList_r2_sound nextState htailSuccess
              refine ⟨specOutput, ?_, outputState⟩
              constructor
              · exact htailRel.satisfiable
              · intro valuation
                rw [htailRel.solutions valuation,
                  hheadRel.solutions valuation]
                simp only [ReducedTypeListConsistent]
                tauto
termination_by 2 * (sizeOf left + sizeOf right) + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

end

/-- Top-level gradual wildcards plus repaired recursive R2 matching realize
the explicitly named core-plus-R2 relation and preserve the reachable state. -/
theorem matchType_corePlusR2_sound
    {left right : Atom}
    {specIncoming : Bindings} {leaIncoming leaOutput : Metta.Bindings}
    (state : TypeBindingState specIncoming leaIncoming)
    (hsuccess : Metta.Minimal.matchType leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput) :
    ∃ specOutput,
      CorePlusR2TypeMatchRel left right specIncoming specOutput ∧
        TypeBindingState specOutput leaOutput := by
  by_cases hleftUndefined : left = Atom.undefinedType
  · subst left
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" == Metta.Atom.sym "%Undefined%") =
          true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      have hconsistent :
          CorePlusR2TypeConsistent valuation Atom.undefinedType right := by
        exact Or.inl rfl
      tauto
  by_cases hrightUndefined : right = Atom.undefinedType
  · subst right
    have hundefinedBeq :
        (Metta.Atom.sym "%Undefined%" == Metta.Atom.sym "%Undefined%") =
          true := by decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.undefinedType, hundefinedBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      have hconsistent :
          CorePlusR2TypeConsistent valuation left Atom.undefinedType := by
        exact Or.inr (Or.inl rfl)
      tauto
  by_cases hleftAtom : left = Atom.atomType
  · subst left
    have hatomBeq :
        (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
      decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.atomType, hatomBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      have hconsistent :
          CorePlusR2TypeConsistent valuation Atom.atomType right := by
        exact Or.inr (Or.inr (Or.inl rfl))
      tauto
  by_cases hrightAtom : right = Atom.atomType
  · subst right
    have hatomBeq :
        (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
      decide
    have hsame : leaIncoming = leaOutput := by
      simpa [Metta.Minimal.matchType, toLeaTTaAtom,
        Atom.atomType, hatomBeq] using hsuccess
    subst leaOutput
    refine ⟨specIncoming, ?_, state⟩
    constructor
    · exact state.specSatisfiable
    · intro valuation
      have hconsistent :
          CorePlusR2TypeConsistent valuation left Atom.atomType := by
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      tauto
  have hleftUndefinedBeq :=
    toLeaTTaAtom_beq_undefined_eq_false left hleftUndefined
  have hrightUndefinedBeq :=
    toLeaTTaAtom_beq_undefined_eq_false right hrightUndefined
  have hleftAtomBeq :=
    toLeaTTaAtom_beq_atomType_eq_false left hleftAtom
  have hrightAtomBeq :=
    toLeaTTaAtom_beq_atomType_eq_false right hrightAtom
  have hreduced : Metta.Minimal.matchReduced leaIncoming
      (toLeaTTaAtom left) (toLeaTTaAtom right) = some leaOutput := by
    rw [Metta.Minimal.matchType, hleftUndefinedBeq,
      hrightUndefinedBeq, hleftAtomBeq, hrightAtomBeq] at hsuccess
    exact hsuccess
  obtain ⟨specOutput, hr2, outputState⟩ :=
    matchReduced_r2_sound state hreduced
  refine ⟨specOutput, ?_, outputState⟩
  constructor
  · exact hr2.satisfiable
  · intro valuation
    rw [hr2.solutions valuation]
    simp [CorePlusR2TypeConsistent, hleftUndefined, hrightUndefined,
      hleftAtom, hrightAtom]

/-- α-closed form of the application-argument fold soundness: each position
carries evidence at a raw base type together with an injective renaming onto
the actual type consumed by the runtime match.  This is exactly the premise
shape of `RuntimeArgumentsApplicableRel.cons`. -/
private theorem matchApplicationTypeArguments_r1_alpha_sound
    {space : Space} {arguments actualTypes : List Atom}
    (evidence : List.Forall₂
      (fun argument actualType => ∃ actualBase,
        RuntimeTypeEvidenceRel space argument actualBase ∧
          TypeVariableRenamingOf actualBase actualType)
      arguments actualTypes) :
    ∀ {expectedTypes : List Atom}
      {specIncoming : Bindings}
      {leaIncoming leaOutput : Metta.Bindings},
      TypeBindingState specIncoming leaIncoming →
      Metta.Minimal.matchApplicationTypeArguments leaIncoming
        (toLeaTTaAtoms expectedTypes) (toLeaTTaAtoms actualTypes) =
          some leaOutput →
      ∃ specOutput,
        RuntimeArgumentsApplicableRel space arguments expectedTypes
            specIncoming specOutput ∧
          TypeBindingState specOutput leaOutput := by
  induction evidence with
  | nil =>
      intro expectedTypes specIncoming leaIncoming leaOutput state hsuccess
      cases expectedTypes with
      | nil =>
          have hsame : leaIncoming = leaOutput := by
            simpa [toLeaTTaAtoms,
              Metta.Minimal.matchApplicationTypeArguments] using hsuccess
          subst leaOutput
          exact ⟨specIncoming, .nil specIncoming, state⟩
      | cons expected expectedTypes =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at hsuccess
  | @cons argument actualType arguments actualTypes hactual htail ih =>
      intro expectedTypes specIncoming leaIncoming leaOutput state hsuccess
      cases expectedTypes with
      | nil =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at hsuccess
      | cons expected expectedTypes =>
          simp only [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at hsuccess
          generalize hnext : Metta.Minimal.matchType leaIncoming
            (toLeaTTaAtom expected) (toLeaTTaAtom actualType) = next at hsuccess
          cases next with
          | none => simp at hsuccess
          | some leaNext =>
              obtain ⟨actualBase, hbase, hrenaming⟩ := hactual
              obtain ⟨specNext, hmatch, nextState⟩ :=
                matchType_corePlusR2_sound state hnext
              obtain ⟨specOutput, hrest, outputState⟩ :=
                ih nextState hsuccess
              exact ⟨specOutput,
                .cons hbase hrenaming hmatch hrest, outputState⟩

/-- Repaired LeaTTa's application-argument fold realizes the spec R1 fold:
each runtime type choice is justified independently, and every successful
core-plus-R2 match extends the shared reachable binding state. -/
theorem matchApplicationTypeArguments_r1_sound
    {space : Space} {arguments actualTypes : List Atom}
    (evidence : List.Forall₂
      (RuntimeTypeEvidenceRel space) arguments actualTypes) :
    ∀ {expectedTypes : List Atom}
      {specIncoming : Bindings}
      {leaIncoming leaOutput : Metta.Bindings},
      TypeBindingState specIncoming leaIncoming →
      Metta.Minimal.matchApplicationTypeArguments leaIncoming
        (toLeaTTaAtoms expectedTypes) (toLeaTTaAtoms actualTypes) =
          some leaOutput →
      ∃ specOutput,
        RuntimeArgumentsApplicableRel space arguments expectedTypes
            specIncoming specOutput ∧
          TypeBindingState specOutput leaOutput :=
  matchApplicationTypeArguments_r1_alpha_sound
    (evidence.imp fun _ _ hactual =>
      ⟨_, hactual, TypeVariableRenamingOf.refl _⟩)

/-! ## Recursive R1 application inference -/

/-- If pointwise decode/re-encode preserves a whole list, it preserves every
member at its corresponding position. -/
private theorem atom_roundtrip_of_atoms_roundtrip
    {atoms : List Metta.Atom}
    (roundtrip : toLeaTTaAtoms (fromLeaTTaAtoms atoms) = atoms) :
    ∀ {atom}, atom ∈ atoms →
      toLeaTTaAtom (fromLeaTTaAtom atom) = atom := by
  induction atoms with
  | nil => simp
  | cons head tail ih =>
      simp only [fromLeaTTaAtoms, toLeaTTaAtoms,
        List.cons.injEq] at roundtrip
      intro atom hmem
      rcases roundtrip with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hmem with rfl | htailMem
      · exact hhead
      · exact ih htail htailMem

/-- The gradual fallback is an image atom when an arrow carries no return;
otherwise the selected last component inherits the list's image provenance. -/
private theorem getLastD_heImage
    (atoms : List Metta.Atom)
    (image : ∀ atom ∈ atoms, LeaAtomHEImage atom) :
    LeaAtomHEImage
      ((atoms.getLast?).getD (.sym "%Undefined%")) := by
  cases atoms with
  | nil => simpa using leaAtomHEImage_sym "%Undefined%"
  | cons head tail =>
      rw [List.getLast?_eq_some_getLast (by simp)]
      simp only [Option.getD_some]
      apply image
      exact List.getLast_mem (by simp)

/-- Every successful R1 candidate assembled from image-valued function types
and an ordered Cartesian family of actual-type choices remains in the exact
native image.  The candidate lists are abstract, so this theorem is the
stable membership boundary for the runtime's expression-type inference. -/
private theorem inferredType_member_heImage
    {functionTypes : List Metta.Atom}
    {actualTypeChoices : List (List Metta.Atom)} {leaType : Metta.Atom}
    (prepareActuals : List Metta.Atom → List Metta.Atom)
    (functionsImage : ∀ type ∈ functionTypes, LeaAtomHEImage type)
    (actualsImage : ∀ actualTypes ∈ actualTypeChoices,
      ∀ type ∈ prepareActuals actualTypes, LeaAtomHEImage type)
    (hmem : leaType ∈
      functionTypes.flatMap (fun type =>
        actualTypeChoices.filterMap (fun actualTypes =>
          match type with
          | .expr (.sym "->" :: types) =>
              match types.getLast? with
              | none => none
              | some returnType =>
                  match Metta.Minimal.matchApplicationTypeArguments []
                      types.dropLast (prepareActuals actualTypes) with
                  | some bindings =>
                      some (Metta.instantiate bindings returnType)
                  | none => none
          | _ => none))) :
    LeaAtomHEImage leaType := by
  obtain ⟨functionType, hfunctionMem, functionResult⟩ :=
    List.mem_flatMap.mp hmem
  obtain ⟨actualTypes, hactualTypesMem, hresult⟩ :=
    List.mem_filterMap.mp functionResult
  cases functionType with
  | sym name => simp at hresult
  | var name => simp at hresult
  | gnd value => simp at hresult
  | expr functionAtoms =>
      cases functionAtoms with
      | nil => simp at hresult
      | cons functionHead types =>
          cases functionHead with
          | var name => simp at hresult
          | gnd value => simp at hresult
          | expr atoms => simp at hresult
          | sym name =>
              by_cases harrow : name = "->"
              · subst name
                cases hlast : types.getLast? with
                | none => simp [hlast] at hresult
                | some returnType =>
                    generalize hmatch :
                      Metta.Minimal.matchApplicationTypeArguments []
                        types.dropLast (prepareActuals actualTypes) = matched
                          at hresult
                    cases matched with
                    | none => simp [hlast, hmatch] at hresult
                    | some bindings =>
                        have houtput :
                            Metta.instantiate bindings returnType =
                              leaType := by
                          simpa [hlast, hmatch] using hresult
                        have hfunctionImage := functionsImage _ hfunctionMem
                        have htypesImage :
                            ∀ type ∈ types, LeaAtomHEImage type := by
                          intro type htype
                          exact leaAtomHEImage_children hfunctionImage type
                            (List.mem_cons_of_mem _ htype)
                        have hbindingsImage : LeaBindingsHEImage bindings :=
                          matchApplicationTypeArguments_result_heImage
                            leaBindingsHEImage_empty
                            (fun type htype => htypesImage type
                              (List.mem_of_mem_dropLast htype))
                            (actualsImage actualTypes hactualTypesMem) hmatch
                        rw [← houtput]
                        exact instantiate_heImage hbindingsImage returnType
                          (htypesImage returnType
                            (List.mem_of_getLast? hlast))
              · simp [harrow] at hresult

/-- With no direct expression annotation, the published core supplies its
gradual `%Undefined%` fallback. -/
private theorem undefined_expression_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (head : Atom) (tail : List Atom)
    (hdirect :
      env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail))) = []) :
    RuntimeTypeEvidenceRel space (.expression (head :: tail))
      Atom.undefinedType := by
  have hannotations :
      getAnnotatedTypes space (.expression (head :: tail)) = [] := by
    have htranslated := index.expressionTypes head tail
    rw [hdirect] at htranslated
    have hdecoded := congrArg fromLeaTTaAtoms htranslated
    simpa using hdecoded.symm
  apply RuntimeTypeEvidenceRel.published
  apply (typeOfRel_iff_mem_getAtomTypes _ _ _).mpr
  simp [getAtomTypes, hannotations, Atom.undefinedType]

/-! ### Capture-avoiding freshening bridge

The runtime consumes α-variants of its raw candidate types: argument types
through `Metta.Minimal.freshenArgumentTypes` and function candidates through
`Metta.Minimal.freshenTypeCandidate`.  The lemmas below commute decoding and
encoding with total variable renaming, transport round trips and image
provenance across freshening, and package the injective renaming witness
demanded by the α-premises of the extended R1 layer. -/

mutual

/-- Decoding commutes with total variable renaming. -/
private theorem fromLeaTTaAtom_renameAllVars
    (rename : Metta.VarName → Metta.VarName) (atom : Metta.Atom) :
    fromLeaTTaAtom (Metta.Minimal.renameAllVars rename atom) =
      renameTypeVars rename (fromLeaTTaAtom atom) := by
  cases atom with
  | sym name =>
      simp [Metta.Minimal.renameAllVars, fromLeaTTaAtom,
        renameTypeVars]
  | var name =>
      simp [Metta.Minimal.renameAllVars, fromLeaTTaAtom,
        renameTypeVars]
  | gnd value =>
      simp [Metta.Minimal.renameAllVars, fromLeaTTaAtom,
        renameTypeVars]
  | expr atoms =>
      simp only [Metta.Minimal.renameAllVars, fromLeaTTaAtom,
        renameTypeVars]
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_renameAllVars rename atoms)
termination_by 2 * sizeOf atom

/-- List companion of `fromLeaTTaAtom_renameAllVars`. -/
private theorem fromLeaTTaAtoms_renameAllVars
    (rename : Metta.VarName → Metta.VarName) (atoms : List Metta.Atom) :
    fromLeaTTaAtoms (atoms.map (Metta.Minimal.renameAllVars rename)) =
      (fromLeaTTaAtoms atoms).map (renameTypeVars rename) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_renameAllVars rename atom)
        (fromLeaTTaAtoms_renameAllVars rename atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

mutual

/-- Encoding commutes with total variable renaming. -/
private theorem toLeaTTaAtom_renameTypeVars
    (rename : String → String) (atom : Atom) :
    toLeaTTaAtom (renameTypeVars rename atom) =
      Metta.Minimal.renameAllVars rename (toLeaTTaAtom atom) := by
  cases atom with
  | symbol name =>
      simp [renameTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | var name =>
      simp [renameTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | grounded value =>
      simp [renameTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
  | expression atoms =>
      simp only [renameTypeVars, toLeaTTaAtom,
        Metta.Minimal.renameAllVars]
      exact congrArg Metta.Atom.expr
        (toLeaTTaAtoms_renameTypeVars rename atoms)
termination_by 2 * sizeOf atom

/-- List companion of `toLeaTTaAtom_renameTypeVars`. -/
private theorem toLeaTTaAtoms_renameTypeVars
    (rename : String → String) (atoms : List Atom) :
    toLeaTTaAtoms (atoms.map (renameTypeVars rename)) =
      (toLeaTTaAtoms atoms).map (Metta.Minimal.renameAllVars rename) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (toLeaTTaAtom_renameTypeVars rename atom)
        (toLeaTTaAtoms_renameTypeVars rename atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Every decoded freshened candidate is an α-variant presentation of the
decoded raw candidate: capture-avoiding renaming is injective. -/
private theorem typeVariableRenamingOf_freshenTypeCandidate
    (avoid : List Metta.VarName) (position : Nat) (atom : Metta.Atom) :
    TypeVariableRenamingOf (fromLeaTTaAtom atom)
      (fromLeaTTaAtom
        (Metta.Minimal.freshenTypeCandidate avoid position atom)) :=
  ⟨Metta.Minimal.captureAvoidingName avoid position,
    Metta.Minimal.captureAvoidingName_injective avoid position,
    fromLeaTTaAtom_renameAllVars
      (Metta.Minimal.captureAvoidingName avoid position) atom⟩

/-- Exact round trips transport across capture-avoiding freshening. -/
private theorem roundtrip_freshenTypeCandidate
    {atom : Metta.Atom}
    (roundtrip : toLeaTTaAtom (fromLeaTTaAtom atom) = atom)
    (avoid : List Metta.VarName) (position : Nat) :
    toLeaTTaAtom (fromLeaTTaAtom
      (Metta.Minimal.freshenTypeCandidate avoid position atom)) =
      Metta.Minimal.freshenTypeCandidate avoid position atom := by
  simp only [Metta.Minimal.freshenTypeCandidate]
  rw [fromLeaTTaAtom_renameAllVars, toLeaTTaAtom_renameTypeVars,
    roundtrip]

/-- Exact image provenance transports across capture-avoiding freshening. -/
private theorem leaAtomHEImage_freshenTypeCandidate
    (avoid : List Metta.VarName) (position : Nat) {atom : Metta.Atom}
    (himage : LeaAtomHEImage atom) :
    LeaAtomHEImage
      (Metta.Minimal.freshenTypeCandidate avoid position atom) := by
  obtain ⟨native, rfl⟩ := himage
  exact ⟨renameTypeVars
      (Metta.Minimal.captureAvoidingName avoid position) native,
    toLeaTTaAtom_renameTypeVars
      (Metta.Minimal.captureAvoidingName avoid position) native⟩

/-- Every freshened argument type is a capture-avoiding freshening of some
member of the raw selected argument-type list. -/
private theorem mem_freshenArgumentTypes
    {avoid : List Metta.VarName} {position : Nat}
    {raws : List Metta.Atom} {fresh : Metta.Atom}
    (hmem : fresh ∈
      Metta.Minimal.freshenArgumentTypes avoid position raws) :
    ∃ raw ∈ raws, ∃ avoid' position',
      fresh = Metta.Minimal.freshenTypeCandidate avoid' position' raw := by
  induction raws generalizing avoid position with
  | nil => simp [Metta.Minimal.freshenArgumentTypes] at hmem
  | cons raw raws ih =>
      simp only [Metta.Minimal.freshenArgumentTypes] at hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact ⟨raw, List.mem_cons_self, avoid, position, rfl⟩
      · obtain ⟨raw', hraw', avoid', position', rfl⟩ := ih htail
        exact ⟨raw', List.mem_cons_of_mem _ hraw', avoid', position', rfl⟩

/-- Every member on the right of an aligned list relation has a related
member on the left. -/
private theorem forall₂_exists_left_of_mem_right
    {α β : Type*} {relation : α → β → Prop} {left : List α} {right : List β}
    (aligned : List.Forall₂ relation left right) :
    ∀ item ∈ right, ∃ source ∈ left, relation source item := by
  induction aligned with
  | nil => simp
  | @cons source item left right head tail inductionHypothesis =>
      intro target member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨source, by simp, head⟩
      · obtain ⟨source', sourceMember, related⟩ :=
          inductionHypothesis target member
        exact ⟨source', by simp [sourceMember], related⟩

/-- Every member on the left of an aligned list relation has a related member
on the right. -/
private theorem forall₂_exists_right_of_mem_left
    {α β : Type*} {relation : α → β → Prop} {left : List α} {right : List β}
    (aligned : List.Forall₂ relation left right) :
    ∀ item ∈ left, ∃ target ∈ right, relation item target := by
  induction aligned with
  | nil => simp
  | @cons source target left right head tail inductionHypothesis =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨target, by simp, head⟩
      · obtain ⟨target', targetMember, related⟩ :=
          inductionHypothesis item member
        exact ⟨target', by simp [targetMember], related⟩

/-- Freshening any member of one Cartesian choice preserves exact native
image provenance, provided every input candidate list is image-valued. -/
private theorem freshened_cartesian_choice_heImage
    {candidateLists : List (List Metta.Atom)} {rawTypes : List Metta.Atom}
    (rawMember : rawTypes ∈ Metta.Minimal.cartesian candidateLists)
    (candidateImages : ∀ candidates ∈ candidateLists,
      ∀ type ∈ candidates, LeaAtomHEImage type)
    (avoid : List Metta.VarName) (position : Nat) :
    ∀ fresh ∈ Metta.Minimal.freshenArgumentTypes avoid position rawTypes,
      LeaAtomHEImage fresh := by
  have aligned := Metta.mem_cartesian_iff_forall₂.mp rawMember
  intro fresh freshMember
  obtain ⟨raw, rawMember, avoid', position', rfl⟩ :=
    mem_freshenArgumentTypes freshMember
  obtain ⟨candidates, candidatesMember, rawInCandidates⟩ :=
    forall₂_exists_right_of_mem_left aligned raw rawMember
  exact leaAtomHEImage_freshenTypeCandidate _ _
    (candidateImages candidates candidatesMember raw rawInCandidates)

/-- An application-argument fold with no declared parameter types succeeds
exactly on the empty actual list and returns its incoming bindings. -/
private theorem matchApplicationTypeArguments_nil_expected
    {incoming output : Metta.Bindings} {actuals : List Metta.Atom}
    (hsuccess : Metta.Minimal.matchApplicationTypeArguments incoming []
      actuals = some output) :
    actuals = [] ∧ output = incoming := by
  cases actuals with
  | nil =>
      refine ⟨rfl, ?_⟩
      have hsame := hsuccess
      simp [Metta.Minimal.matchApplicationTypeArguments] at hsame
      exact hsame.symm
  | cons actual actuals =>
      simp [Metta.Minimal.matchApplicationTypeArguments] at hsuccess

/-- Pointwise recursive soundness supplies α-closed R1 evidence for any one
ordered Cartesian choice of argument types.  This is deliberately
membership-based: no proof depends on how the Cartesian product enumerates
its choices. -/
private theorem freshened_argument_evidence
    {space : Space} {env : Metta.Minimal.MinEnv} (tail : List Atom)
    (tailEvidence : ∀ argument ∈ tail, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        RuntimeTypeEvidenceRel space argument
          (fromLeaTTaAtom leaType))
    (rawTypes : List Metta.Atom)
    (rawMember : rawTypes ∈ Metta.Minimal.cartesian
      (tail.map (fun argument =>
        Metta.Minimal.getTypes env (toLeaTTaAtom argument))))
    (avoid : List Metta.VarName) (position : Nat) :
    List.Forall₂ (fun argument actualType => ∃ actualBase,
        RuntimeTypeEvidenceRel space argument actualBase ∧
          TypeVariableRenamingOf actualBase actualType)
      tail
      (fromLeaTTaAtoms (Metta.Minimal.freshenArgumentTypes avoid position
        rawTypes)) := by
  induction tail generalizing rawTypes avoid position with
  | nil =>
      simp [Metta.Minimal.cartesian] at rawMember
      subst rawTypes
      exact .nil
  | cons argument tail inductionHypothesis =>
      simp only [List.map_cons, Metta.Minimal.cartesian,
        List.mem_flatMap, List.mem_map] at rawMember
      obtain ⟨rawType, rawTypeMember, rawTail, rawTailMember, rfl⟩ :=
        rawMember
      simp only [Metta.Minimal.freshenArgumentTypes,
        fromLeaTTaAtoms]
      apply List.Forall₂.cons
      · refine ⟨fromLeaTTaAtom rawType, ?_, ?_⟩
        · exact tailEvidence argument (by simp) rawTypeMember
        · exact typeVariableRenamingOf_freshenTypeCandidate avoid position _
      · apply inductionHypothesis
        intro child hchild leaType hmem
        exact tailEvidence child (by simp [hchild]) hmem
        exact rawTailMember

/-- List round trips transport across freshening of any one ordered Cartesian
argument-type choice. -/
private theorem freshened_argument_roundtrip
    {env : Metta.Minimal.MinEnv} (tail : List Atom)
    (tailRoundtrip : ∀ argument ∈ tail, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        toLeaTTaAtom (fromLeaTTaAtom leaType) = leaType)
    (rawTypes : List Metta.Atom)
    (rawMember : rawTypes ∈ Metta.Minimal.cartesian
      (tail.map (fun argument =>
        Metta.Minimal.getTypes env (toLeaTTaAtom argument))))
    (avoid : List Metta.VarName) (position : Nat) :
    toLeaTTaAtoms (fromLeaTTaAtoms
      (Metta.Minimal.freshenArgumentTypes avoid position rawTypes)) =
    Metta.Minimal.freshenArgumentTypes avoid position rawTypes := by
  induction tail generalizing rawTypes avoid position with
  | nil =>
      simp [Metta.Minimal.cartesian] at rawMember
      subst rawTypes
      rfl
  | cons argument tail inductionHypothesis =>
      simp only [List.map_cons, Metta.Minimal.cartesian,
        List.mem_flatMap, List.mem_map] at rawMember
      obtain ⟨rawType, rawTypeMember, rawTail, rawTailMember, rfl⟩ :=
        rawMember
      simp only [Metta.Minimal.freshenArgumentTypes, fromLeaTTaAtoms,
        toLeaTTaAtoms]
      rw [roundtrip_freshenTypeCandidate
        (tailRoundtrip argument (by simp) rawTypeMember),
        inductionHypothesis]
      intro child hchild leaType hmem
      exact tailRoundtrip child (by simp [hchild]) hmem
      exact rawTailMember

/-- The recursive application branch of `getTypes` realizes named refinement
R1.  Representation preservation is exposed only as pointwise round-trip
premises; a separate structural theorem supplies them for reachable runtime
outputs. -/
theorem getTypes_inferredExpression_runtimeEvidence
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (head : Atom) (tail : List Atom)
    (hnotState : ∀ leaValue,
      toLeaTTaAtom head = .sym "StateValue" →
      toLeaTTaAtoms tail = [leaValue] → False)
    (hdirect :
      env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom (.expression (head :: tail))) = [])
    (headEvidence : ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom head) →
        RuntimeTypeEvidenceRel space head (fromLeaTTaAtom leaType))
    (tailEvidence : ∀ argument ∈ tail, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        RuntimeTypeEvidenceRel space argument
          (fromLeaTTaAtom leaType))
    (headRoundtrip : ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom head) →
        toLeaTTaAtom (fromLeaTTaAtom leaType) = leaType)
    (tailRoundtrip : ∀ argument ∈ tail, ∀ {leaType},
      leaType ∈ Metta.Minimal.getTypes env (toLeaTTaAtom argument) →
        toLeaTTaAtom (fromLeaTTaAtom leaType) = leaType)
    {leaType : Metta.Atom}
    (hmem : leaType ∈ Metta.Minimal.getTypes env
      (toLeaTTaAtom (.expression (head :: tail)))) :
    RuntimeTypeEvidenceRel space (.expression (head :: tail))
      (fromLeaTTaAtom leaType) := by
  have hdirect' :
      env.exprTypes.filter (fun entry =>
        entry.1 == .expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) = [] := by
    simpa [toLeaTTaAtom] using hdirect
  change leaType ∈ Metta.Minimal.getTypes env
    (.expr (toLeaTTaAtom head :: toLeaTTaAtoms tail)) at hmem
  rw [Metta.Minimal.getTypes.eq_10 env
    (toLeaTTaAtom head) (toLeaTTaAtoms tail) hnotState,
    hdirect'] at hmem
  simp only at hmem
  split at hmem
  next hinferred =>
      have htype : leaType = Metta.Atom.sym "%Undefined%" := by
        simpa using hmem
      subst leaType
      simpa [fromLeaTTaAtom, Atom.undefinedType] using
        undefined_expression_runtimeEvidence index head tail hdirect
  next hinferred =>
      obtain ⟨functionFresh, hfreshMem, functionResults⟩ :=
        List.mem_flatMap.mp hmem
      obtain ⟨rawArgTypes, hrawArgTypes, hfunctionResult⟩ :=
        List.mem_filterMap.mp functionResults
      obtain ⟨functionRaw, hrawMem, hfreshEq⟩ := List.mem_map.mp hfreshMem
      cases functionFresh with
      | sym name => simp at hfunctionResult
      | var name => simp at hfunctionResult
      | gnd value => simp at hfunctionResult
      | expr functionAtoms =>
          cases functionAtoms with
          | nil => simp at hfunctionResult
          | cons functionHead types =>
              cases functionHead with
              | var name => simp at hfunctionResult
              | gnd value => simp at hfunctionResult
              | expr atoms => simp at hfunctionResult
              | sym name =>
                  by_cases harrow : name = "->"
                  · subst name
                    simp only [] at hfunctionResult
                    by_cases htypes : types = []
                    · subst htypes
                      simp at hfunctionResult
                    · have hlast :
                        types.getLast? = some (types.getLast htypes) :=
                      List.getLast?_eq_some_getLast htypes
                      simp only [hlast] at hfunctionResult
                      split at hfunctionResult
                      next leaBindings hmatch =>
                        obtain rfl := Option.some.inj hfunctionResult
                        have hfreshRoundtrip :
                            toLeaTTaAtom (fromLeaTTaAtom
                              (Metta.Atom.expr
                                (Metta.Atom.sym "->" :: types))) =
                              Metta.Atom.expr
                                (Metta.Atom.sym "->" :: types) := by
                          rw [← hfreshEq]
                          exact roundtrip_freshenTypeCandidate
                            (headRoundtrip hrawMem) _ _
                        have htypesRoundtrip :
                            toLeaTTaAtoms (fromLeaTTaAtoms types) = types := by
                          simpa [fromLeaTTaAtom, toLeaTTaAtom,
                            fromLeaTTaAtoms, toLeaTTaAtoms] using
                              Metta.Atom.expr.inj hfreshRoundtrip
                        have hexpectedRoundtrip :
                            toLeaTTaAtoms
                                (fromLeaTTaAtoms types.dropLast) =
                              types.dropLast := by
                          have hdrop := congrArg List.dropLast htypesRoundtrip
                          simpa [toLeaTTaAtoms_eq_map,
                            fromLeaTTaAtoms_eq_map] using hdrop
                        rw [← hexpectedRoundtrip,
                          ← freshened_argument_roundtrip tail
                            tailRoundtrip rawArgTypes
                            (by simpa [toLeaTTaAtoms_eq_map,
                              List.map_map, Function.comp_def] using
                                hrawArgTypes) _ 0] at hmatch
                        obtain ⟨specBindings, harguments, outputState⟩ :=
                          matchApplicationTypeArguments_r1_alpha_sound
                            (freshened_argument_evidence tail
                              tailEvidence rawArgTypes
                              (by simpa [toLeaTTaAtoms_eq_map,
                                List.map_map, Function.comp_def] using
                                  hrawArgTypes) _ 0)
                            typeBindingState_empty hmatch
                        have hsplit :
                            types.dropLast ++
                              [(types.getLast?).getD (.sym "%Undefined%")] =
                              types := by
                          rw [hlast]
                          simpa using List.dropLast_append_getLast htypes
                        have hfunctionType :
                            FunctionTypeRel
                              (fromLeaTTaAtom
                                (.expr (.sym "->" :: types)))
                              (fromLeaTTaAtoms types.dropLast)
                              (fromLeaTTaAtom
                                ((types.getLast?).getD
                                  (.sym "%Undefined%"))) := by
                          change Atom.expression
                              (.symbol "->" :: fromLeaTTaAtoms types) =
                            Atom.expression
                              (.symbol "->" ::
                                (fromLeaTTaAtoms types.dropLast ++
                                  [fromLeaTTaAtom
                                    ((types.getLast?).getD
                                      (.sym "%Undefined%"))]))
                          apply congrArg Atom.expression
                          exact congrArg (List.cons (Atom.symbol "->"))
                            (by
                              simpa [fromLeaTTaAtoms_eq_map] using
                                congrArg (List.map fromLeaTTaAtom)
                                  hsplit.symm)
                        have hreturnRoundtrip :
                            toLeaTTaAtom
                                (fromLeaTTaAtom
                                  ((types.getLast?).getD
                                    (.sym "%Undefined%"))) =
                              (types.getLast?).getD (.sym "%Undefined%") := by
                          apply atom_roundtrip_of_atoms_roundtrip
                            htypesRoundtrip
                          rw [hlast]
                          simp
                        have hrenaming :
                            TypeVariableRenamingOf
                              (fromLeaTTaAtom functionRaw)
                              (fromLeaTTaAtom
                                (.expr (.sym "->" :: types))) := by
                          rw [← hfreshEq]
                          exact typeVariableRenamingOf_freshenTypeCandidate
                            _ _ functionRaw
                        have hreturn :=
                          outputState.returnObserved
                            (fromLeaTTaAtom
                              ((types.getLast?).getD (.sym "%Undefined%")))
                        rw [hreturnRoundtrip] at hreturn
                        have hreturn' : R1ReturnTypeObserved specBindings
                            (fromLeaTTaAtom
                              ((types.getLast?).getD (.sym "%Undefined%")))
                            (fromLeaTTaAtom
                              (Metta.instantiate leaBindings
                                (types.getLast htypes))) := by
                          simpa [hlast] using hreturn
                        exact RuntimeTypeEvidenceRel.application
                          (R1ApplicationResultRel.mk rfl
                            (headEvidence hrawMem) hrenaming hfunctionType
                            harguments hreturn')
                      next hmatch => simp at hfunctionResult
                  · simp [harrow] at hfunctionResult

/-- Every type returned by repaired LeaTTa from an image input and a
translation-indexed environment remains in the exact native image. -/
theorem getTypes_result_heImage
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) :
    ∀ atom leaType,
      LeaAtomHEImage atom →
      leaType ∈ Metta.Minimal.getTypes env atom →
      LeaAtomHEImage leaType := by
  intro atom
  fun_induction Metta.Minimal.getTypes env atom <;>
    intro leaType inputImage hmem
  case case1 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "Number"
  case case2 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "Number"
  case case3 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "String"
  case case4 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "Bool"
  case case5 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym _
  case case6 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "Grounded"
  case case7 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "%Undefined%"
  case case8 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "%Undefined%"
  case case9 s _ =>
    exact index.symbolHEImage hmem
  case case10 value ih =>
    simp at hmem
    subst leaType
    have valueImage : LeaAtomHEImage value :=
      leaAtomHEImage_children inputImage value (by simp)
    rw [leaAtomHEImage_expr_iff]
    apply leaAtomsHEImage_cons (leaAtomHEImage_sym "StateMonad")
    apply leaAtomsHEImage_cons
    · apply getTypes_head_heImage
      intro type htype
      exact ih type valueImage htype
    · exact leaAtomsHEImage_nil
  case case11 head arguments hnotState first rest hquery =>
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = first :: rest := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hindexed : leaType ∈
        (env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments))).map (·.2) := by
      rw [hquery']
      simpa [hquery'] using hmem
    have parts := heImage_expression_roundtrip_parts inputImage
    apply index.expressionHEImage
      (head := fromLeaTTaAtom head)
      (tail := fromLeaTTaAtoms arguments)
    change leaType ∈
      (env.exprTypes.filter (fun entry =>
        entry.1 == .expr
          (toLeaTTaAtom (fromLeaTTaAtom head) ::
            toLeaTTaAtoms (fromLeaTTaAtoms arguments)))).map (·.2)
    rw [parts.1, parts.2]
    exact hindexed
  case case12 head arguments hnotState hquery _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hget := hmem
    rw [hquery'] at hget
    simp only at hget
    split at hget
    next =>
      have htype : leaType = .sym "%Undefined%" := by
        simpa using hget
      subst leaType
      exact leaAtomHEImage_sym "%Undefined%"
    next =>
      have headImage : LeaAtomHEImage head :=
        leaAtomHEImage_children inputImage head (by simp)
      have argumentsImage :
          ∀ argument ∈ arguments, LeaAtomHEImage argument := by
        intro argument hargument
        exact leaAtomHEImage_children inputImage argument
          (List.mem_cons_of_mem _ hargument)
      refine inferredType_member_heImage
        (fun rawTypes =>
          Metta.Minimal.freshenArgumentTypes _ 0 rawTypes) ?_ ?_ hget
      · intro type htype
        obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htype
        exact leaAtomHEImage_freshenTypeCandidate _ _
          (ihHead raw headImage hraw)
      · intro rawTypes rawMember
        apply freshened_cartesian_choice_heImage rawMember
        intro candidates candidatesMember type typeMember
        obtain ⟨argument, argumentMember, rfl⟩ :=
          List.mem_map.mp candidatesMember
        exact ihArguments argument argumentMember type
          (argumentsImage argument argumentMember) typeMember
  case case13 head arguments hnotState hquery _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hget := hmem
    rw [hquery'] at hget
    simp only at hget
    split at hget
    next =>
      have htype : leaType = .sym "%Undefined%" := by
        simpa using hget
      subst leaType
      exact leaAtomHEImage_sym "%Undefined%"
    next =>
      have headImage : LeaAtomHEImage head :=
        leaAtomHEImage_children inputImage head (by simp)
      have argumentsImage :
          ∀ argument ∈ arguments, LeaAtomHEImage argument := by
        intro argument hargument
        exact leaAtomHEImage_children inputImage argument
          (List.mem_cons_of_mem _ hargument)
      refine inferredType_member_heImage
        (fun rawTypes =>
          Metta.Minimal.freshenArgumentTypes _ 0 rawTypes) ?_ ?_ hget
      · intro type htype
        obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htype
        exact leaAtomHEImage_freshenTypeCandidate _ _
          (ihHead raw headImage hraw)
      · intro rawTypes rawMember
        apply freshened_cartesian_choice_heImage rawMember
        intro candidates candidatesMember type typeMember
        obtain ⟨argument, argumentMember, rfl⟩ :=
          List.mem_map.mp candidatesMember
        exact ihArguments argument argumentMember type
          (argumentsImage argument argumentMember) typeMember
  case case14 =>
    simp at hmem
    subst leaType
    exact leaAtomHEImage_sym "%Undefined%"

/-- Repaired LeaTTa's complete recursive type lookup is sound for the
published spec core plus the explicitly named R1/R2/R3 runtime refinements.
The input and every output retain exact native-image provenance separately. -/
theorem getTypes_runtimeEvidence_of_heImage
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) :
    ∀ atom leaType,
      LeaAtomHEImage atom →
      leaType ∈ Metta.Minimal.getTypes env atom →
      RuntimeTypeEvidenceRel space (fromLeaTTaAtom atom)
        (fromLeaTTaAtom leaType) := by
  intro atom
  fun_induction Metta.Minimal.getTypes env atom <;>
    intro leaType inputImage hmem
  case case1 value =>
    apply getTypes_grounded_runtimeEvidence space env (.int value)
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaGround] using hmem
  case case2 value =>
    obtain ⟨native, hnative⟩ := inputImage
    cases native with
    | symbol name => simp [toLeaTTaAtom] at hnative
    | var name => simp [toLeaTTaAtom] at hnative
    | expression atoms => simp [toLeaTTaAtom] at hnative
    | grounded grounded =>
        cases grounded <;>
          simp [toLeaTTaAtom, toLeaTTaGround] at hnative
  case case3 value =>
    apply getTypes_grounded_runtimeEvidence space env (.string value)
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaGround] using hmem
  case case4 value =>
    apply getTypes_grounded_runtimeEvidence space env (.bool value)
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaGround] using hmem
  case case5 typeName payload =>
    apply getTypes_grounded_runtimeEvidence space env
      (.custom typeName payload)
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaGround] using hmem
  case case6 grounded hInt hFloat hString hBool hExternal =>
    obtain ⟨native, hnative⟩ := inputImage
    cases native with
    | symbol name => simp [toLeaTTaAtom] at hnative
    | var name => simp [toLeaTTaAtom] at hnative
    | expression atoms => simp [toLeaTTaAtom] at hnative
    | grounded nativeGrounded =>
        cases nativeGrounded with
        | int value =>
            have : grounded = .int value := by
              simpa [toLeaTTaAtom, toLeaTTaGround] using hnative.symm
            exact (hInt value this).elim
        | bool value =>
            have : grounded = .bool value := by
              simpa [toLeaTTaAtom, toLeaTTaGround] using hnative.symm
            exact (hBool value this).elim
        | string value =>
            have : grounded = .str value := by
              simpa [toLeaTTaAtom, toLeaTTaGround] using hnative.symm
            exact (hString value this).elim
        | custom typeName payload =>
            have : grounded = .external typeName payload := by
              simpa [toLeaTTaAtom, toLeaTTaGround] using hnative.symm
            exact (hExternal typeName payload this).elim
  case case7 name =>
    apply getTypes_variable_runtimeEvidence space env name
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom] using hmem
  case case8 name hbucket =>
    apply getTypes_symbol_runtimeEvidence index name
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, hbucket] using hmem
  case case9 name hbucket =>
    apply getTypes_symbol_runtimeEvidence index name
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, hbucket] using hmem
  case case10 value ih =>
    have valueImage : LeaAtomHEImage value :=
      leaAtomHEImage_children inputImage value (by simp)
    have valueRoundtrip :=
      toLeaTTaAtom_fromLeaTTaAtom_of_heImage valueImage
    have inputRoundtrip :=
      toLeaTTaAtom_fromLeaTTaAtom_of_heImage inputImage
    have translatedInput :
        toLeaTTaAtom
            (.expression [.symbol "StateValue", fromLeaTTaAtom value]) =
          .expr [.sym "StateValue", value] := by
      simpa [fromLeaTTaAtom, fromLeaTTaAtoms] using inputRoundtrip
    have contentEvidence : ∀ {type},
        type ∈ Metta.Minimal.getTypes env
            (toLeaTTaAtom (fromLeaTTaAtom value)) →
          RuntimeTypeEvidenceRel space (fromLeaTTaAtom value)
            (fromLeaTTaAtom type) := by
      intro type htype
      apply ih type valueImage
      simpa [valueRoundtrip] using htype
    have result := getTypes_stateValue_runtimeEvidence
      (value := fromLeaTTaAtom value) contentEvidence
      (leaType := leaType)
    apply result
    rw [translatedInput]
    simpa [Metta.Minimal.getTypes] using hmem
  case case11 head arguments hnotState first rest hquery =>
    have parts := heImage_expression_roundtrip_parts inputImage
    have inputRoundtrip :=
      toLeaTTaAtom_fromLeaTTaAtom_of_heImage inputImage
    have translatedInput :
        toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments)) =
          .expr (head :: arguments) := by
      simpa [fromLeaTTaAtom, fromLeaTTaAtoms] using inputRoundtrip
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = first :: rest := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hnotState' : ∀ leaValue,
        toLeaTTaAtom (fromLeaTTaAtom head) = .sym "StateValue" →
        toLeaTTaAtoms (fromLeaTTaAtoms arguments) = [leaValue] → False := by
      intro leaValue hhead harguments
      apply hnotState leaValue
      · exact parts.1.symm.trans hhead
      · exact parts.2.symm.trans harguments
    have hdirect :
        env.exprTypes.filter (fun entry =>
          entry.1 == toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments))) ≠ [] := by
      intro hempty
      have hempty' := hempty
      change env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom
          (fromLeaTTaAtom (.expr (head :: arguments)))) = [] at hempty'
      rw [inputRoundtrip] at hempty'
      rw [hquery'] at hempty'
      simp at hempty'
    apply getTypes_directExpression_runtimeEvidence index
      (fromLeaTTaAtom head) (fromLeaTTaAtoms arguments)
      hnotState' hdirect
    rw [translatedInput]
    simpa [Metta.Minimal.getTypes] using hmem
  case case12 head arguments hnotState hquery _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have parts := heImage_expression_roundtrip_parts inputImage
    have inputRoundtrip :=
      toLeaTTaAtom_fromLeaTTaAtom_of_heImage inputImage
    have translatedInput :
        toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments)) =
          .expr (head :: arguments) := by
      simpa [fromLeaTTaAtom, fromLeaTTaAtoms] using inputRoundtrip
    have headImage : LeaAtomHEImage head :=
      leaAtomHEImage_children inputImage head (by simp)
    have argumentsImage :
        ∀ argument ∈ arguments, LeaAtomHEImage argument := by
      intro argument hargument
      exact leaAtomHEImage_children inputImage argument
        (List.mem_cons_of_mem _ hargument)
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hnotState' : ∀ leaValue,
        toLeaTTaAtom (fromLeaTTaAtom head) = .sym "StateValue" →
        toLeaTTaAtoms (fromLeaTTaAtoms arguments) = [leaValue] → False := by
      intro leaValue hhead harguments
      exact hnotState leaValue
        (parts.1.symm.trans hhead)
        (parts.2.symm.trans harguments)
    have hdirect :
        env.exprTypes.filter (fun entry =>
          entry.1 == toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments))) = [] := by
      change env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom
          (fromLeaTTaAtom (.expr (head :: arguments)))) = []
      rw [inputRoundtrip]
      exact hquery'
    apply getTypes_inferredExpression_runtimeEvidence index
      (fromLeaTTaAtom head) (fromLeaTTaAtoms arguments)
      hnotState' hdirect
    · intro type htype
      rw [parts.1] at htype
      apply ihHead type headImage
      exact htype
    · intro argument hargument type htype
      rw [fromLeaTTaAtoms_eq_map] at hargument
      obtain ⟨leaArgument, hleaArgument, rfl⟩ :=
        List.mem_map.mp hargument
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage
        (argumentsImage leaArgument hleaArgument)] at htype
      apply ihArguments leaArgument hleaArgument type
        (argumentsImage leaArgument hleaArgument)
      exact htype
    · intro type htype
      rw [parts.1] at htype
      apply toLeaTTaAtom_fromLeaTTaAtom_of_heImage
      apply getTypes_result_heImage index head type headImage
      exact htype
    · intro argument hargument type htype
      rw [fromLeaTTaAtoms_eq_map] at hargument
      obtain ⟨leaArgument, hleaArgument, rfl⟩ :=
        List.mem_map.mp hargument
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage
        (argumentsImage leaArgument hleaArgument)] at htype
      apply toLeaTTaAtom_fromLeaTTaAtom_of_heImage
      apply getTypes_result_heImage index leaArgument type
        (argumentsImage leaArgument hleaArgument)
      exact htype
    · rw [translatedInput]
      simpa [Metta.Minimal.getTypes] using hmem
  case case13 head arguments hnotState hquery _rawArgTypeLists
      _rawArgTypeChoices _allRawArgTypes _rawFunctionTypes _avoid
      _functionAvoid _functionTypes _inferred ihArguments ihHead =>
    have parts := heImage_expression_roundtrip_parts inputImage
    have inputRoundtrip :=
      toLeaTTaAtom_fromLeaTTaAtom_of_heImage inputImage
    have translatedInput :
        toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments)) =
          .expr (head :: arguments) := by
      simpa [fromLeaTTaAtom, fromLeaTTaAtoms] using inputRoundtrip
    have headImage : LeaAtomHEImage head :=
      leaAtomHEImage_children inputImage head (by simp)
    have argumentsImage :
        ∀ argument ∈ arguments, LeaAtomHEImage argument := by
      intro argument hargument
      exact leaAtomHEImage_children inputImage argument
        (List.mem_cons_of_mem _ hargument)
    have hquery' :
        env.exprTypes.filter (fun entry =>
          entry.1 == .expr (head :: arguments)) = [] := by
      rw [unattach_filter_attach env.exprTypes
        (fun entry => entry.1 == .expr (head :: arguments))] at hquery
      exact hquery
    have hnotState' : ∀ leaValue,
        toLeaTTaAtom (fromLeaTTaAtom head) = .sym "StateValue" →
        toLeaTTaAtoms (fromLeaTTaAtoms arguments) = [leaValue] → False := by
      intro leaValue hhead harguments
      exact hnotState leaValue
        (parts.1.symm.trans hhead)
        (parts.2.symm.trans harguments)
    have hdirect :
        env.exprTypes.filter (fun entry =>
          entry.1 == toLeaTTaAtom
            (.expression
              (fromLeaTTaAtom head :: fromLeaTTaAtoms arguments))) = [] := by
      change env.exprTypes.filter (fun entry =>
        entry.1 == toLeaTTaAtom
          (fromLeaTTaAtom (.expr (head :: arguments)))) = []
      rw [inputRoundtrip]
      exact hquery'
    apply getTypes_inferredExpression_runtimeEvidence index
      (fromLeaTTaAtom head) (fromLeaTTaAtoms arguments)
      hnotState' hdirect
    · intro type htype
      rw [parts.1] at htype
      apply ihHead type headImage
      exact htype
    · intro argument hargument type htype
      rw [fromLeaTTaAtoms_eq_map] at hargument
      obtain ⟨leaArgument, hleaArgument, rfl⟩ :=
        List.mem_map.mp hargument
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage
        (argumentsImage leaArgument hleaArgument)] at htype
      apply ihArguments leaArgument hleaArgument type
        (argumentsImage leaArgument hleaArgument)
      exact htype
    · intro type htype
      rw [parts.1] at htype
      apply toLeaTTaAtom_fromLeaTTaAtom_of_heImage
      apply getTypes_result_heImage index head type headImage
      exact htype
    · intro argument hargument type htype
      rw [fromLeaTTaAtoms_eq_map] at hargument
      obtain ⟨leaArgument, hleaArgument, rfl⟩ :=
        List.mem_map.mp hargument
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage
        (argumentsImage leaArgument hleaArgument)] at htype
      apply toLeaTTaAtom_fromLeaTTaAtom_of_heImage
      apply getTypes_result_heImage index leaArgument type
        (argumentsImage leaArgument hleaArgument)
      exact htype
    · rw [translatedInput]
      simpa [Metta.Minimal.getTypes] using hmem
  case case14 =>
    apply getTypes_emptyExpression_runtimeEvidence space env
    simpa [Metta.Minimal.getTypes, toLeaTTaAtom, toLeaTTaAtoms] using hmem

/-- Public recursive lookup seal on native inputs: every repaired-LeaTTa
output remains representable natively and carries published-core or named
R1/R2/R3 evidence for its decoded type. -/
theorem getTypes_runtimeOutput_sound
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) (atom : Atom)
    {leaType : Metta.Atom}
    (hmem : leaType ∈
      Metta.Minimal.getTypes env (toLeaTTaAtom atom)) :
    LeaAtomHEImage leaType ∧
      RuntimeTypeEvidenceRel space atom (fromLeaTTaAtom leaType) := by
  constructor
  · exact getTypes_result_heImage index (toLeaTTaAtom atom) leaType
      (leaAtomHEImage_toLeaTTaAtom atom) hmem
  · simpa using getTypes_runtimeEvidence_of_heImage index
      (toLeaTTaAtom atom) leaType
      (leaAtomHEImage_toLeaTTaAtom atom) hmem

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
