import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSRuleQuotient
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSReceipts
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls
import Mathlib.Tactic.FinCases

/-!
# Multiple positive occurrences, passive arguments and negative guards

Two positive premises at one child/action select successors independently.
The target retains both selected values and the passive second source.
An independently written product operation is proved to be exactly the
clause's denotation. Its reconstructed finite-rule law roundtrip exercises
the general converse. Variable identification merges four complete targets
into one, while duplicate clause identifiers remain distinct in receipts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises.PresentationControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Classical
open GSOSControls (signature Operator naturals units pure)

abbrev actions : signature.Srt → Type := fun _ => Bool

abbrev doublePattern : Pattern (Actions := actions) (sort := ()) (Operator.choose : signature.Operator ()) where
  Occurrence := Fin 2
  finite := inferInstance
  address _ := ⟨false, false⟩
  negative := {⟨true, true⟩}

def build {X : signature.Families} (first second passive : X PUnit.unit ()) : signature.Term X () :=
  GSOSControls.choose (GSOSControls.choose (pure first) (pure second)) (pure passive)

theorem rename_choose {X Y : signature.Families} (mapping : X ⟶ Y)
    (first second : signature.Term X ()) :
    signature.rename mapping (GSOSControls.choose first second) =
      GSOSControls.choose (signature.rename mapping first) (signature.rename mapping second) := by
  unfold GSOSControls.choose Mettapedia.OSLF.DeterministicGSOS.Signature.rename
  rw [IndexedPolynomial.Free.map_node]
  congr 1
  funext position
  cases position <;> rfl

theorem rename_build {X Y : signature.Families} (mapping : X ⟶ Y)
    (first second passive : X PUnit.unit ()) :
    signature.rename mapping (build first second passive) =
      build (mapping PUnit.unit () first) (mapping PUnit.unit () second) (mapping PUnit.unit () passive) := by
  unfold build
  rw [rename_choose, rename_choose]
  rfl

abbrev doubleRule : Rule (Actions := actions) (sort := ()) (Operator.choose : signature.Operator ()) where
  pattern := doublePattern
  target := build (X := variableFamily doublePattern)
    (Variable.derivative (pattern := doublePattern) (0 : Fin 2))
    (Variable.derivative (pattern := doublePattern) (1 : Fin 2))
    (Variable.original (pattern := doublePattern) true)

theorem output_readout {X : signature.Families} (input : Input doublePattern X) :
    doubleRule.output input = build (input.derivatives 0) (input.derivatives 1) (input.originals true) :=
  rename_build input.assignment _ _ _

def selection {X : signature.Families} (sources : signature.Arguments (sort := ()) X Operator.choose)
    (first second : X PUnit.unit ()) : Input doublePattern X where
  originals := sources
  derivatives occurrence := if occurrence.val = 0 then first else second

theorem selection_matches {X : signature.Families}
    (arguments : signature.Arguments (sort := ()) ((sourceBehaviourFunctor signature actions).obj X) Operator.choose)
    (first second : X PUnit.unit ())
    (firstMember : first ∈ (arguments false).2 false)
    (secondMember : second ∈ (arguments false).2 false)
    (negative : (arguments true).2 true = ∅) :
    Matches doublePattern arguments (selection (fun position => (arguments position).1) first second) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro occurrence
    fin_cases occurrence
    · exact firstMember
    · exact secondMember
  · intro address member
    have same : address = ⟨true, true⟩ := Finset.mem_singleton.mp member
    subst address
    exact negative

/-- The target operation is independently written as a finite product. -/
def productTargets {X : signature.Families}
    (arguments : signature.Arguments (sort := ())
      ((sourceBehaviourFunctor signature actions).obj X) Operator.choose) : Finset (signature.Term X ()) :=
  if (arguments true).2 true = ∅ then
    ((arguments false).2 false ×ˢ (arguments false).2 false).image
      (fun pair => build (X := X) pair.1 pair.2 (arguments true).1)
  else ∅

/-- Independent finite-product semantics has the exact complete firing readout. -/
theorem targets_readout {X : signature.Families}
    (arguments : signature.Arguments (sort := ()) ((sourceBehaviourFunctor signature actions).obj X) Operator.choose) :
    doubleRule.targets arguments = productTargets arguments := by
  unfold productTargets
  by_cases negative : (arguments true).2 true = ∅
  · rw [if_pos negative]
    apply Finset.ext
    intro target
    rw [Rule.mem_targets, Finset.mem_image]
    constructor
    · rintro ⟨input, matching, same⟩
      refine ⟨⟨input.derivatives 0, input.derivatives 1⟩,
        Finset.mem_product.mpr ⟨matching.2.1 0, matching.2.1 1⟩, ?_⟩
      rw [output_readout, matching.1 true] at same
      exact same
    · rintro ⟨⟨first, second⟩, member, same⟩
      obtain ⟨firstMember, secondMember⟩ := Finset.mem_product.mp member
      refine ⟨selection (fun position => (arguments position).1) first second,
        selection_matches arguments first second firstMember secondMember negative, ?_⟩
      rw [output_readout]
      exact same
  · rw [if_neg negative]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro target member
    obtain ⟨input, matching, _⟩ := (Rule.mem_targets _ _ _).mp member
    exact negative (matching.2.2 ⟨true, true⟩ (Finset.mem_singleton_self _))

/-- The operation is written directly as a finite product and a negative
availability test; its naturality is earned from exact clause denotation. -/
def pairLaw : Law signature actions where
  app X := fun base sort => match base, sort with
    | .unit, () => ↾(fun layer => match layer with
      | ⟨.stopped, _⟩ => fun _ => ∅
      | ⟨.choose, arguments⟩ => fun _ => productTargets arguments)
  naturality {X Y} mapping := by
    funext base sort
    cases base
    cases sort
    apply ConcreteCategory.hom_ext
    intro layer
    rcases layer with ⟨operator, arguments⟩
    cases operator with
    | stopped =>
        funext action
        exact (Mettapedia.CategoryTheory.FinitePowerset.map_empty _).symm
    | choose =>
        funext action
        change productTargets (mapArguments mapping arguments) =
          Mettapedia.CategoryTheory.FinitePowerset.map (signature.rename mapping)
            (productTargets arguments)
        rw [← targets_readout, ← targets_readout]
        exact doubleRule.targets_map mapping arguments

def offered : signature.Arguments (sort := ()) ((sourceBehaviourFunctor signature actions).obj naturals) Operator.choose :=
  fun position => if position then (20, fun _ => ∅)
    else (10, fun action => if action = false then {11, 21} else ∅)

theorem complete_target_product :
    pairLaw.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ false =
      (({11, 21} : Finset Nat) ×ˢ {11, 21}).image (fun pair => build (X := naturals) pair.1 pair.2 (20 : Nat)) := rfl

def leaves : signature.Term naturals () → List Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ value => [value])
    ⟨fun _ _ layer => match layer with
      | ⟨.stopped, _⟩ => []
      | ⟨.choose, children⟩ => children false ++ children true⟩ PUnit.unit ()

theorem leaves_build (first second passive : Nat) :
    leaves (build (X := naturals) first second passive) = [first, second, passive] := rfl

theorem build_injective (passive : Nat) :
    Function.Injective (fun pair : Nat × Nat => build (X := naturals) pair.1 pair.2 passive) := by
  intro first second same
  have read := congrArg leaves same
  rw [leaves_build, leaves_build] at read
  simp only [List.cons.injEq, and_true] at read
  exact Prod.ext read.1 read.2

theorem four_independent_targets :
    (pairLaw.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ false).card = 4 := by
  rw [complete_target_product, Finset.card_image_of_injective _ (build_injective 20), Finset.card_product]
  simp

theorem both_occurrences_and_passive_retained :
    build (X := naturals) (11 : Nat) 21 20 ∈ pairLaw.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ false := by
  rw [complete_target_product]
  exact Finset.mem_image.mpr ⟨(11, 21), by simp, rfl⟩

theorem coincident_positive_choices_admitted :
    build (X := naturals) (11 : Nat) 11 20 ∈ pairLaw.app naturals PUnit.unit () ⟨Operator.choose, offered⟩ false := by
  rw [complete_target_product]
  exact Finset.mem_image.mpr ⟨(11, 11), by simp, rfl⟩

def collapse : naturals ⟶ units := fun _ _ => ↾(fun _ => ())

theorem full_identification_square (X Y : signature.Families) (mapping : X ⟶ Y)
    (arguments : signature.Arguments (sort := ()) ((sourceBehaviourFunctor signature actions).obj X) Operator.choose)
    (action : Bool) :
    pairLaw.app Y PUnit.unit () ⟨Operator.choose, mapArguments mapping arguments⟩ action =
      Mettapedia.CategoryTheory.FinitePowerset.map (signature.rename mapping)
        (pairLaw.app X PUnit.unit () ⟨Operator.choose, arguments⟩ action) :=
  congrArg (fun square => square PUnit.unit () ⟨Operator.choose, arguments⟩ action) (pairLaw.naturality mapping)

theorem identified_targets :
    pairLaw.app units PUnit.unit () ⟨Operator.choose, mapArguments collapse offered⟩ false =
      {build (X := units) () () ()} := by
  rw [full_identification_square, complete_target_product]
  unfold Mettapedia.CategoryTheory.FinitePowerset.map
  rw [Finset.image_image]
  change (({11, 21} : Finset Nat) ×ˢ {11, 21}).image
    (fun pair => signature.rename collapse (build (X := naturals) pair.1 pair.2 20)) =
      {build (X := units) () () ()}
  simp only [rename_build]
  simp only [collapse]
  have inhabited : (({11, 21} : Finset Nat) ×ˢ {11, 21}).Nonempty :=
    ⟨(11, 11), by simp⟩
  exact Finset.image_const inhabited _

theorem independent_law_roundtrip :
    Presentation.toLaw (Reconstruction.fromLaw pairLaw) = pairLaw := Reconstruction.law_roundtrip pairLaw

theorem actual_rule_quotient_roundtrip :
    ruleLawEquiv (lawQuotient pairLaw) = pairLaw := quotientLaw_lawQuotient pairLaw

def authored : AuthoredPresentation signature actions where
  Origin _ operator _ := match operator with
    | .stopped => Empty
    | .choose => Bool
  finite _ operator _ := by cases operator <;> infer_instance
  rule _ operator _ := match operator with
    | .stopped => fun origin => origin.elim
    | .choose => fun _ => doubleRule

def receipt (origin : Bool) : authored.Firing Operator.choose offered false where
  origin := origin
  input := selection (fun position => (offered position).1) 11 21
  matching := selection_matches offered 11 21 (by simp [offered]) (by simp [offered]) rfl

theorem different_origins_same_target :
    receipt false ≠ receipt true ∧ (receipt false).target = (receipt true).target := by
  constructor
  · intro same
    exact Bool.false_ne_true (congrArg (fun firing => firing.origin) same)
  · rfl

theorem no_target_origin_decoder :
    ¬ ∃ decoder : signature.Term naturals () → Bool,
      ∀ origin, decoder (receipt origin).target = origin := by
  rintro ⟨decoder, recovers⟩
  have same : (receipt false).target = (receipt true).target := rfl
  have recovered := congrArg decoder same
  rw [recovers false, recovers true] at recovered
  exact Bool.false_ne_true recovered

theorem complete_receipt_normalization :
    Presentation.targets authored.readout Operator.choose offered false =
      (authored.firings Operator.choose offered false).image (AuthoredPresentation.Firing.target authored) :=
  authored.targets_eq_firing_image Operator.choose offered false

def forbidden : signature.Arguments (sort := ()) ((sourceBehaviourFunctor signature actions).obj naturals) Operator.choose :=
  fun position => if position then (20, fun action => if action = true then {22} else ∅)
    else (10, fun action => if action = false then {11, 21} else ∅)

theorem negative_guard_blocks :
    pairLaw.app naturals PUnit.unit () ⟨Operator.choose, forbidden⟩ false = ∅ := by
  change productTargets forbidden = ∅
  simp [productTargets, forbidden]

theorem dropping_second_occurrence_changes_target :
    build (X := naturals) (11 : Nat) 11 20 ≠ build (X := naturals) (11 : Nat) 21 20 := by
  intro same
  have read := congrArg leaves same
  rw [leaves_build, leaves_build] at read
  simp at read

end Mettapedia.OSLF.FiniteBranching.Premises.PresentationControls
