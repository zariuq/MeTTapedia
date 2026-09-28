import Mettapedia.Languages.Agda.Native.ProofCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec.ProofControls
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural
open Mettapedia.OSLF.Binding Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open AdministrativeStatics

def emptyContext : Statics.RawContext 0 := .nil
def resultType : Statics.RawTy 0 := (Statics.universeType 0 1).code

def emptyTree : CoreDerivation (Statics.context emptyContext) :=
  .roll (.prior (.core .empty)) (noEvidence _)

def sortTree (level : Nat) : CoreDerivation
    (Statics.typed emptyContext (Statics.universeTerm level) (Statics.universeType 0 (level + 1)).code) :=
  .roll (.prior (.core (.sort emptyContext level))) (consEvidence _ emptyTree (noEvidence _))

def resultFormed : CoreDerivation (Statics.formed emptyContext resultType) :=
  .roll (.prior (.core (.formation emptyContext 2 (Statics.universeTerm 1))))
    (consEvidence _ (sortTree 1) (noEvidence _))

def extendedTree : CoreDerivation (Statics.context (emptyContext.snoc resultType)) :=
  .roll (.prior (.core (.extend emptyContext resultType)))
    (consEvidence _ emptyTree (consEvidence _ resultFormed (noEvidence _)))

def nilTree : Action emptyContext resultType nil resultType := Derivation.nil emptyContext resultType
def administrativeTree := Derivation.elimination (sortTree 0) nilTree
def directEquality := Derivation.spineRefl nilTree
def symmetricEquality := Derivation.spineSymm directEquality
def firstThenSecond := Derivation.spineTrans directEquality symmetricEquality
def secondThenFirst := Derivation.spineTrans symmetricEquality directEquality

theorem distinct_same_endpoint_histories : directEquality ≠ symmetricEquality := by
  intro same
  have shapes := (IndexedPolynomial.Fix.roll.inj same).1
  cases shapes

theorem ordered_repeated_children : firstThenSecond ≠ secondThenFirst := by
  intro same
  have children := eq_of_heq (IndexedPolynomial.Fix.roll.inj same).2
  exact distinct_same_endpoint_histories (congrFun children 0)

theorem distinct_history_wires : encode directEquality ≠ encode symmetricEquality := by
  intro same
  have trees : (⟨_, directEquality⟩ : PackedTree) = ⟨_, symmetricEquality⟩ := encodePacked_injective same
  exact distinct_same_endpoint_histories (eq_of_heq (Sigma.mk.inj trees).2)

theorem ordered_history_wires : encode firstThenSecond ≠ encode secondThenFirst := by
  intro same
  have trees : (⟨_, firstThenSecond⟩ : PackedTree) = ⟨_, secondThenFirst⟩ := encodePacked_injective same
  exact ordered_repeated_children (eq_of_heq (Sigma.mk.inj trees).2)

theorem exact_administrative_history : decode (encode administrativeTree) = some ⟨_, administrativeTree⟩ :=
  decode_encode administrativeTree
theorem first_order_replay : decode (encode firstThenSecond) = some ⟨_, firstThenSecond⟩ :=
  decode_encode firstThenSecond
theorem second_order_replay : decode (encode secondThenFirst) = some ⟨_, secondThenFirst⟩ :=
  decode_encode secondThenFirst

def eliminationLabel : Data := dataShapeCodec.encode
  ⟨_, .prior (.elimination emptyContext (Statics.universeTerm 0) resultType nil resultType)⟩
def sortLabel (level : Nat) : Data := dataShapeCodec.encode ⟨_, .prior (.core (.sort emptyContext level))⟩

private theorem decode_node (label : Data) (children : List ProofWire) :
    decode (.node label children) = do
      let ⟨j, shape⟩ ← dataShapeCodec.decode label
      let checked ← Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.assemble AdministrativeStatics.presentation
        (AdministrativeStatics.premises shape) (children.map decode)
      return ⟨j, .roll shape checked⟩ := by
  rw [decode, Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode]
  simp only [List.attach_map_val]
  rfl

theorem ordered_requirements : expectedPremises eliminationLabel = some
    [.core (Statics.typed emptyContext (Statics.universeTerm 0) resultType),
      .spineAction emptyContext resultType nil resultType] := expectedPremises_encode _

theorem missing_child_rejected : decode (.node eliminationLabel [encode (sortTree 0)]) = none := by
  rw [decode_node]
  simp only [eliminationLabel, dataShapeCodec.roundtrip, List.map_cons, List.map_nil, decode_encode,
    Bind.bind, Option.bind]
  rfl
theorem extra_child_rejected :
    decode (.node eliminationLabel [encode (sortTree 0), encode nilTree, encode nilTree]) = none := by
  rw [decode_node]
  simp only [eliminationLabel, dataShapeCodec.roundtrip, List.map_cons, List.map_nil, decode_encode,
    Bind.bind, Option.bind]
  rfl
theorem swapped_typed_and_action_children_rejected :
    decode (.node eliminationLabel [encode nilTree, encode (sortTree 0)]) = none := by
  rw [decode_node]
  simp only [eliminationLabel, dataShapeCodec.roundtrip, List.map_cons, List.map_nil, decode_encode,
    Bind.bind, Option.bind]
  rfl
theorem context_child_mutation_rejected : decode (.node (sortLabel 0) [encode extendedTree]) = none := by
  rw [decode_node]
  simp only [sortLabel, dataShapeCodec.roundtrip, List.map_cons, List.map_nil, decode_encode,
    Bind.bind, Option.bind]
  rfl
theorem unknown_rule_rejected : decode (.node (.atom 999) []) = none := by rw [decode_node]; rfl
theorem unknown_prior_rule_rejected :
    decode (.node (.pair (.atom 0) (.pair (.atom 0) (.atom 999))) []) = none := by rw [decode_node]; rfl

theorem output_type_mutation_rejected :
    check (.core (Statics.typed emptyContext (Statics.universeTerm 0) (Statics.universeType 0 2).code))
      (encode (sortTree 0)) = false := by
  unfold check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt
  rw [encode, Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode_encode]
  rfl
theorem rule_parameter_mutation_rejected :
    check (.core (Statics.typed emptyContext (Statics.universeTerm 0) resultType))
      (.node (sortLabel 1) [encode emptyTree]) = false := by
  change check _ (encode (sortTree 1)) = false
  unfold check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt
  rw [encode, Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode_encode]
  rfl
theorem nil_action_is_not_head_typing :
    check (.core (Statics.typed emptyContext (Statics.universeTerm 0) resultType)) (encode nilTree) = false := by
  unfold check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.check Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decodeAt
  rw [encode, Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.decode_encode]
  rfl

/-- Ordered repeated premises may both remain well typed after a swap. Their
accepted wires still reconstruct different proof objects. -/
theorem swapped_repeated_children_accepted :
    check (.spineEquality emptyContext resultType nil nil resultType) (encode secondThenFirst) = true :=
  (check_iff _ _).mpr ⟨secondThenFirst, rfl⟩

theorem correct_administrative_wire_accepted :
    check (.core (Statics.typed emptyContext (eliminate (Statics.universeTerm 0) nil) resultType))
      (encode administrativeTree) = true := (check_iff _ _).mpr ⟨administrativeTree, rfl⟩

end Mettapedia.Languages.Agda.Native.Codec.ProofControls
