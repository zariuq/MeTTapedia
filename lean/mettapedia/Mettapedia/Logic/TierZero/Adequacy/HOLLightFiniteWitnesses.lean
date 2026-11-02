import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteSignatureLookup
import Mettapedia.Languages.HOLLight.ProofDataEncoding

/-!
# Finite observations of original annotation-certificate providers

The source provider is function-valued, but one local command asks only
finitely many constant/annotation questions. A finite graph retains the exact
original substitution entries at those keys. No function codec, proof search
or equality between arbitrary providers is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnesses

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open HOLLightFiniteSignatureLookup

abbrev Key := Const × Ty
local instance : DecidableEq Const := constantCodec.decEq
local instance : DecidableEq Ty := tyCodec.decEq

def keyCodec : Codec Key := Codec.prod constantCodec tyCodec

def substitutionCodec : Codec TypeSubst :=
  (Codec.list (Codec.prod nameCodec tyCodec)).mapped (·.entries) (fun entries => some ⟨entries⟩) (fun _ => rfl)

abbrev Graph := List (Key × TypeSubst)

def graphCodec : Codec Graph := Codec.list (Codec.prod keyCodec substitutionCodec)

def witnesses (graph : Graph) : InstanceWitnesses :=
  fun constant annotation => (rowLookup (constant, annotation) graph).getD TypeSubst.empty

def termKeys : DBTerm → Finset Key
  | .const constant annotation => {(constant, annotation)}
  | .free _ | .bound _ => ∅
  | .app function argument => termKeys function ∪ termKeys argument
  | .abs _ body => termKeys body

def sequentKeys (sequent : Sequent) : Finset Key :=
  termKeys sequent.concl.term ∪ sequent.hyp.biUnion (fun hypothesis => termKeys hypothesis.term)

def theoremKeys (fact : Theorem) : Finset Key :=
  sequentKeys fact.sequent ∪ fact.axioms.biUnion sequentKeys

def Agree (keys : Finset Key) (first second : InstanceWitnesses) : Prop :=
  ∀ key ∈ keys, first key.1 key.2 = second key.1 key.2

theorem Agree.mono {larger smaller : Finset Key} {first second : InstanceWitnesses}
    (agrees : Agree larger first second) (included : smaller ⊆ larger) : Agree smaller first second :=
  fun key member => agrees key (included member)

theorem annotations_agree (signature : Signature) (first second : InstanceWitnesses)
    (term : DBTerm) (agrees : Agree (termKeys term) first second) :
    annotationsFormedB signature first term = annotationsFormedB signature second term := by
  induction term with
  | const constant annotation =>
      have same := agrees (constant, annotation) (Finset.mem_singleton_self _)
      simp only [annotationsFormedB, constantInstanceB]
      cases signature.constants constant <;> simp only [same]
  | free parameter => simp only [annotationsFormedB]
  | bound index => simp only [annotationsFormedB]
  | app function argument functionIH argumentIH =>
      have firstAgree := agrees.mono (show termKeys function ⊆ termKeys (.app function argument) from Finset.subset_union_left)
      have secondAgree := agrees.mono (show termKeys argument ⊆ termKeys (.app function argument) from Finset.subset_union_right)
      simp only [annotationsFormedB, functionIH firstAgree, argumentIH secondAgree]
  | abs domain body earlier =>
      simp only [annotationsFormedB, earlier agrees]

theorem sequent_agree (signature : Signature) (first second : InstanceWitnesses)
    (sequent : Sequent) (agrees : Agree (sequentKeys sequent) first second) :
    sequentFormedB signature first sequent = sequentFormedB signature second sequent := by
  unfold sequentFormedB
  congr 1
  · exact annotations_agree signature first second sequent.concl.term (agrees.mono Finset.subset_union_left)
  · apply Finset.fold_congr
    intro hypothesis member
    apply annotations_agree
    exact agrees.mono (fun key present => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨hypothesis, member, present⟩))

theorem theorem_agree (signature : Signature) (first second : InstanceWitnesses)
    (fact : Theorem) (agrees : Agree (theoremKeys fact) first second) :
    theoremFormedB signature first fact = theoremFormedB signature second fact := by
  unfold theoremFormedB
  congr 1
  · exact sequent_agree signature first second fact.sequent (agrees.mono Finset.subset_union_left)
  · apply Finset.fold_congr
    intro commitment member
    apply sequent_agree
    exact agrees.mono (fun key present => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨commitment, member, present⟩))

def sample (keys : Finset Key) (provider : InstanceWitnesses) : Graph :=
  (keys.sort (encodedLe keyCodec)).map (fun key => (key, provider key.1 key.2))

theorem sample_agrees (keys : Finset Key) (provider : InstanceWitnesses) :
    Agree keys provider (witnesses (sample keys provider)) := by
  intro key member
  have inList : key ∈ keys.sort (encodedLe keyCodec) := (Finset.mem_sort _).mpr member
  have chosen : (key, provider key.1 key.2) ∈ sample keys provider := List.mem_map.mpr ⟨key, inList, rfl⟩
  have consistent : ∀ first ∈ sample keys provider, ∀ second ∈ sample keys provider, first.1 = second.1 → first.2 = second.2 := by
    intro first firstMember second secondMember same
    obtain ⟨left, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, _, rfl⟩ := List.mem_map.mp secondMember
    exact congrArg (fun key => provider key.1 key.2) same
  have found := rowLookup_of_consistent_member consistent chosen
  simp only [witnesses, found, Option.getD_some]

theorem sample_annotations (signature : Signature) (provider : InstanceWitnesses) (term : DBTerm) :
    annotationsFormedB signature provider term =
      annotationsFormedB signature (witnesses (sample (termKeys term) provider)) term :=
  annotations_agree signature _ _ term (sample_agrees _ _)

theorem graph_wire_roundtrip (graph : Graph) : graphCodec.get (graphCodec.put graph) = some graph := graphCodec.get_put graph

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnesses
