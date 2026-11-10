import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationTermSource
import Mettapedia.GSLT.LanguageDef.SignatureIndexedABTHeadMap
import Mettapedia.OSLF.Syntax.BindingSignatureABTReadback

/-! # Intrinsic binding terms in the authored transform presentation

The head presentation names its interpretation and version. Scalar parsing,
head decoding and intrinsic sort/scope readback remain separate operations.
Their composition recovers every printed intrinsic term. Unknown head codes
and ill-formed typed trees do not acquire default meanings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Intrinsic

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics

abbrev HeadPresentation (S : Signature) :=
  ExactPresentation.Presentation (fun _ : Unit => CommonABT.Head S) (fun _ => Payloads.Head)

variable {S : Signature} [DecidableEq S.Srt] (code : HeadPresentation S)

def lower {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) : Payloads.Term :=
  SignatureIndexedABT.mapHeads (code.view (sort := ())) (CommonABT.lower term)

def read? (Γ : Ctx S) (sort : S.Srt) (term : Payloads.Term) : Option (Term S Γ sort) := do
  let raw ← SignatureIndexedABT.traverseHeads? (code.expand (sort := ())) term
  CommonABT.read raw Γ sort

theorem read_lower {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    read? code Γ sort (lower code term) = some term := by
  rw [read?, lower, SignatureIndexedABT.traverse_mapHeads _ _ (code.expand_view (sort := ()))]
  exact CommonABT.read_lower term

omit [DecidableEq S.Srt] in
theorem lower_scoped {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    SignatureIndexedABT.Term.supportedAt Γ.length (lower code term) = true := by
  rw [lower, SignatureIndexedABT.mapHeads_scope]
  exact CommonABT.lower_scoped term

omit [DecidableEq S.Srt] in
theorem lower_injective {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (lower code (Γ := Γ) (sort := sort)) := by
  intro first second same
  have heads : Function.Injective (code.view (sort := ())) := by
    intro firstHead secondHead equal
    have decoded := congrArg (code.expand (sort := ())) equal
    simpa only [code.expand_view, Option.some.injEq] using decoded
  apply CommonABT.lower_injective first second
  exact SignatureIndexedABT.mapHeads_injective _ heads _ _ same

abbrev Index (S : Signature) := Ctx S × S.Srt

def termPresentation : ExactPresentation.Presentation
    (fun index : Index S => Term S index.1 index.2) (fun _ => Payloads.Term) where
  key := ⟨code.key.name ++ ".intrinsic-term", code.key.version⟩
  view term := lower code term
  expand {sort} := read? code sort.1 sort.2
  expand_view := read_lower code

noncomputable def readSource? (Γ : Ctx S) (sort : S.Srt) (input : List Nat) : Option (Term S Γ sort) := do
  let tree ← Source.parseTree "TcTerm" input
  let pattern ← LanguageDefScalarStructural.tree? tree
  let term ← Payloads.readTerm pattern
  read? code Γ sort term

def sourceInput {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) : List Nat :=
  Source.termInput (lower code term)

theorem readSource_of_parse (Γ : Ctx S) (sort : S.Srt) {input : List Nat} {tree : CST}
    (parsed : Source.Parses "TcTerm" input tree) :
    readSource? code Γ sort input = (do
      let pattern ← LanguageDefScalarStructural.tree? tree
      let term ← Payloads.readTerm pattern
      read? code Γ sort term) := by
  simp only [readSource?, Source.parseTree_of_derivation parsed]
  rfl

theorem readSource_print {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    readSource? code Γ sort (sourceInput code term) = some term := by
  obtain ⟨tree, erased, ⟨parsed⟩⟩ := Source.canonical_term_source (lower code term)
  rw [sourceInput, readSource_of_parse code Γ sort parsed]
  simp only [erased]
  change (Payloads.readTerm (Payloads.termPattern (lower code term))).bind (read? code Γ sort) = some term
  rw [Payloads.readTerm_pattern]
  exact read_lower code term

noncomputable def sourcePresentation : ExactPresentation.Presentation
    (fun index : Index S => Term S index.1 index.2) (fun _ => List Nat) where
  key := ⟨code.key.name ++ ".intrinsic-scalar", code.key.version⟩
  view term := sourceInput code term
  expand {sort} := readSource? code sort.1 sort.2
  expand_view := readSource_print code

theorem packed_readback (forest : ClassAwarePackedForest.Forest)
    (Γ : Ctx S) (sort : S.Srt) {input : List Nat} {tree : CST}
    (packed : Nonempty (Source.Packed forest "TcTerm" input tree)) :
    readSource? code Γ sort input = (do
      let pattern ← LanguageDefScalarStructural.tree? tree
      let term ← Payloads.readTerm pattern
      read? code Γ sort term) := by
  obtain ⟨parsed⟩ := Source.packed_reflects forest "TcTerm" input tree packed
  exact readSource_of_parse code Γ sort parsed

theorem wrong_version_refused (index : Index S) (document : ExactPresentation.Document (fun _ : Index S => List Nat) index)
    (different : document.key ≠ (sourcePresentation code).key) :
    ExactPresentation.expandDocument (sourcePresentation code) document = none :=
  ExactPresentation.expandDocument_wrong_key _ _ different

theorem empty_fibre_source_refused (Γ : Ctx S) (sort : S.Srt) [IsEmpty (Term S Γ sort)] (input : List Nat) :
    readSource? code Γ sort input = none := by
  cases result : readSource? code Γ sort input with
  | none => rfl
  | some term => exact isEmptyElim term

#print axioms read_lower
#print axioms readSource_print
#print axioms packed_readback

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Intrinsic
