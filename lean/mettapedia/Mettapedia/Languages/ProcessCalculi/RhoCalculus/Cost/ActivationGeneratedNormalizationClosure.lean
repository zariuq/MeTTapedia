import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImageReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureStability

/-!
# Normalization closure of the actual generated parser image

The wrapped quote/drop operation stays inside the existing parser domain.
Normalized code is read back by the actual parser. The result need not be the
literal original cost term; no operational step is inferred from normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  theorem NameImage.weaken {scope depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage scope source name) (larger : scope ≤ depth) :
      NameImage depth source name := by
    cases image with
    | bvar bound => exact .bvar (Nat.lt_of_lt_of_le bound larger)
    | baseZeroQuote => exact .baseZeroQuote
    | quote code => exact .quote code

  theorem CodeImage.weaken {scope depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage scope source term) (larger : scope ≤ depth) :
      CodeImage depth source term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop (name.weaken larger)
    | signed signature accepted process => exact .signed signature accepted (process.weaken larger)
    | collection codes => exact .collection (codes.weaken larger)

  theorem ProcImage.weaken {scope depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage scope source process) (larger : scope ≤ depth) :
      ProcImage depth source process := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send (name.weaken larger) (code.weaken larger)
    | recv name code => exact .recv (name.weaken larger) (code.weaken (Nat.add_le_add_right larger 1))
    | pair left right => exact .pair (left.weaken larger) (right.weaken larger)

  theorem CodeListImage.weaken {scope depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage scope sources term) (larger : scope ≤ depth) :
      CodeListImage depth sources term := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .cons (head.weaken larger) (tail.weaken larger)
end

theorem CodeImage.finish_quote_image {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : CodeImage 0 source term) (depth : Nat) :
    ∃ name, NameImage depth
      (finishNormalizeReflectiveApply wrappedRhoDeclaration "$cost:wrapped-constructor:NQuote" [source]) name := by
  cases image with
  | zero => exact ⟨.quote .nil, .quote .zero⟩
  | drop name => exact ⟨_, name.weaken (Nat.zero_le depth)⟩
  | signed signature accepted process => exact ⟨_, .quote (.signed signature accepted process)⟩
  | collection codes => exact ⟨_, .quote (.collection codes)⟩

mutual
  theorem NameImage.normalize_image {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ normalized, NameImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | bvar bound => exact ⟨_, .bvar bound⟩
    | baseZeroQuote => exact ⟨_, .baseZeroQuote⟩
    | quote code =>
      obtain ⟨normalized, normalizedImage⟩ := code.normalize_image
      exact normalizedImage.finish_quote_image depth

  theorem CodeImage.normalize_image {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      ∃ normalized, CodeImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | drop name =>
      obtain ⟨normalized, normalizedImage⟩ := name.normalize_image
      exact ⟨.drop normalized, .drop normalizedImage⟩
    | signed signature accepted process =>
      obtain ⟨normalized, normalizedImage⟩ := process.normalize_image
      change ∃ normalized, CodeImage depth
        (.apply "$cost:apparatus-constructor:signed"
          [normalizeReflective wrappedRhoDeclaration _, normalizeReflective wrappedRhoDeclaration _]) normalized
      rw [signature?_accepted_normalization_identity accepted]
      exact ⟨_, .signed signature accepted normalizedImage⟩
    | collection codes =>
      obtain ⟨normalized, normalizedImage⟩ := codes.normalize_image
      exact ⟨_, .collection normalizedImage⟩

  theorem ProcImage.normalize_image {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ normalized, ProcImage depth (normalizeReflective wrappedRhoDeclaration source) normalized := by
    cases image with
    | zero => exact ⟨_, .zero⟩
    | send name code =>
      obtain ⟨normalizedName, nameImage⟩ := name.normalize_image
      obtain ⟨normalizedCode, codeImage⟩ := code.normalize_image
      exact ⟨_, .send nameImage codeImage⟩
    | recv name code =>
      obtain ⟨normalizedName, nameImage⟩ := name.normalize_image
      obtain ⟨normalizedCode, codeImage⟩ := code.normalize_image
      exact ⟨_, .recv nameImage codeImage⟩
    | pair left right =>
      obtain ⟨normalizedLeft, leftImage⟩ := left.normalize_image
      obtain ⟨normalizedRight, rightImage⟩ := right.normalize_image
      exact ⟨_, .pair leftImage rightImage⟩

  theorem CodeListImage.normalize_image {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ∃ normalized, CodeListImage depth (normalizeReflectiveList wrappedRhoDeclaration sources) normalized := by
    cases image with
    | nil => exact ⟨_, .nil⟩
    | cons head tail =>
      obtain ⟨normalizedHead, headImage⟩ := head.normalize_image
      obtain ⟨normalizedTail, tailImage⟩ := tail.normalize_image
      exact ⟨_, .cons headImage tailImage⟩
end

private theorem wrapped_quote_name :
    wrappedRhoDeclaration.quoteConstructor = "$cost:wrapped-constructor:NQuote" := rfl

private theorem wrapped_drop_name :
    wrappedRhoDeclaration.dropConstructor = "$cost:wrapped-constructor:PDrop" := rfl

private theorem wrapped_unit_name :
    wrappedRhoDeclaration.parallelUnitConstructor = "$cost:wrapped-constructor:PZero" := rfl

private theorem wrapped_parallel :
    wrappedRhoDeclaration.parallelCollection = .hashBag := rfl

/-- Image code whose declared parallel members are exactly one drop exposes a
name image, and so does such a list of image code. -/
private theorem exposed_names :
    (∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority},
      CodeImage depth source term → ∀ name,
        parallelLeaves wrappedRhoDeclaration source =
          [.apply wrappedRhoDeclaration.dropConstructor [name]] →
        ∃ nameTerm, NameImage depth name nameTerm) ∧
    (∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority},
      CodeListImage depth sources term → ∀ name,
        parallelLeavesList wrappedRhoDeclaration sources =
          [.apply wrappedRhoDeclaration.dropConstructor [name]] →
        ∃ nameTerm, NameImage depth name nameTerm) := by
  let M2 : (depth : Nat) → (source : Pattern) → (term : CostTerm LiteralAuthority) →
      CodeImage depth source term → Prop := fun depth source _ _ => ∀ name,
    parallelLeaves wrappedRhoDeclaration source = [.apply wrappedRhoDeclaration.dropConstructor [name]] →
      ∃ nameTerm, NameImage depth name nameTerm
  let M4 : (depth : Nat) → (sources : List Pattern) → (term : CostTerm LiteralAuthority) →
      CodeListImage depth sources term → Prop := fun depth sources _ _ => ∀ name,
    parallelLeavesList wrappedRhoDeclaration sources = [.apply wrappedRhoDeclaration.dropConstructor [name]] →
      ∃ nameTerm, NameImage depth name nameTerm
  have codeZero : ∀ {depth : Nat}, M2 depth (.apply "$cost:wrapped-constructor:PZero" []) .nil .zero := by
    intro depth name leaves
    simp [parallelLeaves, wrapped_unit_name] at leaves
  have codeDrop : ∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (parsed : NameImage depth source name), True →
      M2 depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name) (.drop parsed) := by
    intro depth source nameTerm parsed _ name leaves
    simp only [parallelLeaves, List.cons.injEq, Pattern.apply.injEq, and_true] at leaves
    rw [← leaves.2]
    exact ⟨_, parsed⟩
  have codeSigned : ∀ {depth : Nat} {core source : Pattern} {process : CostProc LiteralAuthority}
      (signature : TypedSignature source) (accepted : signature? source = some signature)
      (parsed : ProcImage depth core process), True →
      M2 depth (.apply "$cost:apparatus-constructor:signed" [core, source])
        (.signed process signature.val) (.signed signature accepted parsed) := by
    intro depth core source process signature accepted parsed _ name leaves
    simp [parallelLeaves, wrapped_drop_name] at leaves
  have codeCollection : ∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (parsed : CodeListImage depth sources term), M4 depth sources term parsed →
      M2 depth (.collection .hashBag sources none) term (.collection parsed) := by
    intro depth sources term parsed exposed name leaves
    exact exposed name (by simpa [parallelLeaves, wrapped_parallel] using leaves)
  have listNil : ∀ {depth : Nat}, M4 depth [] .nil .nil := by
    intro depth name leaves
    simp [parallelLeavesList] at leaves
  have listCons : ∀ {depth : Nat} {source : Pattern} {sources : List Pattern}
      {head tail : CostTerm LiteralAuthority}
      (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail),
      M2 depth source head headImage → M4 depth sources tail tailImage →
      M4 depth (source :: sources) (.par head tail) (.cons headImage tailImage) := by
    intro depth source sources head tail headImage tailImage headExposed tailExposed name leaves
    simp only [parallelLeavesList] at leaves
    rcases List.append_eq_singleton_iff.mp leaves with ⟨_, rest⟩ | ⟨first, _⟩
    · exact tailExposed name rest
    · exact headExposed name first
  refine ⟨fun image => ?_, fun image => ?_⟩
  · exact CodeImage.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := M2)
      (motive_3 := fun _ _ _ _ => True) (motive_4 := M4)
      (fun _ => trivial) trivial (fun _ _ => trivial) codeZero codeDrop codeSigned codeCollection
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      listNil listCons image
  · exact CodeListImage.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := M2)
      (motive_3 := fun _ _ _ _ => True) (motive_4 := M4)
      (fun _ => trivial) trivial (fun _ _ => trivial) codeZero codeDrop codeSigned codeCollection
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      listNil listCons image

/-- Resolving quotations of drops stays inside the parser image. -/
private theorem resolved_images :
    (∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority},
      NameImage depth source name → ∃ resolved, NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved) ∧
    (∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority},
      CodeImage depth source term → ∃ resolved, CodeImage depth (resolveQuotes wrappedRhoDeclaration source) resolved) ∧
    (∀ {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority},
      ProcImage depth source process → ∃ resolved, ProcImage depth (resolveQuotes wrappedRhoDeclaration source) resolved) ∧
    (∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority},
      CodeListImage depth sources term →
        ∃ resolved, CodeListImage depth (resolveQuotesList wrappedRhoDeclaration sources) resolved) := by
  let M1 : (depth : Nat) → (source : Pattern) → (name : CostName LiteralAuthority) →
      NameImage depth source name → Prop :=
    fun depth source _ _ => ∃ resolved, NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved
  let M2 : (depth : Nat) → (source : Pattern) → (term : CostTerm LiteralAuthority) →
      CodeImage depth source term → Prop :=
    fun depth source _ _ => ∃ resolved, CodeImage depth (resolveQuotes wrappedRhoDeclaration source) resolved
  let M3 : (depth : Nat) → (source : Pattern) → (process : CostProc LiteralAuthority) →
      ProcImage depth source process → Prop :=
    fun depth source _ _ => ∃ resolved, ProcImage depth (resolveQuotes wrappedRhoDeclaration source) resolved
  let M4 : (depth : Nat) → (sources : List Pattern) → (term : CostTerm LiteralAuthority) →
      CodeListImage depth sources term → Prop :=
    fun depth sources _ _ =>
      ∃ resolved, CodeListImage depth (resolveQuotesList wrappedRhoDeclaration sources) resolved
  have nameBvar : ∀ {depth index : Nat} (bound : index < depth),
      M1 depth (.bvar index) (.bvar index) (.bvar bound) :=
    fun bound => ⟨_, .bvar bound⟩
  have nameBaseZero : ∀ {depth : Nat}, M1 depth
      (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])
      (.quote .nil) .baseZeroQuote := by
    intro depth
    refine ⟨.quote .nil, ?_⟩
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, wrapped_quote_name,
      String.reduceEq, ite_false]
    exact .baseZeroQuote
  have nameQuote : ∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (code : CodeImage 0 source term), M2 0 source term code →
      M1 depth (.apply "$cost:wrapped-constructor:NQuote" [source]) (.quote term) (.quote code) := by
    intro depth source term code resolvedCode
    obtain ⟨resolved, resolvedImage⟩ := resolvedCode
    show ∃ name, NameImage depth (finishResolveApply wrappedRhoDeclaration
      "$cost:wrapped-constructor:NQuote" [resolveQuotes wrappedRhoDeclaration source]) name
    simp only [finishResolveApply, wrapped_quote_name, if_true]
    cases exposed : exposedDrop? wrappedRhoDeclaration (resolveQuotes wrappedRhoDeclaration source) with
    | none => exact ⟨_, .quote resolvedImage⟩
    | some name =>
      obtain ⟨nameTerm, nameImage⟩ := exposed_names.1 resolvedImage name
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.exposedDrop?_eq_some_iff).mp exposed)
      exact ⟨_, nameImage.weaken (Nat.zero_le depth)⟩
  have codeZero : ∀ {depth : Nat}, M2 depth (.apply "$cost:wrapped-constructor:PZero" []) .nil .zero :=
    ⟨_, .zero⟩
  have codeDrop : ∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (parsed : NameImage depth source name), M1 depth source name parsed →
      M2 depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name) (.drop parsed) := by
    intro depth source name parsed resolvedName
    obtain ⟨resolved, resolvedImage⟩ := resolvedName
    refine ⟨.drop resolved, ?_⟩
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, wrapped_quote_name,
      String.reduceEq, ite_false]
    exact .drop resolvedImage
  have codeSigned : ∀ {depth : Nat} {core source : Pattern} {process : CostProc LiteralAuthority}
      (signature : TypedSignature source) (accepted : signature? source = some signature)
      (parsed : ProcImage depth core process), M3 depth core process parsed →
      M2 depth (.apply "$cost:apparatus-constructor:signed" [core, source])
        (.signed process signature.val) (.signed signature accepted parsed) := by
    intro depth core source process signature accepted parsed resolvedProcess
    obtain ⟨resolved, resolvedImage⟩ := resolvedProcess
    refine ⟨.signed resolved signature.val, ?_⟩
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply,
      (signature?_accepted_syntax accepted).resolve_identity]
    exact .signed signature accepted resolvedImage
  have codeCollection : ∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (parsed : CodeListImage depth sources term), M4 depth sources term parsed →
      M2 depth (.collection .hashBag sources none) term (.collection parsed) := by
    intro depth sources term parsed resolvedList
    obtain ⟨resolved, resolvedImage⟩ := resolvedList
    exact ⟨_, .collection resolvedImage⟩
  have procZero : ∀ {depth : Nat}, M3 depth (.apply "$cost:base-constructor:PZero" []) .nil .zero :=
    ⟨_, .zero⟩
  have procSend : ∀ {depth : Nat} {channel payload : Pattern} {name : CostName LiteralAuthority}
      {term : CostTerm LiteralAuthority}
      (channelImage : NameImage depth channel name) (payloadImage : CodeImage depth payload term),
      M1 depth channel name channelImage → M2 depth payload term payloadImage →
      M3 depth (.apply "$cost:base-constructor:POutput" [channel, payload]) (.send name term)
        (.send channelImage payloadImage) := by
    intro depth channel payload name term channelImage payloadImage resolvedName resolvedCode
    obtain ⟨resolvedChannel, channelResolved⟩ := resolvedName
    obtain ⟨resolvedPayload, payloadResolved⟩ := resolvedCode
    exact ⟨_, .send channelResolved payloadResolved⟩
  have procRecv : ∀ {depth : Nat} {channel body : Pattern} {name : CostName LiteralAuthority}
      {term : CostTerm LiteralAuthority}
      (channelImage : NameImage depth channel name) (bodyImage : CodeImage (depth + 1) body term),
      M1 depth channel name channelImage → M2 (depth + 1) body term bodyImage →
      M3 depth (.apply "$cost:base-constructor:PInput" [channel, .lambda none body]) (.recv name term)
        (.recv channelImage bodyImage) := by
    intro depth channel body name term channelImage bodyImage resolvedName resolvedBody
    obtain ⟨resolvedChannel, channelResolved⟩ := resolvedName
    obtain ⟨resolvedCode, bodyResolved⟩ := resolvedBody
    exact ⟨_, .recv channelResolved bodyResolved⟩
  have procPair : ∀ {depth : Nat} {left right : Pattern} {first second : CostProc LiteralAuthority}
      (leftImage : ProcImage depth left first) (rightImage : ProcImage depth right second),
      M3 depth left first leftImage → M3 depth right second rightImage →
      M3 depth (.collection .hashBag [left, right] none) (.par first second)
        (.pair leftImage rightImage) := by
    intro depth left right first second leftImage rightImage resolvedLeft resolvedRight
    obtain ⟨resolvedFirst, leftResolved⟩ := resolvedLeft
    obtain ⟨resolvedSecond, rightResolved⟩ := resolvedRight
    exact ⟨_, .pair leftResolved rightResolved⟩
  have listNil : ∀ {depth : Nat}, M4 depth [] .nil .nil := ⟨_, .nil⟩
  have listCons : ∀ {depth : Nat} {source : Pattern} {sources : List Pattern}
      {head tail : CostTerm LiteralAuthority}
      (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail),
      M2 depth source head headImage → M4 depth sources tail tailImage →
      M4 depth (source :: sources) (.par head tail) (.cons headImage tailImage) := by
    intro depth source sources head tail headImage tailImage resolvedHead resolvedTail
    obtain ⟨resolvedFirst, headResolved⟩ := resolvedHead
    obtain ⟨resolvedRest, tailResolved⟩ := resolvedTail
    exact ⟨_, .cons headResolved tailResolved⟩
  refine ⟨fun image => ?_, fun image => ?_, fun image => ?_, fun image => ?_⟩
  · exact NameImage.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
      nameBvar nameBaseZero nameQuote codeZero codeDrop codeSigned codeCollection
      procZero procSend procRecv procPair listNil listCons image
  · exact CodeImage.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
      nameBvar nameBaseZero nameQuote codeZero codeDrop codeSigned codeCollection
      procZero procSend procRecv procPair listNil listCons image
  · exact ProcImage.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
      nameBvar nameBaseZero nameQuote codeZero codeDrop codeSigned codeCollection
      procZero procSend procRecv procPair listNil listCons image
  · exact CodeListImage.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
      nameBvar nameBaseZero nameQuote codeZero codeDrop codeSigned codeCollection
      procZero procSend procRecv procPair listNil listCons image

theorem NameImage.resolve_image {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name) :
    ∃ resolved, NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved :=
  resolved_images.1 image

theorem CodeImage.resolve_image {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
    ∃ resolved, CodeImage depth (resolveQuotes wrappedRhoDeclaration source) resolved :=
  resolved_images.2.1 image

theorem ProcImage.resolve_image {depth : Nat} {source : Pattern}
    {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
    ∃ resolved, ProcImage depth (resolveQuotes wrappedRhoDeclaration source) resolved :=
  resolved_images.2.2.1 image

theorem CodeListImage.resolve_image {depth : Nat} {sources : List Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
    ∃ resolved, CodeListImage depth (resolveQuotesList wrappedRhoDeclaration sources) resolved :=
  resolved_images.2.2.2 image

theorem name_parser_normalization_closed {fuel depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (parsed : (name? fuel depth source).map Subtype.val = some name) :
    ∃ normalized fuel, (name? fuel depth (normalizeReflective wrappedRhoDeclaration source)).map
      Subtype.val = some normalized := by
  obtain ⟨normalized, image⟩ := (name_parser_image parsed).normalize_image
  obtain ⟨fuel, parsed⟩ := name_parser_iff_image.mpr image
  exact ⟨normalized, fuel, parsed⟩

theorem code_parser_normalization_closed {fuel depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (parsed : (code? fuel depth source).map Subtype.val = some term) :
    ∃ normalized fuel, (code? fuel depth (normalizeReflective wrappedRhoDeclaration source)).map
      Subtype.val = some normalized := by
  obtain ⟨normalized, image⟩ := (code_parser_image parsed).normalize_image
  obtain ⟨fuel, parsed⟩ := code_parser_iff_image.mpr image
  exact ⟨normalized, fuel, parsed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
