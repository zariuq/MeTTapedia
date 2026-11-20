import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedRawNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSubstitutionClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRawEncoding

/-!
# Exact raw normal comparison for arbitrary admitted receiver substitution

The actual wrapped reflective operation is decoded structurally. Its readout
has the same raw normal form as the existing binder-eliminating communication
operation. Closed payloads and the anonymous receiver domain remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation (substituteNameMark_closed)

mutual
  theorem NameImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage scope source name)
      (larger : scope ≤ cutoff) (amount : Nat) : name.lift amount cutoff = name := by
    cases image with
    | @bvar _ index bound => simp [CostName.lift, show ¬cutoff ≤ index from by omega]
    | baseZeroQuote => rfl
    | quote code => rfl

  theorem CodeImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage scope source term)
      (larger : scope ≤ cutoff) (amount : Nat) : term.lift amount cutoff = term := by
    cases image with
    | zero => rfl
    | drop name => simp only [CostTerm.lift, name.liftAbove_eq larger amount]
    | signed signature accepted process => simp only [CostTerm.lift, process.liftAbove_eq larger amount]
    | collection codes => exact codes.liftAbove_eq larger amount

  theorem ProcImage.liftAbove_eq {scope cutoff : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage scope source process)
      (larger : scope ≤ cutoff) (amount : Nat) : process.lift amount cutoff = process := by
    cases image with
    | zero => rfl
    | send name code => simp only [CostProc.lift, name.liftAbove_eq larger amount, code.liftAbove_eq larger amount]
    | recv name code =>
      simp only [CostProc.lift, name.liftAbove_eq larger amount,
        code.liftAbove_eq (Nat.add_le_add_right larger 1) amount]
    | pair left right => simp only [CostProc.lift, left.liftAbove_eq larger amount, right.liftAbove_eq larger amount]

  theorem CodeListImage.liftAbove_eq {scope cutoff : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage scope sources term)
      (larger : scope ≤ cutoff) (amount : Nat) : term.lift amount cutoff = term := by
    cases image with
    | nil => rfl
    | cons head tail => simp only [CostTerm.lift, head.liftAbove_eq larger amount, tail.liftAbove_eq larger amount]
end

private theorem wrapped_unit :
    wrappedRhoDeclaration.parallelUnitConstructor = "$cost:wrapped-constructor:PZero" := rfl

private theorem wrapped_drop :
    wrappedRhoDeclaration.dropConstructor = "$cost:wrapped-constructor:PDrop" := rfl

private theorem wrapped_quote :
    wrappedRhoDeclaration.quoteConstructor = "$cost:wrapped-constructor:NQuote" := rfl

private theorem wrapped_bag : wrappedRhoDeclaration.parallelCollection = .hashBag := rfl

/-- The raw normal form of image code whose declared parallel members are
none is nil, and of image code whose members are exactly one drop is that
drop. -/
private theorem raw_exposed :
    (∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority},
      CodeImage depth source term →
        (parallelLeaves wrappedRhoDeclaration source = [] →
          (literalEncodeTerm term).normalize = .nil) ∧
        (∀ name, parallelLeaves wrappedRhoDeclaration source =
            [.apply wrappedRhoDeclaration.dropConstructor [name]] →
          ∃ nameTerm, NameImage depth name nameTerm ∧
            (literalEncodeTerm term).normalize = .drop (literalEncodeName nameTerm).normalize)) ∧
    (∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority},
      CodeListImage depth sources term →
        (parallelLeavesList wrappedRhoDeclaration sources = [] →
          (literalEncodeTerm term).normalize = .nil) ∧
        (∀ name, parallelLeavesList wrappedRhoDeclaration sources =
            [.apply wrappedRhoDeclaration.dropConstructor [name]] →
          ∃ nameTerm, NameImage depth name nameTerm ∧
            (literalEncodeTerm term).normalize = .drop (literalEncodeName nameTerm).normalize)) := by
  let M2 : (depth : Nat) → (source : Pattern) → (term : CostTerm LiteralAuthority) →
      CodeImage depth source term → Prop := fun depth source term _ =>
    (parallelLeaves wrappedRhoDeclaration source = [] → (literalEncodeTerm term).normalize = .nil) ∧
    (∀ name, parallelLeaves wrappedRhoDeclaration source =
        [.apply wrappedRhoDeclaration.dropConstructor [name]] →
      ∃ nameTerm, NameImage depth name nameTerm ∧
        (literalEncodeTerm term).normalize = .drop (literalEncodeName nameTerm).normalize)
  let M4 : (depth : Nat) → (sources : List Pattern) → (term : CostTerm LiteralAuthority) →
      CodeListImage depth sources term → Prop := fun depth sources term _ =>
    (parallelLeavesList wrappedRhoDeclaration sources = [] → (literalEncodeTerm term).normalize = .nil) ∧
    (∀ name, parallelLeavesList wrappedRhoDeclaration sources =
        [.apply wrappedRhoDeclaration.dropConstructor [name]] →
      ∃ nameTerm, NameImage depth name nameTerm ∧
        (literalEncodeTerm term).normalize = .drop (literalEncodeName nameTerm).normalize)
  have codeZero : ∀ {depth : Nat}, M2 depth (.apply "$cost:wrapped-constructor:PZero" []) .nil .zero := by
    intro depth
    refine ⟨fun _ => rfl, fun name leaves => ?_⟩
    simp [parallelLeaves, wrapped_unit] at leaves
  have codeDrop : ∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (parsed : NameImage depth source name), True →
      M2 depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name) (.drop parsed) := by
    intro depth source name parsed _
    refine ⟨fun leaves => by simp [parallelLeaves] at leaves, fun other leaves => ?_⟩
    simp only [parallelLeaves, List.cons.injEq, Pattern.apply.injEq, and_true] at leaves
    rw [← leaves.2]
    exact ⟨name, parsed, rfl⟩
  have codeSigned : ∀ {depth : Nat} {core source : Pattern} {process : CostProc LiteralAuthority}
      (signature : TypedSignature source) (accepted : signature? source = some signature)
      (parsed : ProcImage depth core process), True →
      M2 depth (.apply "$cost:apparatus-constructor:signed" [core, source])
        (.signed process signature.val) (.signed signature accepted parsed) := by
    intro depth core source process signature accepted parsed _
    refine ⟨fun leaves => by simp [parallelLeaves] at leaves, fun name leaves => ?_⟩
    simp [parallelLeaves, wrapped_drop] at leaves
  have codeCollection : ∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (parsed : CodeListImage depth sources term), M4 depth sources term parsed →
      M2 depth (.collection .hashBag sources none) term (.collection parsed) := by
    intro depth sources term parsed listFacts
    refine ⟨fun leaves => listFacts.1 (by simpa [parallelLeaves, wrapped_bag] using leaves),
      fun name leaves => listFacts.2 name (by simpa [parallelLeaves, wrapped_bag] using leaves)⟩
  have listNil : ∀ {depth : Nat}, M4 depth [] .nil .nil := by
    intro depth
    exact ⟨fun _ => rfl, fun name leaves => by simp [parallelLeavesList] at leaves⟩
  have listCons : ∀ {depth : Nat} {source : Pattern} {sources : List Pattern}
      {head tail : CostTerm LiteralAuthority}
      (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail),
      M2 depth source head headImage → M4 depth sources tail tailImage →
      M4 depth (source :: sources) (.par head tail) (.cons headImage tailImage) := by
    intro depth source sources head tail headImage tailImage headFacts tailFacts
    have parNormalize : ∀ (left right : RawCostTerm),
        (RawCostTerm.par left right).normalize =
          RawCostTerm.fromComponents (stableKeySort RawCostTerm.key
            (left.normalize.components ++ right.normalize.components)) := fun _ _ => rfl
    refine ⟨fun leaves => ?_, fun name leaves => ?_⟩
    · simp only [parallelLeavesList, List.append_eq_nil_iff] at leaves
      change (RawCostTerm.par (literalEncodeTerm head) (literalEncodeTerm tail)).normalize = .nil
      rw [parNormalize, headFacts.1 leaves.1, tailFacts.1 leaves.2]
      rfl
    · simp only [parallelLeavesList] at leaves
      change ∃ nameTerm, NameImage depth name nameTerm ∧
        (RawCostTerm.par (literalEncodeTerm head) (literalEncodeTerm tail)).normalize = _
      rcases List.append_eq_singleton_iff.mp leaves with ⟨headEmpty, tailOne⟩ | ⟨headOne, tailEmpty⟩
      · obtain ⟨nameTerm, nameImage, tailDrop⟩ := tailFacts.2 name tailOne
        refine ⟨nameTerm, nameImage, ?_⟩
        rw [parNormalize, headFacts.1 headEmpty, tailDrop]
        rfl
      · obtain ⟨nameTerm, nameImage, headDrop⟩ := headFacts.2 name headOne
        refine ⟨nameTerm, nameImage, ?_⟩
        rw [parNormalize, headDrop, tailFacts.1 tailEmpty]
        rfl
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

/-- Resolving quotations of drops keeps admitted code inside the parser image
with the same raw normal readout. -/
private theorem resolved_raw_readouts :
    (∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority},
      NameImage depth source name → ∃ resolved,
        NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
        (literalEncodeName name).normalize = (literalEncodeName resolved).normalize) ∧
    (∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority},
      CodeImage depth source term → ∃ resolved,
        CodeImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm resolved).normalize) ∧
    (∀ {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority},
      ProcImage depth source process → ∃ resolved,
        ProcImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
        (literalEncodeProc process).normalize = (literalEncodeProc resolved).normalize) ∧
    (∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority},
      CodeListImage depth sources term → ∃ resolved,
        CodeListImage depth (resolveQuotesList wrappedRhoDeclaration sources) resolved ∧
        (literalEncodeTerm term).normalize = (literalEncodeTerm resolved).normalize) := by
  let M1 : (depth : Nat) → (source : Pattern) → (name : CostName LiteralAuthority) →
      NameImage depth source name → Prop := fun depth source name _ => ∃ resolved,
    NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
      (literalEncodeName name).normalize = (literalEncodeName resolved).normalize
  let M2 : (depth : Nat) → (source : Pattern) → (term : CostTerm LiteralAuthority) →
      CodeImage depth source term → Prop := fun depth source term _ => ∃ resolved,
    CodeImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
      (literalEncodeTerm term).normalize = (literalEncodeTerm resolved).normalize
  let M3 : (depth : Nat) → (source : Pattern) → (process : CostProc LiteralAuthority) →
      ProcImage depth source process → Prop := fun depth source process _ => ∃ resolved,
    ProcImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
      (literalEncodeProc process).normalize = (literalEncodeProc resolved).normalize
  let M4 : (depth : Nat) → (sources : List Pattern) → (term : CostTerm LiteralAuthority) →
      CodeListImage depth sources term → Prop := fun depth sources term _ => ∃ resolved,
    CodeListImage depth (resolveQuotesList wrappedRhoDeclaration sources) resolved ∧
      (literalEncodeTerm term).normalize = (literalEncodeTerm resolved).normalize
  have nameBvar : ∀ {depth index : Nat} (bound : index < depth),
      M1 depth (.bvar index) (.bvar index) (.bvar bound) :=
    fun bound => ⟨_, .bvar bound, rfl⟩
  have nameBaseZero : ∀ {depth : Nat}, M1 depth
      (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])
      (.quote .nil) .baseZeroQuote := by
    intro depth
    refine ⟨.quote .nil, ?_, rfl⟩
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, wrapped_quote,
      String.reduceEq, ite_false]
    exact .baseZeroQuote
  have nameQuote : ∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (code : CodeImage 0 source term), M2 0 source term code →
      M1 depth (.apply "$cost:wrapped-constructor:NQuote" [source]) (.quote term) (.quote code) := by
    intro depth source term code resolvedCode
    obtain ⟨resolved, resolvedImage, same⟩ := resolvedCode
    show ∃ name, NameImage depth (finishResolveApply wrappedRhoDeclaration
      "$cost:wrapped-constructor:NQuote" [resolveQuotes wrappedRhoDeclaration source]) name ∧ _
    simp only [finishResolveApply, wrapped_quote, if_true]
    cases exposed : exposedDrop? wrappedRhoDeclaration (resolveQuotes wrappedRhoDeclaration source) with
    | none => exact ⟨_, .quote resolvedImage, raw_quote_normalize_congr same⟩
    | some name =>
      obtain ⟨nameTerm, nameImage, dropped⟩ := (raw_exposed.1 resolvedImage).2 name
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.exposedDrop?_eq_some_iff).mp exposed)
      refine ⟨nameTerm, nameImage.weaken (Nat.zero_le depth), ?_⟩
      change (RawCostName.quote (literalEncodeTerm term)).normalize = _
      simp only [RawCostName.normalize]
      rw [same, dropped]
  have codeZero : ∀ {depth : Nat}, M2 depth (.apply "$cost:wrapped-constructor:PZero" []) .nil .zero :=
    ⟨_, .zero, rfl⟩
  have codeDrop : ∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (parsed : NameImage depth source name), M1 depth source name parsed →
      M2 depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name) (.drop parsed) := by
    intro depth source name parsed resolvedName
    obtain ⟨resolved, resolvedImage, same⟩ := resolvedName
    refine ⟨.drop resolved, ?_, ?_⟩
    · simp only [resolveQuotes, resolveQuotesList, finishResolveApply, wrapped_quote,
        String.reduceEq, ite_false]
      exact .drop resolvedImage
    · change RawCostTerm.drop (literalEncodeName name).normalize =
        RawCostTerm.drop (literalEncodeName resolved).normalize
      rw [same]
  have codeSigned : ∀ {depth : Nat} {core source : Pattern} {process : CostProc LiteralAuthority}
      (signature : TypedSignature source) (accepted : signature? source = some signature)
      (parsed : ProcImage depth core process), M3 depth core process parsed →
      M2 depth (.apply "$cost:apparatus-constructor:signed" [core, source])
        (.signed process signature.val) (.signed signature accepted parsed) := by
    intro depth core source process signature accepted parsed resolvedProcess
    obtain ⟨resolved, resolvedImage, same⟩ := resolvedProcess
    refine ⟨.signed resolved signature.val, ?_, ?_⟩
    · simp only [resolveQuotes, resolveQuotesList, finishResolveApply,
        (signature?_accepted_syntax accepted).resolve_identity]
      exact .signed signature accepted resolvedImage
    · change RawCostTerm.signed (literalEncodeProc process).normalize _ =
        RawCostTerm.signed (literalEncodeProc resolved).normalize _
      rw [same]
  have codeCollection : ∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (parsed : CodeListImage depth sources term), M4 depth sources term parsed →
      M2 depth (.collection .hashBag sources none) term (.collection parsed) := by
    intro depth sources term parsed resolvedList
    obtain ⟨resolved, resolvedImage, same⟩ := resolvedList
    exact ⟨_, .collection resolvedImage, same⟩
  have procZero : ∀ {depth : Nat}, M3 depth (.apply "$cost:base-constructor:PZero" []) .nil .zero := by
    intro depth
    refine ⟨.nil, ?_, rfl⟩
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply]
    exact .zero
  have procSend : ∀ {depth : Nat} {channel payload : Pattern} {name : CostName LiteralAuthority}
      {term : CostTerm LiteralAuthority}
      (channelImage : NameImage depth channel name) (payloadImage : CodeImage depth payload term),
      M1 depth channel name channelImage → M2 depth payload term payloadImage →
      M3 depth (.apply "$cost:base-constructor:POutput" [channel, payload]) (.send name term)
        (.send channelImage payloadImage) := by
    intro depth channel payload name term channelImage payloadImage resolvedName resolvedCode
    obtain ⟨resolvedChannel, channelResolved, nameSame⟩ := resolvedName
    obtain ⟨resolvedPayload, payloadResolved, codeSame⟩ := resolvedCode
    refine ⟨_, .send channelResolved payloadResolved, ?_⟩
    change RawCostProc.send (literalEncodeName name).normalize (literalEncodeTerm term).normalize =
      RawCostProc.send (literalEncodeName resolvedChannel).normalize
        (literalEncodeTerm resolvedPayload).normalize
    rw [nameSame, codeSame]
  have procRecv : ∀ {depth : Nat} {channel body : Pattern} {name : CostName LiteralAuthority}
      {term : CostTerm LiteralAuthority}
      (channelImage : NameImage depth channel name) (bodyImage : CodeImage (depth + 1) body term),
      M1 depth channel name channelImage → M2 (depth + 1) body term bodyImage →
      M3 depth (.apply "$cost:base-constructor:PInput" [channel, .lambda none body]) (.recv name term)
        (.recv channelImage bodyImage) := by
    intro depth channel body name term channelImage bodyImage resolvedName resolvedBody
    obtain ⟨resolvedChannel, channelResolved, nameSame⟩ := resolvedName
    obtain ⟨resolvedCode, bodyResolved, codeSame⟩ := resolvedBody
    refine ⟨_, .recv channelResolved bodyResolved, ?_⟩
    change RawCostProc.recv (literalEncodeName name).normalize (literalEncodeTerm term).normalize =
      RawCostProc.recv (literalEncodeName resolvedChannel).normalize
        (literalEncodeTerm resolvedCode).normalize
    rw [nameSame, codeSame]
  have procPair : ∀ {depth : Nat} {left right : Pattern} {first second : CostProc LiteralAuthority}
      (leftImage : ProcImage depth left first) (rightImage : ProcImage depth right second),
      M3 depth left first leftImage → M3 depth right second rightImage →
      M3 depth (.collection .hashBag [left, right] none) (.par first second)
        (.pair leftImage rightImage) := by
    intro depth left right first second leftImage rightImage resolvedLeft resolvedRight
    obtain ⟨resolvedFirst, leftResolved, leftSame⟩ := resolvedLeft
    obtain ⟨resolvedSecond, rightResolved, rightSame⟩ := resolvedRight
    exact ⟨_, .pair leftResolved rightResolved, raw_proc_par_normalize_congr leftSame rightSame⟩
  have listNil : ∀ {depth : Nat}, M4 depth [] .nil .nil := ⟨_, .nil, rfl⟩
  have listCons : ∀ {depth : Nat} {source : Pattern} {sources : List Pattern}
      {head tail : CostTerm LiteralAuthority}
      (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail),
      M2 depth source head headImage → M4 depth sources tail tailImage →
      M4 depth (source :: sources) (.par head tail) (.cons headImage tailImage) := by
    intro depth source sources head tail headImage tailImage resolvedHead resolvedTail
    obtain ⟨resolvedFirst, headResolved, headSame⟩ := resolvedHead
    obtain ⟨resolvedRest, tailResolved, tailSame⟩ := resolvedTail
    exact ⟨_, .cons headResolved tailResolved, raw_term_par_normalize_congr headSame tailSame⟩
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

theorem NameImage.resolve_raw_readout {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name) :
    ∃ resolved, NameImage depth (resolveQuotes wrappedRhoDeclaration source) resolved ∧
      (literalEncodeName name).normalize = (literalEncodeName resolved).normalize :=
  resolved_raw_readouts.1 image

theorem NameImage.literal_substitute_raw_readout {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote term))
    (replacement : Pattern) :
    ∃ normalized, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth replacement source) normalized ∧
      (literalEncodeName (.quote term)).normalize = (literalEncodeName normalized).normalize := by
  obtain ⟨resolved, resolvedImage, same⟩ := image.quote_closed_image.resolve_raw_readout
  rw [image.substituteReflective_eq_mark,
    substituteNameMark_closed wrappedRhoDeclaration depth replacement image.quote_source_closed]
  exact ⟨resolved, resolvedImage.weaken (Nat.zero_le depth), same⟩

theorem NameImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
    {name : CostName LiteralAuthority} {payload : CostTerm LiteralAuthority}
    (image : NameImage (depth + 1) source name) (payloadImage : CodeImage 0 payloadSource payload) :
    ∃ result, NameImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
      (literalEncodeName (CostName.substitute payload depth name)).normalize =
        (literalEncodeName result).normalize := by
  cases image with
  | @bvar _ index bound =>
    by_cases matched : index = depth
    · subst index
      obtain ⟨normalized, normalizedImage, same⟩ := payloadImage.normalize_raw_readout
      simp only [substituteReflective, resolveQuotes, substituteResolved, if_true, generatedReplacement]
      refine ⟨_, .quote normalizedImage, ?_⟩
      rw [CostName.substitute, if_pos rfl, payloadImage.liftAbove_eq (le_refl 0) depth]
      exact raw_quote_normalize_congr same
    · simp only [substituteReflective, resolveQuotes, substituteResolved, matched, if_false]
      refine ⟨_, .bvar (by omega), ?_⟩
      simp [CostName.substitute, matched, show ¬depth < index from by omega]
  | baseZeroQuote => exact NameImage.literal_substitute_raw_readout .baseZeroQuote _
  | quote code => exact NameImage.literal_substitute_raw_readout (.quote code) _

private theorem drop_literal_substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
    {quoted payload : CostTerm LiteralAuthority} (image : NameImage (depth + 1) source (.quote quoted)) :
    ∃ result, CodeImage depth
      (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource)
        (.apply "$cost:wrapped-constructor:PDrop" [source])) result ∧
      (literalEncodeTerm (CostTerm.substitute payload depth (.drop (.quote quoted)))).normalize =
        (literalEncodeTerm result).normalize := by
  rw [substituteReflective_drop_closed depth _ image.quote_source_closed]
  obtain ⟨resolved, resolvedImage, same⟩ := image.quote_closed_image.resolve_raw_readout
  refine ⟨_, .drop (resolvedImage.weaken (Nat.zero_le depth)), ?_⟩
  change RawCostTerm.drop (literalEncodeName (.quote quoted)).normalize =
    RawCostTerm.drop (literalEncodeName resolved).normalize
  rw [same]

mutual
  theorem CodeImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
      {term payload : CostTerm LiteralAuthority} (image : CodeImage (depth + 1) source term)
      (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
        (literalEncodeTerm (CostTerm.substitute payload depth term)).normalize =
          (literalEncodeTerm result).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | drop name =>
      cases name with
      | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          obtain ⟨normalized, normalizedImage, same⟩ := payloadImage.normalize_raw_readout
          simp only [substituteReflective, resolveQuotes, resolveQuotesList, finishResolveApply,
            substituteResolved, matchesBinder_bvar, receive, generatedReplacement, wrapped_quote,
            wrapped_drop, beq_self_eq_true, ite_true, String.reduceEq, ite_false]
          refine ⟨_, normalizedImage.weaken (Nat.zero_le depth), ?_⟩
          rw [CostTerm.substitute, if_pos rfl, payloadImage.liftAbove_eq (le_refl 0) depth]
          exact same
        · simp only [substituteReflective, resolveQuotes, resolveQuotesList, finishResolveApply,
            substituteResolved, matchesBinder_bvar, wrapped_quote, wrapped_drop,
            beq_iff_eq, matched, ite_false, String.reduceEq]
          refine ⟨_, .drop (.bvar (by omega)), ?_⟩
          simp [CostTerm.substitute, matched, show ¬depth < index from by omega]
      | baseZeroQuote => exact drop_literal_substitute_raw_readout .baseZeroQuote
      | quote code => exact drop_literal_substitute_raw_readout (.quote code)
    | signed signature accepted process =>
      obtain ⟨result, resultImage, same⟩ := process.substitute_raw_readout payloadImage
      change ∃ result, CodeImage depth (.apply "$cost:apparatus-constructor:signed"
        [substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _,
         substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) _]) result ∧ _
      rw [signature?_accepted_substitution_identity accepted]
      refine ⟨_, .signed signature accepted resultImage, ?_⟩
      change RawCostTerm.signed (literalEncodeProc (CostProc.substitute payload depth _)).normalize _ =
        RawCostTerm.signed (literalEncodeProc result).normalize _
      rw [same]
    | collection codes =>
      obtain ⟨result, resultImage, same⟩ := codes.substitute_raw_readout payloadImage
      rw [substituteReflective_collection]
      exact ⟨_, .collection resultImage, same⟩

  theorem ProcImage.substitute_raw_readout {depth : Nat} {source payloadSource : Pattern}
      {process : CostProc LiteralAuthority} {payload : CostTerm LiteralAuthority}
      (image : ProcImage (depth + 1) source process) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, ProcImage depth
        (substituteReflective wrappedRhoDeclaration depth (generatedReplacement payloadSource) source) result ∧
        (literalEncodeProc (CostProc.substitute payload depth process)).normalize =
          (literalEncodeProc result).normalize := by
    cases image with
    | zero => exact ⟨_, .zero, rfl⟩
    | send name code =>
      obtain ⟨resultName, nameImage, nameSame⟩ := name.substitute_raw_readout payloadImage
      obtain ⟨resultCode, codeImage, codeSame⟩ := code.substitute_raw_readout payloadImage
      refine ⟨_, .send nameImage codeImage, ?_⟩
      change RawCostProc.send (literalEncodeName (CostName.substitute payload depth _)).normalize
        (literalEncodeTerm (CostTerm.substitute payload depth _)).normalize =
        RawCostProc.send (literalEncodeName resultName).normalize (literalEncodeTerm resultCode).normalize
      rw [nameSame, codeSame]
    | recv name code =>
      obtain ⟨resultName, nameImage, nameSame⟩ := name.substitute_raw_readout payloadImage
      obtain ⟨resultCode, codeImage, codeSame⟩ := code.substitute_raw_readout payloadImage
      refine ⟨_, .recv nameImage codeImage, ?_⟩
      change RawCostProc.recv (literalEncodeName (CostName.substitute payload depth _)).normalize
        (literalEncodeTerm (CostTerm.substitute payload (depth + 1) _)).normalize =
        RawCostProc.recv (literalEncodeName resultName).normalize (literalEncodeTerm resultCode).normalize
      rw [nameSame, codeSame]
    | pair left right =>
      obtain ⟨resultLeft, leftImage, leftSame⟩ := left.substitute_raw_readout payloadImage
      obtain ⟨resultRight, rightImage, rightSame⟩ := right.substitute_raw_readout payloadImage
      exact ⟨_, .pair leftImage rightImage, raw_proc_par_normalize_congr leftSame rightSame⟩

  theorem CodeListImage.substitute_raw_readout {depth : Nat} {sources : List Pattern}
      {payloadSource : Pattern} {term payload : CostTerm LiteralAuthority}
      (image : CodeListImage (depth + 1) sources term) (payloadImage : CodeImage 0 payloadSource payload) :
      ∃ result, CodeListImage depth
        (substituteReflectiveList wrappedRhoDeclaration depth (generatedReplacement payloadSource) sources) result ∧
        (literalEncodeTerm (CostTerm.substitute payload depth term)).normalize =
          (literalEncodeTerm result).normalize := by
    cases image with
    | nil => exact ⟨_, .nil, rfl⟩
    | cons head tail =>
      obtain ⟨resultHead, headImage, headSame⟩ := head.substitute_raw_readout payloadImage
      obtain ⟨resultTail, tailImage, tailSame⟩ := tail.substitute_raw_readout payloadImage
      exact ⟨_, .cons headImage tailImage, raw_term_par_normalize_congr headSame tailSame⟩
end

theorem code_parser_commSubst_raw_readout {bodyFuel payloadFuel : Nat}
    {bodySource payloadSource : Pattern} {body payload : CostTerm LiteralAuthority}
    (bodyParsed : (code? bodyFuel 1 bodySource).map Subtype.val = some body)
    (payloadParsed : (code? payloadFuel 0 payloadSource).map Subtype.val = some payload) :
    ∃ result fuel, (code? fuel 0
      (substituteReflective wrappedRhoDeclaration 0 (generatedReplacement payloadSource) bodySource)).map
        Subtype.val = some result ∧
      ((literalEncodeTerm body).commSubst (literalEncodeTerm payload)).normalize =
        (literalEncodeTerm result).normalize := by
  obtain ⟨result, image, same⟩ := (code_parser_image bodyParsed).substitute_raw_readout
    (code_parser_image payloadParsed)
  obtain ⟨fuel, readback⟩ := image.parser_eventually
  refine ⟨result, fuel, readback fuel (le_refl fuel), ?_⟩
  rw [← literalEncodeTerm_commSubst]
  exact same

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
