import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin
import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatch

/-! Reading compiled atom instances back into the independent source
judgment. Pool slots retain declared names/literals and repeated source
variables read one shared binding. Source trees are not runtime arguments. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match

structure PoolsRead (pools : Join.Pools) (bindings : Bindings) : Prop where
  relations : ∀ index name, pools.relations[index]? = some name →
    bindings.lookup (Join.relationSlot index) = some (IRCodec.relation name)
  literals : ∀ index value, pools.literals[index]? = some value →
    bindings.lookup (Join.literalSlot index) = some (IRCodec.value value)

def assignment (bindings : Bindings) : Mettapedia.Languages.Datalog.Assignment := fun name =>
  (bindings.lookup (Join.logicalVariable name)).bind IRCodec.value?

private theorem index_reads {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (value : α) (index : Nat) (selected : items.idxOf? value = some index) :
    items[index]? = some value := by
  obtain ⟨bound,same,_⟩ := List.idxOf?_eq_some_iff.mp selected
  simp [bound,same]

theorem relation_instantiation (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (name : QualifiedName) (code : Pattern) (compiled : Join.relation? pools name = some code) :
    applyBindings bindings code = IRCodec.relation name := by
  cases selected : pools.relations.idxOf? name with
  | none => simp [Join.relation?,selected] at compiled
  | some index =>
    have same : Pattern.fvar (Join.relationSlot index) = code := by simpa [Join.relation?,selected] using compiled
    subst code
    rw [GeneralFirstOrderProjection.apply_variable,read.relations index name (index_reads _ _ _ selected)]
    rfl

theorem literal_instantiation (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (value : Value) (code : Pattern) (compiled : Join.literal? pools value = some code) :
    applyBindings bindings code = IRCodec.value value := by
  cases selected : pools.literals.idxOf? value with
  | none => simp [Join.literal?,selected] at compiled
  | some index =>
    have same : Pattern.fvar (Join.literalSlot index) = code := by simpa [Join.literal?,selected] using compiled
    subst code
    rw [GeneralFirstOrderProjection.apply_variable,read.literals index value (index_reads _ _ _ selected)]
    rfl

theorem argument_decodes_iff (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (position index : Nat) (argument : Argument) (code : Pattern)
    (compiled : Join.argument? pools position index argument = some code) (notAnonymous : argument ≠ .anonymous)
    (value : Value) :
    IRCodec.value? (applyBindings bindings code) = some value ↔ argument.Matches (assignment bindings) value := by
  cases argument with
  | literal expected =>
    rw [literal_instantiation pools bindings read expected code compiled,IRCodec.value_roundtrip]
    simp only [Argument.Matches,Option.some.injEq]
  | var name =>
    have same : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj compiled
    subst code
    rw [GeneralFirstOrderProjection.apply_variable]
    cases selected : bindings.lookup (Join.logicalVariable name) <;>
      simp [Argument.Matches,assignment,selected,IRCodec.value?]
  | anonymous => exact (notAnonymous rfl).elim

theorem argument_decoding_sound (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (position index : Nat) (argument : Argument) (code : Pattern)
    (compiled : Join.argument? pools position index argument = some code) (value : Value)
    (decoded : IRCodec.value? (applyBindings bindings code) = some value) :
    argument.Matches (assignment bindings) value := by
  by_cases anonymous : argument = .anonymous
  · subst argument
    trivial
  · exact (argument_decodes_iff pools bindings read position index argument code compiled anonymous value).mp decoded

private theorem traverse_sound {α β γ : Type} (compile : α → Option β) (decode : β → Option γ)
    (relation : α → γ → Prop)
    (sound : ∀ input code value, compile input = some code → decode code = some value → relation input value)
    (inputs : List α) (codes : List β) (values : List γ)
    (compiled : inputs.mapM compile = some codes) (decoded : codes.mapM decode = some values) :
    List.Forall₂ relation inputs values := by
  induction inputs generalizing codes values with
  | nil =>
    have empty : codes = [] := by simpa using compiled.symm
    subst codes
    have empty : values = [] := by simpa using decoded.symm
    subst values
    exact .nil
  | cons input rest ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons,first] at compiled
    | some code =>
      cases tail : rest.mapM compile with
      | none => simp [List.mapM_cons,first,tail] at compiled
      | some remaining =>
        have same : code :: remaining = codes := by simpa [List.mapM_cons,first,tail] using compiled
        subst codes
        cases valueAt : decode code with
        | none => simp [List.mapM_cons,valueAt] at decoded
        | some value =>
          cases later : remaining.mapM decode with
          | none => simp [List.mapM_cons,valueAt,later] at decoded
          | some result =>
            have same : value :: result = values := by simpa [List.mapM_cons,valueAt,later] using decoded
            subst values
            exact .cons (sound input code value first valueAt) (ih remaining result tail later)

theorem atom_decoding_sound (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) (fact : GroundFact)
    (decoded : IRCodec.groundFact? (applyBindings bindings code) = some fact) :
    source.Matches (assignment bindings) fact := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  have named := relation_instantiation pools bindings read source.relation name named
  simp only [applyBindings,List.map_cons,List.map_nil,named,Join.vector,List.append_nil,
    IRCodec.groundFact?,IRCodec.groundTuple?,IRCodec.vector?,IRCodec.relation_roundtrip] at decoded
  simp only [Option.bind_eq_bind,Option.bind_some] at decoded
  obtain ⟨values,valuesRead,same⟩ := Option.bind_eq_some_iff.mp decoded
  have final : GroundFact.mk source.relation values = fact := Option.some.inj same
  subst fact
  refine ⟨rfl,?_⟩
  have decodedArgs : arguments.mapM (fun code => IRCodec.value? (applyBindings bindings code)) = some values := by
    simpa only [List.mapM_map,Function.comp_def] using valuesRead
  have indexed := traverse_sound (fun entry : Argument × Nat => Join.argument? pools position entry.2 entry.1)
    (fun code => IRCodec.value? (applyBindings bindings code))
    (fun entry value => entry.1.Matches (assignment bindings) value)
    (fun entry code value compiled decoded => argument_decoding_sound pools bindings read position entry.2 entry.1 code compiled value decoded)
    source.arguments.zipIdx arguments values argsCompiled decodedArgs
  have unindexed : List.Forall₂ (Argument.Matches (assignment bindings)) (source.arguments.zipIdx.map Prod.fst) values :=
    List.forall₂_map_left_iff.mpr indexed
  simpa using unindexed

private theorem traverse_complete {α β γ : Type} (compile : α → Option β) (decode : β → Option γ)
    (relation : α → γ → Prop) (inputs : List α) (codes : List β) (values : List γ)
    (complete : ∀ input ∈ inputs, ∀ code value, compile input = some code → relation input value → decode code = some value)
    (compiled : inputs.mapM compile = some codes) (matched : List.Forall₂ relation inputs values) :
    codes.mapM decode = some values := by
  induction matched generalizing codes with
  | nil =>
    have empty : codes = [] := by simpa using compiled.symm
    subst codes
    rfl
  | @cons input value rest values firstMatch tailMatch ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons,first] at compiled
    | some code =>
      cases later : rest.mapM compile with
      | none => simp [List.mapM_cons,first,later] at compiled
      | some remaining =>
        have same : code :: remaining = codes := by simpa [List.mapM_cons,first,later] using compiled
        subst codes
        have head := complete input List.mem_cons_self code value first firstMatch
        have tail := ih remaining (fun other member => complete other (List.mem_cons_of_mem _ member)) later
        simp [List.mapM_cons,head,tail]

theorem atom_decoding_complete (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    (notAnonymous : ∀ argument ∈ source.arguments, argument ≠ .anonymous) (fact : GroundFact)
    (matched : source.Matches (assignment bindings) fact) :
    IRCodec.groundFact? (applyBindings bindings code) = some fact := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  have indexed : List.Forall₂ (fun entry : Argument × Nat => Argument.Matches (assignment bindings) entry.1)
      source.arguments.zipIdx fact.values := List.forall₂_map_left_iff.mp (by simpa using matched.2)
  have valuesRead := traverse_complete (fun entry : Argument × Nat => Join.argument? pools position entry.2 entry.1)
    (fun code => IRCodec.value? (applyBindings bindings code))
    (fun entry value => entry.1.Matches (assignment bindings) value)
    source.arguments.zipIdx arguments fact.values
    (fun entry member code value compiled matched =>
      (argument_decodes_iff pools bindings read position entry.2 entry.1 code compiled
        (notAnonymous entry.1 (List.fst_mem_of_mem_zipIdx member)) value).mpr matched)
    argsCompiled indexed
  have named := relation_instantiation pools bindings read source.relation name named
  simp only [applyBindings,List.map_cons,List.map_nil,named,Join.vector,List.append_nil,
    IRCodec.groundFact?,IRCodec.groundTuple?,IRCodec.vector?,IRCodec.relation_roundtrip,
    Option.bind_eq_bind,Option.bind_some]
  rw [List.mapM_map]
  change (arguments.mapM (fun code => IRCodec.value? (applyBindings bindings code))).bind
    (fun values => some (GroundFact.mk source.relation values)) = some fact
  rw [valuesRead]
  have same : GroundFact.mk source.relation fact.values = fact := by
    rcases fact with ⟨actual,values⟩
    have relation : source.relation = actual := matched.1
    cases relation
    rfl
  exact congrArg some same

theorem atom_decodes_iff (pools : Join.Pools) (bindings : Bindings) (read : PoolsRead pools bindings)
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    (notAnonymous : ∀ argument ∈ source.arguments, argument ≠ .anonymous) (fact : GroundFact) :
    IRCodec.groundFact? (applyBindings bindings code) = some fact ↔ source.Matches (assignment bindings) fact :=
  ⟨atom_decoding_sound pools bindings read position source code compiled fact,
   atom_decoding_complete pools bindings read position source code compiled notAnonymous fact⟩

private def examplePools : Join.Pools := ⟨[["Pair"]],[.number 1,.number 2]⟩
private def exampleBindings : Bindings :=
  [(Join.relationSlot 0,IRCodec.relation ["Pair"]),
   (Join.literalSlot 0,IRCodec.value (.number 1)),(Join.literalSlot 1,IRCodec.value (.number 2)),
   (Join.logicalVariable "X",IRCodec.value (.number 1))]
private def repeatedVariable : Mettapedia.Languages.Datalog.Atom := ⟨["Pair"],[.var "X",.var "X"]⟩
private def repeatedResult := (Join.atom? examplePools 0 repeatedVariable).bind fun code =>
  IRCodec.groundFact? (applyBindings exampleBindings code)

#guard repeatedResult == some ⟨["Pair"],[.number 1,.number 1]⟩
#guard repeatedResult != some ⟨["Pair"],[.number 1,.number 2]⟩
#guard Join.atom? ⟨[],[]⟩ 0 repeatedVariable == none

#print axioms relation_instantiation
#print axioms literal_instantiation
#print axioms argument_decodes_iff
#print axioms argument_decoding_sound
#print axioms atom_decoding_sound
#print axioms atom_decoding_complete
#print axioms atom_decodes_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseReading
