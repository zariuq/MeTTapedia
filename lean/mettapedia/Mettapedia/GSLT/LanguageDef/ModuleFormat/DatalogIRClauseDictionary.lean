import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReferenceCodec

/-! The executable reference dictionary commutes with compiled atom
instantiation. This connects source atom readings to actual native carrier
references, without interpreting a source syntax tree at runtime. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseDictionary

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match

def expand (pools : Join.Pools) (bindings : Bindings) : Bindings :=
  bindings.map fun entry => (entry.1,applyBindings (Executable.dictionary pools) entry.2)

theorem expand_lookup (pools : Join.Pools) (bindings : Bindings) (name : String) :
    (expand pools bindings).lookup name =
      (bindings.lookup name).map (applyBindings (Executable.dictionary pools)) := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key,value⟩
    by_cases same : key == name
    · simp [expand,Bindings.lookup,same]
    · simpa [expand,Bindings.lookup,same] using ih

private theorem dictionary_key (pools : Join.Pools) (entry : String × Pattern)
    (present : entry ∈ Executable.dictionary pools) : entry.1.toList.head? = some 'd' := by
  rcases List.mem_append.mp present with relation | literal
  · obtain ⟨⟨name,index⟩,_,same⟩ := List.mem_map.mp relation
    subst entry
    simp only [String.toList_append]
    rfl
  · obtain ⟨⟨value,index⟩,_,same⟩ := List.mem_map.mp literal
    subst entry
    simp only [String.toList_append]
    rfl

theorem fresh_lookup (pools : Join.Pools) (name : String) (fresh : name.toList.head? ≠ some 'd') :
    (Executable.dictionary pools).lookup name = none := by
  have absent : (Executable.dictionary pools).find? (fun entry => entry.1 == name) = none := by
    apply List.find?_eq_none.mpr
    intro entry present accepted
    have same : entry.1 = name := beq_iff_eq.mp accepted
    exact fresh (same ▸ dictionary_key pools entry present)
  simp [Bindings.lookup,absent]

theorem relation_slot_fresh (pools : Join.Pools) (index : Nat) :
    (Executable.dictionary pools).lookup (Join.relationSlot index) = none :=
  fresh_lookup pools _ (by simp [Join.relationSlot,String.toList_append])

theorem literal_slot_fresh (pools : Join.Pools) (index : Nat) :
    (Executable.dictionary pools).lookup (Join.literalSlot index) = none :=
  fresh_lookup pools _ (by simp [Join.literalSlot,String.toList_append])

theorem logical_variable_fresh (pools : Join.Pools) (name : String) :
    (Executable.dictionary pools).lookup (Join.logicalVariable name) = none :=
  fresh_lookup pools _ (by simp [Join.logicalVariable,String.toList_append])

theorem anonymous_variable_fresh (pools : Join.Pools) (position index : Nat) :
    (Executable.dictionary pools).lookup (Join.anonymousVariable position index) = none :=
  fresh_lookup pools _ (by simp [Join.anonymousVariable,String.toList_append])

theorem variable_expands (pools : Join.Pools) (bindings : Bindings) (name : String)
    (fresh : (Executable.dictionary pools).lookup name = none) :
    applyBindings (expand pools bindings) (.fvar name) =
      applyBindings (Executable.dictionary pools) (applyBindings bindings (.fvar name)) := by
  rw [GeneralFirstOrderProjection.apply_variable,expand_lookup]
  cases selected : bindings.lookup name with
  | none => simp [selected,GeneralFirstOrderProjection.apply_variable,fresh]
  | some value => simp [selected,GeneralFirstOrderProjection.apply_variable]

theorem relation_expands (pools : Join.Pools) (bindings : Bindings) (name : QualifiedName) (code : Pattern)
    (compiled : Join.relation? pools name = some code) :
    applyBindings (expand pools bindings) code =
      applyBindings (Executable.dictionary pools) (applyBindings bindings code) := by
  cases selected : pools.relations.idxOf? name with
  | none => simp [Join.relation?,selected] at compiled
  | some index =>
    have same : Pattern.fvar (Join.relationSlot index) = code := by simpa [Join.relation?,selected] using compiled
    subst code
    exact variable_expands pools bindings _ (relation_slot_fresh pools index)

theorem argument_expands (pools : Join.Pools) (bindings : Bindings) (position index : Nat)
    (argument : Argument) (code : Pattern) (compiled : Join.argument? pools position index argument = some code) :
    applyBindings (expand pools bindings) code =
      applyBindings (Executable.dictionary pools) (applyBindings bindings code) := by
  cases argument with
  | literal value =>
    cases selected : pools.literals.idxOf? value with
    | none => simp [Join.argument?,Join.literal?,selected] at compiled
    | some index =>
      have same : Pattern.fvar (Join.literalSlot index) = code := by simpa [Join.argument?,Join.literal?,selected] using compiled
      subst code
      exact variable_expands pools bindings _ (literal_slot_fresh pools index)
  | var name =>
    have same : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj compiled
    subst code
    exact variable_expands pools bindings _ (logical_variable_fresh pools name)
  | anonymous =>
    have same : Pattern.fvar (Join.anonymousVariable position index) = code := Option.some.inj compiled
    subst code
    exact variable_expands pools bindings _ (anonymous_variable_fresh pools position index)

theorem pools_read (pools : Join.Pools) (bindings : Bindings)
    (relations : ∀ index name, pools.relations[index]? = some name →
      bindings.lookup (Join.relationSlot index) = some (Executable.relationRef index))
    (literals : ∀ index value, pools.literals[index]? = some value →
      bindings.lookup (Join.literalSlot index) = some (Executable.valueRef index)) :
    ClauseReading.PoolsRead pools (expand pools bindings) := by
  constructor
  · intro index name present
    rw [expand_lookup,relations index name present]
    exact congrArg some (Executable.relation_dictionary_expands pools index name present)
  · intro index value present
    rw [expand_lookup,literals index value present]
    exact congrArg some (Executable.value_dictionary_expands pools index value present)

private theorem mapM_member {α β : Type} (compile : α → Option β) (inputs : List α) (codes : List β)
    (compiled : inputs.mapM compile = some codes) (code : β) (present : code ∈ codes) :
    ∃ input ∈ inputs, compile input = some code := by
  induction inputs generalizing codes with
  | nil =>
    have empty : codes = [] := by simpa using compiled.symm
    subst codes
    cases present
  | cons input rest ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons,first] at compiled
    | some firstCode =>
      cases later : rest.mapM compile with
      | none => simp [List.mapM_cons,first,later] at compiled
      | some remaining =>
        have same : firstCode :: remaining = codes := by simpa [List.mapM_cons,first,later] using compiled
        subst codes
        rcases List.mem_cons.mp present with rfl | after
        · exact ⟨input,List.mem_cons_self,first⟩
        · obtain ⟨other,member,selected⟩ := ih remaining later after
          exact ⟨other,List.mem_cons_of_mem _ member,selected⟩

theorem relation_variable (pools : Join.Pools) (name : QualifiedName) (code : Pattern)
    (compiled : Join.relation? pools name = some code) : ∃ slotName, code = .fvar slotName := by
  cases selected : pools.relations.idxOf? name with
  | none => simp [Join.relation?,selected] at compiled
  | some index =>
    refine ⟨Join.relationSlot index,?_⟩
    symm
    simpa [Join.relation?,selected] using compiled

theorem argument_variable (pools : Join.Pools) (position index : Nat) (argument : Argument)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code) :
    ∃ slotName, code = .fvar slotName := by
  cases argument with
  | literal value =>
    cases selected : pools.literals.idxOf? value with
    | none => simp [Join.argument?,Join.literal?,selected] at compiled
    | some index =>
      refine ⟨Join.literalSlot index,?_⟩
      symm
      simpa [Join.argument?,Join.literal?,selected] using compiled
  | var name => exact ⟨Join.logicalVariable name,(Option.some.inj compiled).symm⟩
  | anonymous => exact ⟨Join.anonymousVariable position index,(Option.some.inj compiled).symm⟩

theorem compiled_arguments_are_variables (pools : Join.Pools) (position : Nat) (arguments : List Argument)
    (codes : List Pattern)
    (compiled : arguments.zipIdx.mapM (fun entry => Join.argument? pools position entry.2 entry.1) = some codes) :
    ∀ code ∈ codes, ∃ slotName, code = .fvar slotName := by
  intro code present
  obtain ⟨entry,_,selected⟩ := mapM_member _ _ _ compiled code present
  exact argument_variable pools position entry.2 entry.1 code selected

private theorem argument_binderFree (pools : Join.Pools) (position index : Nat) (argument : Argument)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code) : binderFree code = true := by
  obtain ⟨name,rfl⟩ := argument_variable pools position index argument code compiled
  rfl

private theorem binderFreeList_of_all (patterns : List Pattern)
    (free : ∀ pattern ∈ patterns, binderFree pattern = true) : binderFreeList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih =>
    exact Bool.and_eq_true_iff.mpr ⟨free pattern List.mem_cons_self,
      ih (fun other member => free other (List.mem_cons_of_mem _ member))⟩

theorem atom_binderFree (pools : Join.Pools) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) : binderFree code = true := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  have nameFree : binderFree name = true := by
    cases selected : pools.relations.idxOf? source.relation with
    | none => simp [Join.relation?,selected] at named
    | some index =>
      have same : Pattern.fvar (Join.relationSlot index) = name := by simpa [Join.relation?,selected] using named
      subst name
      rfl
  have argumentsFree : binderFreeList arguments = true := by
    apply binderFreeList_of_all
    intro code present
    obtain ⟨entry,_,compiled⟩ := mapM_member _ _ _ argsCompiled code present
    exact argument_binderFree pools position entry.2 entry.1 code compiled
  simp only [binderFree,binderFreeList,Join.vector,nameFree,argumentsFree,Bool.and_true]

theorem atom_expands (pools : Join.Pools) (bindings : Bindings) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) :
    applyBindings (expand pools bindings) code =
      applyBindings (Executable.dictionary pools) (applyBindings bindings code) := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  have nameRead := relation_expands pools bindings source.relation name named
  have valuesRead : arguments.map (applyBindings (expand pools bindings)) =
      arguments.map (fun code => applyBindings (Executable.dictionary pools) (applyBindings bindings code)) := by
    apply List.map_congr_left
    intro code present
    obtain ⟨entry,_,selected⟩ := mapM_member _ _ _ argsCompiled code present
    exact argument_expands pools bindings position entry.2 entry.1 code selected
  simp only [applyBindings,List.map_cons,List.map_nil,Join.vector,List.append_nil,List.map_map,
    Function.comp_def,nameRead,valuesRead]

theorem source_atom_sound (pools : Join.Pools) (bindings : Bindings)
    (relations : ∀ index name, pools.relations[index]? = some name →
      bindings.lookup (Join.relationSlot index) = some (Executable.relationRef index))
    (literals : ∀ index value, pools.literals[index]? = some value →
      bindings.lookup (Join.literalSlot index) = some (Executable.valueRef index))
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) (fact : GroundFact)
    (decoded : IRCodec.groundFact? (applyBindings (Executable.dictionary pools) (applyBindings bindings code)) = some fact) :
    source.Matches (ClauseReading.assignment (expand pools bindings)) fact := by
  rw [← atom_expands pools bindings position source code compiled] at decoded
  exact ClauseReading.atom_decoding_sound pools _ (pools_read pools bindings relations literals) position source code compiled fact decoded

theorem source_atom_iff (pools : Join.Pools) (bindings : Bindings)
    (relations : ∀ index name, pools.relations[index]? = some name →
      bindings.lookup (Join.relationSlot index) = some (Executable.relationRef index))
    (literals : ∀ index value, pools.literals[index]? = some value →
      bindings.lookup (Join.literalSlot index) = some (Executable.valueRef index))
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    (notAnonymous : ∀ argument ∈ source.arguments, argument ≠ .anonymous) (fact : GroundFact) :
    IRCodec.groundFact? (applyBindings (Executable.dictionary pools) (applyBindings bindings code)) = some fact ↔
      source.Matches (ClauseReading.assignment (expand pools bindings)) fact := by
  rw [← atom_expands pools bindings position source code compiled]
  exact ClauseReading.atom_decodes_iff pools _ (pools_read pools bindings relations literals) position source code compiled notAnonymous fact

#print axioms expand_lookup
#print axioms fresh_lookup
#print axioms variable_expands
#print axioms argument_expands
#print axioms pools_read
#print axioms atom_binderFree
#print axioms atom_expands
#print axioms source_atom_sound
#print axioms source_atom_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClauseDictionary
