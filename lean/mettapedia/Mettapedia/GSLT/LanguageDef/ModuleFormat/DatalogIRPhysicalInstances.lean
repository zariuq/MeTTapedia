import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRInstanceMatching

/-! Source matches reconstruct the physical fact representation used by the
native provider. Anonymous slots are local to the actual body occurrence. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalInstances

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec
open GeneralFirstOrderProjection

def value? (pools : Join.Pools) (value : Value) : Option Pattern :=
  Executable.valueRef <$> pools.literals.idxOf? value

structure PoolBindings (pools : Join.Pools) (bindings : Bindings) : Prop where
  relations : ∀ index, index < pools.relations.length →
    bindings.lookup (Join.relationSlot index) = some (Executable.relationRef index)
  literals : ∀ index, index < pools.literals.length →
    bindings.lookup (Join.literalSlot index) = some (Executable.valueRef index)

def VariablesRead (pools : Join.Pools) (bindings : Bindings) (model : Assignment) : Prop :=
  ∀ name value, model name = some value →
    ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.logicalVariable name) = some encoded

theorem relation_instance (pools : Join.Pools) (bindings : Bindings) (read : PoolBindings pools bindings)
    (name : QualifiedName) (code : Pattern) (compiled : Join.relation? pools name = some code) :
    ∃ encoded, (pools.relations.idxOf? name).map Executable.relationRef = some encoded ∧
      applyBindings bindings code = encoded := by
  cases selected : pools.relations.idxOf? name with
  | none => simp [Join.relation?,selected] at compiled
  | some index =>
    have bound := (List.idxOf?_eq_some_iff.mp selected).1
    have same : Pattern.fvar (Join.relationSlot index) = code := by simpa [Join.relation?,selected] using compiled
    subst code
    exact ⟨Executable.relationRef index,rfl,by rw [apply_variable,read.relations index bound]; rfl⟩

theorem argument_lookup (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model)
    (position index : Nat) (argument : Argument) (code : Pattern) (value : Value)
    (compiled : Join.argument? pools position index argument = some code)
    (matched : argument.Matches model value)
    (anonymous : argument = .anonymous → ∃ encoded, value? pools value = some encoded ∧
      bindings.lookup (Join.anonymousVariable position index) = some encoded) :
    ∃ name encoded, code = .fvar name ∧ value? pools value = some encoded ∧ bindings.lookup name = some encoded := by
  cases argument with
  | literal expected =>
    have sameValue : expected = value := matched
    subst expected
    cases selected : pools.literals.idxOf? value with
    | none => simp [Join.argument?,Join.literal?,selected] at compiled
    | some index =>
      have bound := (List.idxOf?_eq_some_iff.mp selected).1
      have same : Pattern.fvar (Join.literalSlot index) = code := by simpa [Join.argument?,Join.literal?,selected] using compiled
      subst code
      exact ⟨Join.literalSlot index,Executable.valueRef index,rfl,by simp [value?,selected],poolRead.literals index bound⟩
  | var name =>
    obtain ⟨encoded,formed,found⟩ := read name value matched
    have same : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj compiled
    subst code
    exact ⟨_,encoded,rfl,formed,found⟩
  | anonymous =>
    obtain ⟨encoded,formed,found⟩ := anonymous rfl
    have same : Pattern.fvar (Join.anonymousVariable position index) = code := Option.some.inj compiled
    subst code
    exact ⟨_,encoded,rfl,formed,found⟩

theorem argument_instance (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model)
    (position index : Nat) (argument : Argument) (code : Pattern) (value : Value)
    (compiled : Join.argument? pools position index argument = some code)
    (matched : argument.Matches model value)
    (anonymous : argument = .anonymous → ∃ encoded, value? pools value = some encoded ∧
      bindings.lookup (Join.anonymousVariable position index) = some encoded) :
    ∃ encoded, value? pools value = some encoded ∧ applyBindings bindings code = encoded := by
  obtain ⟨name,encoded,rfl,formed,found⟩ := argument_lookup pools bindings poolRead model read
    position index argument code value compiled matched anonymous
  exact ⟨encoded,formed,by rw [apply_variable,found]; rfl⟩

private theorem arguments_instance (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model) (position : Nat)
    (entries : List (Argument × Nat)) (values : List Value) (codes : List Pattern)
    (compiled : entries.mapM (fun entry => Join.argument? pools position entry.2 entry.1) = some codes)
    (matched : List.Forall₂ (fun entry value => entry.1.Matches model value) entries values)
    (anonymous : List.Forall₂ (fun entry value => entry.1 = .anonymous →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position entry.2) = some encoded) entries values) :
    values.mapM (value? pools) = some (codes.map (applyBindings bindings)) := by
  induction matched generalizing codes with
  | nil =>
    have empty : codes = [] := by simpa using compiled.symm
    subst codes
    rfl
  | @cons entry value entries values first rest ih =>
    cases anonymous with
    | cons anonymousHead anonymousTail =>
      cases head : Join.argument? pools position entry.2 entry.1 with
      | none => simp [List.mapM_cons,head] at compiled
      | some code =>
        cases tail : entries.mapM (fun entry => Join.argument? pools position entry.2 entry.1) with
        | none => simp [List.mapM_cons,head,tail] at compiled
        | some remaining =>
          have same : code :: remaining = codes := by simpa [List.mapM_cons,head,tail] using compiled
          subst codes
          obtain ⟨encoded,formed,reconstructed⟩ := argument_instance pools bindings poolRead model read position entry.2 entry.1 code value
            head first anonymousHead
          have later := ih remaining tail anonymousTail
          simp [List.mapM_cons,formed,reconstructed,later]

theorem arguments_defined (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model) (position : Nat)
    (entries : List (Argument × Nat)) (values : List Value) (codes : List Pattern)
    (compiled : entries.mapM (fun entry => Join.argument? pools position entry.2 entry.1) = some codes)
    (matched : List.Forall₂ (fun entry value => entry.1.Matches model value) entries values)
    (anonymous : List.Forall₂ (fun entry value => entry.1 = .anonymous →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position entry.2) = some encoded) entries values) :
    Defined bindings (codes.flatMap Pattern.freeFvarNames) := by
  induction matched generalizing codes with
  | nil =>
    have empty : codes = [] := by simpa using compiled.symm
    subst codes
    intro name member
    cases member
  | @cons entry value entries values first rest ih =>
    cases anonymous with
    | cons anonymousHead anonymousTail =>
      cases head : Join.argument? pools position entry.2 entry.1 with
      | none => simp [List.mapM_cons,head] at compiled
      | some code =>
        cases tail : entries.mapM (fun entry => Join.argument? pools position entry.2 entry.1) with
        | none => simp [List.mapM_cons,head,tail] at compiled
        | some remaining =>
          have same : code :: remaining = codes := by simpa [List.mapM_cons,head,tail] using compiled
          subst codes
          obtain ⟨slot,encoded,rfl,_,lookup⟩ := argument_lookup pools bindings poolRead model read position entry.2 entry.1 code value head first anonymousHead
          have later := ih remaining tail anonymousTail
          intro name member
          rcases List.mem_append.mp member with first | rest
          · have same : name = slot := by simpa [Pattern.freeFvarNames] using first
            subst name
            exact ⟨encoded,lookup⟩
          · exact later name rest

theorem atom_instance (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) (matched : source.Matches model fact)
    (anonymous : ∀ index value, source.arguments[index]? = some .anonymous → fact.values[index]? = some value →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position index) = some encoded) :
    Executable.fact? pools fact = some (applyBindings bindings code) := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,codes,arguments,rfl⟩ := compiled
  obtain ⟨relation,relationEncoded,relationRead⟩ := relation_instance pools bindings poolRead source.relation name named
  have indexed : List.Forall₂ (fun (entry : Argument × Nat) (value : Value) => entry.1.Matches model value) source.arguments.zipIdx fact.values :=
    List.forall₂_map_left_iff.mp (by simpa using matched.2)
  have anonymousPairs : List.Forall₂ (fun entry value => entry.1 = .anonymous →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position entry.2) = some encoded)
      source.arguments.zipIdx fact.values := by
    apply List.forall₂_iff_get.mpr
    refine ⟨indexed.length_eq,?_⟩
    intro index leftBound rightBound isAnonymous
    simp only [List.get_eq_getElem,List.getElem_zipIdx,Nat.zero_add] at isAnonymous ⊢
    have atSource : source.arguments[index]? = some .anonymous := by
      rw [List.getElem?_eq_getElem (by simpa using leftBound),isAnonymous]
    exact anonymous index fact.values[index] atSource (List.getElem?_eq_getElem rightBound)
  have values := arguments_instance pools bindings poolRead model read position source.arguments.zipIdx fact.values codes arguments indexed anonymousPairs
  change ((pools.relations.idxOf? fact.relation).bind fun index =>
    (fact.values.mapM (value? pools)).bind fun values =>
      some (Pattern.apply "GroundFact" [Executable.relationRef index,.apply "GroundTuple" [Join.vector values]])) = _
  rw [← matched.1]
  obtain ⟨index,selected,same⟩ := Option.map_eq_some_iff.mp relationEncoded
  subst relation
  rw [selected,Option.bind_some,values,Option.bind_some]
  simp only [applyBindings,List.map_cons,List.map_nil,Join.vector,List.append_nil]
  rw [← same]

theorem atom_defined (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) (matched : source.Matches model fact)
    (anonymous : ∀ index value, source.arguments[index]? = some .anonymous → fact.values[index]? = some value →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position index) = some encoded) :
    Defined bindings code.freeFvarNames := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,codes,arguments,rfl⟩ := compiled
  have relationDefined : Defined bindings name.freeFvarNames := by
    cases selected : pools.relations.idxOf? source.relation with
    | none => simp [Join.relation?,selected] at named
    | some index =>
      have same : Pattern.fvar (Join.relationSlot index) = name := by simpa [Join.relation?,selected] using named
      subst name
      intro queried member
      have same : queried = Join.relationSlot index := by simpa only [Pattern.freeFvarNames,List.mem_singleton] using member
      subst queried
      exact ⟨Executable.relationRef index,poolRead.relations index (List.idxOf?_eq_some_iff.mp selected).1⟩
  have indexed : List.Forall₂ (fun (entry : Argument × Nat) (value : Value) => entry.1.Matches model value) source.arguments.zipIdx fact.values :=
    List.forall₂_map_left_iff.mp (by simpa using matched.2)
  have anonymousPairs : List.Forall₂ (fun entry value => entry.1 = .anonymous →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position entry.2) = some encoded)
      source.arguments.zipIdx fact.values := by
    apply List.forall₂_iff_get.mpr
    refine ⟨indexed.length_eq,?_⟩
    intro index leftBound rightBound isAnonymous
    simp only [List.get_eq_getElem,List.getElem_zipIdx,Nat.zero_add] at isAnonymous ⊢
    have atSource : source.arguments[index]? = some .anonymous := by
      rw [List.getElem?_eq_getElem (by simpa using leftBound),isAnonymous]
    exact anonymous index fact.values[index] atSource (List.getElem?_eq_getElem rightBound)
  have argumentDefined := arguments_defined pools bindings poolRead model read position _ _ codes arguments indexed anonymousPairs
  intro queried member
  have places : queried ∈ name.freeFvarNames ∨ queried ∈ codes.flatMap Pattern.freeFvarNames := by
    simpa only [Pattern.freeFvarNames,List.flatMap_cons,List.flatMap_nil,Join.vector,
      Option.toList_none,List.append_nil,List.nil_append,List.mem_append] using member
  rcases places with left | right
  · exact relationDefined queried left
  · exact argumentDefined queried right

theorem atom_scoped_witness (pools : Join.Pools) (bindings : Bindings) (poolRead : PoolBindings pools bindings)
    (model : Assignment) (read : VariablesRead pools bindings model) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact) (code : Pattern)
    (compiled : Join.atom? pools position source = some code) (matched : source.Matches model fact)
    (anonymous : ∀ index value, source.arguments[index]? = some .anonymous → fact.values[index]? = some value →
      ∃ encoded, value? pools value = some encoded ∧ bindings.lookup (Join.anonymousVariable position index) = some encoded) :
    ∀ (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat),
      RuleBinding.admittedFor rule spec = true → NameCoherent rule site path code →
      (∀ name ∈ code.freeFvarNames, RuleBinding.dependencies? spec name = some []) →
      ∀ encoded, Executable.fact? pools fact = some encoded →
      encoded.isWellScopedAt ambient = true → Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern encoded = true →
      ∀ initial, ScopedCompatible ambient bindings initial →
        ∃ final, GeneralScopedMatch.Matches rule spec ambient site path 0 initial code encoded final ∧
          ScopedCompatible ambient bindings final := by
  intro rule spec ambient site path admitted coherent declared encoded encodedFact scope object initial before
  have defined := atom_defined pools bindings poolRead model read position source fact code compiled matched anonymous
  obtain ⟨raw,rawMatched,compatible,_,_⟩ := InstanceMatching.atom_instance pools position source code compiled bindings defined
  have same : applyBindings bindings code = encoded := Option.some.inj
    ((atom_instance pools bindings poolRead model read position source fact code compiled matched anonymous).symm.trans encodedFact)
  rw [same] at rawMatched
  exact GeneralFirstOrderProjection.binderFree_scoped_of_matchRel_admitted admitted
    (ClauseDictionary.atom_binderFree pools position source code compiled) coherent declared rawMatched compatible scope object before

#print axioms relation_instance
#print axioms argument_lookup
#print axioms argument_instance
#print axioms arguments_defined
#print axioms atom_instance
#print axioms atom_defined
#print axioms atom_scoped_witness

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PhysicalInstances
