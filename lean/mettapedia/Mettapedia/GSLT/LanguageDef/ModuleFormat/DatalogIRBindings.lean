import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRNames
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPhysicalInstances

/-! Finite physical substitutions for a clause instance. The domain consists
of pool slots, source variables and the actual anonymous argument positions. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Bindings

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)

def materialize (domain : List Names.Role) (values : Names.Role → Option Pattern) : Bindings :=
  domain.filterMap fun role => (values role).map fun value => (Names.encode role,value)

theorem materialize_lookup (domain : List Names.Role) (values : Names.Role → Option Pattern)
    (role : Names.Role) (value : Pattern) (present : role ∈ domain) (defined : values role = some value) :
    (materialize domain values).lookup (Names.encode role) = some value := by
  have member : (Names.encode role,value) ∈ materialize domain values :=
    List.mem_filterMap.mpr ⟨role,present,by simp [defined]⟩
  cases found : (materialize domain values).find? (fun entry => entry.1 == Names.encode role) with
  | none =>
    have rejected := List.find?_eq_none.mp found (Names.encode role,value) member
    simp at rejected
  | some entry =>
    obtain ⟨actual,_,formed⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some found)
    obtain ⟨actualValue,actualDefined,same⟩ := Option.map_eq_some_iff.mp formed
    subst entry
    have key : Names.encode actual = Names.encode role := by simpa using List.find?_some found
    have actualSame := Names.encode_injective key
    subst actual
    have valueSame := Option.some.inj (actualDefined.symm.trans defined)
    subst actualValue
    simp [Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup,found]

def domain (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment)
    (chosen : List GroundFact) : List Names.Role :=
  (List.range pools.relations.length).map Names.Role.relation ++
  (List.range pools.literals.length).map Names.Role.literal ++
  (environment.map Prod.fst).map Names.Role.logical ++
  chosen.zipIdx.flatMap fun (fact,position) =>
    (List.range fact.values.length).map fun index => Names.Role.anonymous position index

def values (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment)
    (chosen : List GroundFact) : Names.Role → Option Pattern
  | .relation index => some (Executable.relationRef index)
  | .literal index => some (Executable.valueRef index)
  | .logical name => (environment.lookup name).bind (PhysicalInstances.value? pools)
  | .anonymous position index => do
      let fact ← chosen[position]?
      let value ← fact.values[index]?
      PhysicalInstances.value? pools value

def ofInstance (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment)
    (chosen : List GroundFact) : Bindings := materialize (domain pools environment chosen) (values pools environment chosen)

theorem pools_read (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment) (chosen : List GroundFact) :
    PhysicalInstances.PoolBindings pools (ofInstance pools environment chosen) := by
  constructor
  · intro index inside
    exact materialize_lookup _ _ (.relation index) _ (by simp [domain,inside]) rfl
  · intro index inside
    exact materialize_lookup _ _ (.literal index) _ (by simp [domain,inside]) rfl

private theorem lookup_member {environment : Mettapedia.Languages.Datalog.Join.Environment} {name : String} {value : Value}
    (found : environment.lookup name = some value) : (name,value) ∈ environment := by
  induction environment with
  | nil => simp at found
  | cons entry rest ih =>
    rcases entry with ⟨key,actual⟩
    by_cases same : name = key
    · subst key
      have sameValue : actual = value := Option.some.inj (by simpa [List.lookup] using found)
      subst actual
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa only [List.lookup,show (name == key) = false from beq_eq_false_iff_ne.mpr same] using found))

theorem variables_read (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment) (chosen : List GroundFact)
    (available : ∀ pair ∈ environment, pair.2 ∈ pools.literals) :
    PhysicalInstances.VariablesRead pools (ofInstance pools environment chosen) (Mettapedia.Languages.Datalog.Join.assignment environment) := by
  intro name value found
  have present := lookup_member found
  obtain ⟨index,selected⟩ := Option.isSome_iff_exists.mp ((List.isSome_idxOf?).mpr (available (name,value) present))
  have encoded : PhysicalInstances.value? pools value = some (Executable.valueRef index) := by simp [PhysicalInstances.value?,selected]
  refine ⟨Executable.valueRef index,encoded,?_⟩
  apply materialize_lookup _ _ (.logical name)
  · simp only [domain,List.mem_append,List.mem_map]
    exact Or.inl (Or.inr ⟨name,⟨(name,value),present,rfl⟩,rfl⟩)
  · simp only [values,show environment.lookup name = some value from found,Option.bind_some,encoded]

theorem anonymous_read (pools : Join.Pools) (environment : Mettapedia.Languages.Datalog.Join.Environment)
    (chosen : List GroundFact) (position index : Nat) (fact : GroundFact) (value : Value)
    (atFact : chosen[position]? = some fact) (atValue : fact.values[index]? = some value)
    (available : value ∈ pools.literals) :
    ∃ encoded, PhysicalInstances.value? pools value = some encoded ∧
      (ofInstance pools environment chosen).lookup (Join.anonymousVariable position index) = some encoded := by
  obtain ⟨slot,selected⟩ := Option.isSome_iff_exists.mp ((List.isSome_idxOf?).mpr available)
  have encoded : PhysicalInstances.value? pools value = some (Executable.valueRef slot) := by simp [PhysicalInstances.value?,selected]
  refine ⟨Executable.valueRef slot,encoded,?_⟩
  apply materialize_lookup _ _ (.anonymous position index)
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨(fact,position),List.mk_mem_zipIdx_iff_getElem?.mpr atFact,
      List.mem_map.mpr ⟨index,List.mem_range.mpr (List.getElem?_eq_some_iff.mp atValue).1,rfl⟩⟩
  · simp [values,atFact,atValue,encoded]

#print axioms materialize_lookup
#print axioms pools_read
#print axioms variables_read
#print axioms anonymous_read

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Bindings
