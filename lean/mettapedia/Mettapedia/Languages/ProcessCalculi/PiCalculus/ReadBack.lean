import Mettapedia.Languages.ProcessCalculi.PiCalculus.NamedStaticAdequacy
import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceKeys
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSteps

/-!
# Reading π's patterns back as named processes

A pattern of `piCalc` is **named** when its channels and data are variables and no variable stands as a process
(`Named`): the patterns the named calculus translates to, up to the bag's nesting. Such a pattern has a **normal
form** (`normal`): its bags nested as the translation nests parallel composition, its binders without display names.

A named pattern **reads back** as a named process (`readBack`), its bound variables given fresh names. The read-back's
translation is the normal form, opened at the names of the variables free in it (`piToPattern_readBack`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock piBlockSignature)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars closeFVar freeVars)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piToPattern piPar piComponents
  piPar_components)
open Mettapedia.FreshString (fresh fresh_not_mem)

/-! ## Named patterns and their normal form -/

/-- A variable: what a name position of a named pattern holds. -/
def isName : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | _ => false

mutual
  /-- **A named pattern**: inaction, a bag, a restriction, an input, a replicated input or an output, with variables at
  every name position and no variable as a process. -/
  def Named : Pattern → Bool
    | .apply "PiNil" [] => true
    | .collection .hashBag elements none => NamedList elements
    | .apply "PiNu" [.lambda _ body] => Named body
    | .apply "PiInp" [channel, .lambda _ body] => isName channel && Named body
    | .apply "PiRep" [.apply "PiInp" [channel, .lambda _ body]] => isName channel && Named body
    | .apply "PiOut" [channel, datum] => isName channel && isName datum
    | _ => false

  def NamedList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => Named pattern && NamedList patterns
end

/-- Parallel composition of a list, nested as the translation nests it. -/
def piParList : List Pattern → Pattern
  | [] => .apply "PiNil" []
  | first :: rest => piPar first (piParList rest)

mutual
  /-- **The normal form**: bags nested as the translation nests parallel composition, binders without display
  names. -/
  def normal : Pattern → Pattern
    | .apply "PiNil" [] => .apply "PiNil" []
    | .collection .hashBag elements none => piParList (normalList elements)
    | .apply "PiNu" [.lambda _ body] => .apply "PiNu" [.lambda none (normal body)]
    | .apply "PiInp" [channel, .lambda _ body] => .apply "PiInp" [channel, .lambda none (normal body)]
    | .apply "PiRep" [.apply "PiInp" [channel, .lambda _ body]] =>
        .apply "PiRep" [.apply "PiInp" [channel, .lambda none (normal body)]]
    | .apply "PiOut" [channel, datum] => .apply "PiOut" [channel, datum]
    | _ => .apply "PiNil" []

  def normalList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => normal pattern :: normalList patterns
end

theorem normalList_eq_map : ∀ patterns : List Pattern, normalList patterns = patterns.map normal
  | [] => rfl
  | pattern :: patterns => by simp [normalList, normalList_eq_map patterns]

theorem namedList_iff : ∀ {patterns : List Pattern}, NamedList patterns = true ↔ ∀ pattern ∈ patterns, Named pattern = true
  | [] => by simp [NamedList]
  | pattern :: patterns => by simp [NamedList, namedList_iff]

/-- The translation of a parallel composition of a list nests the bag the same way. -/
theorem piToPattern_parList : ∀ processes : List Process,
    piToPattern (parList processes) = piParList (processes.map piToPattern)
  | [] => rfl
  | process :: processes => by
      simp [parList, piParList, piToPattern, piToPattern_parList processes]

/-! ## Opening the free variables at names -/

/-- The variables free at the root, named by a list, the others moved down past it. -/
def envAssignment (env : List Name) : Assignment := fun index =>
  if inside : index < env.length then .fvar env[index] else .bvar (index - env.length)

/-- **Open the variables free at the root at names.** -/
def openWith (env : List Name) (pattern : Pattern) : Pattern := substitute (envAssignment env) pattern

/-- The name of a variable at a name position. -/
def nameOf (env : List Name) : Pattern → Name
  | .fvar name => name
  | .bvar index => env.getD index ""
  | _ => ""

/-- **Read a named pattern back** as a named process, the bound variables given names fresh for `avoid` and for the
names already given. -/
def readBack (avoid : Finset Name) : List Name → Pattern → Process
  | _, .apply "PiNil" [] => .nil
  | env, .collection .hashBag elements none => parList (elements.attach.map fun ⟨element, _⟩ => readBack avoid env element)
  | env, .apply "PiNu" [.lambda _ body] =>
      .nu (fresh (avoid ∪ env.toFinset)) (readBack avoid (fresh (avoid ∪ env.toFinset) :: env) body)
  | env, .apply "PiInp" [channel, .lambda _ body] =>
      .input (nameOf env channel) (fresh (avoid ∪ env.toFinset))
        (readBack avoid (fresh (avoid ∪ env.toFinset) :: env) body)
  | env, .apply "PiRep" [.apply "PiInp" [channel, .lambda _ body]] =>
      .replicate (nameOf env channel) (fresh (avoid ∪ env.toFinset))
        (readBack avoid (fresh (avoid ∪ env.toFinset) :: env) body)
  | env, .apply "PiOut" [channel, datum] => .output (nameOf env channel) (nameOf env datum)
  | _, _ => .nil
termination_by _ pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)


/-! ## Opening and closing -/

/-- **Closing a fresh name after opening it** is opening the rest one level deeper. -/
theorem closeFVar_open {name : String} {env : List Name} (absentEnv : name ∉ env) (pattern : Pattern) :
    ∀ level, name ∉ freeVars pattern → pattern.isWellScopedAt (level + env.length + 1) = true →
      closeFVar level name (substitute (lift level (envAssignment (name :: env))) pattern) =
        substitute (lift (level + 1) (envAssignment env)) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level _ wellScoped
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at wellScoped
      simp only [substitute, lift]
      by_cases below : index < level
      · have below' : index < level + 1 := by omega
        simp [below, below', closeFVar]
      · by_cases atLevel : index = level
        · subst atLevel
          simp [envAssignment, closeFVar, liftBVars]
        · have above : index - level = (index - (level + 1)) + 1 := by omega
          have notBelow' : ¬ index < level + 1 := by omega
          have insideEnv : index - (level + 1) < env.length := by omega
          simp only [below, notBelow', if_false, above, envAssignment, List.length_cons,
            show index - (level + 1) + 1 < env.length + 1 by omega, insideEnv, dif_pos, List.getElem_cons_succ]
          simp only [liftBVars, closeFVar]
          have different : env[index - (level + 1)] ≠ name := fun same => absentEnv (same ▸ List.getElem_mem _)
          simp [different]
  | hfvar other =>
      intro level absent _
      simp only [freeVars, List.mem_singleton] at absent
      simp only [substitute, closeFVar]
      have different : (other == name) = false := by simpa [beq_iff_eq] using fun same => absent same.symm
      simp [different]
  | happly constructor arguments recurse =>
      intro level absent wellScoped
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
      simp only [substitute, substituteList_eq_map, closeFVar, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member =>
        recurse argument member level (absent argument member) (wellScoped argument member)
  | hlambda binder body recurse =>
      intro level absent wellScoped
      simp only [freeVars] at absent
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [substitute, closeFVar, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
      congr 1
      have deeper : body.isWellScopedAt (level + 1 + env.length + 1) = true := by
        rw [show level + 1 + env.length + 1 = level + env.length + 1 + 1 by omega]
        exact wellScoped
      exact recurse (level + 1) absent deeper
  | hmultiLambda arity binders body recurse =>
      intro level absent wellScoped
      simp only [freeVars] at absent
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [substitute, closeFVar, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
      congr 1
      have deeper : body.isWellScopedAt (level + arity + env.length + 1) = true := by
        rw [show level + arity + env.length + 1 = level + env.length + 1 + arity by omega]
        exact wellScoped
      rw [show level + 1 + arity = level + arity + 1 by omega]
      exact recurse (level + arity) absent deeper
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro level absent wellScoped
      simp only [freeVars, List.mem_append, not_or] at absent
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
      simp only [substitute, closeFVar, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
      congr 1
      · have deeper : body.isWellScopedAt (level + 1 + env.length + 1) = true := by
          rw [show level + 1 + env.length + 1 = level + env.length + 1 + 1 by omega]
          exact wellScoped.1
        exact bodyRecurse (level + 1) absent.1 deeper
      · exact replacementRecurse level absent.2 wellScoped.2
  | hcollection kind elements rest recurse =>
      intro level absent wellScoped
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
      simp only [substitute, substituteList_eq_map, closeFVar, List.map_map]
      congr 1
      exact List.map_congr_left fun element member =>
        recurse element member level (absent element member) (wellScoped element member)

/-- An assignment of variables: no bag is assigned. -/
def VariableAssignment (assignment : Assignment) : Prop := ∀ index, isName (assignment index) = true

theorem VariableAssignment.lift {assignment : Assignment} (onVariables : VariableAssignment assignment) (arity : Nat) :
    VariableAssignment (lift arity assignment) := by
  intro index
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split
  · rfl
  · have named := onVariables (index - arity)
    revert named
    cases assignment (index - arity) <;> simp [isName, liftBVars]

theorem envAssignment_variables (env : List Name) : VariableAssignment (envAssignment env) := by
  intro index
  unfold envAssignment
  split <;> rfl

theorem components_substitute {assignment : Assignment} (onVariables : VariableAssignment assignment) (pattern : Pattern) :
    piComponents (substitute assignment pattern) = (piComponents pattern).map (substitute assignment) := by
  cases pattern with
  | bvar index =>
      have named := onVariables index
      simp only [substitute, piComponents, List.map_cons, List.map_nil]
      generalize assignment index = value at named ⊢
      cases value <;> simp_all [isName]
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp [piComponents, substitute, substituteList_eq_map]
  | _ => simp [piComponents, substitute, substituteList_eq_map]

theorem substitute_piPar {assignment : Assignment} (onVariables : VariableAssignment assignment) (first second : Pattern) :
    substitute assignment (piPar first second) = piPar (substitute assignment first) (substitute assignment second) := by
  rw [piPar_components, piPar_components]
  simp [substitute, substituteList_eq_map, components_substitute onVariables]

theorem substitute_piParList {assignment : Assignment} (onVariables : VariableAssignment assignment) :
    ∀ patterns : List Pattern,
      substitute assignment (piParList patterns) = piParList (patterns.map (substitute assignment))
  | [] => by simp [piParList, substitute]
  | first :: rest => by
      simp [piParList, substitute_piPar onVariables, substitute_piParList onVariables rest]


/-! ## The shapes of a named pattern -/

theorem named_cases {pattern : Pattern} (named : Named pattern = true) :
    pattern = .apply "PiNil" [] ∨
    (∃ elements, pattern = .collection .hashBag elements none ∧ NamedList elements = true) ∨
    (∃ binder body, pattern = .apply "PiNu" [.lambda binder body] ∧ Named body = true) ∨
    (∃ channel binder body, pattern = .apply "PiInp" [channel, .lambda binder body] ∧ isName channel = true ∧
      Named body = true) ∨
    (∃ channel binder body, pattern = .apply "PiRep" [.apply "PiInp" [channel, .lambda binder body]] ∧
      isName channel = true ∧ Named body = true) ∨
    (∃ channel datum, pattern = .apply "PiOut" [channel, datum] ∧ isName channel = true ∧ isName datum = true) := by
  unfold Named at named
  split at named
  · exact .inl rfl
  · exact .inr (.inl ⟨_, rfl, named⟩)
  · exact .inr (.inr (.inl ⟨_, _, rfl, named⟩))
  · simp only [Bool.and_eq_true] at named
    exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, named.1, named.2⟩)))
  · simp only [Bool.and_eq_true] at named
    exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, named.1, named.2⟩))))
  · simp only [Bool.and_eq_true] at named
    exact .inr (.inr (.inr (.inr (.inr ⟨_, _, rfl, named.1, named.2⟩))))
  · cases named

theorem mem_freeVars_components {pattern : Pattern} {name : String} {element : Pattern}
    (member : element ∈ piComponents pattern) (free : name ∈ freeVars element) : name ∈ freeVars pattern := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp only [piComponents, List.mem_singleton] at member
      all_goals first
        | (subst member; exact free)
        | (simp only [freeVars, List.mem_flatMap]; exact ⟨element, member, free⟩)
  | _ => simp only [piComponents, List.mem_singleton] at member; subst member; exact free

theorem freeVars_piPar {first second : Pattern} {name : String} (free : name ∈ freeVars (piPar first second)) :
    name ∈ freeVars first ∨ name ∈ freeVars second := by
  rw [piPar_components] at free
  simp only [freeVars, List.mem_flatMap, List.mem_append] at free
  obtain ⟨element, member | member, inside⟩ := free
  · exact .inl (mem_freeVars_components member inside)
  · exact .inr (mem_freeVars_components member inside)

theorem freeVars_piParList {name : String} : ∀ {patterns : List Pattern}, name ∈ freeVars (piParList patterns) →
    ∃ pattern ∈ patterns, name ∈ freeVars pattern
  | [], free => by simp [piParList, freeVars] at free
  | first :: rest, free => by
      rcases freeVars_piPar free with inFirst | inRest
      · exact ⟨first, List.mem_cons_self, inFirst⟩
      · obtain ⟨pattern, member, inside⟩ := freeVars_piParList inRest
        exact ⟨pattern, List.mem_cons_of_mem _ member, inside⟩

theorem scoped_components {pattern : Pattern} {depth : Nat} (wellScoped : pattern.isWellScopedAt depth = true) :
    ∀ element ∈ piComponents pattern, element.isWellScopedAt depth = true := by
  intro element member
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp only [piComponents, List.mem_singleton] at member
      all_goals first
        | (subst member; exact wellScoped)
        | (simp only [Pattern.isWellScopedAt,
            Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
           exact wellScoped element member)
  | _ => simp only [piComponents, List.mem_singleton] at member; subst member; exact wellScoped

theorem scoped_piPar {first second : Pattern} {depth : Nat} (firstScoped : first.isWellScopedAt depth = true)
    (secondScoped : second.isWellScopedAt depth = true) : (piPar first second).isWellScopedAt depth = true := by
  rw [piPar_components]
  simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff,
    List.mem_append]
  rintro element (member | member)
  · exact scoped_components firstScoped element member
  · exact scoped_components secondScoped element member

theorem scoped_piParList {depth : Nat} : ∀ {patterns : List Pattern},
    (∀ pattern ∈ patterns, pattern.isWellScopedAt depth = true) → (piParList patterns).isWellScopedAt depth = true
  | [], _ => rfl
  | first :: _, all => scoped_piPar (all first List.mem_cons_self)
      (scoped_piParList fun pattern member => all pattern (List.mem_cons_of_mem _ member))

/-- **The normal form keeps the scope and the free names** of a named pattern. -/
theorem normal_facts : ∀ (size : Nat) {pattern : Pattern}, sizeOf pattern < size → Named pattern = true →
    (∀ depth, pattern.isWellScopedAt depth = true → (normal pattern).isWellScopedAt depth = true) ∧
      (∀ name ∈ freeVars (normal pattern), name ∈ freeVars pattern)
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, _, bodyNamed⟩ | ⟨channel, binder, body, rfl, _, bodyNamed⟩ |
        ⟨channel, datum, rfl, _, _⟩
      · exact ⟨fun _ wellScoped => wellScoped, fun _ free => free⟩
      · have each : ∀ element ∈ elements, _ := fun element member =>
          normal_facts size (show sizeOf element < size by
            have := List.sizeOf_lt_of_mem member
            simp only [Pattern.collection.sizeOf_spec] at small
            omega) (namedList_iff.mp elementsNamed element member)
        simp only [normal, normalList_eq_map]
        refine ⟨fun depth wellScoped => scoped_piParList fun normalized member => ?_, fun name free => ?_⟩
        · obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
          simp only [Pattern.isWellScopedAt,
            Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
          exact (each element elementMember).1 depth (wellScoped element elementMember)
        · obtain ⟨normalized, member, inside⟩ := freeVars_piParList free
          obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
          simp only [freeVars, List.mem_flatMap]
          exact ⟨element, elementMember, (each element elementMember).2 name inside⟩
      · have inner := normal_facts size (show sizeOf body < size by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [normal]
        refine ⟨fun depth wellScoped => ?_, fun name free => ?_⟩
        · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true] at wellScoped ⊢
          exact inner.1 _ wellScoped
        · simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at free ⊢
          exact inner.2 name free
      · have inner := normal_facts size (show sizeOf body < size by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [normal]
        refine ⟨fun depth wellScoped => ?_, fun name free => ?_⟩
        · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped ⊢
          exact ⟨wellScoped.1, inner.1 _ wellScoped.2⟩
        · simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at free ⊢
          rcases free with free | free
          · exact .inl free
          · exact .inr (inner.2 name free)
      · have inner := normal_facts size (show sizeOf body < size by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [normal]
        refine ⟨fun depth wellScoped => ?_, fun name free => ?_⟩
        · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped ⊢
          exact ⟨wellScoped.1, inner.1 _ wellScoped.2⟩
        · simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at free ⊢
          rcases free with free | free
          · exact .inl free
          · exact .inr (inner.2 name free)
      · simp only [normal]
        exact ⟨fun _ wellScoped => wellScoped, fun _ free => free⟩


/-! ## The read-back's translation -/

theorem substitute_name {env : List Name} {channel : Pattern} (named : isName channel = true)
    (wellScoped : channel.isWellScopedAt env.length = true) :
    substitute (envAssignment env) channel = .fvar (nameOf env channel) := by
  cases channel with
  | fvar name => rfl
  | bvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at wellScoped
      simp [substitute, envAssignment, wellScoped, nameOf, List.getD_eq_getElem?_getD]
  | _ => simp [isName] at named

/-- **The translation of a read-back is the normal form, opened at the names of its free variables.** -/
theorem piToPattern_readBack (avoid : Finset Name) : ∀ (size : Nat) {pattern : Pattern} (env : List Name),
    sizeOf pattern < size → Named pattern = true → pattern.isWellScopedAt env.length = true →
      (∀ name ∈ freeVars pattern, name ∈ avoid) →
      piToPattern (readBack avoid env pattern) = openWith env (normal pattern)
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, env, small, named, wellScoped, avoided => by
      have facts := normal_facts (size + 1) small named
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · simp [readBack, normal, piToPattern, openWith, substitute]
      · have attached : (elements.attach.map fun ⟨element, _⟩ => readBack avoid env element) =
            elements.map (readBack avoid env) := by simp
        simp only [readBack]
        rw [attached]
        simp only [normal, normalList_eq_map, openWith, piToPattern_parList,
          substitute_piParList (envAssignment_variables env), List.map_map]
        congr 1
        apply List.map_congr_left
        intro element member
        simp only [Pattern.isWellScopedAt,
          Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at wellScoped
        simp only [freeVars, List.mem_flatMap] at avoided
        exact piToPattern_readBack avoid size env (by
            have := List.sizeOf_lt_of_mem member
            simp only [Pattern.collection.sizeOf_spec] at small
            omega)
          (namedList_iff.mp elementsNamed element member) (wellScoped element member)
          (fun name free => avoided name ⟨element, member, free⟩)
      · have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        have fresh' := fresh_not_mem (avoid ∪ env.toFinset)
        simp only [Finset.mem_union, List.mem_toFinset, not_or] at fresh'
        have bodyScoped : body.isWellScopedAt (fresh (avoid ∪ env.toFinset) :: env).length = true := by
          simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true] at wellScoped
          simpa using wellScoped
        have bodyAvoided : ∀ name ∈ freeVars body, name ∈ avoid := fun name free => avoided name (by
          simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact free)
        have inner := piToPattern_readBack avoid size (fresh (avoid ∪ env.toFinset) :: env) smaller bodyNamed bodyScoped
          bodyAvoided
        have bodyFacts := normal_facts size smaller bodyNamed
        have closed := closeFVar_open fresh'.2 (normal body) 0
          (fun free => fresh'.1 (bodyAvoided _ (bodyFacts.2 _ free)))
          (bodyFacts.1 _ (by simpa [Nat.add_comm] using bodyScoped))
        simp only [lift_zero, Nat.zero_add] at closed
        simp only [readBack, piToPattern, normal, openWith, substitute, substituteList_eq_map, List.map_cons,
          List.map_nil]
        rw [inner]
        unfold openWith
        rw [closed]
      · have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        have fresh' := fresh_not_mem (avoid ∪ env.toFinset)
        simp only [Finset.mem_union, List.mem_toFinset, not_or] at fresh'
        have bodyScoped : body.isWellScopedAt (fresh (avoid ∪ env.toFinset) :: env).length = true := by
          simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped
          simpa using wellScoped.2
        have bodyAvoided : ∀ name ∈ freeVars body, name ∈ avoid := fun name free => avoided name (by
          simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
          exact .inr free)
        have inner := piToPattern_readBack avoid size (fresh (avoid ∪ env.toFinset) :: env) smaller bodyNamed bodyScoped
          bodyAvoided
        have bodyFacts := normal_facts size smaller bodyNamed
        have closed := closeFVar_open fresh'.2 (normal body) 0
          (fun free => fresh'.1 (bodyAvoided _ (bodyFacts.2 _ free)))
          (bodyFacts.1 _ (by simpa [Nat.add_comm] using bodyScoped))
        simp only [lift_zero, Nat.zero_add] at closed
        simp only [readBack, piToPattern, normal, openWith, substitute, substituteList_eq_map, List.map_cons,
          List.map_nil]
        rw [inner]
        unfold openWith
        rw [closed, substitute_name channelNamed (by
          simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped
          exact wellScoped.1)]
      · have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        have fresh' := fresh_not_mem (avoid ∪ env.toFinset)
        simp only [Finset.mem_union, List.mem_toFinset, not_or] at fresh'
        have bodyScoped : body.isWellScopedAt (fresh (avoid ∪ env.toFinset) :: env).length = true := by
          simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped
          simpa using wellScoped.2
        have bodyAvoided : ∀ name ∈ freeVars body, name ∈ avoid := fun name free => avoided name (by
          simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
          exact .inr free)
        have inner := piToPattern_readBack avoid size (fresh (avoid ∪ env.toFinset) :: env) smaller bodyNamed bodyScoped
          bodyAvoided
        have bodyFacts := normal_facts size smaller bodyNamed
        have closed := closeFVar_open fresh'.2 (normal body) 0
          (fun free => fresh'.1 (bodyAvoided _ (bodyFacts.2 _ free)))
          (bodyFacts.1 _ (by simpa [Nat.add_comm] using bodyScoped))
        simp only [lift_zero, Nat.zero_add] at closed
        simp only [readBack, piToPattern, normal, openWith, substitute, substituteList_eq_map, List.map_cons,
          List.map_nil]
        rw [inner]
        unfold openWith
        rw [closed, substitute_name channelNamed (by
          simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped
          exact wellScoped.1)]
      · simp only [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true, Bool.and_eq_true] at wellScoped
        simp only [readBack, piToPattern, normal, openWith, substitute, substituteList_eq_map, List.map_cons,
          List.map_nil, substitute_name channelNamed wellScoped.1, substitute_name datumNamed wellScoped.2]


/-! ## A named process is equivalent to its normal form -/

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList
  hasType_apply_inversion)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent
  equationEquiv_fill)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piBagPresentation piPar_hasType
  piPar_equivalent_bag restriction_typed params_of_label)

theorem piParList_equivalent {free : FreeTypeContext} {bound : List TypeExpr} : ∀ (elements : List Pattern),
    (∀ element ∈ elements, HasType piCalc free bound element (.base "Proc") ∧
      HasType piCalc free bound (normal element) (.base "Proc") ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc element (normal element)) →
    HasType piCalc free bound (piParList (elements.map normal)) (.base "Proc") ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (.collection .hashBag elements none)
        (piParList (elements.map normal))
  | [], _ => by
      refine ⟨piBlockSignature.unit_typed, derivedInstance_equivalent (.emptyUnit piBagPresentation.bagAlgebraRule rfl
        ⟨free, bound, bag_typed (block := piBlock) (rest := none) fun _ member => by simp at member⟩)⟩
  | first :: rest, each => by
      obtain ⟨firstTyped, firstNormalTyped, firstEquivalent⟩ := each first List.mem_cons_self
      obtain ⟨restTyped, restEquivalent⟩ := piParList_equivalent rest fun element member =>
        each element (List.mem_cons_of_mem _ member)
      have restMembers : Members piCalc piBlock free bound rest := fun element member =>
        (each element (List.mem_cons_of_mem _ member)).1
      have outer : Members piCalc piBlock free bound [first, .collection .hashBag rest none] := by
        intro element member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact firstTyped
        · exact bag_typed (block := piBlock) (rest := none) restMembers
      have flattened := DerivedInstance.flatten piBagPresentation.bagAlgebraRule rfl (pre := [first]) (inner := rest)
        (post := []) ⟨free, bound, bag_typed (block := piBlock) (rest := none) outer⟩
      simp only [List.append_nil, List.cons_append, List.nil_append] at flattened
      have unflat := Relation.EqvGen.symm _ _ (derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
        flattened)
      have firstPart := equationEquiv_fill (.collection .hashBag [] .hole [.collection .hashBag rest none] none)
        firstEquivalent
      have restPart := equationEquiv_fill (.collection .hashBag [normal first] .hole [] none) restEquivalent
      simp only [OneHoleContext.fill, List.nil_append, List.cons_append] at firstPart restPart
      refine ⟨piPar_hasType firstNormalTyped restTyped, ?_⟩
      exact .trans _ _ _ unflat (.trans _ _ _ firstPart (.trans _ _ _ restPart
        (piPar_equivalent_bag firstNormalTyped restTyped)))

theorem binder_none {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    {binder : Option String} {body : Pattern} (typed : HasType piCalc free bound (.apply label arguments) (.base "Proc"))
    (object : isObjectPattern (.apply label arguments) = true) (member : .lambda binder body ∈ arguments) :
    binder = none := by
  have canonical := (metadata_of_typed (block := piBlock) _ typed object).1 ⟨_, rfl⟩
  simp only [Pattern.hasCanonicalBinderMetadata,
    Mettapedia.GSLT.LanguageDef.BagNormalForm.hasCanonicalBinderMetadataList_iff] at canonical
  have lambdaCanonical := canonical _ member
  simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, Option.isNone_iff_eq_none] at lambdaCanonical
  exact lambdaCanonical.1

/-- **A named process of the process sort is equivalent to its normal form**, which has the process sort. -/
theorem normal_equivalent {free : FreeTypeContext} : ∀ (size : Nat) {bound : List TypeExpr} {pattern : Pattern},
    sizeOf pattern < size → HasType piCalc free bound pattern (.base "Proc") → isObjectPattern pattern = true →
    Named pattern = true →
      HasType piCalc free bound (normal pattern) (.base "Proc") ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc pattern (normal pattern)
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, bound, pattern, small, typed, object, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, _, bodyNamed⟩ | ⟨channel, binder, body, rfl, _, bodyNamed⟩ |
        ⟨channel, datum, rfl, _, _⟩
      · exact ⟨typed, .refl _⟩
      · simp only [normal, normalList_eq_map]
        have members := members_of_bag (block := piBlock) typed
        refine piParList_equivalent elements fun element member => ?_
        have inner := normal_equivalent size (show sizeOf element < size by
            have := List.sizeOf_lt_of_mem member
            simp only [Pattern.collection.sizeOf_spec] at small
            omega) (members element member)
          (bag_objects object element member)
          (namedList_iff.mp elementsNamed element member)
        exact ⟨members element member, inner⟩
      · have binderIs := restriction_binder (block := piBlock) typed
        subst binderIs
        have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        have bodyObject : isObjectPattern body = true := by rwa [isObject_restriction] at object
        obtain ⟨normalTyped, equivalent⟩ := normal_equivalent size smaller (restriction_typed typed) bodyObject bodyNamed
        simp only [normal]
        have filled := equationEquiv_fill (.apply "PiNu" [] (.lambda none .hole) []) equivalent
        exact ⟨restrict_typed (block := piBlock) normalTyped, by simpa [OneHoleContext.fill] using filled⟩
      · have binderIs := binder_none (binder := binder) (body := body) typed object (by simp)
        subst binderIs
        have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        obtain ⟨channelTyped, bodyTyped⟩ := listener_parts typed
        have bodyObject : isObjectPattern body = true := by
          simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
          exact object.2
        obtain ⟨normalTyped, equivalent⟩ := normal_equivalent size smaller bodyTyped bodyObject bodyNamed
        obtain ⟨rule, member, labelIs, notBare, typeIs, arguments⟩ := hasType_apply_inversion typed
        have params := (params_of_label member).1 labelIs.symm
        simp only [normal]
        have filled := equationEquiv_fill (.apply "PiInp" [channel] (.lambda none .hole) []) equivalent
        refine ⟨?_, by simpa [OneHoleContext.fill] using filled⟩
        have rebuilt := HasType.constructor (free := free) (bound := bound) (arguments := [channel, .lambda none (normal body)])
          member notBare (by rw [params]; exact .cons trivial rfl channelTyped (.cons trivial rfl (.lambda normalTyped) .nil))
        rw [← labelIs, ← typeIs] at rebuilt
        exact rebuilt
      · -- a server: the replication of an input
        have inputTyped : HasType piCalc free bound (.apply "PiInp" [channel, .lambda binder body]) (.base "Proc") :=
          replicate_argument_typed (block := piRepBlock) typed
        have inputObject : isObjectPattern (.apply "PiInp" [channel, .lambda binder body]) = true := by
          simp only [isObjectPattern, isObjectPatternList, Bool.and_true] at object ⊢
          exact object
        have binderIs := binder_none (binder := binder) (body := body) inputTyped inputObject (by simp)
        subst binderIs
        have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        obtain ⟨channelTyped, bodyTyped⟩ := listener_parts inputTyped
        have bodyObject : isObjectPattern body = true := by
          simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at inputObject
          exact inputObject.2
        obtain ⟨normalTyped, equivalent⟩ := normal_equivalent size smaller bodyTyped bodyObject bodyNamed
        obtain ⟨rule, member, labelIs, notBare, typeIs, arguments⟩ := hasType_apply_inversion inputTyped
        have params := (params_of_label member).1 labelIs.symm
        simp only [normal]
        have filled := equationEquiv_fill
          (.apply "PiRep" [] (.apply "PiInp" [channel] (.lambda none .hole) []) []) equivalent
        refine ⟨?_, by simpa [OneHoleContext.fill] using filled⟩
        have rebuilt := HasType.constructor (free := free) (bound := bound) (arguments := [channel, .lambda none (normal body)])
          member notBare (by rw [params]; exact .cons trivial rfl channelTyped (.cons trivial rfl (.lambda normalTyped) .nil))
        rw [← labelIs, ← typeIs] at rebuilt
        exact replicate_typed (block := piRepBlock) rebuilt
      · simp only [normal]
        exact ⟨typed, .refl _⟩


/-! ## Substituting variables for variables -/

open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar applySubst)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (single substitute_single_eq_instantiateBVar substitute_comp)

theorem isName_substitute {assignment : Assignment} (onVariables : VariableAssignment assignment) {channel : Pattern}
    (named : isName channel = true) : isName (substitute assignment channel) = true := by
  cases channel with
  | bvar index => exact onVariables index
  | fvar name => rfl
  | _ => simp [isName] at named

/-- **Substituting variables for variables keeps a pattern named, and commutes with the normal form.** -/
theorem normal_substitute : ∀ (size : Nat) {assignment : Assignment} {pattern : Pattern},
    VariableAssignment assignment → sizeOf pattern < size → Named pattern = true →
      Named (substitute assignment pattern) = true ∧
        normal (substitute assignment pattern) = substitute assignment (normal pattern)
  | 0, _, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, assignment, pattern, onVariables, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · simp [substitute, normal, Named]
      · have each : ∀ element ∈ elements, Named (substitute assignment element) = true ∧
            normal (substitute assignment element) = substitute assignment (normal element) :=
          fun element member => normal_substitute size onVariables (by
            have := List.sizeOf_lt_of_mem member
            simp only [Pattern.collection.sizeOf_spec] at small
            omega) (namedList_iff.mp elementsNamed element member)
        simp only [substitute, substituteList_eq_map, normal, normalList_eq_map, Named]
        refine ⟨namedList_iff.mpr fun element member => ?_, ?_⟩
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (each original originalMember).1
        · rw [substitute_piParList onVariables, List.map_map, List.map_map]
          congr 1
          exact List.map_congr_left fun element member => (each element member).2
      · have inner := normal_substitute size (onVariables.lift 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, normal, Named]
        exact ⟨inner.1, by rw [inner.2]⟩
      · have inner := normal_substitute size (onVariables.lift 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_substitute onVariables channelNamed, inner.1⟩, by rw [inner.2]⟩
      · have inner := normal_substitute size (onVariables.lift 1) (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_substitute onVariables channelNamed, inner.1⟩, by rw [inner.2]⟩
      · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, normal, Named, Bool.and_eq_true]
        exact ⟨⟨isName_substitute onVariables channelNamed, isName_substitute onVariables datumNamed⟩, trivial⟩

theorem single_variables {datum : Pattern} (named : isName datum = true) : VariableAssignment (single datum) := by
  intro index
  cases index with
  | zero => exact named
  | succ => rfl

/-- **Renaming a fresh name after opening it** is opening at the new name, in an object pattern. -/
theorem applySubst_open {old new : String} {env : List Name} (absentEnv : old ∉ env) (pattern : Pattern) :
    ∀ level, old ∉ freeVars pattern → isObjectPattern pattern = true →
      applySubst [(old, .fvar new)] (substitute (lift level (envAssignment (old :: env))) pattern) =
        substitute (lift level (envAssignment (new :: env))) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level _ _
      simp only [substitute, lift]
      split
      · simp [applySubst]
      · unfold envAssignment
        cases position : index - level with
        | zero => simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.applySubst_fvar_single]
        | succ rest =>
            simp only [List.length_cons, Nat.add_lt_add_iff_right]
            split
            · rename_i inside
              have different : env[rest] ≠ old := fun same => absentEnv (same ▸ List.getElem_mem _)
              simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.applySubst_fvar_single, different]
            · simp [liftBVars, applySubst]
  | hfvar other =>
      intro level absent _
      simp only [freeVars, List.mem_singleton] at absent
      have different : other ≠ old := fun same => absent same.symm
      simp [substitute, Mettapedia.OSLF.MeTTaIL.Substitution.applySubst_fvar_single, different]
  | happly constructor arguments recurse =>
      intro level absent object
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff] at object
      simp only [substitute, substituteList_eq_map, applySubst, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member =>
        recurse argument member level (absent argument member) (object argument member)
  | hlambda binder body recurse =>
      intro level absent object
      simp only [freeVars] at absent
      simp only [isObjectPattern] at object
      simp only [substitute, applySubst, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
      rw [recurse (level + 1) absent object]
  | hmultiLambda arity binders body recurse =>
      intro level absent object
      simp only [freeVars] at absent
      simp only [isObjectPattern] at object
      simp only [substitute, applySubst, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
      rw [recurse (level + arity) absent object]
  | hsubst => intro _ _ object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro level absent object
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [isObjectPattern, Bool.and_eq_true,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff] at object
      simp only [substitute, substituteList_eq_map, applySubst, List.map_map]
      congr 1
      exact List.map_congr_left fun element member =>
        recurse element member level (absent element member) (object.2 element member)

/-- **Opening a reception** is opening the continuation at the received name. -/
theorem open_instantiate {env : List Name} {datum : Pattern} (named : isName datum = true)
    (wellScoped : datum.isWellScopedAt env.length = true) (body : Pattern) :
    openWith env (instantiateBVar datum body) = substitute (envAssignment (nameOf env datum :: env)) body := by
  rw [← substitute_single_eq_instantiateBVar, openWith, substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => simpa [single, envAssignment] using substitute_name named wellScoped
  | succ index =>
      simp only [single, substitute, envAssignment, List.length_cons, Nat.add_lt_add_iff_right]
      split
      · simp
      · congr 1
        omega

/-! ## Free names, objects and named normal forms -/

theorem VariableAssignment.lift_fvar {assignment : Assignment} (onVariables : VariableAssignment assignment)
    {arity index : Nat} {name : String}
    (found : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift arity assignment index = .fvar name) :
    ∃ original, assignment original = .fvar name := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift at found
  split at found
  · cases found
  · refine ⟨index - arity, ?_⟩
    have named := onVariables (index - arity)
    generalize assignment (index - arity) = value at found named ⊢
    cases value <;> simp_all [isName, liftBVars]

/-- **A free name of a pattern with variables substituted** is free in the pattern or substituted for a variable. -/
theorem freeVars_substitute_variables (pattern : Pattern) : ∀ {assignment : Assignment},
    VariableAssignment assignment → ∀ {name : String}, name ∈ freeVars (substitute assignment pattern) →
      name ∈ freeVars pattern ∨ ∃ index, assignment index = .fvar name := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro assignment onVariables name free
      simp only [substitute] at free
      have named := onVariables index
      refine .inr ⟨index, ?_⟩
      generalize assignment index = value at free named ⊢
      cases value <;> simp_all [isName, freeVars]
  | hfvar other =>
      intro assignment _ name free
      exact .inl (by simpa [substitute] using free)
  | happly constructor arguments recurse =>
      intro assignment onVariables name free
      simp only [substitute, substituteList_eq_map, freeVars, List.mem_flatMap, List.mem_map] at free
      obtain ⟨_, ⟨argument, member, rfl⟩, inside⟩ := free
      rcases recurse argument member onVariables inside with here | there
      · exact .inl (by simp only [freeVars, List.mem_flatMap]; exact ⟨argument, member, here⟩)
      · exact .inr there
  | hlambda binder body recurse =>
      intro assignment onVariables name free
      simp only [substitute, freeVars] at free
      rcases recurse (onVariables.lift 1) free with here | ⟨_, found⟩
      · exact .inl (by simpa [freeVars] using here)
      · exact .inr (onVariables.lift_fvar found)
  | hmultiLambda arity binders body recurse =>
      intro assignment onVariables name free
      simp only [substitute, freeVars] at free
      rcases recurse (onVariables.lift arity) free with here | ⟨_, found⟩
      · exact .inl (by simpa [freeVars] using here)
      · exact .inr (onVariables.lift_fvar found)
  | hsubst body replacement recurseBody recurseReplacement =>
      intro assignment onVariables name free
      simp only [substitute, freeVars, List.mem_append] at free
      rcases free with free | free
      · rcases recurseBody (onVariables.lift 1) free with here | ⟨_, found⟩
        · exact .inl (by simp [freeVars, here])
        · exact .inr (onVariables.lift_fvar found)
      · rcases recurseReplacement onVariables free with here | there
        · exact .inl (by simp [freeVars, here])
        · exact .inr there
  | hcollection kind elements rest recurse =>
      intro assignment onVariables name free
      simp only [substitute, substituteList_eq_map, freeVars, List.mem_flatMap, List.mem_map] at free
      obtain ⟨_, ⟨element, member, rfl⟩, inside⟩ := free
      rcases recurse element member onVariables inside with here | there
      · exact .inl (by simp only [freeVars, List.mem_flatMap]; exact ⟨element, member, here⟩)
      · exact .inr there

theorem isObject_of_name {channel : Pattern} (named : isName channel = true) : isObjectPattern channel = true := by
  cases channel <;> simp_all [isName, isObjectPattern]

/-- **A named pattern is an object pattern.** -/
theorem named_object : ∀ (size : Nat) {pattern : Pattern}, sizeOf pattern < size → Named pattern = true →
    isObjectPattern pattern = true
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · simp [isObjectPattern, isObjectPatternList]
      · rw [isObject_bag]
        intro element member
        exact named_object size (by
          have := List.sizeOf_lt_of_mem member
          simp only [Pattern.collection.sizeOf_spec] at small
          omega) (namedList_iff.mp elementsNamed element member)
      · have inner := named_object size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp [isObjectPattern, isObjectPatternList, inner]
      · have inner := named_object size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp [isObjectPattern, isObjectPatternList, inner, isObject_of_name channelNamed]
      · have inner := named_object size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp [isObjectPattern, isObjectPatternList, inner, isObject_of_name channelNamed]
      · simp [isObjectPattern, isObjectPatternList, isObject_of_name channelNamed, isObject_of_name datumNamed]

theorem components_named {pattern : Pattern} (named : Named pattern = true) :
    ∀ component ∈ piComponents pattern, Named component = true := by
  intro component member
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp only [piComponents, List.mem_singleton] at member
      all_goals first
        | (subst member; exact named)
        | exact namedList_iff.mp (by simpa [Named] using named) component member
  | _ => simp only [piComponents, List.mem_singleton] at member; subst member; exact named

theorem named_piPar {first second : Pattern} (firstNamed : Named first = true) (secondNamed : Named second = true) :
    Named (piPar first second) = true := by
  rw [piPar_components]
  simp only [Named]
  apply namedList_iff.mpr
  intro component member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact components_named firstNamed component inFirst
  · exact components_named secondNamed component inSecond

theorem named_piParList : ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, Named pattern = true) →
    Named (piParList patterns) = true
  | [], _ => rfl
  | first :: _, all => named_piPar (all first List.mem_cons_self)
      (named_piParList fun pattern member => all pattern (List.mem_cons_of_mem _ member))

/-- **The normal form of a named pattern is named.** -/
theorem named_normal : ∀ (size : Nat) {pattern : Pattern}, sizeOf pattern < size → Named pattern = true →
    Named (normal pattern) = true
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ | ⟨channel, binder, body, rfl, channelNamed, bodyNamed⟩ |
        ⟨channel, datum, rfl, channelNamed, datumNamed⟩
      · rfl
      · simp only [normal, normalList_eq_map]
        apply named_piParList
        intro normalized member
        obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
        exact named_normal size (by
          have := List.sizeOf_lt_of_mem elementMember
          simp only [Pattern.collection.sizeOf_spec] at small
          omega) (namedList_iff.mp elementsNamed element elementMember)
      · have inner := named_normal size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simpa [normal, Named] using inner
      · have inner := named_normal size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp [normal, Named, inner, channelNamed]
      · have inner := named_normal size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed
        simp [normal, Named, inner, channelNamed]
      · simp [normal, Named, channelNamed, datumNamed]

/-! ## Reading back a reception -/

open Mettapedia.Languages.ProcessCalculi.PiCalculus (Congruent congruent_of_piToPattern_eq)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piToPattern_substitute)

/-- A received name is named, in scope, and among the avoided names; so is the continuation it is received into. -/
theorem instantiate_facts {env : List Name} {avoid : Finset Name} {body datum : Pattern}
    (bodyNamed : Named body = true) (bodyScoped : body.isWellScopedAt (env.length + 1) = true)
    (bodyAvoided : ∀ name ∈ freeVars body, name ∈ avoid)
    (datumNamed : isName datum = true) (datumScoped : datum.isWellScopedAt env.length = true)
    (datumAvoided : ∀ name ∈ freeVars datum, name ∈ avoid) :
    Named (instantiateBVar datum body) = true ∧ (instantiateBVar datum body).isWellScopedAt env.length = true ∧
      ∀ name ∈ freeVars (instantiateBVar datum body), name ∈ avoid := by
  rw [← substitute_single_eq_instantiateBVar]
  refine ⟨(normal_substitute (sizeOf body + 1) (single_variables datumNamed) (Nat.lt_succ_self _) bodyNamed).1, ?_, ?_⟩
  · rw [substitute_single_eq_instantiateBVar]
    exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt_isWellScopedAt (ambient := env.length)
      (depth := 0) bodyScoped datumScoped
  · intro name free
    rcases freeVars_substitute_variables body (single_variables datumNamed) free with here | ⟨index, found⟩
    · exact bodyAvoided name here
    · cases index with
      | zero =>
          simp only [single] at found
          exact datumAvoided name (by simp [found, freeVars])
      | succ => cases found

/-- **Receiving a name in a read-back is reading back the reception**, up to structural congruence: the bound name of
the input, renamed to the received one, reads as the received variable. -/
theorem readBack_receive (avoid : Finset Name) {env : List Name} {body datum : Pattern}
    (bodyNamed : Named body = true) (bodyScoped : body.isWellScopedAt (env.length + 1) = true)
    (bodyAvoided : ∀ name ∈ freeVars body, name ∈ avoid)
    (datumNamed : isName datum = true) (datumScoped : datum.isWellScopedAt env.length = true)
    (datumAvoided : ∀ name ∈ freeVars datum, name ∈ avoid) :
    Congruent ((readBack avoid (fresh (avoid ∪ env.toFinset) :: env) body).substitute
        (fresh (avoid ∪ env.toFinset)) (nameOf env datum))
      (readBack avoid env (instantiateBVar datum body)) := by
  have boundFresh := fresh_not_mem (avoid ∪ env.toFinset)
  generalize fresh (avoid ∪ env.toFinset) = bound at boundFresh ⊢
  have notAvoid : bound ∉ avoid := fun inside => boundFresh (Finset.mem_union_left _ inside)
  have notEnv : bound ∉ env := fun inside => boundFresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
  have facts := normal_facts (sizeOf body + 1) (Nat.lt_succ_self _) bodyNamed
  have received := instantiate_facts bodyNamed bodyScoped bodyAvoided datumNamed datumScoped datumAvoided
  apply congruent_of_piToPattern_eq _ _ _ le_rfl
  rw [piToPattern_substitute, piToPattern_readBack avoid (sizeOf body + 1) _ (Nat.lt_succ_self _) bodyNamed
      (by simpa using bodyScoped) bodyAvoided,
    piToPattern_readBack avoid (sizeOf (instantiateBVar datum body) + 1) _ (Nat.lt_succ_self _) received.1
      received.2.1 received.2.2]
  have renamed := applySubst_open (new := nameOf env datum) notEnv (normal body) 0
    (fun free => notAvoid (bodyAvoided _ (facts.2 _ free)))
    (named_object _ (Nat.lt_succ_self _) (named_normal (sizeOf body + 1) (Nat.lt_succ_self _) bodyNamed))
  simp only [lift_zero] at renamed
  rw [openWith, renamed, ← substitute_single_eq_instantiateBVar,
    (normal_substitute (sizeOf body + 1) (single_variables datumNamed) (Nat.lt_succ_self _) bodyNamed).2,
    substitute_single_eq_instantiateBVar, open_instantiate datumNamed datumScoped]

/-! ## Raw steps read back -/

open Mettapedia.Languages.ProcessCalculi.PiCalculus (parList parList_perm reduces_of_congruent reduces_parLeft
  Reduces StructuralCongruence)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (PiRawStep)

theorem readBack_bag (avoid : Finset Name) (env : List Name) (elements : List Pattern) :
    readBack avoid env (.collection .hashBag elements none) = parList (elements.map (readBack avoid env)) := by
  simp only [readBack]
  congr 1
  simp

theorem scoped_bag {elements : List Pattern} {depth : Nat}
    (wellScoped : (Pattern.collection .hashBag elements none).isWellScopedAt depth = true) :
    ∀ element ∈ elements, element.isWellScopedAt depth = true := by
  simpa only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
    using wellScoped

theorem scoped_binary {label : String} {first second : Pattern} {depth : Nat}
    (wellScoped : (Pattern.apply label [first, second]).isWellScopedAt depth = true) :
    first.isWellScopedAt depth = true ∧ second.isWellScopedAt depth = true := by
  simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at wellScoped
  exact wellScoped

theorem scoped_unary {label : String} {only : Pattern} {depth : Nat}
    (wellScoped : (Pattern.apply label [only]).isWellScopedAt depth = true) : only.isWellScopedAt depth = true := by
  simpa only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq] using wellScoped

theorem scoped_lambda {binder : Option String} {body : Pattern} {depth : Nat}
    (wellScoped : (Pattern.lambda binder body).isWellScopedAt depth = true) : body.isWellScopedAt (depth + 1) = true := by
  simpa only [Pattern.isWellScopedAt] using wellScoped

theorem avoided_binary {avoid : Finset Name} {label : String} {first second : Pattern}
    (avoided : ∀ name ∈ freeVars (.apply label [first, second]), name ∈ avoid) :
    (∀ name ∈ freeVars first, name ∈ avoid) ∧ ∀ name ∈ freeVars second, name ∈ avoid :=
  ⟨fun name free => avoided name (by simp [freeVars, free]), fun name free => avoided name (by simp [freeVars, free])⟩

theorem avoided_unary {avoid : Finset Name} {label : String} {only : Pattern}
    (avoided : ∀ name ∈ freeVars (.apply label [only]), name ∈ avoid) : ∀ name ∈ freeVars only, name ∈ avoid :=
  fun name free => avoided name (by simp [freeVars, free])

theorem avoided_lambda {avoid : Finset Name} {binder : Option String} {body : Pattern}
    (avoided : ∀ name ∈ freeVars (.lambda binder body), name ∈ avoid) : ∀ name ∈ freeVars body, name ∈ avoid :=
  fun name free => avoided name (by simpa [freeVars] using free)

theorem avoided_bag {avoid : Finset Name} {elements : List Pattern}
    (avoided : ∀ name ∈ freeVars (.collection .hashBag elements none), name ∈ avoid) :
    ∀ element ∈ elements, ∀ name ∈ freeVars element, name ∈ avoid :=
  fun element member name free => avoided name (by simp only [freeVars, List.mem_flatMap]; exact ⟨element, member, free⟩)

/-- The two partners of a communication and the rest of the bag. -/
theorem pair_perm {elements : List Pattern} {first second : Nat} (firstBound : first < elements.length)
    (secondBound : second < (elements.eraseIdx first).length) :
    (elements[first] :: (elements.eraseIdx first)[second] :: (elements.eraseIdx first).eraseIdx second).Perm elements :=
  ((List.getElem_cons_eraseIdx_perm secondBound).cons _).trans (List.getElem_cons_eraseIdx_perm firstBound)

/-- **A server communicates through an unfolded copy and stays.** -/
theorem server_comm (subject bound : Name) (continuation : Process) (datum : Name) (others received : Process)
    (receives : Congruent (continuation.substitute bound datum) received) :
    Nonempty (((Process.replicate subject bound continuation ||| Process.output subject datum) ||| others) ⇝
      (received ||| (Process.replicate subject bound continuation ||| others))) := by
  have unfolded : Congruent ((Process.replicate subject bound continuation ||| Process.output subject datum) ||| others)
      (((Process.input subject bound continuation ||| Process.output subject datum) |||
        Process.replicate subject bound continuation) ||| others) := by
    refine Congruent.par ?_ (Congruent.refl _)
    refine (Congruent.par ⟨.replicate_unfold _ _ _⟩ (Congruent.refl _)).trans ?_
    refine (Congruent.assoc _ _ _).trans ?_
    refine (Congruent.par (Congruent.refl _) (Congruent.comm _ _)).trans ?_
    exact (Congruent.assoc _ _ _).symm
  refine reduces_of_congruent unfolded (reduces_parLeft _ (reduces_parLeft _ ⟨.comm _ _ _ _⟩)) ?_
  exact (Congruent.assoc _ _ _).trans (Congruent.par receives (Congruent.refl _))

/-- **A raw step of a named pattern reads back as a reduction** of the named calculus, to a named pattern. -/
theorem rawStep_readBack (avoid : Finset Name) {source target : Pattern} (step : PiRawStep source target) :
    ∀ (env : List Name), Named source = true → source.isWellScopedAt env.length = true →
      (∀ name ∈ freeVars source, name ∈ avoid) →
      Named target = true ∧ Nonempty (readBack avoid env source ⇝ readBack avoid env target) := by
  induction step with
  | @comm elements tail i hi j hj channel binder body datum input output =>
      intro env named wellScoped avoided
      cases tail with
      | some _ => simp [Named] at named
      | none =>
      have allNamed := namedList_iff.mp (by simpa [Named] using named)
      have allScoped := scoped_bag wellScoped
      have allAvoided := avoided_bag avoided
      have perm := pair_perm hi hj
      have inputMember : elements[i] ∈ elements := List.getElem_mem hi
      have outputMember : (elements.eraseIdx i)[j] ∈ elements := List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      have restMember : ∀ element ∈ (elements.eraseIdx i).eraseIdx j, element ∈ elements := fun element member =>
        List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
      have inputNamed := allNamed _ inputMember
      have outputNamed := allNamed _ outputMember
      have inputScoped := allScoped _ inputMember
      have outputScoped := allScoped _ outputMember
      have inputAvoided := allAvoided _ inputMember
      have outputAvoided := allAvoided _ outputMember
      rw [input] at inputNamed inputScoped inputAvoided
      rw [output] at outputNamed outputScoped outputAvoided
      simp only [Named, Bool.and_eq_true] at inputNamed outputNamed
      have bodyScoped := scoped_lambda (scoped_binary inputScoped).2
      have datumScoped := (scoped_binary outputScoped).2
      have bodyAvoided := avoided_lambda (avoided_binary inputAvoided).2
      have datumAvoided := (avoided_binary outputAvoided).2
      have received := instantiate_facts inputNamed.2 bodyScoped bodyAvoided outputNamed.2 datumScoped datumAvoided
      refine ⟨?_, ?_⟩
      · simp only [Named]
        apply namedList_iff.mpr
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact received.1
        · exact allNamed _ (restMember _ inRest)
      · set rest := (elements.eraseIdx i).eraseIdx j
        rw [readBack_bag, readBack_bag]
        have before : Congruent (parList (elements.map (readBack avoid env)))
            ((readBack avoid env elements[i] ||| readBack avoid env (elements.eraseIdx i)[j]) |||
              parList (rest.map (readBack avoid env))) := by
          refine (parList_perm (perm.symm.map _)).trans ?_
          simpa [parList] using (Congruent.assoc _ _ _).symm
        refine reduces_of_congruent before ?_ (Congruent.refl _)
        rw [input, output]
        simp only [readBack, List.map_cons, parList]
        exact reduces_of_congruent (Congruent.refl _)
          (reduces_parLeft _ ⟨.comm _ _ _ _⟩)
          (Congruent.par (readBack_receive avoid inputNamed.2 bodyScoped bodyAvoided outputNamed.2 datumScoped
            datumAvoided) (Congruent.refl _))
  | @par elements tail i hi target inner recurse =>
      intro env named wellScoped avoided
      cases tail with
      | some _ => simp [Named] at named
      | none =>
      have allNamed := namedList_iff.mp (by simpa [Named] using named)
      have allScoped := scoped_bag wellScoped
      have allAvoided := avoided_bag avoided
      have member : elements[i] ∈ elements := List.getElem_mem hi
      obtain ⟨targetNamed, stepped⟩ := recurse env (allNamed _ member) (allScoped _ member) (allAvoided _ member)
      refine ⟨?_, ?_⟩
      · simp only [Named]
        apply namedList_iff.mpr
        intro element inside
        rcases List.mem_cons.mp inside with rfl | inRest
        · exact targetNamed
        · exact allNamed _ (List.mem_of_mem_eraseIdx inRest)
      · rw [readBack_bag, readBack_bag]
        refine reduces_of_congruent (parList_perm ((List.getElem_cons_eraseIdx_perm hi).symm.map _)) ?_
          (Congruent.refl _)
        simpa [parList] using reduces_parLeft _ stepped
  | @res binder source target inner recurse =>
      intro env named wellScoped avoided
      simp only [Named] at named
      obtain ⟨targetNamed, stepped⟩ := recurse (fresh (avoid ∪ env.toFinset) :: env) named
        (by simpa using scoped_lambda (scoped_unary wellScoped)) (avoided_lambda (avoided_unary avoided))
      refine ⟨by simpa [Named] using targetNamed, ?_⟩
      simp only [readBack]
      exact stepped.map fun step => .res _ _ _ step

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
