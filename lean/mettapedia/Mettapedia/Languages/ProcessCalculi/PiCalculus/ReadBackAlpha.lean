import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBack

/-!
# Read-backs up to α

A named pattern reads back with names of its own choice (`readBack`). Other fresh names give a structurally congruent
process:

- two read-backs are congruent when their translations agree (`congruent_of_translation`);
- a restriction reads back at any fresh name (`readBack_nu`), and a block of restrictions at any fresh, distinct names
  (`readBack_restricts`, `readBack_toPattern`);
- a restriction no component uses is garbage (`nu_garbage`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock piBlockSignature)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero substituteList_eq_map
  substitute_comp)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars closeFVar freeVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piToPattern piPar piComponents
  freeVars_piToPattern)
open Mettapedia.FreshString (fresh fresh_not_mem)

/-! ## Substitutions that agree on the free variables -/

theorem lift_congr_free {first second : Assignment} {arity index : Nat}
    (agree : arity ≤ index → first (index - arity) = second (index - arity)) :
    lift arity first index = lift arity second index := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  by_cases inside : index < arity
  · simp [inside]
  · simp only [inside, if_false]
    rw [agree (by omega)]

/-- **Substitutions agreeing on the free variables of a pattern substitute it alike.** -/
theorem substitute_congr_free (pattern : Pattern) : ∀ {first second : Assignment},
    (∀ index, FreeIn index pattern → first index = second index) →
      substitute first pattern = substitute second pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro first second agree; exact agree index (.bvar index)
  | hfvar => intros; rfl
  | happly constructor arguments recurse =>
      intro first second agree
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun argument member =>
        recurse argument member fun index free => agree index (.apply member free)
  | hlambda binder body recurse =>
      intro first second agree
      simp only [substitute]
      congr 1
      exact recurse fun index free => lift_congr_free fun outside =>
        agree _ (.lambda (by rwa [Nat.sub_add_cancel outside]))
  | hmultiLambda arity binders body recurse =>
      intro first second agree
      simp only [substitute]
      congr 1
      exact recurse fun index free => lift_congr_free fun outside =>
        agree _ (.multiLambda (by rwa [Nat.sub_add_cancel outside]))
  | hsubst body replacement recurseBody recurseReplacement =>
      intro first second agree
      simp only [substitute]
      congr 1
      · exact recurseBody fun index free => lift_congr_free fun outside =>
          agree _ (.substBody (by rwa [Nat.sub_add_cancel outside]))
      · exact recurseReplacement fun index free => agree index (.substReplacement free)
  | hcollection kind elements rest recurse =>
      intro first second agree
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun element member =>
        recurse element member fun index free => agree index (.element member free)

theorem openWith_substitute (env : List Name) (assignment : Assignment) (pattern : Pattern) :
    openWith env (substitute assignment pattern) = substitute (fun index => openWith env (assignment index)) pattern :=
  substitute_comp _ _ _

/-- **Opening a renamed pattern** is opening it at the renamed names. -/
theorem openWith_rename {env env' : List Name} (relabel : Nat → Nat) (pattern : Pattern)
    (agree : ∀ index, FreeIn index pattern → envAssignment env (relabel index) = envAssignment env' index) :
    openWith env (substitute (fun index => .bvar (relabel index)) pattern) = openWith env' pattern := by
  rw [openWith_substitute]
  exact substitute_congr_free pattern fun index free => by simpa [openWith, substitute] using agree index free

/-! ## Translations of read-backs -/

/-- What a read-back needs of a pattern: named, in scope, its free names avoided. -/
structure Readable (avoid : Finset Name) (depth : Nat) (pattern : Pattern) : Prop where
  named : Named pattern = true
  inScope : pattern.isWellScopedAt depth = true
  avoided : ∀ name ∈ freeVars pattern, name ∈ avoid

theorem Readable.depth {avoid : Finset Name} {depth depth' : Nat} {pattern : Pattern}
    (readable : Readable avoid depth pattern) (same : depth = depth') : Readable avoid depth' pattern :=
  same ▸ readable

theorem Readable.translation {avoid : Finset Name} {env : List Name} {pattern : Pattern}
    (readable : Readable avoid env.length pattern) :
    piToPattern (readBack avoid env pattern) = openWith env (normal pattern) :=
  piToPattern_readBack avoid _ env (Nat.lt_succ_self _) readable.named readable.inScope readable.avoided

theorem Readable.normal_scoped {avoid : Finset Name} {depth : Nat} {pattern : Pattern}
    (readable : Readable avoid depth pattern) : (normal pattern).isWellScopedAt depth = true :=
  (normal_facts _ (Nat.lt_succ_self _) readable.named).1 _ readable.inScope

theorem Readable.normal_absent {avoid : Finset Name} {depth : Nat} {pattern : Pattern}
    (readable : Readable avoid depth pattern) {name : Name} (notAvoid : name ∉ avoid) :
    name ∉ freeVars (normal pattern) := fun free =>
  notAvoid (readable.avoided _ ((normal_facts _ (Nat.lt_succ_self _) readable.named).2 _ free))

/-- **Two read-backs whose translations agree are congruent.** -/
theorem congruent_of_translation {avoid avoid' : Finset Name} {env env' : List Name} {first second : Pattern}
    (firstReadable : Readable avoid env.length first) (secondReadable : Readable avoid' env'.length second)
    (same : openWith env (normal first) = openWith env' (normal second)) :
    Congruent (readBack avoid env first) (readBack avoid' env' second) :=
  congruent_of_piToPattern_eq _ _ _ le_rfl (by rw [firstReadable.translation, secondReadable.translation, same])

/-- **The free names of a read-back** are avoided or given. -/
theorem Readable.freeNames {avoid : Finset Name} {env : List Name} {pattern : Pattern}
    (readable : Readable avoid env.length pattern) {name : Name}
    (free : name ∈ (readBack avoid env pattern).freeNames) : name ∈ avoid ∨ name ∈ env := by
  rw [← freeVars_piToPattern, readable.translation, openWith] at free
  rcases freeVars_substitute_variables _ (envAssignment_variables env) free with here | ⟨index, found⟩
  · exact .inl (readable.avoided _ ((normal_facts _ (Nat.lt_succ_self _) readable.named).2 _ here))
  · right
    unfold envAssignment at found
    split at found
    · cases found
      exact List.getElem_mem _
    · cases found

/-! ## Restrictions at any fresh names -/

/-- **A restriction reads back at any fresh name.** -/
theorem readBack_nu {avoid : Finset Name} {env : List Name} {binder : Option String} {body : Pattern} {name : Name}
    (readable : Readable avoid (env.length + 1) body) (notAvoid : name ∉ avoid) (notEnv : name ∉ env) :
    Congruent (readBack avoid env (.apply "PiNu" [.lambda binder body]))
      (.nu name (readBack avoid (name :: env) body)) := by
  apply congruent_of_piToPattern_eq _ _ _ le_rfl
  have chosenFresh := fresh_not_mem (avoid ∪ env.toFinset)
  simp only [readBack, piToPattern]
  generalize fresh (avoid ∪ env.toFinset) = chosen at chosenFresh ⊢
  have chosenAvoid : chosen ∉ avoid := fun inside => chosenFresh (Finset.mem_union_left _ inside)
  have chosenEnv : chosen ∉ env := fun inside =>
    chosenFresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
  have readable' : ∀ other : Name, Readable avoid (other :: env).length body := fun _ => by simpa using readable
  rw [(readable' chosen).translation, (readable' name).translation, openWith, openWith]
  have inScope : (normal body).isWellScopedAt (0 + env.length + 1) = true := by simpa using readable.normal_scoped
  have chosenClosed := closeFVar_open chosenEnv (normal body) 0 (readable.normal_absent chosenAvoid) inScope
  have nameClosed := closeFVar_open notEnv (normal body) 0 (readable.normal_absent notAvoid) inScope
  simp only [lift_zero] at chosenClosed nameClosed
  rw [chosenClosed, nameClosed]

theorem named_restricts : ∀ (count : Nat) (body : Pattern), Named (Prenex.restricts piBlock count body) = Named body
  | 0, _ => rfl
  | count + 1, body => by simp [Prenex.restricts, Named, named_restricts count body]

theorem scoped_restricts : ∀ (count : Nat) (body : Pattern) (depth : Nat),
    (Prenex.restricts piBlock count body).isWellScopedAt depth = body.isWellScopedAt (depth + count)
  | 0, _, _ => rfl
  | count + 1, body, depth => by
      rw [show depth + (count + 1) = (depth + 1) + count by omega, ← scoped_restricts count body (depth + 1)]
      simp [Prenex.restricts, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

theorem freeVars_restricts : ∀ (count : Nat) (body : Pattern),
    freeVars (Prenex.restricts piBlock count body) = freeVars body
  | 0, _ => rfl
  | count + 1, body => by simp [Prenex.restricts, freeVars, freeVars_restricts count body]

theorem Readable.restricts {avoid : Finset Name} {depth : Nat} {body : Pattern} (count : Nat)
    (readable : Readable avoid (depth + count) body) : Readable avoid depth (Prenex.restricts piBlock count body) :=
  ⟨by rw [named_restricts]; exact readable.named, by rw [scoped_restricts]; exact readable.inScope,
    fun name free => readable.avoided name (by rwa [freeVars_restricts] at free)⟩

/-- **A block of restrictions reads back at any fresh, distinct names.** -/
theorem readBack_restricts {avoid : Finset Name} : ∀ (names : List Name) {env : List Name} {body : Pattern},
    Readable avoid (env.length + names.length) body → names.Nodup → (∀ name ∈ names, name ∉ avoid ∧ name ∉ env) →
      Congruent (readBack avoid env (Prenex.restricts piBlock names.length body))
        (nuList names (readBack avoid (names.reverse ++ env) body))
  | [], env, body, _, _, _ => by simpa [Prenex.restricts, nuList] using Congruent.refl (readBack avoid env body)
  | name :: names, env, body, readable, nodup, fresh => by
      obtain ⟨notMember, rest⟩ := List.nodup_cons.mp nodup
      have inner : Readable avoid (env.length + 1) (Prenex.restricts piBlock names.length body) :=
        Readable.restricts names.length (readable.depth (by simp; omega))
      rw [List.length_cons, Prenex.restricts_succ]
      refine (readBack_nu inner (fresh name List.mem_cons_self).1 (fresh name List.mem_cons_self).2).trans ?_
      simp only [nuList]
      refine Congruent.nu name ?_
      have restFresh : ∀ other ∈ names, other ∉ avoid ∧ other ∉ name :: env := fun other member =>
        ⟨(fresh other (List.mem_cons_of_mem _ member)).1, by
          simp only [List.mem_cons, not_or]
          exact ⟨fun same => notMember (same ▸ member), (fresh other (List.mem_cons_of_mem _ member)).2⟩⟩
      have recursive := readBack_restricts names (env := name :: env) (body := body)
        (readable.depth (by simp; omega)) rest restFresh
      simpa [List.reverse_cons, List.append_assoc] using recursive

/-- **A restriction no component uses is garbage.** -/
theorem nu_garbage {name : Name} {process : Process} (absent : name ∉ process.freeNames) :
    Congruent (.nu name process) process :=
  Congruent.trans (Congruent.nu name (Congruent.nilLeft process).symm)
    (Congruent.trans ⟨.nu_par name .nil process absent⟩
      ((Congruent.par ⟨.nu_nil name⟩ (Congruent.refl process)).trans (Congruent.nilLeft process)))

/-! ## Blocks -/

theorem named_body : ∀ {components : List Pattern}, (∀ component ∈ components, Named component = true) →
    Named (Prenex.body piBlock components) = true
  | [], _ => rfl
  | [component], all => all component List.mem_cons_self
  | first :: second :: rest, all => by
      simp only [Prenex.body, Named]
      exact namedList_iff.mpr all

theorem scoped_body {depth : Nat} : ∀ {components : List Pattern},
    (∀ component ∈ components, component.isWellScopedAt depth = true) →
      (Prenex.body piBlock components).isWellScopedAt depth = true
  | [], _ => rfl
  | [component], all => all component List.mem_cons_self
  | first :: second :: rest, all => by
      simpa only [Prenex.body, Pattern.isWellScopedAt,
        Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] using all

theorem avoided_body {avoid : Finset Name} : ∀ {components : List Pattern},
    (∀ component ∈ components, ∀ name ∈ freeVars component, name ∈ avoid) →
      ∀ name ∈ freeVars (Prenex.body piBlock components), name ∈ avoid
  | [], _ => by simp [Prenex.body, freeVars]
  | [component], all => all component List.mem_cons_self
  | first :: second :: rest, all => by
      intro name free
      simp only [Prenex.body, freeVars, List.mem_flatMap] at free
      obtain ⟨component, member, inside⟩ := free
      exact all component member name inside

theorem Readable.body {avoid : Finset Name} {depth : Nat} {components : List Pattern}
    (readable : ∀ component ∈ components, Readable avoid depth component) :
    Readable avoid depth (Prenex.body piBlock components) :=
  ⟨named_body fun component member => (readable component member).named,
    scoped_body fun component member => (readable component member).inScope,
    avoided_body fun component member => (readable component member).avoided⟩

/-- **The bag of a block's components reads back as their parallel composition.** -/
theorem readBack_body (avoid : Finset Name) (env : List Name) : ∀ components : List Pattern,
    Congruent (readBack avoid env (Prenex.body piBlock components)) (parList (components.map (readBack avoid env)))
  | [] => by simpa [Prenex.body, readBack, parList] using Congruent.refl Process.nil
  | [component] => by simpa [Prenex.body, parList] using (Congruent.nilRight (readBack avoid env component)).symm
  | first :: second :: rest => by
      simp only [Prenex.body]
      rw [readBack_bag]
      exact Congruent.refl _

/-- **A block reads back at any fresh, distinct names** as their restriction over its components. -/
theorem readBack_toPattern {avoid : Finset Name} {env : List Name} {components : List Pattern} (names : List Name)
    (readable : ∀ component ∈ components, Readable avoid (env.length + names.length) component)
    (nodup : names.Nodup) (fresh : ∀ name ∈ names, name ∉ avoid ∧ name ∉ env) :
    Congruent (readBack avoid env (Prenex.toPattern piBlock ⟨names.length, components⟩))
      (nuList names (parList (components.map (readBack avoid (names.reverse ++ env))))) :=
  (readBack_restricts names (Readable.body readable) nodup fresh).trans
    (nuList_congruent names (readBack_body avoid _ components))

/-! ## Free indices of named patterns and their read-backs -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (freeIn_apply freeIn_lambda freeIn_collection)

theorem freeIn_component {index : Nat} {pattern element : Pattern} (member : element ∈ piComponents pattern)
    (free : FreeIn index element) : FreeIn index pattern := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp only [piComponents, List.mem_singleton] at member
      all_goals first | (subst member; exact free) | exact .element member free
  | _ => simp only [piComponents, List.mem_singleton] at member; subst member; exact free

theorem freeIn_piPar {index : Nat} {first second : Pattern} (free : FreeIn index (piPar first second)) :
    FreeIn index first ∨ FreeIn index second := by
  rw [Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piPar_components] at free
  obtain ⟨element, member, inside⟩ := freeIn_collection.mp free
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact .inl (freeIn_component inFirst inside)
  · exact .inr (freeIn_component inSecond inside)

theorem freeIn_piParList {index : Nat} : ∀ {patterns : List Pattern}, FreeIn index (piParList patterns) →
    ∃ pattern ∈ patterns, FreeIn index pattern
  | [], free => by
      obtain ⟨_, member, _⟩ := freeIn_apply.mp free
      simp at member
  | first :: rest, free => by
      rcases freeIn_piPar free with here | there
      · exact ⟨first, List.mem_cons_self, here⟩
      · obtain ⟨pattern, member, inside⟩ := freeIn_piParList there
        exact ⟨pattern, List.mem_cons_of_mem _ member, inside⟩

/-- **The normal form has no free index the pattern lacks.** -/
theorem freeIn_normal : ∀ (size : Nat) {pattern : Pattern}, sizeOf pattern < size → Named pattern = true →
    ∀ {index : Nat}, FreeIn index (normal pattern) → FreeIn index pattern
  | 0, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, pattern, small, named => by
      rcases named_cases named with rfl | ⟨elements, rfl, elementsNamed⟩ | ⟨binder, body, rfl, bodyNamed⟩ |
        ⟨channel, binder, body, rfl, _, bodyNamed⟩ | ⟨channel, binder, body, rfl, _, bodyNamed⟩ |
        ⟨channel, datum, rfl, _, _⟩
      · intro free; simpa [normal] using free
      · intro free
        simp only [normal, normalList_eq_map] at free
        obtain ⟨normalized, member, inside⟩ := freeIn_piParList free
        obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
        exact .element elementMember (freeIn_normal size (by
          have := List.sizeOf_lt_of_mem elementMember
          simp only [Pattern.collection.sizeOf_spec] at small
          omega) (namedList_iff.mp elementsNamed element elementMember) inside)
      · intro free
        simp only [normal] at free
        obtain ⟨argument, member, inside⟩ := freeIn_apply.mp free
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst member
        exact .apply List.mem_cons_self (.lambda (freeIn_normal size (by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega) bodyNamed (freeIn_lambda.mp inside)))
      · intro free
        simp only [normal] at free
        obtain ⟨argument, member, inside⟩ := freeIn_apply.mp free
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .apply List.mem_cons_self inside
        · exact .apply (List.mem_cons_of_mem _ List.mem_cons_self) (.lambda (freeIn_normal size (by
            simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
            omega) bodyNamed (freeIn_lambda.mp inside)))
      · -- a server, the replication of an input
        intro free
        simp only [normal] at free
        obtain ⟨inputPart, inputMember, inputInside⟩ := freeIn_apply.mp free
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inputMember
        subst inputMember
        obtain ⟨argument, member, inside⟩ := freeIn_apply.mp inputInside
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        refine .apply List.mem_cons_self ?_
        rcases member with rfl | rfl
        · exact .apply List.mem_cons_self inside
        · exact .apply (List.mem_cons_of_mem _ List.mem_cons_self) (.lambda (freeIn_normal size (by
            simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
            omega) bodyNamed (freeIn_lambda.mp inside)))
      · intro free
        simpa [normal] using free

theorem VariableAssignment.lift_fvar_at {assignment : Assignment} (onVariables : VariableAssignment assignment)
    {arity index : Nat} {name : String}
    (found : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift arity assignment index = .fvar name) :
    arity ≤ index ∧ assignment (index - arity) = .fvar name := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift at found
  split at found
  · cases found
  · refine ⟨by omega, ?_⟩
    have named := onVariables (index - arity)
    generalize assignment (index - arity) = value at found named ⊢
    cases value <;> simp_all [isName, liftBVars]

/-- **A free name of a pattern with variables substituted** is free in it, or substituted for a free variable. -/
theorem freeVars_substitute_free (pattern : Pattern) : ∀ {assignment : Assignment},
    VariableAssignment assignment → ∀ {name : String}, name ∈ freeVars (substitute assignment pattern) →
      name ∈ freeVars pattern ∨ ∃ index, FreeIn index pattern ∧ assignment index = .fvar name := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro assignment onVariables name free
      simp only [substitute] at free
      have named := onVariables index
      refine .inr ⟨index, .bvar index, ?_⟩
      generalize assignment index = value at free named ⊢
      cases value <;> simp_all [isName, freeVars]
  | hfvar other =>
      intro assignment _ name free
      exact .inl (by simpa [substitute] using free)
  | happly constructor arguments recurse =>
      intro assignment onVariables name free
      simp only [substitute, substituteList_eq_map, freeVars, List.mem_flatMap, List.mem_map] at free
      obtain ⟨_, ⟨argument, member, rfl⟩, inside⟩ := free
      rcases recurse argument member onVariables inside with here | ⟨index, freeIndex, found⟩
      · exact .inl (by simp only [freeVars, List.mem_flatMap]; exact ⟨argument, member, here⟩)
      · exact .inr ⟨index, .apply member freeIndex, found⟩
  | hlambda binder body recurse =>
      intro assignment onVariables name free
      simp only [substitute, freeVars] at free
      rcases recurse (onVariables.lift 1) free with here | ⟨index, freeIndex, found⟩
      · exact .inl (by simpa [freeVars] using here)
      · obtain ⟨outside, original⟩ := onVariables.lift_fvar_at found
        exact .inr ⟨index - 1, .lambda (by rwa [Nat.sub_add_cancel outside]), original⟩
  | hmultiLambda arity binders body recurse =>
      intro assignment onVariables name free
      simp only [substitute, freeVars] at free
      rcases recurse (onVariables.lift arity) free with here | ⟨index, freeIndex, found⟩
      · exact .inl (by simpa [freeVars] using here)
      · obtain ⟨outside, original⟩ := onVariables.lift_fvar_at found
        exact .inr ⟨index - arity, .multiLambda (by rwa [Nat.sub_add_cancel outside]), original⟩
  | hsubst body replacement recurseBody recurseReplacement =>
      intro assignment onVariables name free
      simp only [substitute, freeVars, List.mem_append] at free
      rcases free with free | free
      · rcases recurseBody (onVariables.lift 1) free with here | ⟨index, freeIndex, found⟩
        · exact .inl (by simp [freeVars, here])
        · obtain ⟨outside, original⟩ := onVariables.lift_fvar_at found
          exact .inr ⟨index - 1, .substBody (by rwa [Nat.sub_add_cancel outside]), original⟩
      · rcases recurseReplacement onVariables free with here | ⟨index, freeIndex, found⟩
        · exact .inl (by simp [freeVars, here])
        · exact .inr ⟨index, .substReplacement freeIndex, found⟩
  | hcollection kind elements rest recurse =>
      intro assignment onVariables name free
      simp only [substitute, substituteList_eq_map, freeVars, List.mem_flatMap, List.mem_map] at free
      obtain ⟨_, ⟨element, member, rfl⟩, inside⟩ := free
      rcases recurse element member onVariables inside with here | ⟨index, freeIndex, found⟩
      · exact .inl (by simp only [freeVars, List.mem_flatMap]; exact ⟨element, member, here⟩)
      · exact .inr ⟨index, .element member freeIndex, found⟩

/-- **A free name of a read-back** is avoided, or the name given to a free variable of the pattern. -/
theorem Readable.freeName_index {avoid : Finset Name} {env : List Name} {pattern : Pattern}
    (readable : Readable avoid env.length pattern) {name : Name}
    (free : name ∈ (readBack avoid env pattern).freeNames) :
    name ∈ avoid ∨ ∃ index, FreeIn index pattern ∧ ∃ inside : index < env.length, env[index] = name := by
  rw [← freeVars_piToPattern, readable.translation, openWith] at free
  rcases freeVars_substitute_free _ (envAssignment_variables env) free with here | ⟨index, freeIndex, found⟩
  · exact .inl (readable.avoided _ ((normal_facts _ (Nat.lt_succ_self _) readable.named).2 _ here))
  · right
    refine ⟨index, freeIn_normal _ (Nat.lt_succ_self _) readable.named freeIndex, ?_⟩
    unfold envAssignment at found
    split at found
    · rename_i inside
      cases found
      exact ⟨inside, rfl⟩
    · cases found

/-! ## Renaming the variables of a read-back -/

/-- **Shifting past a middle segment of names**: the variables of the front keep their names, the others skip the
middle. -/
theorem envAssignment_shift (front middle back : List Name) (index : Nat) :
    envAssignment (front ++ middle ++ back) (if index < front.length then index else index + middle.length) =
      envAssignment (front ++ back) index := by
  unfold envAssignment
  by_cases inFront : index < front.length
  · simp only [inFront, if_true, List.length_append]
    rw [dif_pos (by omega), dif_pos (by omega)]
    simp [List.getElem_append_left inFront]
  · simp only [inFront, if_false, List.length_append]
    by_cases inBack : index < front.length + back.length
    · rw [dif_pos (by omega), dif_pos (by omega)]
      congr 1
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
      simp only [List.length_append]
      congr 1
      omega
    · rw [dif_neg (by omega), dif_neg (by omega)]
      congr 1
      omega

theorem renaming_variables (relabel : Nat → Nat) : VariableAssignment (fun index => .bvar (relabel index)) :=
  fun _ => rfl

/-- **A renamed named pattern** is named, its free names kept, in the scope of its renamed free variables. -/
theorem Readable.rename {avoid : Finset Name} {depth depth' : Nat} {pattern : Pattern} (relabel : Nat → Nat)
    (readable : Readable avoid depth pattern) (below : ∀ index, FreeIn index pattern → relabel index < depth') :
    Readable avoid depth' (rename relabel pattern) := by
  refine ⟨(normal_substitute _ (renaming_variables relabel) (Nat.lt_succ_self _) readable.named).1, ?_, ?_⟩
  · apply scoped_of_freeIn
    intro index free
    obtain ⟨original, originalFree, image⟩ := freeIn_substitute pattern free
    rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_bvar] at image
    rw [image]
    exact below original originalFree
  · intro name free
    rcases freeVars_substitute_free pattern (renaming_variables relabel) free with here | ⟨_, _, found⟩
    · exact readable.avoided name here
    · cases found

/-- **Reading back a renamed pattern is reading it back at the renamed names.** -/
theorem readBack_rename {avoid : Finset Name} {env env' : List Name} {pattern : Pattern} (relabel : Nat → Nat)
    (readable : Readable avoid env'.length pattern) (below : ∀ index, FreeIn index pattern → relabel index < env.length)
    (agree : ∀ index, FreeIn index pattern → envAssignment env (relabel index) = envAssignment env' index) :
    Congruent (readBack avoid env (rename relabel pattern)) (readBack avoid env' pattern) := by
  apply congruent_of_translation (readable.rename relabel below) readable
  rw [rename, (normal_substitute _ (renaming_variables relabel) (Nat.lt_succ_self _) readable.named).2]
  exact openWith_rename relabel (normal pattern) fun index free =>
    agree index (freeIn_normal _ (Nat.lt_succ_self _) readable.named free)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
