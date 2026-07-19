import Mettapedia.Languages.MeTTa.HE.HumanTypePresentation

/-!
# Normal finite type substitutions

This module records the closure facts that make the finite presentation
carrier compositional.  A normal substitution is key-unique and none of its
stored values mentions a key assigned by the same substitution.  Consequently
one-pass application removes every assigned variable, and the declarative
`bind` operation preserves normality when its resolved right-hand side passes
the occurs check.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentation.TypeSubst

theorem lookup_eq_some_mem
    {substitution : TypeSubst} {name : String} {value : Atom}
    (lookup : substitution.lookup name = some value) :
    (name, value) ∈ substitution := by
  induction substitution with
  | nil => simp [TypeSubst.lookup] at lookup
  | cons head tail ih =>
      rcases head with ⟨key, stored⟩
      by_cases hkey : name = key
      · subst key
        simp [TypeSubst.lookup] at lookup
        subst stored
        simp
      · simp [TypeSubst.lookup, hkey] at lookup
        exact List.mem_cons_of_mem _ (ih lookup)

theorem lookup_eq_none_of_not_mem_keys
    {substitution : TypeSubst} {name : String}
    (absent : name ∉ substitution.keys) :
    substitution.lookup name = none := by
  induction substitution with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      simp only [keys, List.map_cons, List.mem_cons, not_or] at absent
      simp [TypeSubst.lookup, absent.1, ih absent.2]

theorem not_mem_keys_of_lookup_eq_none
    {substitution : TypeSubst} {name : String}
    (lookup : substitution.lookup name = none) :
    name ∉ substitution.keys := by
  induction substitution with
  | nil => simp [keys]
  | cons head tail ih =>
      rcases head with ⟨key, stored⟩
      by_cases hkey : name = key
      · subst key
        simp [TypeSubst.lookup] at lookup
      · simp [TypeSubst.lookup, hkey] at lookup
        simpa [keys, hkey] using ih lookup

private theorem typeVars_mem_typeVarsList_of_mem
    {atom : Atom} {atoms : List Atom} (hatom : atom ∈ atoms) :
    ∀ name, name ∈ typeVars atom → name ∈ typeVarsList atoms := by
  induction atoms with
  | nil => simp at hatom
  | cons head tail ih =>
      simp only [List.mem_cons] at hatom
      rcases hatom with rfl | htail
      · intro name hname
        simp [typeVarsList, hname]
      · intro name hname
        simp only [typeVarsList, List.mem_append]
        exact Or.inr (ih htail name hname)

private theorem exists_typeVars_of_mem_typeVarsList :
    ∀ {atoms : List Atom} {name : String},
      name ∈ typeVarsList atoms →
        ∃ atom ∈ atoms, name ∈ typeVars atom := by
  intro atoms
  induction atoms with
  | nil => simp [typeVarsList]
  | cons head tail ih =>
      intro name hname
      simp only [typeVarsList, List.mem_append] at hname
      rcases hname with hhead | htail
      · exact ⟨head, by simp, hhead⟩
      · obtain ⟨atom, hatom, hvar⟩ := ih htail
        exact ⟨atom, by simp [hatom], hvar⟩

private theorem atom_size_pos (atom : Atom) : 0 < sizeOf atom := by
  cases atom <;> simp

private theorem atom_size_lt_of_mem {atom : Atom} :
    ∀ {atoms : List Atom}, atom ∈ atoms → sizeOf atom < sizeOf atoms
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp
        omega
      · have hlt := atom_size_lt_of_mem htail
        simp
        omega

/-- Applying a normal substitution leaves no variable assigned by that
substitution in the result. -/
theorem Normal.apply_variable_not_key
    {substitution : TypeSubst} (normal : substitution.Normal) :
    ∀ atom name, name ∈ typeVars (substitution.apply atom) →
      name ∉ substitution.keys := by
  suffices key : ∀ n (atom : Atom), sizeOf atom ≤ n →
      ∀ name, name ∈ typeVars (substitution.apply atom) →
        name ∉ substitution.keys by
    intro atom name hname
    exact key (sizeOf atom) atom le_rfl name hname
  intro n
  induction n with
  | zero =>
      intro atom hsize
      exact absurd hsize (by have := atom_size_pos atom; omega)
  | succ n ih =>
      intro atom hsize name hname
      cases atom with
      | symbol symbol => simp [TypeSubst.apply, typeVars] at hname
      | grounded value => simp [TypeSubst.apply, typeVars] at hname
      | var variableName =>
          simp only [TypeSubst.apply] at hname
          cases hlookup : substitution.lookup variableName with
          | none =>
              simp [hlookup, Option.getD, typeVars] at hname
              subst name
              exact not_mem_keys_of_lookup_eq_none hlookup
          | some value =>
              simp [hlookup, Option.getD] at hname
              exact normal.2 variableName value
                (lookup_eq_some_mem hlookup) name hname
      | expression atoms =>
          simp only [TypeSubst.apply, typeVars] at hname
          obtain ⟨appliedChild, happliedChild, hchildName⟩ :=
            exists_typeVars_of_mem_typeVarsList hname
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp happliedChild
          apply ih child
          · have hlt := atom_size_lt_of_mem hchild
            have hatoms : sizeOf atoms ≤ n := by
              simp at hsize
              omega
            omega
          · simpa using hchildName

/-- A one-pass substitution leaves an atom unchanged when none of that
atom's variables is assigned. -/
theorem apply_eq_self_of_variables_not_keys
    (substitution : TypeSubst) :
    ∀ atom,
      (∀ name, name ∈ typeVars atom → name ∉ substitution.keys) →
      substitution.apply atom = atom := by
  suffices key : ∀ n (atom : Atom), sizeOf atom ≤ n →
      (∀ name, name ∈ typeVars atom → name ∉ substitution.keys) →
      substitution.apply atom = atom by
    intro atom avoids
    exact key (sizeOf atom) atom le_rfl avoids
  intro n
  induction n with
  | zero =>
      intro atom hsize
      exact absurd hsize (by have := atom_size_pos atom; omega)
  | succ n ih =>
      intro atom hsize avoids
      cases atom with
      | symbol symbol => simp [TypeSubst.apply]
      | grounded value => simp [TypeSubst.apply]
      | var variableName =>
          have habsent : variableName ∉ substitution.keys :=
            avoids variableName (by simp [typeVars])
          simp [TypeSubst.apply,
            lookup_eq_none_of_not_mem_keys habsent, Option.getD]
      | expression atoms =>
          simp only [TypeSubst.apply, Atom.expression.injEq]
          calc
            List.map substitution.apply atoms = List.map id atoms := by
              apply List.map_congr_left
              intro child hchild
              apply ih child
              · have hlt := atom_size_lt_of_mem hchild
                have hatoms : sizeOf atoms ≤ n := by
                  simp at hsize
                  omega
                omega
              · intro name hname
                exact avoids name
                  (typeVars_mem_typeVarsList_of_mem hchild name hname)
            _ = atoms := List.map_id atoms

/-- Normal one-pass substitutions are idempotent on every atom. -/
theorem Normal.apply_idempotent
    {substitution : TypeSubst} (normal : substitution.Normal)
    (atom : Atom) :
    substitution.apply (substitution.apply atom) =
      substitution.apply atom := by
  apply apply_eq_self_of_variables_not_keys
  exact normal.apply_variable_not_key atom

/-- Homomorphic application preserves avoidance of any external finite name
set when both the source atom and every stored substitution value avoid it. -/
theorem apply_variable_avoids
    {substitution : TypeSubst} {forbidden : List String}
    (valuesAvoid : ∀ key value, (key, value) ∈ substitution →
      ∀ name, name ∈ typeVars value → name ∉ forbidden) :
    ∀ atom,
      (∀ name, name ∈ typeVars atom → name ∉ forbidden) →
      ∀ name, name ∈ typeVars (substitution.apply atom) →
        name ∉ forbidden := by
  suffices key : ∀ n (atom : Atom), sizeOf atom ≤ n →
      (∀ name, name ∈ typeVars atom → name ∉ forbidden) →
      ∀ name, name ∈ typeVars (substitution.apply atom) →
        name ∉ forbidden by
    intro atom avoids name hname
    exact key (sizeOf atom) atom le_rfl avoids name hname
  intro n
  induction n with
  | zero =>
      intro atom hsize
      exact absurd hsize (by have := atom_size_pos atom; omega)
  | succ n ih =>
      intro atom hsize avoids name hname
      cases atom with
      | symbol symbol => simp [TypeSubst.apply, typeVars] at hname
      | grounded value => simp [TypeSubst.apply, typeVars] at hname
      | var variableName =>
          simp only [TypeSubst.apply] at hname
          cases hlookup : substitution.lookup variableName with
          | none =>
              simp [hlookup, Option.getD, typeVars] at hname
              subst name
              exact avoids variableName (by simp [typeVars])
          | some value =>
              simp [hlookup, Option.getD] at hname
              exact valuesAvoid variableName value
                (lookup_eq_some_mem hlookup) name hname
      | expression atoms =>
          simp only [TypeSubst.apply, typeVars] at hname
          obtain ⟨appliedChild, happliedChild, hchildName⟩ :=
            exists_typeVars_of_mem_typeVarsList hname
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp happliedChild
          apply ih child
          · have hlt := atom_size_lt_of_mem hchild
            have hatoms : sizeOf atoms ≤ n := by
              simp at hsize
              omega
            omega
          · intro candidate hcandidate
            exact avoids candidate
              (typeVars_mem_typeVarsList_of_mem
                hchild candidate hcandidate)
          · exact hchildName

@[simp] theorem keys_erase (substitution : TypeSubst) (name : String) :
    (substitution.erase name).keys =
      substitution.keys.filter (fun key => key != name) := by
  unfold erase keys
  induction substitution with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      by_cases hkey : key = name
      · subst key
        simp [ih]
      · simp [hkey, ih]

@[simp] theorem keys_bind
    (substitution : TypeSubst) (name : String) (value : Atom) :
    (substitution.bind name value).keys =
      name :: substitution.keys.filter (fun key => key != name) := by
  unfold bind
  simp only [keys, List.map_cons, List.map_map]
  congr 1
  calc
    List.map
        (Prod.fst ∘ fun entry =>
          (entry.1, applyAssignment name (substitution.apply value) entry.2))
        (substitution.erase name) =
        (substitution.erase name).keys := by
          apply List.map_congr_left
          intro entry _
          rfl
    _ = substitution.keys.filter (fun key => key != name) :=
      keys_erase substitution name

/-- Extending a normal finite presentation by one occurs-clean assignment
preserves its one-pass normal form. -/
theorem Normal.bind
    {substitution : TypeSubst} (normal : substitution.Normal)
    {name : String} {value : Atom}
    (occursClean : name ∉ typeVars (substitution.apply value)) :
    (substitution.bind name value).Normal := by
  let resolved := substitution.apply value
  have resolvedAvoidsOld :
      ∀ candidate, candidate ∈ typeVars resolved →
        candidate ∉ substitution.keys := by
    intro candidate hcandidate
    exact normal.apply_variable_not_key value candidate hcandidate
  constructor
  · rw [keys_bind]
    apply List.Nodup.cons
    · intro hmem
      simp only [List.mem_filter] at hmem
      exact (by simpa using hmem.2)
    · exact normal.1.filter _
  · intro storedName storedValue hstored candidate hcandidate
    rw [keys_bind]
    simp only [List.mem_cons, List.mem_filter, not_or]
    change name ∉ typeVars resolved at occursClean
    simp only [TypeSubst.bind, List.mem_cons] at hstored
    rcases hstored with hhead | htail
    · have hpair : storedName = name ∧ storedValue = resolved := by
        simpa [resolved] using hhead
      rcases hpair with ⟨rfl, rfl⟩
      constructor
      · exact fun heq => occursClean (heq ▸ hcandidate)
      · intro hparts
        exact resolvedAvoidsOld candidate hcandidate hparts.1
    · obtain ⟨oldEntry, holdErase, hmapped⟩ := List.mem_map.mp htail
      rcases oldEntry with ⟨oldName, oldValue⟩
      have hold : (oldName, oldValue) ∈ substitution :=
        (List.mem_filter.mp holdErase).1
      have oldAvoids : ∀ candidateName,
          candidateName ∈ typeVars oldValue →
          candidateName ∉ substitution.keys :=
        normal.2 oldName oldValue hold
      have transformedAvoidsOld :
          ∀ candidateName,
            candidateName ∈ typeVars
              (applyAssignment name resolved oldValue) →
            candidateName ∉ substitution.keys := by
        apply apply_variable_avoids
          (substitution := [(name, resolved)])
        · intro key assigned hassigned candidateName hcandidateName
          simp only [List.mem_singleton, Prod.mk.injEq] at hassigned
          rcases hassigned with ⟨rfl, rfl⟩
          exact resolvedAvoidsOld candidateName hcandidateName
        · exact oldAvoids
      have transformedAvoidsName :
          ∀ candidateName,
            candidateName ∈ typeVars
              (applyAssignment name resolved oldValue) →
            candidateName ≠ name := by
        intro candidateName hcandidateName heq
        subst candidateName
        have singletonNormal :
            TypeSubst.Normal ([(name, resolved)] : TypeSubst) := by
          constructor
          · simp [keys]
          · intro key assigned hassigned candidateName hcandidateName
            simp only [List.mem_singleton, Prod.mk.injEq] at hassigned
            have hkey : key = name := hassigned.1
            have hvalue : assigned = resolved := hassigned.2
            subst key
            subst assigned
            simp only [keys, List.map_singleton, List.mem_singleton]
            intro heq
            exact occursClean (heq ▸ hcandidateName)
        exact singletonNormal.apply_variable_not_key
          oldValue name hcandidateName (by simp [keys])
      have hstoredValue :
          storedValue = applyAssignment name resolved oldValue := by
        have hsnd := congrArg Prod.snd hmapped.symm
        simpa [resolved] using hsnd
      rw [hstoredValue] at hcandidate
      constructor
      · exact transformedAvoidsName candidate hcandidate
      · intro hparts
        exact transformedAvoidsOld candidate hcandidate hparts.1

private theorem lookup_map_values
    (transform : Atom → Atom) :
    ∀ (substitution : TypeSubst) (name : String),
      TypeSubst.lookup
          (substitution.map fun entry => (entry.1, transform entry.2)) name =
        (substitution.lookup name).map transform := by
  intro substitution
  induction substitution with
  | nil => intro name; rfl
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      intro name
      by_cases hkey : name = key
      · subst key
        simp [TypeSubst.lookup]
      · simp [TypeSubst.lookup, hkey, ih]

private theorem lookup_erase_of_ne
    (substitution : TypeSubst) {name candidate : String}
    (hne : candidate ≠ name) :
    (substitution.erase name).lookup candidate =
      substitution.lookup candidate := by
  unfold erase
  induction substitution with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      by_cases hkeyName : key = name
      · subst key
        simp [TypeSubst.lookup, hne, ih]
      · by_cases hcandidateKey : candidate = key
        · subst key
          simp [TypeSubst.lookup, hkeyName]
        · simp [TypeSubst.lookup, hkeyName,
            hcandidateKey, ih]

/-- Lookup after `bind` is a new authoritative hit at the bound name and the
new assignment mapped through every older hit elsewhere. -/
theorem lookup_bind
    (substitution : TypeSubst) (name : String) (value : Atom)
    (candidate : String) :
    (substitution.bind name value).lookup candidate =
      if candidate = name then some (substitution.apply value)
      else
        (substitution.lookup candidate).map
          (applyAssignment name (substitution.apply value)) := by
  unfold bind
  by_cases hcandidate : candidate = name
  · subst candidate
    simp [TypeSubst.lookup]
  · simp only [TypeSubst.lookup, hcandidate, if_false]
    rw [lookup_map_values]
    rw [lookup_erase_of_ne substitution hcandidate]

/-- If the newly bound name was previously unassigned, `bind` is exactly
composition of the old one-pass presentation followed by the new resolved
assignment. -/
theorem bind_apply_eq_applyAssignment_apply
    (substitution : TypeSubst) (name : String) (value atom : Atom)
    (unassigned : substitution.lookup name = none) :
    (substitution.bind name value).apply atom =
      applyAssignment name (substitution.apply value)
        (substitution.apply atom) := by
  suffices key : ∀ n (current : Atom), sizeOf current ≤ n →
      (substitution.bind name value).apply current =
        applyAssignment name (substitution.apply value)
          (substitution.apply current) by
    exact key (sizeOf atom) atom le_rfl
  intro n
  induction n with
  | zero =>
      intro current hsize
      exact absurd hsize (by have := atom_size_pos current; omega)
  | succ n ih =>
      intro current hsize
      cases current with
      | symbol symbol =>
          simp [TypeSubst.apply, applyAssignment]
      | grounded grounded =>
          simp [TypeSubst.apply, applyAssignment]
      | var variableName =>
          simp only [TypeSubst.apply, lookup_bind]
          by_cases hsame : variableName = name
          · subst variableName
            simp [unassigned, Option.getD, applyAssignment,
              TypeSubst.apply, TypeSubst.lookup]
          · cases hlookup : substitution.lookup variableName with
            | none =>
                simp [hsame, Option.getD, applyAssignment,
                  TypeSubst.apply, TypeSubst.lookup]
            | some stored =>
                simp [hsame, Option.getD, applyAssignment]
      | expression atoms =>
          simp only [TypeSubst.apply, applyAssignment,
            Atom.expression.injEq, List.map_map]
          apply List.map_congr_left
          intro child hchild
          apply ih child
          have hlt := atom_size_lt_of_mem hchild
          have hatoms : sizeOf atoms ≤ n := by
            simp at hsize
            omega
          omega

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentation.TypeSubst

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentation

open TypeSubst

mutual

private def appliedOutputNormal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel substitution left right output)
    (normal : substitution.Normal)
    (leftFixed : substitution.apply left = left)
    (rightFixed : substitution.apply right = right) :
    output.Normal :=
  match derivation with
  | .identical _ _ => normal
  | .bindLeft occursClean => by
      apply normal.bind
      simpa [rightFixed] using occursClean
  | .bindRight _ occursClean => by
      apply normal.bind
      simpa [leftFixed] using occursClean
  | .expression children => appliedListOutputNormal children normal

private def appliedPresentationOutputNormal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  match derivation with
  | .ordinary leftApply rightApply applied =>
      appliedOutputNormal applied normal
        (by rw [← leftApply]; exact normal.apply_idempotent left)
        (by rw [← rightApply]; exact normal.apply_idempotent right)

private def appliedListOutputNormal
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : AppliedReducedTypeListMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  match derivation with
  | .nil _ => normal
  | .cons head tail =>
      appliedListOutputNormal tail
        (appliedPresentationOutputNormal head normal)

private def reducedOutputNormal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  match derivation with
  | .undefinedLeft _ _ => normal
  | .undefinedRight _ _ => normal
  | .expression children => reducedListOutputNormal children normal
  | .ordinary _ _ _ leftApply rightApply applied =>
      appliedOutputNormal applied normal
        (by rw [← leftApply]; exact normal.apply_idempotent left)
        (by rw [← rightApply]; exact normal.apply_idempotent right)

private def reducedListOutputNormal
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : ReducedTypePresentationListMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  match derivation with
  | .nil _ => normal
  | .cons head tail =>
      reducedListOutputNormal tail (reducedOutputNormal head normal)

end

/-- An applied reduced-type step preserves normality when its already-resolved
inputs are fixed points of the incoming normal substitution. -/
theorem AppliedReducedTypeMatchRel.output_normal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedReducedTypeMatchRel substitution left right output)
    (normal : substitution.Normal)
    (leftFixed : substitution.apply left = left)
    (rightFixed : substitution.apply right = right) :
    output.Normal :=
  appliedOutputNormal derivation normal leftFixed rightFixed

/-- Resolving an ordinary child before matching preserves normality. -/
theorem AppliedTypePresentationMatchRel.output_normal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : AppliedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  appliedPresentationOutputNormal derivation normal

/-- Pointwise ordinary matching preserves normality through its threaded
substitution. -/
theorem AppliedReducedTypeListMatchRel.output_normal
    {substitution output : TypeSubst} {left right : List Atom}
    (derivation : AppliedReducedTypeListMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  appliedListOutputNormal derivation normal

/-- Every reduced presentation match starting from a normal substitution
ends in a normal substitution. -/
theorem ReducedTypePresentationMatchRel.output_normal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  reducedOutputNormal derivation normal

/-- The left-to-right list fold preserves normality at every threaded
presentation state. -/
theorem ReducedTypePresentationListMatchRel.output_normal
    {substitution output : TypeSubst} {left right : List Atom}
  (derivation : ReducedTypePresentationListMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal :=
  reducedListOutputNormal derivation normal

/-- Published top-level gradual wildcards and the reduced R2 lane both
preserve normal presentation states. -/
theorem CorePlusR2TypePresentationMatchRel.output_normal
    {substitution output : TypeSubst} {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right output)
    (normal : substitution.Normal) : output.Normal := by
  cases derivation with
  | undefinedLeft => exact normal
  | undefinedRight => exact normal
  | atomLeft => exact normal
  | atomRight => exact normal
  | reduced _ _ _ _ reduced => exact reducedOutputNormal reduced normal

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentation

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentation.TypeSubst

/-! ## Boundary examples -/

/-- Positive: binding one fresh type variable to a concrete type produces a
normal one-pass presentation. -/
theorem fresh_symbol_binding_is_normal :
    TypeSubst.Normal
      (TypeSubst.bind [] "t" (.symbol "A")) := by
  apply TypeSubst.normal_empty.bind
  simp [typeVars]

/-- Negative: retaining a reflexive assignment would violate normality even
though its one-pass observation happens to be the identity. -/
theorem reflexive_assignment_is_not_normal :
    ¬TypeSubst.Normal [("t", .var "t")] := by
  simp [TypeSubst.Normal, keys, typeVars]

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentation.TypeSubst
