import Mettapedia.OSLF.MeTTaIL.EngineCoded.Bindings

/-!
# Substitution computed on codes

The parts of a pattern and a pattern rebuilt from new parts are computable on
codes. By structural recursion on codes, so are the free names of a pattern
(`freeVars`), the elimination of one bound level (`instantiateBVarAt`) and the
application of bindings to a pattern (`applyBindings`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable

/-! ## Parts and rebuilding -/

theorem parts_computable : CodeComputable parts :=
  ⟨fun n => Encodable.encode (partsCode n), Primrec.encode.to_comp.comp partsCode_primrec.to_comp,
    fun pattern => by
      show Encodable.encode (partsCode (patternCode pattern)) = Encodable.encode ((parts pattern).map code)
      rw [partsCode_patternCode]
      rfl⟩

theorem withParts_computable : CodeComputable₂ withParts :=
  ⟨fun n => rebuildCode n.unpair.1 (Denumerable.ofNat (List ℕ) n.unpair.2),
    rebuildCode_primrec.to_comp.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
      ((Primrec.ofNat (List ℕ)).to_comp.comp (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)),
    fun input => by
      show rebuildCode (Nat.pair (code input.1) (code input.2)).unpair.1
          (Denumerable.ofNat (List ℕ) (Nat.pair (code input.1) (code input.2)).unpair.2) =
        code (withParts input.1 input.2)
      rw [Nat.unpair_pair, ofNat_code_list]
      exact rebuildCode_patternCode input.1 input.2⟩

theorem fvar_computable : CodeComputable fun name : String => Pattern.fvar name :=
  ⟨fun n => Nat.pair 1 n, (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id).to_comp, fun _ => rfl⟩

/-- Calls to every part with the same parameter. -/
def partCalls {α : Type} (parameter : α) (pattern : Pattern) : List (α × Pattern) :=
  (parts pattern).map fun part => (parameter, part)

theorem partCalls_computable {α : Type} [Coded α] : CodeComputable₂ (partCalls (α := α)) :=
  list_map (parts_computable.comp snd) (pair (fst.comp fst) snd)

theorem partCalls_smaller {α : Type} (parameter : α) (pattern : Pattern) :
    ∀ call ∈ partCalls parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [partCalls, List.mem_map] at member
  obtain ⟨part, inParts, rfl⟩ := member
  exact patternCode_lt_of_mem_parts inParts

/-! ## Free names -/

/-- The free names of a pattern from those of its parts. -/
def freeVarsCombine (pattern : Pattern) (values : List (List String)) : List String :=
  @Pattern.casesOn (fun _ => List String) pattern (fun _ => []) (fun name => [name])
    (fun _ _ => values.flatten) (fun _ _ => values.flatten) (fun _ _ _ => values.flatten)
    (fun _ _ => values.flatten) (fun _ _ _ => values.flatten)

theorem freeVars_node (pattern : Pattern) :
    freeVars pattern = freeVarsCombine pattern ((parts pattern).map freeVars) := by
  cases pattern <;> simp [freeVars, freeVarsCombine, parts, List.flatMap_def]

theorem freeVars_computable : CodeComputable freeVars := by
  have flat : CodeComputable fun input : ℕ × Pattern × List (List String) => input.2.2.flatten :=
    list_flatten (snd.comp snd)
  have combine : CodeComputable fun input : ℕ × Pattern × List (List String) =>
      freeVarsCombine input.2.1 input.2.2 :=
    (casesOn (pattern := fun input : ℕ × Pattern × List (List String) => input.2.1)
      (onBVar := fun _ _ => ([] : List String)) (onFVar := fun _ name => [name])
      (onApply := fun input _ _ => input.2.2.flatten) (onLambda := fun input _ _ => input.2.2.flatten)
      (onMultiLambda := fun input _ _ _ => input.2.2.flatten) (onSubst := fun input _ _ => input.2.2.flatten)
      (onCollection := fun input _ _ _ => input.2.2.flatten) (fst.comp snd) (const [])
      (list_cons snd (const [])) (flat.comp fst) (flat.comp fst) (flat.comp fst) (flat.comp fst)
      (flat.comp fst)).of_eq fun _ => rfl
  have structured := structural (value := fun (_ : ℕ) pattern => freeVars pattern)
    (calls := partCalls) (combine := fun _ pattern values => freeVarsCombine pattern values)
    (fun _ pattern => by rw [freeVars_node, partCalls, List.map_map]; rfl)
    partCalls_smaller partCalls_computable combine
  exact structured.comp ((const 0).pair id)

/-! ## Eliminating one bound level -/

theorem zip_zeros (patterns : List Pattern) :
    (List.replicate patterns.length (0 : ℕ)).zip patterns = patterns.map fun pattern => (0, pattern) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [List.replicate_succ, recurse]

/-- The parts of a pattern, each with the depth of the level it eliminates. -/
def instantiateCalls (parameter : ℕ × Pattern) (pattern : Pattern) : List ((ℕ × Pattern) × Pattern) :=
  (underCalls (· + ·) parameter.1 pattern).map fun call => ((call.1, parameter.2), call.2)

/-- The leaf of an elimination at a bound variable. -/
def instantiateLeaf (parameter : ℕ × Pattern) (index : ℕ) : Pattern :=
  if index < parameter.1 then .bvar index
  else if index = parameter.1 then liftBVars 0 parameter.1 parameter.2
  else .bvar (index - 1)

/-- An elimination at a node from the eliminations of its parts. -/
def instantiateCombine (parameter : ℕ × Pattern) (pattern : Pattern) (values : List Pattern) : Pattern :=
  @Pattern.casesOn (fun _ => Pattern) pattern (fun index => instantiateLeaf parameter index)
    (fun _ => withParts pattern values) (fun _ _ => withParts pattern values) (fun _ _ => withParts pattern values)
    (fun _ _ _ => withParts pattern values) (fun _ _ => withParts pattern values)
    (fun _ _ _ => withParts pattern values)

theorem instantiate_node (parameter : ℕ × Pattern) (pattern : Pattern) :
    instantiateBVarAt parameter.1 parameter.2 pattern = instantiateCombine parameter pattern
      ((instantiateCalls parameter pattern).map fun call => instantiateBVarAt call.1.1 call.1.2 call.2) := by
  obtain ⟨depth, replacement⟩ := parameter
  cases pattern <;>
    simp [instantiateBVarAt, instantiateCombine, instantiateLeaf, instantiateCalls, underCalls, partBinders,
      parts, withParts, zip_zeros, Function.comp_def]

theorem instantiateLeaf_computable : CodeComputable₂ instantiateLeaf := by
  have depth : CodeComputable fun input : (ℕ × Pattern) × ℕ => input.1.1 := fst.comp fst
  refine (CodeComputable.ite (nat_lt snd depth) (bvar snd)
    (CodeComputable.ite (nat_eq snd depth) (liftBVars'.comp (pair (const 0) (pair depth (snd.comp fst))))
      (bvar (nat_sub snd (const 1))))).of_eq fun input => ?_
  by_cases below : input.2 < input.1.1 <;> by_cases same : input.2 = input.1.1 <;>
    simp [instantiateLeaf, below, same]

theorem instantiateCalls_computable : CodeComputable₂ instantiateCalls :=
  list_map ((underCalls_codeComputable Primrec.nat_add.to_comp).comp (pair (fst.comp fst) snd))
    (pair (pair (fst.comp snd) (snd.comp (fst.comp fst))) (snd.comp snd))

theorem instantiateCalls_smaller (parameter : ℕ × Pattern) (pattern : Pattern) :
    ∀ call ∈ instantiateCalls parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [instantiateCalls, List.mem_map] at member
  obtain ⟨inner, inside, rfl⟩ := member
  exact underCalls_smaller _ _ _ inner inside

/-- **Eliminating a bound level is computable on codes.** -/
theorem instantiateBVarAt_computable :
    CodeComputable fun input : (ℕ × Pattern) × Pattern => instantiateBVarAt input.1.1 input.1.2 input.2 := by
  have rebuilt : CodeComputable fun input : (ℕ × Pattern) × Pattern × List Pattern =>
      withParts input.2.1 input.2.2 := withParts_computable.comp (pair (fst.comp snd) (snd.comp snd))
  have combine : CodeComputable fun input : (ℕ × Pattern) × Pattern × List Pattern =>
      instantiateCombine input.1 input.2.1 input.2.2 :=
    (casesOn (pattern := fun input : (ℕ × Pattern) × Pattern × List Pattern => input.2.1)
      (onBVar := fun input index => instantiateLeaf input.1 index)
      (onFVar := fun input _ => withParts input.2.1 input.2.2)
      (onApply := fun input _ _ => withParts input.2.1 input.2.2)
      (onLambda := fun input _ _ => withParts input.2.1 input.2.2)
      (onMultiLambda := fun input _ _ _ => withParts input.2.1 input.2.2)
      (onSubst := fun input _ _ => withParts input.2.1 input.2.2)
      (onCollection := fun input _ _ _ => withParts input.2.1 input.2.2) (fst.comp snd)
      (instantiateLeaf_computable.comp (pair (fst.comp fst) snd)) (rebuilt.comp fst) (rebuilt.comp fst)
      (rebuilt.comp fst) (rebuilt.comp fst) (rebuilt.comp fst) (rebuilt.comp fst)).of_eq fun input => by
        rcases input with ⟨parameter, pattern, values⟩
        cases pattern <;> rfl
  exact structural (value := fun parameter pattern => instantiateBVarAt parameter.1 parameter.2 pattern)
    (calls := instantiateCalls) (combine := instantiateCombine) instantiate_node instantiateCalls_smaller
    instantiateCalls_computable combine

theorem instantiateBVar_computable : CodeComputable₂ instantiateBVar :=
  (instantiateBVarAt_computable.comp (pair (pair (const 0) fst) snd)).of_eq fun _ => rfl

/-! ## Applying bindings -/

/-- Case analysis on an optional string, under its pattern code. -/
theorem optionString_casesOn {α β : Type} [Coded α] [Coded β] {option : α → Option String} {onNone : α → β}
    {onSome : α → String → β} (hOption : CodeComputable option) (hNone : CodeComputable onNone)
    (hSome : CodeComputable₂ onSome) :
    CodeComputable fun argument => Option.casesOn (motive := fun _ => β) (option argument) (onNone argument)
      (onSome argument) := by
  obtain ⟨trackOption, computableOption, tracksOption⟩ := hOption
  obtain ⟨trackNone, computableNone, tracksNone⟩ := hNone
  obtain ⟨trackSome, computableSome, tracksSome⟩ := hSome
  refine ⟨fun n => cond (decide ((trackOption n).unpair.1 = 0)) (trackNone n)
      (trackSome (Nat.pair n (trackOption n).unpair.2)), ?_, fun argument => ?_⟩
  · have tag : Computable fun n => (trackOption n).unpair.1 :=
      (Primrec.fst.to_comp.comp Primrec.unpair.to_comp).comp computableOption
    have value : Computable fun n => (trackOption n).unpair.2 :=
      (Primrec.snd.to_comp.comp Primrec.unpair.to_comp).comp computableOption
    exact Computable.cond (Primrec.eq.decide.to_comp.comp tag (Computable.const 0)) computableNone
      (computableSome.comp (Primrec₂.natPair.to_comp.comp Computable.id value))
  · beta_reduce
    rw [tracksOption]
    cases found : option argument with
    | none =>
        simp only [code_optionString, optionStringCode]
        rw [tracksNone]
        rfl
    | some name =>
        simp only [code_optionString, optionStringCode, Nat.unpair_pair]
        have := tracksSome (argument, name)
        simp only [code_pair, code_string] at this
        simpa using this

/-- A present optional string, under its pattern code. -/
theorem optionString_some {α : Type} [Coded α] {value : α → String} (hValue : CodeComputable value) :
    CodeComputable fun argument => (some (value argument) : Option String) := by
  obtain ⟨track, computable, tracks⟩ := hValue
  exact ⟨fun n => Nat.pair 1 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 1) computable,
    fun argument => by simp [code_optionString, optionStringCode, tracks]⟩

/-- The value bound to a collection's rest name, when it is a closed collection of the same kind. -/
def restValue (kind : CollType) (name : String) (value : Pattern) : List Pattern × Option String :=
  @Pattern.casesOn (fun _ => List Pattern × Option String) value (fun _ => ([], some name))
    (fun _ => ([], some name)) (fun _ _ => ([], some name)) (fun _ _ => ([], some name))
    (fun _ _ _ => ([], some name)) (fun _ _ => ([], some name))
    (fun boundKind elements boundRest =>
      if boundRest.isNone && boundKind == kind then (elements, none) else ([], some name))

/-- The elements a collection's rest name contributes under bindings, and the rest name left unresolved. -/
def restOf (bindings : Bindings) (kind : CollType) (rest : Option String) : List Pattern × Option String :=
  match rest with
  | some name =>
      match bindings.find? (·.1 == name) with
      | some (_, .collection boundKind elements none) =>
          if boundKind == kind then (elements, none) else ([], some name)
      | _ => ([], some name)
  | none => ([], none)

theorem restOf_eq (bindings : Bindings) (kind : CollType) (rest : Option String) :
    restOf bindings kind rest = Option.casesOn (motive := fun _ => List Pattern × Option String) rest ([], none)
      fun name => Option.casesOn (motive := fun _ => List Pattern × Option String)
        (bindings.find? (·.1 == name)) ([], some name) fun entry => restValue kind name entry.2 := by
  cases rest with
  | none => rfl
  | some name =>
      simp only [restOf]
      cases bindings.find? (·.1 == name) with
      | none => rfl
      | some entry =>
          obtain ⟨_, value⟩ := entry
          cases value with
          | collection boundKind elements boundRest =>
              cases boundRest <;> simp [restValue]
          | _ => rfl

theorem restValue_computable :
    CodeComputable fun input : (CollType × String) × Pattern => restValue input.1.1 input.1.2 input.2 := by
  have stuck : CodeComputable fun input : (CollType × String) × Pattern => (([] : List Pattern), some input.1.2) :=
    pair (const []) (optionString_some (snd.comp fst))
  have kindEq : CodeComputable fun input : ((CollType × String) × Pattern) × CollType × List Pattern × Option String =>
      decide (input.2.1 = input.1.1.1) :=
    (beq_of_injective collectionCode_injective).comp (pair (fst.comp snd) (fst.comp (fst.comp fst)))
  have closed : CodeComputable fun input : ((CollType × String) × Pattern) × CollType × List Pattern × Option String =>
      decide ((code input.2.2.2).unpair.1 = 0) :=
    nat_eq ((of_computable (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)).comp
      ((code' (α := Option String)).comp (snd.comp (snd.comp snd)))) (const 0)
  refine (casesOn (pattern := fun input : (CollType × String) × Pattern => input.2)
    (onBVar := fun input _ => (([] : List Pattern), some input.1.2))
    (onFVar := fun input _ => (([] : List Pattern), some input.1.2))
    (onApply := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onLambda := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onMultiLambda := fun input _ _ _ => (([] : List Pattern), some input.1.2))
    (onSubst := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onCollection := fun input boundKind elements boundRest =>
      if decide ((code boundRest).unpair.1 = 0) && decide (boundKind = input.1.1) then (elements, none)
      else (([] : List Pattern), some input.1.2)) snd (stuck.comp fst) (stuck.comp fst) (stuck.comp fst)
    (stuck.comp fst) (stuck.comp fst) (stuck.comp fst)
    (CodeComputable.ite (CodeComputable.and closed kindEq) (pair (fst.comp (snd.comp snd)) (const none))
      (stuck.comp fst))).of_eq fun input => ?_
  rcases input with ⟨⟨kind, name⟩, value⟩
  cases value with
  | collection boundKind elements boundRest =>
      cases boundRest <;> simp [restValue, optionStringCode, Nat.unpair_pair]
  | _ => rfl

theorem restOf_computable :
    CodeComputable fun input : Bindings × CollType × Option String => restOf input.1 input.2.1 input.2.2 := by
  have found : CodeComputable fun input : (Bindings × CollType × Option String) × String =>
      input.1.1.find? (·.1 == input.2) :=
    list_find? (fst.comp fst) (stringBEq.comp (pair (fst.comp snd) (snd.comp fst)))
  have inner : CodeComputable₂ fun (input : Bindings × CollType × Option String) (name : String) =>
      Option.casesOn (motive := fun _ => List Pattern × Option String) (input.1.find? (·.1 == name))
        ([], some name) fun entry => restValue input.2.1 name entry.2 :=
    option_casesOn found (pair (const []) (optionString_some snd))
      (restValue_computable.comp (pair (pair (fst.comp (snd.comp (fst.comp fst))) (snd.comp fst)) (snd.comp snd)))
  exact (optionString_casesOn (snd.comp snd) (const ([], none)) inner).of_eq fun input =>
    (restOf_eq input.1 input.2.1 input.2.2).symm

/-- Bindings applied at a node, from the applications to its parts. -/
def applyCombine (bindings : Bindings) (pattern : Pattern) (values : List Pattern) : Pattern :=
  @Pattern.casesOn (fun _ => Pattern) pattern (fun index => .bvar index)
    (fun name => (bindings.lookup name).getD (.fvar name))
    (fun label _ => .apply label values) (fun binder _ => .lambda binder (values.getD 0 (.bvar 0)))
    (fun arity names _ => .multiLambda arity names (values.getD 0 (.bvar 0)))
    (fun _ _ => instantiateBVar (values.getD 1 (.bvar 0)) (values.getD 0 (.bvar 0)))
    (fun kind _ rest => .collection kind (values ++ (restOf bindings kind rest).1) (restOf bindings kind rest).2)

theorem applyBindings_node (bindings : Bindings) (pattern : Pattern) :
    applyBindings bindings pattern =
      applyCombine bindings pattern ((partCalls bindings pattern).map fun call => applyBindings call.1 call.2) := by
  cases pattern with
  | fvar name =>
      simp only [applyBindings, applyCombine, Bindings.lookup]
      cases bindings.find? (·.1 == name) with
      | none => rfl
      | some found => rfl
  | collection kind elements rest =>
      simp only [applyCombine, partCalls, parts, List.map_map, Function.comp_def]
      rw [applyBindings.eq_def]
      rfl
  | _ => simp [applyBindings, applyCombine, partCalls, parts, Function.comp_def]

theorem applyCombine_computable :
    CodeComputable fun input : Bindings × Pattern × List Pattern => applyCombine input.1 input.2.1 input.2.2 := by
  have values : CodeComputable fun input : (Bindings × Pattern × List Pattern) × String × List Pattern =>
      input.1.2.2 := snd.comp (snd.comp fst)
  exact (casesOn (pattern := fun input : Bindings × Pattern × List Pattern => input.2.1)
    (onBVar := fun _ index => Pattern.bvar index)
    (onFVar := fun input name => (input.1.lookup name).getD (.fvar name))
    (onApply := fun input label _ => .apply label input.2.2)
    (onLambda := fun input binder _ => .lambda binder (input.2.2.getD 0 (.bvar 0)))
    (onMultiLambda := fun input arity names _ => .multiLambda arity names (input.2.2.getD 0 (.bvar 0)))
    (onSubst := fun input _ _ => instantiateBVar (input.2.2.getD 1 (.bvar 0)) (input.2.2.getD 0 (.bvar 0)))
    (onCollection := fun input kind _ rest =>
      .collection kind (input.2.2 ++ (restOf input.1 kind rest).1) (restOf input.1 kind rest).2)
    (fst.comp snd) (bvar snd)
    (option_getD (lookup_computable.comp (pair (fst.comp fst) snd)) (fvar_computable.comp snd))
    (apply (fst.comp snd) values)
    (lambda (fst.comp snd) (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 0)))
    (multiLambda (fst.comp snd) (fst.comp (snd.comp snd)) (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 0)))
    (instantiateBVar_computable.comp (pair (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 1))
      (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 0))))
    (collection (fst.comp snd)
      (list_append (snd.comp (snd.comp fst))
        (fst.comp (restOf_computable.comp (pair (fst.comp fst) (pair (fst.comp snd) (snd.comp (snd.comp snd)))))))
      (snd.comp (restOf_computable.comp (pair (fst.comp fst) (pair (fst.comp snd) (snd.comp (snd.comp snd))))))))
    |>.of_eq fun input => by
      rcases input with ⟨bindings, pattern, values⟩
      cases pattern <;> rfl

/-- **Applying bindings to a pattern is computable on codes.** -/
theorem applyBindings_computable : CodeComputable₂ applyBindings :=
  structural (value := applyBindings) (calls := partCalls) (combine := applyCombine) applyBindings_node
    partCalls_smaller partCalls_computable applyCombine_computable

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.freeVars_computable
#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.instantiateBVarAt_computable
#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.applyBindings_computable
