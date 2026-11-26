import Mettapedia.GSLT.Compilation.Uniform.CollectionMatching
import Mettapedia.GSLT.Compilation.Uniform.ScopeClauses
import Mettapedia.GSLT.Compilation.Uniform.DataClauses

/-!
# Instantiating a pattern scope-correctly, as clauses

The source instantiates a pattern at a depth (`Match.applyBindingsScoped`): a matched value is lifted from the depth
where the sites captured it to the depth where the pattern uses it, a bag's or a vector's rest is spliced in lifted
the same way, and an explicit substitution is evaluated. The instantiation lowering (`buildRow`) gives the row pattern
of the instance with its goals: unwrap a rest, lift a value, instantiate a substitution. Its row is the instance's row
whenever its goals hold (`buildRow_sound`), and its goals hold at every instance (`buildRow_complete`).

An instance is read back by the converses of its goals, the last goal's first (`buildConverses`): lowering for a lift,
wrapping for an unwrap, and for a substitution, its value chosen as a datum over the supply and the instance abstracted
over it (`buildConverse_instantiate`). The values so chosen are exactly the values the instance substitutes
(`substValues`, `buildRow_substituted`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.Instantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVars_zero instantiateBVar instantiateBVarAt)
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode encodeList labelCode numeral numeralTerm optionRow namesRow)
open DemandTransformation (Goal Clause goalHolds goalUnknowns goalInputs Derives InputsBound)
open OrderedMatching (names namesList)
open OrderedRows (Holds vectorTerm)
open MatchesAndInstances (bagRests bagRestsList BagSettled)
open CollectionMatching (collectionTerm inst_collectionTerm encode_collection unwrapRelation unwrapClauses
  unwrapClause wrapRelation wrapClauses wrapClause unwrap_sound unwrap_complete listUnknown listUnknown_ne listUnknown_injective find_of_lookup_collection InScope
  Untouched AgreeOutside untouched_name holds_congr goals_agree)
open ScopeClauses (ScopeProgram liftRelation liftListRelation instantiateRelation lift_iff instantiate_iff
  liftList_sound liftList_complete LowerProgram lowerRelation lowerListRelation abstractRelation)
open UnificationClauses (triple)
open PatternRows (encode_closed_inv)

/-! ## The instance of a name and of a rest -/

/-- How far a name's value is lifted where a pattern uses it at a depth: beyond the depth where the sites capture
it. -/
def shiftOf (sites : Pattern) (name : String) (depth : ℕ) : ℕ :=
  match captureDepth name 0 sites with
  | some captured => depth - captured
  | none => 0

theorem applyBindingsScoped_fvar (sites : Pattern) (witness : Bindings) (depth : ℕ) (name : String) :
    applyBindingsScoped sites witness depth (.fvar name) =
      liftBVars 0 (shiftOf sites name depth) (lookupOrFvar witness name) := by
  simp only [applyBindingsScoped, shiftOf, lookupOrFvar, applyBindings]
  cases witness.find? (·.1 == name) with
  | none => simp [liftBVars]
  | some entry =>
      obtain ⟨_, value⟩ := entry
      cases captureDepth name 0 sites with
      | none => simp [liftBVars_zero]
      | some captured => rfl

theorem restSplice_bound {sites : Pattern} {witness : Bindings} {depth : ℕ} {kind : CollType} {rest : String}
    {tail : List Pattern} (bound : witness.find? (·.1 == rest) = some (rest, .collection kind tail none)) :
    restSplice sites witness depth kind (some rest) = (tail.map (liftBVars 0 (shiftOf sites rest depth)), none) := by
  simp only [restSplice, bound, beq_self_eq_true, ↓reduceIte, shiftOf]
  cases captureDepth rest 0 sites with
  | none => simp [map_liftBVars_zero]
  | some captured => rfl

theorem applyBindingsScoped_collection (sites : Pattern) (witness : Bindings) (depth : ℕ) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    applyBindingsScoped sites witness depth (.collection kind elements rest) =
      .collection kind (elements.map (applyBindingsScoped sites witness depth) ++
        (restSplice sites witness depth kind rest).1) (restSplice sites witness depth kind rest).2 := by
  simp [applyBindingsScoped]

/-! ## A lifted value -/

/-- **A value lifted by a shift into a fresh unknown**: the value's own unknown when the shift is zero, else the
fresh unknown, with a goal that lifts into it. -/
def lifted (relation shift source fresh : ℕ) : Tm × List Goal :=
  if shift = 0 then (.var source, []) else
    (.var fresh, [.ask relation (triple (symTerm 0) (numeralTerm shift) (.var source)) (.var fresh)])

section Lifted

variable {R : Relations} {program : List Clause}

theorem lifted_sound (scope : ScopeProgram program) {shift source fresh : ℕ} {θ : ℕ → Expr} {value : Pattern}
    (valued : θ source = encode value)
    (goals : ∀ g ∈ (lifted liftRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    inst θ (lifted liftRelation shift source fresh).1 = encode (liftBVars 0 shift value) := by
  by_cases zero : shift = 0
  · subst zero
    simp [lifted, valued, liftBVars_zero]
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton, forall_eq] at goals ⊢
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      RootRewritesOnTheStep.inst_numeralTerm, DemandTransformation.inst_unknown, valued] at goals
    exact (lift_iff scope 0 shift value).mp goals

theorem liftedList_sound (scope : ScopeProgram program) {shift source fresh : ℕ} {θ : ℕ → Expr}
    {values : List Pattern} (valued : θ source = encodeList values)
    (goals : ∀ g ∈ (lifted liftListRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    inst θ (lifted liftListRelation shift source fresh).1 = encodeList (values.map (liftBVars 0 shift)) := by
  by_cases zero : shift = 0
  · subst zero
    simp [lifted, valued, map_liftBVars_zero]
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton, forall_eq] at goals ⊢
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      RootRewritesOnTheStep.inst_numeralTerm, DemandTransformation.inst_unknown, valued] at goals
    obtain ⟨depth, derived⟩ := goals
    exact liftList_sound scope depth 0 shift values _ derived

theorem lifted_complete (scope : ScopeProgram program) {shift source fresh : ℕ} {θ : ℕ → Expr} {value : Pattern}
    (valued : θ source = encode value) (distinct : source ≠ fresh) :
    let θ' := Function.update θ fresh (encode (liftBVars 0 shift value))
    inst θ' (lifted liftRelation shift source fresh).1 = encode (liftBVars 0 shift value) ∧
      ∀ g ∈ (lifted liftRelation shift source fresh).2, goalHolds R (Derives R program) θ' g := by
  intro θ'
  have sourceKept : θ' source = encode value := by simp [θ', Function.update_of_ne distinct, valued]
  by_cases zero : shift = 0
  · subst zero
    simp [lifted, sourceKept, liftBVars_zero]
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton, forall_eq]
    refine ⟨by simp [θ'], ?_⟩
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      RootRewritesOnTheStep.inst_numeralTerm, DemandTransformation.inst_unknown, sourceKept]
    exact (lift_iff scope 0 shift value).mpr (by simp [θ'])

theorem liftedList_complete (scope : ScopeProgram program) {shift source fresh : ℕ} {θ : ℕ → Expr}
    {values : List Pattern} (valued : θ source = encodeList values) (distinct : source ≠ fresh) :
    let θ' := Function.update θ fresh (encodeList (values.map (liftBVars 0 shift)))
    inst θ' (lifted liftListRelation shift source fresh).1 = encodeList (values.map (liftBVars 0 shift)) ∧
      ∀ g ∈ (lifted liftListRelation shift source fresh).2, goalHolds R (Derives R program) θ' g := by
  intro θ'
  have sourceKept : θ' source = encodeList values := by simp [θ', Function.update_of_ne distinct, valued]
  by_cases zero : shift = 0
  · subst zero
    simp [lifted, sourceKept, map_liftBVars_zero]
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton, forall_eq]
    refine ⟨by simp [θ'], ?_⟩
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      RootRewritesOnTheStep.inst_numeralTerm, DemandTransformation.inst_unknown, sourceKept]
    simpa [θ', numeral] using liftList_complete (R := R) scope 0 shift values

theorem lifted_unknowns (relation shift source fresh : ℕ) :
    ∀ u ∈ unknowns (lifted relation shift source fresh).1 ++
      (lifted relation shift source fresh).2.flatMap goalUnknowns, u = source ∨ u = fresh := by
  intro u inside
  by_cases zero : shift = 0
  · simp [lifted, zero] at inside
    exact .inl inside
  · simp only [lifted, zero, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, triple,
      RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
      RootRewritesOnTheStep.unknowns_numeralTerm, DemandTransformation.unknowns_unknown, List.nil_append,
      List.mem_append, List.mem_singleton] at inside
    tauto

theorem lifted_moded (relation shift source fresh : ℕ) {bound : List ℕ} (sourceBound : source ∈ bound) :
    InputsBound bound (lifted relation shift source fresh).2 ∧
      ∀ u ∈ unknowns (lifted relation shift source fresh).1,
        u ∈ bound ++ (lifted relation shift source fresh).2.flatMap goalUnknowns := by
  by_cases zero : shift = 0
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.unknowns_unknown, List.mem_singleton,
      List.flatMap_nil, List.append_nil, forall_eq]
    exact ⟨.nil bound, sourceBound⟩
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.unknowns_unknown, List.mem_singleton, forall_eq]
    refine ⟨.cons (fun x inside => ?_) (.nil _), by simp [goalUnknowns]⟩
    simp only [goalInputs, triple, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
      RootRewritesOnTheStep.unknowns_numeralTerm, DemandTransformation.unknowns_unknown, List.nil_append,
      List.mem_singleton] at inside
    rw [inside]
    exact sourceBound

end Lifted

/-! ## The instantiation lowering -/

theorem unknowns_toTerm : ∀ e : Expr, unknowns (toTerm e) = []
  | .sym _ => rfl
  | .name _ => rfl
  | .app f a => by
      rw [show toTerm (.app f a) = appTerm (toTerm f) (toTerm a) from rfl, RootRewritesOnTheStep.unknowns_appTerm,
        unknowns_toTerm f, unknowns_toTerm a]
      rfl
  | .code e => by rw [show unknowns (toTerm (.code e)) = unknowns (toTerm e) from rfl, unknowns_toTerm e]

mutual
  /-- **A pattern at an instantiation position, at a depth**: its row pattern, the goals that unwrap rests, lift
  values to the depth and instantiate substitutions, and the next fresh unknown. -/
  def buildRow (rests avoid : List String) (sites : Pattern) : ℕ → ℕ → Pattern → Option (Tm × List Goal × ℕ)
    | depth, next, .fvar name =>
        let found := lifted (if name ∈ rests then liftListRelation else liftRelation) (shiftOf sites name depth)
          (labelCode name) (listUnknown avoid next)
        some (if name ∈ rests then vectorTerm found.1 else found.1, found.2, next + 1)
    | _, next, .bvar index => some (appTerm (symTerm 0) (numeralTerm index), [], next)
    | depth, next, .apply label arguments => (buildRows rests avoid sites depth next arguments (symTerm 0)).map
        fun found => (appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) found.1), found.2.1, found.2.2)
    | depth, next, .lambda binder body => (buildRow rests avoid sites (depth + 1) next body).map fun found =>
        (appTerm (symTerm 3) (appTerm (toTerm (optionRow binder)) found.1), found.2.1, found.2.2)
    | depth, next, .multiLambda arity binders body => (buildRow rests avoid sites (depth + arity) next body).map
        fun found => (appTerm (symTerm 4) (appTerm (numeralTerm arity) (appTerm (toTerm (namesRow binders)) found.1)),
          found.2.1, found.2.2)
    | depth, next, .subst body value => (buildRow rests avoid sites (depth + 1) next body).bind fun bodyFound =>
        (buildRow rests avoid sites depth bodyFound.2.2 value).map fun valueFound =>
          (.var (listUnknown avoid valueFound.2.2), bodyFound.2.1 ++ valueFound.2.1 ++
            [.ask instantiateRelation (triple (symTerm 0) valueFound.1 bodyFound.1)
              (.var (listUnknown avoid valueFound.2.2))], valueFound.2.2 + 1)
    | depth, next, .collection .vec elements none =>
        (buildRows rests avoid sites depth next elements (symTerm 0)).map fun found =>
          (vectorTerm found.1, found.2.1, found.2.2)
    | depth, next, .collection .vec elements (some rest) =>
        if rest ∈ rests then
          (buildRows rests avoid sites depth (next + 1) elements
            (lifted liftListRelation (shiftOf sites rest depth) (labelCode rest) (listUnknown avoid next)).1).map
            fun found => (vectorTerm found.1,
              (lifted liftListRelation (shiftOf sites rest depth) (labelCode rest) (listUnknown avoid next)).2 ++
                found.2.1, found.2.2)
        else none
    | depth, next, .collection .hashBag elements none =>
        (buildRows rests avoid sites depth next elements (symTerm 0)).map fun found =>
          (collectionTerm .hashBag found.1, found.2.1, found.2.2)
    | depth, next, .collection .hashBag elements (some rest) =>
        if rest ∉ rests then
          (buildRows rests avoid sites depth (next + 2) elements (lifted liftListRelation (shiftOf sites rest depth)
            (listUnknown avoid next) (listUnknown avoid (next + 1))).1).map fun found =>
            (collectionTerm .hashBag found.1, .ask unwrapRelation (.var (labelCode rest))
              (appTerm (symTerm (collectionCode .hashBag)) (.var (listUnknown avoid next))) ::
                (lifted liftListRelation (shiftOf sites rest depth) (listUnknown avoid next)
                  (listUnknown avoid (next + 1))).2 ++ found.2.1, found.2.2)
        else none
    | depth, next, .collection .hashSet elements none =>
        (buildRows rests avoid sites depth next elements (symTerm 0)).map fun found =>
          (collectionTerm .hashSet found.1, found.2.1, found.2.2)
    | depth, next, .collection .hashSet elements (some rest) =>
        if rest ∉ rests then
          (buildRows rests avoid sites depth (next + 2) elements (lifted liftListRelation (shiftOf sites rest depth)
            (listUnknown avoid next) (listUnknown avoid (next + 1))).1).map fun found =>
            (collectionTerm .hashSet found.1, .ask unwrapRelation (.var (labelCode rest))
              (appTerm (symTerm (collectionCode .hashSet)) (.var (listUnknown avoid next))) ::
                (lifted liftListRelation (shiftOf sites rest depth) (listUnknown avoid next)
                  (listUnknown avoid (next + 1))).2 ++ found.2.1, found.2.2)
        else none

  /-- Patterns as one list closed by a tail, at an instantiation position, at a depth. -/
  def buildRows (rests avoid : List String) (sites : Pattern) (depth : ℕ) :
      ℕ → List Pattern → Tm → Option (Tm × List Goal × ℕ)
    | next, [], close => some (close, [], next)
    | next, pattern :: patterns, close => (buildRow rests avoid sites depth next pattern).bind fun head =>
        (buildRows rests avoid sites depth head.2.2 patterns close).map fun tail =>
          (appTerm head.1 tail.1, head.2.1 ++ tail.2.1, tail.2.2)
end

/-! ## The row of an instance -/

/-- **The clauses an instantiation's goals ask**: unwrapping, lifting and instantiating. -/
structure BuildClauses (program : List Clause) : Prop where
  scope : ScopeProgram program
  unwraps : ∀ c ∈ unwrapClauses, c ∈ program
  onlyUnwraps : ∀ c ∈ program, c.relation = unwrapRelation → c ∈ unwrapClauses

section BuildSound

variable {R : Relations} {program : List Clause} {rests avoid : List String} {sites : Pattern}

theorem restSplice_none (witness : Bindings) (depth : ℕ) (kind : CollType) :
    restSplice sites witness depth kind none = ([], none) := rfl

mutual
  /-- **An instantiation whose goals hold is the instance's row.** -/
  theorem buildRow_sound (build : BuildClauses program) : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm}
      {goals : List Goal}, buildRow rests avoid sites depth next p = some (t, goals, next') →
      ∀ {θ : ℕ → Expr} {witness : Bindings}, (∀ name ∈ names p, Holds rests θ witness name) →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      inst θ t = encode (applyBindingsScoped sites witness depth p)
    | .fvar name, depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have held := holds name (by simp [names])
        rw [applyBindingsScoped_fvar]
        unfold Holds at held
        split at held
        · rename_i inRests
          obtain ⟨tail, value, listed⟩ := held
          simp only [if_pos inRests] at goals ⊢
          rw [OrderedRows.inst_vectorTerm (liftedList_sound build.scope listed goals), value]
          simp [liftBVars]
        · rename_i outside
          simp only [if_neg outside] at goals ⊢
          exact lifted_sound build.scope held goals
    | .bvar _, _, _, _, _, _, lowered, θ, _, _, _ => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        simp [applyBindingsScoped, encode]
    | .apply label arguments, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have listed := buildRows_sound build arguments found
          (fun name inside => holds name (by simpa [names] using inside)) goals (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        simp [applyBindingsScoped, encode, listed]
    | .lambda binder body, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have bodyIs := buildRow_sound build body found
          (fun name inside => holds name (by simpa [names] using inside)) goals
        simp [applyBindingsScoped, encode, inst_toTerm, bodyIs]
    | .multiLambda arity binders body, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have bodyIs := buildRow_sound build body found
          (fun name inside => holds name (by simpa [names] using inside)) goals
        simp [applyBindingsScoped, encode, inst_toTerm, bodyIs]
    | .subst body value, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        have bodyIs := buildRow_sound build body bodyFound
          (fun name inside => holds name (by simp [names, inside]))
          (fun g inside => goals g (List.mem_append_left _ (List.mem_append_left _ inside)))
        have valueIs := buildRow_sound build value valueFound
          (fun name inside => holds name (by simp [names, inside]))
          (fun g inside => goals g (List.mem_append_left _ (List.mem_append_right _ inside)))
        have asked := goals _ (List.mem_append_right _ List.mem_cons_self)
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, bodyIs, valueIs] at asked
        rw [DemandTransformation.inst_unknown, (instantiate_iff build.scope 0 _ _).mp asked]
        simp [applyBindingsScoped, instantiateBVar]
    | .collection .vec elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have listed := buildRows_sound build elements found
          (fun name inside => holds name (by simpa [names] using inside)) goals (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        rw [OrderedRows.inst_vectorTerm listed, applyBindingsScoped_collection, restSplice_none]
        simp
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          have restHolds := holds restName (by simp [names])
          simp only [Holds, if_pos inRests] at restHolds
          obtain ⟨tail, restValue, restListed⟩ := restHolds
          have closeIs := liftedList_sound build.scope restListed
            (fun g inside => goals g (List.mem_append_left _ inside))
          have listed := buildRows_sound build elements found
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_append_right _ inside)) closeIs
          rw [OrderedRows.inst_vectorTerm listed, applyBindingsScoped_collection,
            restSplice_bound (find_of_lookup_collection restValue)]
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have listed := buildRows_sound build elements found
          (fun name inside => holds name (by simpa [names] using inside)) goals (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        rw [inst_collectionTerm, listed, applyBindingsScoped_collection, restSplice_none, encode_collection]
        simp
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i notRest
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          have unwrapped := goals _ List.mem_cons_self
          simp only [goalHolds, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm] at unwrapped
          have restRow := unwrap_sound build.onlyUnwraps unwrapped
          have restHolds := holds restName (by simp [names])
          simp only [Holds, if_neg notRest] at restHolds
          obtain ⟨items, restValue, listIs⟩ := encode_closed_inv (restHolds.symm.trans restRow).symm
          have closeIs := liftedList_sound build.scope listIs
            (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_left _ inside)))
          have listed := buildRows_sound build elements found
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_right _ inside))) closeIs
          rw [inst_collectionTerm, listed, applyBindingsScoped_collection,
            restSplice_bound (find_of_lookup_collection restValue), encode_collection]
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        have listed := buildRows_sound build elements found
          (fun name inside => holds name (by simpa [names] using inside)) goals (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        rw [inst_collectionTerm, listed, applyBindingsScoped_collection, restSplice_none, encode_collection]
        simp
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i notRest
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          have unwrapped := goals _ List.mem_cons_self
          simp only [goalHolds, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm] at unwrapped
          have restRow := unwrap_sound build.onlyUnwraps unwrapped
          have restHolds := holds restName (by simp [names])
          simp only [Holds, if_neg notRest] at restHolds
          obtain ⟨items, restValue, listIs⟩ := encode_closed_inv (restHolds.symm.trans restRow).symm
          have closeIs := liftedList_sound build.scope listIs
            (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_left _ inside)))
          have listed := buildRows_sound build elements found
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_right _ inside))) closeIs
          rw [inst_collectionTerm, listed, applyBindingsScoped_collection,
            restSplice_bound (find_of_lookup_collection restValue), encode_collection]
        · cases lowered

  theorem buildRows_sound (build : BuildClauses program) : ∀ (patterns : List Pattern) {depth next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {witness : Bindings}, (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) → ∀ {tail : List Pattern},
      inst θ close = encodeList tail →
      inst θ list = encodeList (patterns.map (applyBindingsScoped sites witness depth) ++ tail)
    | [], _, _, _, _, _, _, lowered, θ, _, _, _, tail, closed => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        simpa using closed
    | pattern :: patterns, _, _, _, _, _, _, lowered, θ, witness, holds, goals, tail, closed => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tailRow, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, List.map_cons, List.cons_append, encodeList]
        rw [buildRow_sound build pattern headFound (fun name inside => holds name (by simp [namesList, inside]))
            (fun g inside => goals g (List.mem_append_left _ inside)),
          buildRows_sound build patterns tailFound (fun name inside => holds name (by simp [namesList, inside]))
            (fun g inside => goals g (List.mem_append_right _ inside)) closed]
end

end BuildSound

/-! ## What an instantiation lowering mentions -/

section BuildScope

variable {rests avoid : List String} {sites : Pattern}

theorem lifted_scope {names' : List String} {name : String} (named : name ∈ names') {relation shift next last : ℕ}
    (ordered : next < last) : ∀ u ∈ unknowns (lifted relation shift (labelCode name) (listUnknown avoid next)).1 ++
      (lifted relation shift (labelCode name) (listUnknown avoid next)).2.flatMap goalUnknowns,
      InScope avoid names' next last u := by
  intro u inside
  rcases lifted_unknowns relation shift _ _ u inside with rfl | rfl
  · exact .inl ⟨name, named, rfl⟩
  · exact .inr ⟨next, le_rfl, ordered, rfl⟩

/-- The scope of the rest of a bag or a set: its unwrapped list, its lifted list, then its elements. -/
theorem bagRest_scope {kind : CollType} {elements : List Pattern} {restName : String} {depth next last : ℕ}
    {list : Tm} {elementGoals : List Goal} (ordered : next + 2 ≤ last)
    (within : ∀ u ∈ unknowns list ++ elementGoals.flatMap goalUnknowns,
      u ∈ unknowns (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
        (listUnknown avoid (next + 1))).1 ∨ InScope avoid (namesList elements) (next + 2) last u) :
    next ≤ last ∧ ∀ u ∈ unknowns (collectionTerm kind list) ++
      (Goal.ask unwrapRelation (.var (labelCode restName))
        (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        ((lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals)).flatMap goalUnknowns,
      InScope avoid (names (.collection kind elements (some restName))) next last u := by
  refine ⟨by omega, fun u inside => ?_⟩
  have freshSide : ∀ v, v = listUnknown avoid next ∨ v = listUnknown avoid (next + 1) →
      InScope avoid (names (.collection kind elements (some restName))) next last v := by
    rintro v (rfl | rfl)
    · exact .inr ⟨next, le_rfl, by omega, rfl⟩
    · exact .inr ⟨next + 1, by omega, by omega, rfl⟩
  have closeSide : ∀ v ∈ unknowns (lifted liftListRelation (shiftOf sites restName depth)
      (listUnknown avoid next) (listUnknown avoid (next + 1))).1 ++ (lifted liftListRelation
      (shiftOf sites restName depth) (listUnknown avoid next) (listUnknown avoid (next + 1))).2.flatMap goalUnknowns,
      InScope avoid (names (.collection kind elements (some restName))) next last v :=
    fun v member => freshSide v (lifted_unknowns _ _ _ _ v member)
  rw [CollectionMatching.unknowns_collectionTerm, List.flatMap_cons, List.flatMap_append] at inside
  simp only [goalUnknowns, DemandTransformation.unknowns_unknown, RootRewritesOnTheStep.unknowns_appTerm,
    RootRewritesOnTheStep.unknowns_symTerm, List.nil_append, List.mem_append, List.mem_singleton] at inside
  rcases inside with inList | ((isRest | isList) | (inLiftGoals | inGoals))
  · rcases within u (List.mem_append_left _ inList) with inClose | inScope
    · exact closeSide u (List.mem_append_left _ inClose)
    · exact inScope.widen (fun name member => by simp [names, member]) (by omega) le_rfl
  · exact .inl ⟨restName, by simp [names], isRest⟩
  · exact freshSide u (.inl isList)
  · exact closeSide u (List.mem_append_right _ inLiftGoals)
  · rcases within u (List.mem_append_right _ inGoals) with inClose | inScope
    · exact closeSide u (List.mem_append_left _ inClose)
    · exact inScope.widen (fun name member => by simp [names, member]) (by omega) le_rfl

mutual
  /-- **An instantiation lowering mentions the pattern's names and its own fresh unknowns.** -/
  theorem buildRow_scope : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm} {goals : List Goal},
      buildRow rests avoid sites depth next p = some (t, goals, next') →
      next ≤ next' ∧ ∀ u ∈ unknowns t ++ goals.flatMap goalUnknowns, InScope avoid (names p) next next' u
    | .fvar name, depth, next, _, _, _, lowered => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨by omega, fun u inside => ?_⟩
        have named : name ∈ names (.fvar name) := by simp [names]
        by_cases inRests : name ∈ rests
        · simp only [inRests, ↓reduceIte, CollectionMatching.unknowns_vectorTerm] at inside
          exact lifted_scope named (by omega) u inside
        · simp only [inRests, ↓reduceIte] at inside
          exact lifted_scope named (by omega) u inside
    | .bvar _, _, _, _, _, _, lowered => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨le_rfl, fun u inside => by simp at inside⟩
    | .apply label arguments, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRows_scope arguments found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append]
          at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .lambda binder body, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRow_scope body found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, unknowns_toTerm,
          List.nil_append] at inside
        exact (within u inside).widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .multiLambda arity binders body, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRow_scope body found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, unknowns_toTerm,
          RootRewritesOnTheStep.unknowns_numeralTerm, List.nil_append] at inside
        exact (within u inside).widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .subst body value, depth, next, _, _, _, lowered => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        dsimp only at valueFound ⊢
        obtain ⟨bodyOrdered, bodyScoped⟩ := buildRow_scope body bodyFound
        obtain ⟨valueOrdered, valueScoped⟩ := buildRow_scope value valueFound
        refine ⟨by omega, fun u inside => ?_⟩
        have bodySide : ∀ v, InScope avoid (names body) next middle v →
            InScope avoid (names (.subst body value)) next (last + 1) v := fun v within =>
          within.widen (fun name member => by simp [names, member]) le_rfl (by omega)
        have valueSide : ∀ v, InScope avoid (names value) middle last v →
            InScope avoid (names (.subst body value)) next (last + 1) v := fun v within =>
          within.widen (fun name member => by simp [names, member]) bodyOrdered (by omega)
        have fresh : InScope avoid (names (.subst body value)) next (last + 1) (listUnknown avoid last) :=
          .inr ⟨last, by omega, by omega, rfl⟩
        simp only [DemandTransformation.unknowns_unknown, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          goalUnknowns, triple, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
          List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | (inBodyGoals | inValueGoals) | ((inValue | inBody) | rfl)
        · exact fresh
        · exact bodySide u (bodyScoped u (List.mem_append_right _ inBodyGoals))
        · exact valueSide u (valueScoped u (List.mem_append_right _ inValueGoals))
        · exact valueSide u (valueScoped u (List.mem_append_left _ inValue))
        · exact bodySide u (bodyScoped u (List.mem_append_left _ inBody))
        · exact fresh
    | .collection .vec elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRows_scope elements found
        refine ⟨ordered, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_vectorTerm] at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simp [names, member]) le_rfl le_rfl
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨ordered, within⟩ := buildRows_scope elements found
          dsimp only
          refine ⟨by omega, fun u inside => ?_⟩
          have restSide := lifted_scope (avoid := avoid) (names' := names (.collection .vec elements (some restName)))
            (name := restName) (by simp [names]) (relation := liftListRelation) (shift := shiftOf sites restName depth)
            (show next < last by omega)
          rw [CollectionMatching.unknowns_vectorTerm, List.flatMap_append, List.mem_append, List.mem_append] at inside
          rcases inside with inList | inRestGoals | inGoals
          · rcases within u (List.mem_append_left _ inList) with inClose | inScope
            · exact restSide u (List.mem_append_left _ inClose)
            · exact inScope.widen (fun name member => by simp [names, member]) (by omega) le_rfl
          · exact restSide u (List.mem_append_right _ inRestGoals)
          · rcases within u (List.mem_append_right _ inGoals) with inClose | inScope
            · exact restSide u (List.mem_append_left _ inClose)
            · exact inScope.widen (fun name member => by simp [names, member]) (by omega) le_rfl
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRows_scope elements found
        refine ⟨ordered, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_collectionTerm] at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simp [names, member]) le_rfl le_rfl
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          exact bagRest_scope (buildRows_scope elements found).1 (buildRows_scope elements found).2
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := buildRows_scope elements found
        refine ⟨ordered, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_collectionTerm] at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simp [names, member]) le_rfl le_rfl
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          exact bagRest_scope (buildRows_scope elements found).1 (buildRows_scope elements found).2
        · cases lowered

  theorem buildRows_scope : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      next ≤ next' ∧ ∀ u ∈ unknowns list ++ goals.flatMap goalUnknowns,
        u ∈ unknowns close ∨ InScope avoid (namesList patterns) next next' u
    | [], _, _, _, _, _, _, lowered => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨le_rfl, fun u inside => .inl (by simpa using inside)⟩
    | pattern :: patterns, _, next, _, _, _, _, lowered => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨headOrdered, headScoped⟩ := buildRow_scope pattern headFound
        obtain ⟨tailOrdered, tailScoped⟩ := buildRows_scope patterns tailFound
        refine ⟨le_trans headOrdered tailOrdered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, List.flatMap_append, List.mem_append] at inside
        have headSide : ∀ v, InScope avoid (names pattern) next middle v →
            InScope avoid (namesList (pattern :: patterns)) next last v := fun v within =>
          within.widen (fun name member => by simp [namesList, member]) le_rfl tailOrdered
        have tailSide : ∀ v, InScope avoid (namesList patterns) middle last v →
            InScope avoid (namesList (pattern :: patterns)) next last v := fun v within =>
          within.widen (fun name member => by simp [namesList, member]) headOrdered le_rfl
        rcases inside with (inHead | inTail) | inHeadGoals | inTailGoals
        · exact .inr (headSide u (headScoped u (List.mem_append_left _ inHead)))
        · rcases tailScoped u (List.mem_append_left _ inTail) with inClose | within
          · exact .inl inClose
          · exact .inr (tailSide u within)
        · exact .inr (headSide u (headScoped u (List.mem_append_right _ inHeadGoals)))
        · rcases tailScoped u (List.mem_append_right _ inTailGoals) with inClose | within
          · exact .inl inClose
          · exact .inr (tailSide u within)

end

end BuildScope

/-! ## Every instance is reached -/

section BuildComplete

variable {R : Relations} {program : List Clause} {rests avoid : List String} {sites : Pattern}

theorem lifted_untouched {name : String} (named : name ∈ avoid) {relation shift next first last : ℕ}
    (above : next < first) : ∀ u ∈ unknowns (lifted relation shift (labelCode name) (listUnknown avoid next)).1 ++
      (lifted relation shift (labelCode name) (listUnknown avoid next)).2.flatMap goalUnknowns,
      Untouched avoid first last u := by
  intro u inside
  rcases lifted_unknowns relation shift _ _ u inside with rfl | rfl
  · exact untouched_name named _ _
  · intro k low _ same
    have := listUnknown_injective avoid same
    omega

/-- The bag or set case of completeness of instantiation, once its elements are complete: the rest is unwrapped into
a fresh list, which is lifted into another. -/
theorem bagRest_complete (build : BuildClauses program) {kind : CollType} (unordered : kind ≠ .vec)
    {elements : List Pattern} {restName : String} {depth next last : ℕ} {list : Tm} {elementGoals : List Goal}
    (ordered : next + 2 ≤ last) (outside : restName ∉ rests)
    (named : ∀ name ∈ names (.collection kind elements (some restName)), name ∈ avoid)
    {witness : Bindings} {items : List Pattern}
    (bound : witness.find? (·.1 == restName) = some (restName, .collection kind items none))
    {θ : ℕ → Expr} (holds : ∀ name ∈ names (.collection kind elements (some restName)), Holds rests θ witness name)
    (elementsComplete : ∀ θ₁ : ℕ → Expr, (∀ name ∈ namesList elements, Holds rests θ₁ witness name) →
      inst θ₁ (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
        (listUnknown avoid (next + 1))).1 = encodeList (items.map (liftBVars 0 (shiftOf sites restName depth))) →
      (∀ u ∈ unknowns (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
        (listUnknown avoid (next + 1))).1, Untouched avoid (next + 2) last u) →
      ∃ θ', AgreeOutside avoid (next + 2) last θ₁ θ' ∧
        inst θ' list = encodeList (elements.map (applyBindingsScoped sites witness depth) ++
          items.map (liftBVars 0 (shiftOf sites restName depth))) ∧
        ∀ g ∈ elementGoals, goalHolds R (Derives R program) θ' g) :
    ∃ θ', AgreeOutside avoid next last θ θ' ∧
      inst θ' (collectionTerm kind list) =
        encode (applyBindingsScoped sites witness depth (.collection kind elements (some restName))) ∧
      ∀ g ∈ Goal.ask unwrapRelation (.var (labelCode restName))
          (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
          ((lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
            (listUnknown avoid (next + 1))).2 ++ elementGoals),
        goalHolds R (Derives R program) θ' g := by
  have restNamed := named restName (by simp [names])
  have namesUntouched : ∀ name ∈ names (.collection kind elements (some restName)), ∀ k,
      listUnknown avoid k ≠ labelCode name := fun name inside k => listUnknown_ne (named name inside) k
  have lists : listUnknown avoid next ≠ listUnknown avoid (next + 1) := fun same => by
    have := listUnknown_injective avoid same
    omega
  obtain ⟨θ₁, θ₁Is⟩ : ∃ θ₁ : ℕ → Expr, θ₁ = Function.update θ (listUnknown avoid next) (encodeList items) :=
    ⟨_, rfl⟩
  have unwrappedIs : θ₁ (listUnknown avoid next) = encodeList items := by simp [θ₁Is]
  obtain ⟨closeIs, closeHolds⟩ := liftedList_complete (R := R) build.scope (shift := shiftOf sites restName depth)
    unwrappedIs lists
  set θ₂ := Function.update θ₁ (listUnknown avoid (next + 1))
    (encodeList (items.map (liftBVars 0 (shiftOf sites restName depth)))) with θ₂Is
  have onNames : ∀ name ∈ names (.collection kind elements (some restName)), θ₂ (labelCode name) = θ (labelCode name) :=
    fun name inside => by
      rw [θ₂Is, Function.update_of_ne (namesUntouched name inside _).symm, θ₁Is,
        Function.update_of_ne (namesUntouched name inside _).symm]
  have closeUntouched : ∀ u ∈ unknowns (lifted liftListRelation (shiftOf sites restName depth)
      (listUnknown avoid next) (listUnknown avoid (next + 1))).1 ++ (lifted liftListRelation
      (shiftOf sites restName depth) (listUnknown avoid next) (listUnknown avoid (next + 1))).2.flatMap goalUnknowns,
      Untouched avoid (next + 2) last u := by
    intro u inside
    rcases lifted_unknowns _ _ _ _ u inside with rfl | rfl <;>
      · intro k low _ same
        have := listUnknown_injective avoid same
        omega
  obtain ⟨θ₃, agree, listed, goalsHold⟩ := elementsComplete θ₂
    (fun name inside => holds_congr (onNames name (by simp [names, inside])) (holds name (by simp [names, inside])))
    closeIs (fun u inside => closeUntouched u (List.mem_append_left _ inside))
  refine ⟨θ₃, fun u untouched => ?_, ?_, fun g inside => ?_⟩
  · rw [agree u fun k low high => untouched k (by omega) high, θ₂Is,
      Function.update_of_ne (untouched (next + 1) (by omega) (by omega)), θ₁Is,
      Function.update_of_ne (untouched next le_rfl (by omega))]
  · rw [inst_collectionTerm, listed, applyBindingsScoped_collection, restSplice_bound bound, encode_collection]
  · rcases List.mem_cons.mp inside with rfl | later
    · have restHolds := holds restName (by simp [names])
      simp only [Holds, if_neg outside] at restHolds
      have value : lookupOrFvar witness restName = .collection kind items none := by
        simp [lookupOrFvar, applyBindings, bound]
      have restKept : θ₃ (labelCode restName) = θ (labelCode restName) := by
        rw [agree _ (untouched_name restNamed _ _)]
        exact onNames restName (by simp [names])
      have listKept : θ₃ (listUnknown avoid next) = encodeList items := by
        rw [agree _ fun k low _ same => by have := listUnknown_injective avoid same; omega, θ₂Is,
          Function.update_of_ne lists]
        exact unwrappedIs
      simp only [goalHolds, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_appTerm,
        RootRewritesOnTheStep.inst_symTerm, restKept, listKept, restHolds, value, encode_collection]
      exact unwrap_complete build.unwraps unordered (encodeList items)
    · rcases List.mem_append.mp later with inLift | inElements
      · exact goals_agree (fun u inU => agree u (closeUntouched u (List.mem_append_right _ inU))) closeHolds g inLift
      · exact goalsHold g inElements

mutual
  /-- **Every instance of a pattern is a clause instance whose goals hold**, changed only at the lowering's own
  fresh unknowns. -/
  theorem buildRow_complete (build : BuildClauses program) : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm}
      {goals : List Goal}, buildRow rests avoid sites depth next p = some (t, goals, next') →
      (∀ name ∈ names p, name ∈ avoid) → ∀ {witness : Bindings}, BagSettled witness (bagRests p) →
      ∀ {θ : ℕ → Expr}, (∀ name ∈ names p, Holds rests θ witness name) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧ inst θ' t = encode (applyBindingsScoped sites witness depth p) ∧
        ∀ g ∈ goals, goalHolds R (Derives R program) θ' g
    | .fvar name, depth, next, _, _, _, lowered, named, witness, _, θ, holds => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have held := holds name (by simp [names])
        have distinct : labelCode name ≠ listUnknown avoid next :=
          (listUnknown_ne (named name (by simp [names])) next).symm
        rw [applyBindingsScoped_fvar]
        by_cases inRests : name ∈ rests
        · simp only [Holds, if_pos inRests] at held
          obtain ⟨tail, value, listed⟩ := held
          obtain ⟨rowIs, goalsHold⟩ := liftedList_complete (R := R) build.scope (shift := shiftOf sites name depth)
            listed distinct
          refine ⟨Function.update θ (listUnknown avoid next) (encodeList (tail.map
            (liftBVars 0 (shiftOf sites name depth)))), fun u untouched =>
              Function.update_of_ne (untouched next le_rfl (by omega)) _ _, ?_, ?_⟩
          · simp only [inRests, ↓reduceIte]
            rw [OrderedRows.inst_vectorTerm rowIs, value]
            simp [liftBVars]
          · simpa only [inRests, ↓reduceIte] using goalsHold
        · simp only [Holds, if_neg inRests] at held
          obtain ⟨rowIs, goalsHold⟩ := lifted_complete (R := R) build.scope (shift := shiftOf sites name depth)
            held distinct
          refine ⟨Function.update θ (listUnknown avoid next) (encode (liftBVars 0 (shiftOf sites name depth)
            (lookupOrFvar witness name))), fun u untouched =>
              Function.update_of_ne (untouched next le_rfl (by omega)) _ _, ?_, ?_⟩
          · simpa only [inRests, ↓reduceIte] using rowIs
          · simpa only [inRests, ↓reduceIte] using goalsHold
    | .bvar _, _, _, _, _, _, lowered, _, _, _, θ, _ => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨θ, AgreeOutside.refl θ, by simp [applyBindingsScoped, encode],
          fun _ inside => absurd inside List.not_mem_nil⟩
    | .apply label arguments, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, listed, goalsHold⟩ := buildRows_complete build arguments found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
          (fun u inside => by simp at inside)
        refine ⟨θ', agree, ?_, goalsHold⟩
        rw [List.append_nil] at listed
        simp [applyBindingsScoped, encode, listed]
    | .lambda binder body, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, bodyIs, goalsHold⟩ := buildRow_complete build body found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside))
        exact ⟨θ', agree, by simp [applyBindingsScoped, encode, inst_toTerm, bodyIs], goalsHold⟩
    | .multiLambda arity binders body, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, bodyIs, goalsHold⟩ := buildRow_complete build body found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside))
        exact ⟨θ', agree, by simp [applyBindingsScoped, encode, inst_toTerm, bodyIs], goalsHold⟩
    | .subst body value, depth, next, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        dsimp only at valueFound ⊢
        obtain ⟨bodyOrdered, bodyScope⟩ := buildRow_scope body bodyFound
        obtain ⟨valueOrdered, valueScope⟩ := buildRow_scope value valueFound
        have bodyNamed : ∀ name ∈ names body, name ∈ avoid :=
          fun name inside => named name (by simp [names, inside])
        have valueNamed : ∀ name ∈ names value, name ∈ avoid :=
          fun name inside => named name (by simp [names, inside])
        obtain ⟨θ₁, agree₁, bodyIs, bodyHolds⟩ := buildRow_complete build body bodyFound bodyNamed
          (fun pair member => bags pair (by simp [bagRests, member]))
          (fun name inside => holds name (by simp [names, inside]))
        have onValueNames : ∀ name ∈ names value, θ₁ (labelCode name) = θ (labelCode name) :=
          fun name inside => agree₁ _ (untouched_name (valueNamed name inside) _ _)
        obtain ⟨θ₂, agree₂, valueIs, valueHolds⟩ := buildRow_complete build value valueFound valueNamed
          (fun pair member => bags pair (by simp [bagRests, member]))
          (fun name inside => holds_congr (onValueNames name inside) (holds name (by simp [names, inside])))
        have bodyStays : ∀ u ∈ unknowns bodyRow ++ bodyGoals.flatMap goalUnknowns, θ₂ u = θ₁ u :=
          fun u inside => agree₂ u ((bodyScope u inside).untouched bodyNamed (.inl le_rfl))
        have bodyIs₂ : inst θ₂ bodyRow = encode (applyBindingsScoped sites witness (depth + 1) body) := by
          rw [DemandTransformation.inst_agree bodyRow fun u inside => bodyStays u (List.mem_append_left _ inside),
            bodyIs]
        have bodyFresh : ∀ u ∈ unknowns bodyRow ++ bodyGoals.flatMap goalUnknowns, u ≠ listUnknown avoid last :=
          fun u inside => InScope.untouched (c := last) (d := last + 1) (bodyScope u inside) bodyNamed
            (.inl valueOrdered) last le_rfl (by omega)
        have valueFresh : ∀ u ∈ unknowns valueRow ++ valueGoals.flatMap goalUnknowns, u ≠ listUnknown avoid last :=
          fun u inside => InScope.untouched (c := last) (d := last + 1) (valueScope u inside) valueNamed
            (.inl le_rfl) last le_rfl (by omega)
        refine ⟨Function.update θ₂ (listUnknown avoid last)
          (encode (applyBindingsScoped sites witness depth (.subst body value))), fun u untouched => ?_, ?_,
          fun g inside => ?_⟩
        · rw [Function.update_of_ne (untouched last (by omega) (by omega))]
          exact (agree₁.trans agree₂ bodyOrdered valueOrdered) u fun k low high => untouched k low (by omega)
        · simp
        · simp only [List.mem_append, List.mem_singleton] at inside
          rcases inside with (inBody | inValue) | rfl
          · exact goals_agree (fun u inU => (Function.update_of_ne (bodyFresh u (List.mem_append_right _ inU)) _ _).trans
              (bodyStays u (List.mem_append_right _ inU))) bodyHolds g inBody
          · exact goals_agree (fun u inU => Function.update_of_ne (valueFresh u (List.mem_append_right _ inU)) _ _)
              valueHolds g inValue
          · simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, Function.update_self]
            rw [DemandTransformation.inst_agree valueRow fun u inU =>
                Function.update_of_ne (valueFresh u (List.mem_append_left _ inU)) _ _, valueIs,
              DemandTransformation.inst_agree bodyRow fun u inU =>
                Function.update_of_ne (bodyFresh u (List.mem_append_left _ inU)) _ _, bodyIs₂]
            exact (instantiate_iff build.scope 0 _ _).mpr (by simp [applyBindingsScoped, instantiateBVar])
    | .collection .vec elements none, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, listed, goalsHold⟩ := buildRows_complete build elements found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
          (fun u inside => by simp at inside)
        refine ⟨θ', agree, ?_, goalsHold⟩
        rw [List.append_nil] at listed
        rw [OrderedRows.inst_vectorTerm listed, applyBindingsScoped_collection, restSplice_none]
        simp
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨ordered, -⟩ := buildRows_scope elements found
          dsimp only
          have restNamed := named restName (by simp [names])
          have restHolds := holds restName (by simp [names])
          simp only [Holds, if_pos inRests] at restHolds
          obtain ⟨tail, restValue, restListed⟩ := restHolds
          obtain ⟨closeIs, closeHolds⟩ := liftedList_complete (R := R) build.scope
            (shift := shiftOf sites restName depth) restListed (listUnknown_ne restNamed next).symm
          set θ₁ := Function.update θ (listUnknown avoid next)
            (encodeList (tail.map (liftBVars 0 (shiftOf sites restName depth)))) with θ₁Is
          have closeUntouched := lifted_untouched (avoid := avoid) (relation := liftListRelation)
            (shift := shiftOf sites restName depth) restNamed (next := next) (first := next + 1) (last := last)
            (by omega)
          obtain ⟨θ₂, agree₂, listed, goalsHold⟩ := buildRows_complete build elements found
            (fun name inside => named name (by simp [names, inside]))
            (fun pair member => bags pair (by simpa [bagRests] using member)) (θ := θ₁)
            (fun name inside => holds_congr (by
              rw [θ₁Is]
              exact Function.update_of_ne (listUnknown_ne (named name (by simp [names, inside])) next).symm _ _)
              (holds name (by simp [names, inside]))) closeIs
            (fun u inside => closeUntouched u (List.mem_append_left _ inside))
          refine ⟨θ₂, fun u untouched => ?_, ?_, fun g inside => ?_⟩
          · rw [agree₂ u fun k low high => untouched k (by omega) high, θ₁Is]
            exact Function.update_of_ne (untouched next le_rfl (by omega)) _ _
          · rw [OrderedRows.inst_vectorTerm listed, applyBindingsScoped_collection,
              restSplice_bound (find_of_lookup_collection restValue)]
          · rcases List.mem_append.mp inside with inClose | inElements
            · exact goals_agree (fun u inU => agree₂ u (closeUntouched u (List.mem_append_right _ inU))) closeHolds g
                inClose
            · exact goalsHold g inElements
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, listed, goalsHold⟩ := buildRows_complete build elements found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
          (fun u inside => by simp at inside)
        refine ⟨θ', agree, ?_, goalsHold⟩
        rw [List.append_nil] at listed
        rw [inst_collectionTerm, listed, applyBindingsScoped_collection, restSplice_none, encode_collection]
        simp
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, named, witness, bags, θ,
        holds => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, bound⟩ := bags (restName, .hashBag) (by simp [bagRests])
          exact bagRest_complete build (by decide) (buildRows_scope elements found).1 outside named bound holds
            fun θ₁ holds₁ closed untouched => buildRows_complete build elements found
              (fun name inside => named name (by simp [names, inside]))
              (fun pair member => bags pair (by simp [bagRests, member])) holds₁ closed untouched
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, named, witness, bags, θ, holds => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨θ', agree, listed, goalsHold⟩ := buildRows_complete build elements found
          (fun name inside => named name (by simpa [names] using inside))
          (fun pair member => bags pair (by simpa [bagRests] using member))
          (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
          (fun u inside => by simp at inside)
        refine ⟨θ', agree, ?_, goalsHold⟩
        rw [List.append_nil] at listed
        rw [inst_collectionTerm, listed, applyBindingsScoped_collection, restSplice_none, encode_collection]
        simp
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, named, witness, bags, θ,
        holds => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, bound⟩ := bags (restName, .hashSet) (by simp [bagRests])
          exact bagRest_complete build (by decide) (buildRows_scope elements found).1 outside named bound holds
            fun θ₁ holds₁ closed untouched => buildRows_complete build elements found
              (fun name inside => named name (by simp [names, inside]))
              (fun pair member => bags pair (by simp [bagRests, member])) holds₁ closed untouched
        · cases lowered

  theorem buildRows_complete (build : BuildClauses program) : ∀ (patterns : List Pattern) {depth next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      (∀ name ∈ namesList patterns, name ∈ avoid) → ∀ {witness : Bindings},
      BagSettled witness (bagRestsList patterns) → ∀ {θ : ℕ → Expr},
      (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      ∀ {tail : List Pattern}, inst θ close = encodeList tail → (∀ u ∈ unknowns close, Untouched avoid next next' u) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧
        inst θ' list = encodeList (patterns.map (applyBindingsScoped sites witness depth) ++ tail) ∧
        ∀ g ∈ goals, goalHolds R (Derives R program) θ' g
    | [], _, _, _, _, _, _, lowered, _, _, _, θ, _, tail, closed, _ => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨θ, AgreeOutside.refl θ, by simpa using closed, fun _ inside => absurd inside List.not_mem_nil⟩
    | pattern :: patterns, depth, next, _, close, _, _, lowered, named, witness, bags, θ, holds, tail, closed,
        closeUntouched => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tailRow, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        dsimp only at tailFound closeUntouched ⊢
        obtain ⟨headOrdered, headScope⟩ := buildRow_scope pattern headFound
        obtain ⟨tailOrdered, -⟩ := buildRows_scope patterns tailFound
        have headNamed : ∀ name ∈ names pattern, name ∈ avoid :=
          fun name inside => named name (by simp [namesList, inside])
        have tailNamed : ∀ name ∈ namesList patterns, name ∈ avoid :=
          fun name inside => named name (by simp [namesList, inside])
        obtain ⟨θ₁, agree₁, headIs, headHolds⟩ := buildRow_complete build pattern headFound headNamed
          (fun pair member => bags pair (by simp [bagRestsList, member]))
          fun name inside => holds name (by simp [namesList, inside])
        have onTailNames : ∀ name ∈ namesList patterns, θ₁ (labelCode name) = θ (labelCode name) :=
          fun name inside => agree₁ _ (untouched_name (tailNamed name inside) _ _)
        obtain ⟨θ₂, agree₂, tailIs, tailHolds⟩ := buildRows_complete build patterns tailFound tailNamed
          (fun pair member => bags pair (by simp [bagRestsList, member]))
          (fun name inside => holds_congr (onTailNames name inside) (holds name (by simp [namesList, inside])))
          (tail := tail)
          (by rw [← closed]; exact DemandTransformation.inst_agree close fun u inside =>
            agree₁ u fun k low high => closeUntouched u inside k low (by omega))
          (fun u inside k low high => closeUntouched u inside k (by omega) high)
        have headStays : ∀ u ∈ unknowns head ++ headGoals.flatMap goalUnknowns, θ₂ u = θ₁ u := fun u inside =>
          agree₂ u ((headScope u inside).untouched headNamed (.inl le_rfl))
        refine ⟨θ₂, agree₁.trans agree₂ headOrdered tailOrdered, ?_, fun g inside => ?_⟩
        · simp only [RootRewritesOnTheStep.inst_appTerm, List.map_cons, List.cons_append, encodeList, tailIs]
          rw [DemandTransformation.inst_agree head fun u inside => headStays u (List.mem_append_left _ inside),
            headIs]
        · rcases List.mem_append.mp inside with inHead | inTail
          · exact goals_agree (fun u inU => headStays u (List.mem_append_right _ inU)) headHolds g inHead
          · exact tailHolds g inTail
end

end BuildComplete

/-! ## The goals of an instantiation in order -/

section BuildModes

variable {rests avoid : List String} {sites : Pattern}

/-- The modes of the rest of a bag or a set: unwrapped from its name, lifted, then the elements. -/
theorem bagRest_moded {kind : CollType} {restName : String} {depth next : ℕ} {list : Tm} {elementGoals : List Goal}
    {bound : List ℕ} (restBound : labelCode restName ∈ bound)
    (elements : ∀ {bound' : List ℕ}, (∀ u ∈ unknowns (lifted liftListRelation (shiftOf sites restName depth)
        (listUnknown avoid next) (listUnknown avoid (next + 1))).1, u ∈ bound') → (∀ u ∈ bound, u ∈ bound') →
      InputsBound bound' elementGoals ∧ ∀ u ∈ unknowns list, u ∈ bound' ++ elementGoals.flatMap goalUnknowns) :
    InputsBound bound (Goal.ask unwrapRelation (.var (labelCode restName))
        (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        ((lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals)) ∧
      ∀ u ∈ unknowns (collectionTerm kind list), u ∈ bound ++ (Goal.ask unwrapRelation (.var (labelCode restName))
        (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        ((lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals)).flatMap goalUnknowns := by
  set unwrapGoal : Goal := .ask unwrapRelation (.var (labelCode restName))
    (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next)))
  set found := lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
    (listUnknown avoid (next + 1))
  have listBound : listUnknown avoid next ∈ bound ++ goalUnknowns unwrapGoal := by
    simp [unwrapGoal, goalUnknowns]
  obtain ⟨liftFlows, liftBound⟩ := lifted_moded liftListRelation (shiftOf sites restName depth)
    (listUnknown avoid next) (listUnknown avoid (next + 1)) listBound
  obtain ⟨elementFlows, rowBound⟩ := elements (bound' := bound ++ goalUnknowns unwrapGoal ++ found.2.flatMap goalUnknowns)
    (fun u inside => liftBound u inside) (fun u inside => List.mem_append_left _ (List.mem_append_left _ inside))
  refine ⟨.cons (fun x inside => ?_) (liftFlows.append elementFlows), fun u inside => ?_⟩
  · simp only [unwrapGoal, goalInputs, DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
    rw [inside]
    exact restBound
  · rw [CollectionMatching.unknowns_collectionTerm] at inside
    have here := rowBound u inside
    simp only [List.flatMap_cons, List.flatMap_append, List.mem_append] at here ⊢
    tauto

mutual
  /-- **An instantiation lowering's goals are bound in order from the pattern's names, and bind its row.** -/
  theorem buildRow_moded : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm} {goals : List Goal},
      buildRow rests avoid sites depth next p = some (t, goals, next') → ∀ {bound : List ℕ},
      (∀ name ∈ names p, labelCode name ∈ bound) →
      InputsBound bound goals ∧ ∀ u ∈ unknowns t, u ∈ bound ++ goals.flatMap goalUnknowns
    | .fvar name, depth, next, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have nameBound := named name (by simp [names])
        by_cases inRests : name ∈ rests
        · simp only [inRests, ↓reduceIte, CollectionMatching.unknowns_vectorTerm]
          exact lifted_moded _ _ _ _ nameBound
        · simp only [inRests, ↓reduceIte]
          exact lifted_moded _ _ _ _ nameBound
    | .bvar _, _, _, _, _, _, lowered, bound, _ => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => by simp at inside⟩
    | .apply _ arguments, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRows_moded arguments found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append]
          at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .lambda _ body, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRow_moded body found fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, unknowns_toTerm,
          List.nil_append] at inside
        exact rowBound u inside
    | .multiLambda _ _ body, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRow_moded body found fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, unknowns_toTerm,
          RootRewritesOnTheStep.unknowns_numeralTerm, List.nil_append] at inside
        exact rowBound u inside
    | .subst body value, depth, next, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        obtain ⟨bodyFlows, bodyBound⟩ := buildRow_moded body bodyFound
          fun name inside => named name (by simp [names, inside])
        obtain ⟨valueFlows, valueBound⟩ := buildRow_moded value valueFound
          (bound := bound ++ bodyGoals.flatMap goalUnknowns)
          fun name inside => List.mem_append_left _ (named name (by simp [names, inside]))
        refine ⟨(bodyFlows.append valueFlows).append (.cons (fun x inside => ?_) (.nil _)), fun u inside => ?_⟩
        · simp only [goalInputs, triple, RootRewritesOnTheStep.unknowns_appTerm,
            RootRewritesOnTheStep.unknowns_symTerm, List.nil_append, List.mem_append] at inside
          rcases inside with inValue | inBody
          · have here := valueBound x inValue
            simp only [List.flatMap_append, List.mem_append] at here ⊢
            tauto
          · have here := bodyBound x inBody
            simp only [List.flatMap_append, List.mem_append] at here ⊢
            tauto
        · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
          subst inside
          simp [goalUnknowns]
    | .collection .vec elements none, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRows_moded elements found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_vectorTerm] at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, bound, named => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨liftFlows, liftBound⟩ := lifted_moded liftListRelation (shiftOf sites restName depth)
            (labelCode restName) (listUnknown avoid next) (named restName (by simp [names]))
          obtain ⟨flows, rowBound⟩ := buildRows_moded elements found
            (bound := bound ++ (lifted liftListRelation (shiftOf sites restName depth) (labelCode restName)
              (listUnknown avoid next)).2.flatMap goalUnknowns)
            fun name inside => List.mem_append_left _ (named name (by simp [names, inside]))
          refine ⟨liftFlows.append flows, fun u inside => ?_⟩
          rw [CollectionMatching.unknowns_vectorTerm] at inside
          rcases rowBound u inside with inClose | inBound
          · have here := liftBound u inClose
            simp only [List.flatMap_append, List.mem_append] at here ⊢
            tauto
          · simp only [List.flatMap_append, List.mem_append] at inBound ⊢
            tauto
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRows_moded elements found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_collectionTerm] at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, bound, named => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          exact bagRest_moded (named restName (by simp [names])) fun closeBound wider =>
            (buildRows_moded elements found fun name inside => wider _ (named name (by simp [names, inside]))).imp_right
              fun rowBound u inside => (rowBound u inside).elim (fun inClose => List.mem_append_left _
                (closeBound u inClose)) id
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, bound, named => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := buildRows_moded elements found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        rw [CollectionMatching.unknowns_collectionTerm] at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, bound, named => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          exact bagRest_moded (named restName (by simp [names])) fun closeBound wider =>
            (buildRows_moded elements found fun name inside => wider _ (named name (by simp [names, inside]))).imp_right
              fun rowBound u inside => (rowBound u inside).elim (fun inClose => List.mem_append_left _
                (closeBound u inClose)) id
        · cases lowered

  theorem buildRows_moded : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') → ∀ {bound : List ℕ},
      (∀ name ∈ namesList patterns, labelCode name ∈ bound) →
      InputsBound bound goals ∧ ∀ u ∈ unknowns list, u ∈ unknowns close ∨ u ∈ bound ++ goals.flatMap goalUnknowns
    | [], _, _, _, _, _, _, lowered, bound, _ => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => .inl inside⟩
    | pattern :: patterns, _, _, _, _, _, _, lowered, bound, named => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨headFlows, headBound⟩ := buildRow_moded pattern headFound
          fun name inside => named name (by simp [namesList, inside])
        obtain ⟨tailFlows, tailBound⟩ := buildRows_moded patterns tailFound
          (bound := bound ++ headGoals.flatMap goalUnknowns)
          fun name inside => List.mem_append_left _ (named name (by simp [namesList, inside]))
        refine ⟨headFlows.append tailFlows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, List.mem_append] at inside
        rcases inside with inHead | inTail
        · have here := headBound u inHead
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
        · have here := tailBound u inTail
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
end

end BuildModes

/-! ## The instance depends on the values of its names, and data stays data -/

section ScopedData

open OrderedMatching (isData isDataList isDataList_iff DataOn Settled)
open MatchesAndInstances (vectorRests vectorRestsList)
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVarAt liftBVarsList_eq_map)

/-- What a rest contributes depends on the value of its name. -/
theorem restSplice_some (sites : Pattern) (witness : Bindings) (depth : ℕ) (kind : CollType) (rest : String) :
    restSplice sites witness depth kind (some rest) =
      match lookupOrFvar witness rest with
      | .collection boundKind tail none =>
          if boundKind == kind then (tail.map (liftBVars 0 (shiftOf sites rest depth)), none) else ([], some rest)
      | _ => ([], some rest) := by
  simp only [restSplice, lookupOrFvar, applyBindings, shiftOf]
  cases found : witness.find? (·.1 == rest) with
  | none => rfl
  | some entry =>
      obtain ⟨key, value⟩ := entry
      cases value with
      | collection boundKind tail open_ =>
          cases open_ with
          | none =>
              simp only
              split
              · cases captureDepth rest 0 sites with
                | none => simp [map_liftBVars_zero]
                | some captured => rfl
              · rfl
          | some _ => rfl
      | _ => rfl

mutual
  /-- **A scope-correct instance depends only on the values of the pattern's names.** -/
  theorem applyBindingsScoped_agree (sites : Pattern) {first second : Bindings} : ∀ (depth : ℕ) (p : Pattern),
      (∀ name ∈ names p, lookupOrFvar first name = lookupOrFvar second name) →
      applyBindingsScoped sites first depth p = applyBindingsScoped sites second depth p
    | depth, .fvar name, agree => by
        rw [applyBindingsScoped_fvar, applyBindingsScoped_fvar, agree name (by simp [names])]
    | _, .bvar _, _ => rfl
    | depth, .apply label arguments, agree => by
        simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]
        rw [applyBindingsScopedList_agree sites depth arguments fun name inside => agree name (by simpa [names] using inside)]
    | depth, .lambda binder body, agree => by
        simp only [applyBindingsScoped]
        rw [applyBindingsScoped_agree sites (depth + 1) body fun name inside => agree name (by simpa [names] using inside)]
    | depth, .multiLambda arity binders body, agree => by
        simp only [applyBindingsScoped]
        rw [applyBindingsScoped_agree sites (depth + arity) body
          fun name inside => agree name (by simpa [names] using inside)]
    | depth, .subst body value, agree => by
        simp only [applyBindingsScoped]
        rw [applyBindingsScoped_agree sites (depth + 1) body fun name inside => agree name (by simp [names, inside]),
          applyBindingsScoped_agree sites depth value fun name inside => agree name (by simp [names, inside])]
    | depth, .collection kind elements rest, agree => by
        rw [applyBindingsScoped_collection, applyBindingsScoped_collection,
          applyBindingsScopedList_agree sites depth elements fun name inside => agree name (by simp [names, inside])]
        cases rest with
        | none => rfl
        | some restName =>
            rw [restSplice_some, restSplice_some, agree restName (by simp [names])]

  theorem applyBindingsScopedList_agree (sites : Pattern) {first second : Bindings} : ∀ (depth : ℕ) (ps : List Pattern),
      (∀ name ∈ namesList ps, lookupOrFvar first name = lookupOrFvar second name) →
      ps.map (applyBindingsScoped sites first depth) = ps.map (applyBindingsScoped sites second depth)
    | _, [], _ => rfl
    | depth, p :: ps, agree => by
        simp only [List.map_cons]
        rw [applyBindingsScoped_agree sites depth p fun name inside => agree name (by simp [namesList, inside]),
          applyBindingsScopedList_agree sites depth ps fun name inside => agree name (by simp [namesList, inside])]
end

theorem lookupOrFvar_data {bindings : Bindings} (values : DataOn bindings) (name : String) :
    isData (lookupOrFvar bindings name) = true := by
  simp only [lookupOrFvar, applyBindings]
  cases found : bindings.find? (·.1 == name) with
  | none => rfl
  | some entry =>
      obtain ⟨key, value⟩ := entry
      have same : key = name := by simpa using List.find?_some found
      subst same
      exact values key value found

mutual
  theorem isData_liftBVars (cutoff shift : ℕ) : ∀ p : Pattern, isData (liftBVars cutoff shift p) = isData p
    | .bvar index => by
        simp only [liftBVars]
        split <;> rfl
    | .fvar _ => rfl
    | .apply _ arguments => by
        simp only [liftBVars, liftBVarsList_eq_map, isData]
        exact isDataList_liftBVars cutoff shift arguments
    | .lambda _ body => by simp only [liftBVars, isData, isData_liftBVars (cutoff + 1) shift body]
    | .multiLambda arity _ body => by simp only [liftBVars, isData, isData_liftBVars (cutoff + arity) shift body]
    | .subst body value => by
        simp only [liftBVars, isData, isData_liftBVars (cutoff + 1) shift body, isData_liftBVars cutoff shift value]
    | .collection _ elements _ => by
        simp only [liftBVars, liftBVarsList_eq_map, isData]
        rw [isDataList_liftBVars cutoff shift elements]

  theorem isDataList_liftBVars (cutoff shift : ℕ) :
      ∀ ps : List Pattern, isDataList (ps.map (liftBVars cutoff shift)) = isDataList ps
    | [] => rfl
    | p :: ps => by
        simp only [List.map_cons, isDataList, isData_liftBVars cutoff shift p, isDataList_liftBVars cutoff shift ps]
end

mutual
  theorem isData_instantiateBVarAt {replacement : Pattern} (data : isData replacement = true) :
      ∀ (depth : ℕ) (p : Pattern), isData p = true → isData (instantiateBVarAt depth replacement p) = true
    | depth, .bvar index, _ => by
        rw [instantiateBVarAt]
        split
        · rfl
        · split
          · rw [isData_liftBVars]
            exact data
          · rfl
    | _, .fvar _, _ => by
        rw [instantiateBVarAt]
        rfl
    | depth, .apply _ arguments, pData => by
        rw [instantiateBVarAt]
        simp only [isData] at pData ⊢
        exact isDataList_instantiateBVarAt data depth arguments pData
    | depth, .lambda _ body, pData => by
        rw [instantiateBVarAt]
        simp only [isData, Bool.and_eq_true] at pData ⊢
        exact ⟨pData.1, isData_instantiateBVarAt data (depth + 1) body pData.2⟩
    | depth, .multiLambda arity _ body, pData => by
        rw [instantiateBVarAt]
        simp only [isData, Bool.and_eq_true] at pData ⊢
        exact ⟨pData.1, isData_instantiateBVarAt data (depth + arity) body pData.2⟩
    | depth, .subst body value, pData => by
        rw [instantiateBVarAt]
        simp only [isData, Bool.and_eq_true] at pData ⊢
        exact ⟨isData_instantiateBVarAt data (depth + 1) body pData.1, isData_instantiateBVarAt data depth value pData.2⟩
    | depth, .collection _ elements _, pData => by
        rw [instantiateBVarAt]
        simp only [isData, Bool.and_eq_true] at pData ⊢
        exact ⟨pData.1, isDataList_instantiateBVarAt data depth elements pData.2⟩

  theorem isDataList_instantiateBVarAt {replacement : Pattern} (data : isData replacement = true) :
      ∀ (depth : ℕ) (ps : List Pattern), isDataList ps = true →
        isDataList (ps.map (instantiateBVarAt depth replacement)) = true
    | _, [], _ => rfl
    | depth, p :: ps, psData => by
        simp only [isDataList, Bool.and_eq_true, List.map_cons] at psData ⊢
        exact ⟨isData_instantiateBVarAt data depth p psData.1, isDataList_instantiateBVarAt data depth ps psData.2⟩
end

mutual
  /-- **What instantiates to data is data.** -/
  theorem isData_of_instantiateBVarAt {replacement : Pattern} :
      ∀ (depth : ℕ) (p : Pattern), isData (instantiateBVarAt depth replacement p) = true → isData p = true
    | _, .bvar _, _ => rfl
    | _, .fvar _, _ => rfl
    | depth, .apply _ arguments, instData => by
        rw [instantiateBVarAt] at instData
        simp only [isData] at instData ⊢
        exact isDataList_of_instantiateBVarAt depth arguments instData
    | depth, .lambda _ body, instData => by
        rw [instantiateBVarAt] at instData
        simp only [isData, Bool.and_eq_true] at instData ⊢
        exact ⟨instData.1, isData_of_instantiateBVarAt (depth + 1) body instData.2⟩
    | depth, .multiLambda arity _ body, instData => by
        rw [instantiateBVarAt] at instData
        simp only [isData, Bool.and_eq_true] at instData ⊢
        exact ⟨instData.1, isData_of_instantiateBVarAt (depth + arity) body instData.2⟩
    | depth, .subst body value, instData => by
        rw [instantiateBVarAt] at instData
        simp only [isData, Bool.and_eq_true] at instData ⊢
        exact ⟨isData_of_instantiateBVarAt (depth + 1) body instData.1,
          isData_of_instantiateBVarAt depth value instData.2⟩
    | depth, .collection _ elements _, instData => by
        rw [instantiateBVarAt] at instData
        simp only [isData, Bool.and_eq_true] at instData ⊢
        exact ⟨instData.1, isDataList_of_instantiateBVarAt depth elements instData.2⟩

  theorem isDataList_of_instantiateBVarAt {replacement : Pattern} :
      ∀ (depth : ℕ) (ps : List Pattern), isDataList (ps.map (instantiateBVarAt depth replacement)) = true →
        isDataList ps = true
    | _, [], _ => rfl
    | depth, p :: ps, psData => by
        simp only [isDataList, Bool.and_eq_true, List.map_cons] at psData ⊢
        exact ⟨isData_of_instantiateBVarAt depth p psData.1, isDataList_of_instantiateBVarAt depth ps psData.2⟩
end

mutual
  /-- **A scope-correct instance of a pattern without binder names, under data whose rests are settled, is data.** -/
  theorem scoped_data {bindings : Bindings} (values : DataOn bindings) (sites : Pattern) : ∀ (depth : ℕ) (p : Pattern),
      p.hasCanonicalBinderMetadata = true → Settled bindings (vectorRests p) → BagSettled bindings (bagRests p) →
      isData (applyBindingsScoped sites bindings depth p) = true
    | depth, .fvar name, _, _, _ => by
        rw [applyBindingsScoped_fvar, isData_liftBVars]
        exact lookupOrFvar_data values name
    | _, .bvar _, _, _, _ => rfl
    | depth, .apply _ arguments, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simp only [applyBindingsScoped, applyBindingsScopedList_eq_map, isData]
        exact scopedList_data values sites depth arguments canonical settled bags
    | depth, .lambda _ body, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [applyBindingsScoped, isData, Bool.and_eq_true]
        exact ⟨canonical.1, scoped_data values sites (depth + 1) body canonical.2 settled bags⟩
    | depth, .multiLambda arity _ body, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [applyBindingsScoped, isData, Bool.and_eq_true]
        exact ⟨canonical.1, scoped_data values sites (depth + arity) body canonical.2 settled bags⟩
    | depth, .subst body value, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [applyBindingsScoped, instantiateBVar]
        exact isData_instantiateBVarAt
          (scoped_data values sites depth value canonical.2
            (fun rest inside => settled rest (by simp [vectorRests, inside]))
            (fun pair inside => bags pair (by simp [bagRests, inside])))
          0 _ (scoped_data values sites (depth + 1) body canonical.1
            (fun rest inside => settled rest (by simp [vectorRests, inside]))
            (fun pair inside => bags pair (by simp [bagRests, inside])))
    | depth, .collection kind elements rest, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        have front := isDataList_iff.mp (scopedList_data values sites depth elements canonical
          (fun name inside => settled name (by cases kind <;> simp [vectorRests, inside]))
          (fun pair inside => bags pair (by cases kind <;> simp [bagRests, inside])))
        rw [applyBindingsScoped_collection]
        cases rest with
        | none =>
            simp only [restSplice_none, List.append_nil, isData, Option.isNone_none, Bool.true_and]
            exact isDataList_iff.mpr front
        | some restName =>
            obtain ⟨tail, bound⟩ : ∃ tail, bindings.find? (·.1 == restName) =
                some (restName, .collection kind tail none) := by
              cases kind with
              | vec => exact settled restName (by simp [vectorRests])
              | hashBag => exact bags (restName, .hashBag) (by simp [bagRests])
              | hashSet => exact bags (restName, .hashSet) (by simp [bagRests])
            have back : isDataList tail = true := by
              simpa [isData] using values restName _ bound
            rw [restSplice_bound bound]
            simp only [isData, Option.isNone_none, Bool.true_and]
            refine isDataList_iff.mpr fun term member => ?_
            rcases List.mem_append.mp member with inFront | inBack
            · exact front term inFront
            · obtain ⟨original, inTail, rfl⟩ := List.mem_map.mp inBack
              rw [isData_liftBVars]
              exact isDataList_iff.mp back original inTail

  theorem scopedList_data {bindings : Bindings} (values : DataOn bindings) (sites : Pattern) :
      ∀ (depth : ℕ) (ps : List Pattern), Pattern.hasCanonicalBinderMetadataList ps = true →
        Settled bindings (vectorRestsList ps) → BagSettled bindings (bagRestsList ps) →
        isDataList (ps.map (applyBindingsScoped sites bindings depth)) = true
    | _, [], _, _, _ => rfl
    | depth, p :: ps, canonical, settled, bags => by
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
        simp only [List.map_cons, isDataList, Bool.and_eq_true]
        exact ⟨scoped_data values sites depth p canonical.1
            (fun name inside => settled name (by simp [vectorRestsList, inside]))
            (fun pair inside => bags pair (by simp [bagRestsList, inside])),
          scopedList_data values sites depth ps canonical.2
            (fun name inside => settled name (by simp [vectorRestsList, inside]))
            (fun pair inside => bags pair (by simp [bagRestsList, inside]))⟩
end

/-! ## The values an instance substitutes -/

mutual
  /-- **The values an instance substitutes**: at each explicit substitution of a pattern, the instance of its value. -/
  def substValues (sites : Pattern) (witness : Bindings) : ℕ → Pattern → List Pattern
    | _, .fvar _ => []
    | _, .bvar _ => []
    | depth, .apply _ arguments => substValuesList sites witness depth arguments
    | depth, .lambda _ body => substValues sites witness (depth + 1) body
    | depth, .multiLambda arity _ body => substValues sites witness (depth + arity) body
    | depth, .subst body value => applyBindingsScoped sites witness depth value ::
        (substValues sites witness (depth + 1) body ++ substValues sites witness depth value)
    | depth, .collection _ elements _ => substValuesList sites witness depth elements

  def substValuesList (sites : Pattern) (witness : Bindings) (depth : ℕ) : List Pattern → List Pattern
    | [] => []
    | p :: ps => substValues sites witness depth p ++ substValuesList sites witness depth ps
end

mutual
  /-- **The values an instance substitutes depend only on the values of the pattern's names.** -/
  theorem substValues_agree (sites : Pattern) {first second : Bindings} : ∀ (depth : ℕ) (p : Pattern),
      (∀ name ∈ names p, lookupOrFvar first name = lookupOrFvar second name) →
      substValues sites first depth p = substValues sites second depth p
    | _, .fvar _, _ => rfl
    | _, .bvar _, _ => rfl
    | depth, .apply _ arguments, agree => by
        simp only [substValues]
        exact substValuesList_agree sites depth arguments fun name inside => agree name (by simpa [names] using inside)
    | depth, .lambda _ body, agree => by
        simp only [substValues]
        exact substValues_agree sites (depth + 1) body fun name inside => agree name (by simpa [names] using inside)
    | depth, .multiLambda arity _ body, agree => by
        simp only [substValues]
        exact substValues_agree sites (depth + arity) body fun name inside =>
          agree name (by simpa [names] using inside)
    | depth, .subst body value, agree => by
        simp only [substValues]
        rw [applyBindingsScoped_agree sites depth value fun name inside => agree name (by simp [names, inside]),
          substValues_agree sites (depth + 1) body fun name inside => agree name (by simp [names, inside]),
          substValues_agree sites depth value fun name inside => agree name (by simp [names, inside])]
    | depth, .collection _ elements _, agree => by
        simp only [substValues]
        exact substValuesList_agree sites depth elements fun name inside => agree name (by simp [names, inside])

  theorem substValuesList_agree (sites : Pattern) {first second : Bindings} : ∀ (depth : ℕ) (ps : List Pattern),
      (∀ name ∈ namesList ps, lookupOrFvar first name = lookupOrFvar second name) →
      substValuesList sites first depth ps = substValuesList sites second depth ps
    | _, [], _ => rfl
    | depth, p :: ps, agree => by
        simp only [substValuesList]
        rw [substValues_agree sites depth p fun name inside => agree name (by simp [namesList, inside]),
          substValuesList_agree sites depth ps fun name inside => agree name (by simp [namesList, inside])]
end

mutual
  /-- **The values a scope-correct instance substitutes are data**, under data whose rests are settled. -/
  theorem substValues_data {bindings : Bindings} (values : DataOn bindings) (sites : Pattern) :
      ∀ (depth : ℕ) (p : Pattern), p.hasCanonicalBinderMetadata = true → Settled bindings (vectorRests p) →
        BagSettled bindings (bagRests p) → ∀ v ∈ substValues sites bindings depth p, isData v = true
    | _, .fvar _, _, _, _, _, inside => by simp [substValues] at inside
    | _, .bvar _, _, _, _, _, inside => by simp [substValues] at inside
    | depth, .apply _ arguments, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simp only [substValues] at inside
        exact substValuesList_data values sites depth arguments canonical settled bags v inside
    | depth, .lambda _ body, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [substValues] at inside
        exact substValues_data values sites (depth + 1) body canonical.2 settled bags v inside
    | depth, .multiLambda arity _ body, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [substValues] at inside
        exact substValues_data values sites (depth + arity) body canonical.2 settled bags v inside
    | depth, .subst body value, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        have bodySettled : Settled bindings (vectorRests body) := fun rest member =>
          settled rest (by simp [vectorRests, member])
        have bodyBags : BagSettled bindings (bagRests body) := fun pair member =>
          bags pair (by simp [bagRests, member])
        have valueSettled : Settled bindings (vectorRests value) := fun rest member =>
          settled rest (by simp [vectorRests, member])
        have valueBags : BagSettled bindings (bagRests value) := fun pair member =>
          bags pair (by simp [bagRests, member])
        simp only [substValues, List.mem_cons, List.mem_append] at inside
        rcases inside with rfl | inBody | inValue
        · exact scoped_data values sites depth value canonical.2 valueSettled valueBags
        · exact substValues_data values sites (depth + 1) body canonical.1 bodySettled bodyBags v inBody
        · exact substValues_data values sites depth value canonical.2 valueSettled valueBags v inValue
    | depth, .collection kind elements rest, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadata] at canonical
        simp only [substValues] at inside
        exact substValuesList_data values sites depth elements canonical
          (fun name member => settled name (by cases kind <;> simp [vectorRests, member]))
          (fun pair member => bags pair (by cases kind <;> simp [bagRests, member])) v inside

  theorem substValuesList_data {bindings : Bindings} (values : DataOn bindings) (sites : Pattern) :
      ∀ (depth : ℕ) (ps : List Pattern), Pattern.hasCanonicalBinderMetadataList ps = true →
        Settled bindings (vectorRestsList ps) → BagSettled bindings (bagRestsList ps) →
        ∀ v ∈ substValuesList sites bindings depth ps, isData v = true
    | _, [], _, _, _, _, inside => by simp [substValuesList] at inside
    | depth, p :: ps, canonical, settled, bags, v, inside => by
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
        simp only [substValuesList, List.mem_append] at inside
        rcases inside with here | later
        · exact substValues_data values sites depth p canonical.1
            (fun name member => settled name (by simp [vectorRestsList, member]))
            (fun pair member => bags pair (by simp [bagRestsList, member])) v here
        · exact substValuesList_data values sites depth ps canonical.2
            (fun name member => settled name (by simp [vectorRestsList, member]))
            (fun pair member => bags pair (by simp [bagRestsList, member])) v later
end

end ScopedData

/-! ## Reading an instance back: the converses of its goals -/

/-- The two parts of an application row. -/
def splitRow? : Tm → Option (Tm × Tm)
  | .app .app arguments => some (arguments head, arguments tail)
  | _ => none

theorem splitRow?_appTerm (function argument : Tm) :
    splitRow? (appTerm function argument) = some (function, argument) := rfl

theorem splitRow?_some {row function argument : Tm} (split : splitRow? row = some (function, argument)) :
    row = appTerm function argument := by
  cases row with
  | var _ => simp [splitRow?] at split
  | const _ => simp [splitRow?] at split
  | app former arguments =>
      cases former with
      | app =>
          simp only [splitRow?, Option.some.injEq, Prod.mk.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          simp only [appTerm]
          congr 1
          funext position
          rcases fin_app position with rfl | rfl <;> rfl
      | code => simp [splitRow?] at split

theorem appTerm_inj {a b c d : Tm} (same : appTerm a b = appTerm c d) : a = c ∧ b = d := by
  have split := congrArg splitRow? same
  simpa [splitRow?_appTerm] using split

/-- **The converses of a goal of an instantiation**: lowering for a lift, wrapping for an unwrap. For an instantiation
of a substitution, the value is not read off the instance: it is chosen as a datum over the supply, and the instance
is abstracted over it, which reads every body back. -/
def buildConverse? : Goal → Option (List Goal)
  | .ask relation input output =>
      if relation = liftRelation then
        (splitRow? input).map fun split => [.ask lowerRelation (appTerm split.1 output) split.2]
      else if relation = liftListRelation then
        (splitRow? input).map fun split => [.ask lowerListRelation (appTerm split.1 output) split.2]
      else if relation = unwrapRelation then some [.ask wrapRelation output input]
      else if relation = instantiateRelation then
        (splitRow? input).bind fun split => (splitRow? split.1).map fun inner =>
          [.ask DataClauses.datumRelation DataClauses.unitTerm inner.2,
            .ask abstractRelation (appTerm split.1 output) split.2]
      else none
  | .query _ => none

/-- The converses of an instantiation's goals, the last goal's first. -/
def buildConverses : List Goal → Option (List Goal)
  | [] => some []
  | goal :: goals => (buildConverses goals).bind fun later =>
      (buildConverse? goal).map fun converse => later ++ converse

theorem buildConverses_append : ∀ (first second : List Goal),
    buildConverses (first ++ second) = (buildConverses second).bind fun later =>
      (buildConverses first).map fun earlier => later ++ earlier
  | [], second => by
      rcases found : buildConverses second with _ | later <;> simp [buildConverses, found]
  | goal :: first, second => by
      simp only [List.cons_append, buildConverses, buildConverses_append first second]
      rcases foundSecond : buildConverses second with _ | later <;>
        rcases foundFirst : buildConverses first with _ | earlier <;>
        rcases foundGoal : buildConverse? goal with _ | converse <;> simp_all

/-- The converses of an instantiation of a substitution: its value chosen, then the instance abstracted over it. -/
theorem buildConverse_instantiate (depthRow value body output : Tm) :
    buildConverse? (.ask instantiateRelation (triple depthRow value body) output) =
      some [.ask DataClauses.datumRelation DataClauses.unitTerm value,
        .ask abstractRelation (appTerm (appTerm depthRow value) output) body] := by
  simp [buildConverse?, show instantiateRelation ≠ liftRelation by decide,
    show instantiateRelation ≠ liftListRelation by decide, show instantiateRelation ≠ unwrapRelation by decide,
    triple, splitRow?_appTerm]

/-- **The clauses an instantiation's converses ask**: lowering, abstracting, and wrapping a list as a bag or a set. -/
structure ConverseClauses (program : List Clause) : Prop where
  lowers : LowerProgram program
  abstracts : ScopeClauses.AbstractProgram program
  wraps : ∀ c ∈ wrapClauses, c ∈ program
  onlyWraps : ∀ c ∈ program, c.relation = wrapRelation → c ∈ wrapClauses

/-- **A goal an instantiation asks**: a lift of a value or of a list by a shift, an unwrap, or an instantiation. -/
inductive BuildGoal : Goal → Prop
  | lift {relation shift : ℕ} {source fresh : Tm} : relation = liftRelation ∨ relation = liftListRelation →
      BuildGoal (.ask relation (triple (symTerm 0) (numeralTerm shift) source) fresh)
  | unwrap {rest list : Tm} : BuildGoal (.ask unwrapRelation rest list)
  | instantiate {input output : Tm} : BuildGoal (.ask instantiateRelation input output)

section Converses

variable {R : Relations} {program : List Clause}

theorem wrap_unwrap (build : BuildClauses program) (converses : ConverseClauses program) {x y : Expr}
    (wrapped : Derives R program wrapRelation x y) : Derives R program unwrapRelation y x := by
  obtain ⟨c, member, isWrap, θ, input, output, -⟩ := DemandTransformation.derives_cases wrapped
  have inWraps := converses.onlyWraps c member isWrap
  simp only [wrapClauses, List.mem_cons, List.not_mem_nil, or_false] at inWraps
  obtain ⟨kind, rfl, kindIn⟩ : ∃ kind, c = wrapClause kind ∧ unwrapClause kind ∈ unwrapClauses := by
    rcases inWraps with rfl | rfl
    · exact ⟨.hashBag, rfl, by simp [unwrapClauses]⟩
    · exact ⟨.hashSet, rfl, by simp [unwrapClauses]⟩
  have clause := DemandTransformation.derives_of_clause (R := R) (build.unwraps _ kindIn) θ
    fun _ inside => absurd inside List.not_mem_nil
  simp only [wrapClause, unwrapClause] at input output clause
  rw [output, input] at clause
  exact clause

theorem unwrap_wrap (build : BuildClauses program) (converses : ConverseClauses program) {x y : Expr}
    (unwrapped : Derives R program unwrapRelation x y) : Derives R program wrapRelation y x := by
  obtain ⟨c, member, isUnwrap, θ, input, output, -⟩ := DemandTransformation.derives_cases unwrapped
  have inUnwraps := build.onlyUnwraps c member isUnwrap
  simp only [unwrapClauses, List.mem_cons, List.not_mem_nil, or_false] at inUnwraps
  obtain ⟨kind, rfl, kindIn⟩ : ∃ kind, c = unwrapClause kind ∧ wrapClause kind ∈ wrapClauses := by
    rcases inUnwraps with rfl | rfl
    · exact ⟨.hashBag, rfl, by simp [wrapClauses]⟩
    · exact ⟨.hashSet, rfl, by simp [wrapClauses]⟩
  have clause := DemandTransformation.derives_of_clause (R := R) (converses.wraps _ kindIn) θ
    fun _ inside => absurd inside List.not_mem_nil
  simp only [wrapClause, unwrapClause] at input output clause
  rw [output, input] at clause
  exact clause

/-- **A goal whose converses hold holds.** -/
theorem buildConverse_sound (build : BuildClauses program) (converses : ConverseClauses program) {θ : ℕ → Expr}
    {goal : Goal} {converse : List Goal} (found : buildConverse? goal = some converse)
    (holds : ∀ g ∈ converse, goalHolds R (Derives R program) θ g) : goalHolds R (Derives R program) θ goal := by
  cases goal with
  | query _ => simp [buildConverse?] at found
  | ask relation input output =>
      simp only [buildConverse?] at found
      split_ifs at found with isLift isList isUnwrap isInstantiate
      · obtain ⟨⟨function, argument⟩, split, rfl⟩ := Option.map_eq_some_iff.mp found
        subst isLift
        rw [splitRow?_some split]
        have held := holds _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm] at held ⊢
        obtain ⟨depth, derived⟩ := held
        exact ScopeClauses.lower_lift converses.lowers depth _ _ _ derived
      · obtain ⟨⟨function, argument⟩, split, rfl⟩ := Option.map_eq_some_iff.mp found
        subst isList
        rw [splitRow?_some split]
        have held := holds _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm] at held ⊢
        obtain ⟨depth, derived⟩ := held
        exact ScopeClauses.lowerList_lift converses.lowers depth _ _ _ derived
      · simp only [Option.some.injEq] at found
        subst found isUnwrap
        exact wrap_unwrap build converses (holds _ List.mem_cons_self)
      · obtain ⟨⟨function, argument⟩, split, found⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨⟨depthRow, value⟩, -, rfl⟩ := Option.map_eq_some_iff.mp found
        subst isInstantiate
        rw [splitRow?_some split]
        have held := holds _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm] at held ⊢
        obtain ⟨depth, derived⟩ := held
        exact ScopeClauses.abstract_instantiate converses.abstracts depth _ _ _ derived

/-- **The converses of a goal an instantiation asks hold when the goal does**, and the values it chooses hold. -/
theorem buildConverse_complete (build : BuildClauses program) (converses : ConverseClauses program)
    {θ : ℕ → Expr} {goal : Goal} {converse : List Goal} (shape : BuildGoal goal)
    (found : buildConverse? goal = some converse) (holds : goalHolds R (Derives R program) θ goal)
    (chosen : ∀ value, Goal.ask DataClauses.datumRelation DataClauses.unitTerm value ∈ converse →
      goalHolds R (Derives R program) θ (.ask DataClauses.datumRelation DataClauses.unitTerm value)) :
    ∀ g ∈ converse, goalHolds R (Derives R program) θ g := by
  cases shape with
  | lift isLift =>
      rcases isLift with rfl | rfl
      · simp only [buildConverse?, ↓reduceIte, triple, splitRow?_appTerm, Option.map_some,
          Option.some.injEq] at found
        subst found
        intro g inside
        rw [List.mem_singleton.mp inside]
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          RootRewritesOnTheStep.inst_numeralTerm] at holds ⊢
        obtain ⟨depth, derived⟩ := holds
        exact ScopeClauses.lift_lower converses.lowers depth _ _ _ _ derived
      · simp only [buildConverse?, show liftListRelation ≠ liftRelation by decide, ↓reduceIte, triple,
          splitRow?_appTerm, Option.map_some, Option.some.injEq] at found
        subst found
        intro g inside
        rw [List.mem_singleton.mp inside]
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          RootRewritesOnTheStep.inst_numeralTerm] at holds ⊢
        obtain ⟨depth, derived⟩ := holds
        exact ScopeClauses.liftList_lower converses.lowers depth _ _ _ _ derived
  | unwrap =>
      simp only [buildConverse?, show unwrapRelation ≠ liftRelation by decide,
        show unwrapRelation ≠ liftListRelation by decide, ↓reduceIte, Option.some.injEq] at found
      subst found
      intro g inside
      rw [List.mem_singleton.mp inside]
      exact unwrap_wrap build converses holds
  | @instantiate input output =>
      simp only [buildConverse?, show instantiateRelation ≠ liftRelation by decide,
        show instantiateRelation ≠ liftListRelation by decide,
        show instantiateRelation ≠ unwrapRelation by decide, ↓reduceIte] at found
      obtain ⟨⟨function, argument⟩, split, found⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨⟨depthRow, value⟩, -, rfl⟩ := Option.map_eq_some_iff.mp found
      intro g inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact chosen _ List.mem_cons_self
      · rw [splitRow?_some split] at holds
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm] at holds ⊢
        obtain ⟨depth, derived⟩ := holds
        exact ScopeClauses.instantiate_abstract converses.abstracts depth _ _ _ derived

theorem buildConverses_sound (build : BuildClauses program) (converses : ConverseClauses program) {θ : ℕ → Expr} :
    ∀ {goals inverse : List Goal}, buildConverses goals = some inverse →
      (∀ g ∈ inverse, goalHolds R (Derives R program) θ g) → ∀ g ∈ goals, goalHolds R (Derives R program) θ g
  | [], _, _, _, _, inside => absurd inside List.not_mem_nil
  | goal :: goals, inverse, found, holds, g, inside => by
      simp only [buildConverses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, converse, converseFound, rfl⟩ := found
      rcases List.mem_cons.mp inside with rfl | inLater
      · exact buildConverse_sound build converses converseFound fun g' inside' =>
          holds g' (List.mem_append_right _ inside')
      · exact buildConverses_sound build converses laterFound
          (fun g' inside' => holds g' (List.mem_append_left _ inside')) g inLater

/-- **The converses of an instantiation's goals hold when the goals do**, and the values they choose hold. -/
theorem buildConverses_complete (build : BuildClauses program) (converses : ConverseClauses program)
    {θ : ℕ → Expr} : ∀ {goals inverse : List Goal}, (∀ g ∈ goals, BuildGoal g) → buildConverses goals = some inverse →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ value, Goal.ask DataClauses.datumRelation DataClauses.unitTerm value ∈ inverse →
        goalHolds R (Derives R program) θ (.ask DataClauses.datumRelation DataClauses.unitTerm value)) →
      ∀ g ∈ inverse, goalHolds R (Derives R program) θ g
  | [], _, _, found, _, _, g, inside => by
      simp only [buildConverses, Option.some.injEq] at found
      subst found
      exact absurd inside List.not_mem_nil
  | goal :: goals, inverse, shapes, found, holds, chosen, g, inside => by
      simp only [buildConverses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, converse, converseFound, rfl⟩ := found
      rcases List.mem_append.mp inside with inLater | here
      · exact buildConverses_complete build converses (fun g' inside' => shapes g' (List.mem_cons_of_mem _ inside'))
          laterFound (fun g' inside' => holds g' (List.mem_cons_of_mem _ inside'))
          (fun value member => chosen value (List.mem_append_left _ member)) g inLater
      · exact buildConverse_complete build converses (shapes _ List.mem_cons_self) converseFound
          (holds _ List.mem_cons_self) (fun value member => chosen value (List.mem_append_right _ member)) g here

/-- **The converses of an instantiation of a substitution are among the converses.** -/
theorem converses_of_instantiate : ∀ {goals inverse : List Goal}, buildConverses goals = some inverse →
    ∀ {depthRow value body out : Tm}, Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals →
      Goal.ask DataClauses.datumRelation DataClauses.unitTerm value ∈ inverse ∧
        Goal.ask abstractRelation (appTerm (appTerm depthRow value) out) body ∈ inverse
  | [], _, _, _, _, _, _, inside => absurd inside List.not_mem_nil
  | goal :: goals, inverse, found, depthRow, value, body, out, inside => by
      simp only [buildConverses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, converse, converseFound, rfl⟩ := found
      rcases List.mem_cons.mp inside with rfl | inLater
      · rw [buildConverse_instantiate] at converseFound
        simp only [Option.some.injEq] at converseFound
        subst converseFound
        simp
      · obtain ⟨chosen, abstracted⟩ := converses_of_instantiate laterFound inLater
        exact ⟨List.mem_append_left _ chosen, List.mem_append_left _ abstracted⟩

/-- **A value chosen among the converses is the value of an instantiation of a substitution.** -/
theorem datum_of_converses : ∀ {goals inverse : List Goal}, buildConverses goals = some inverse →
    ∀ {value : Tm}, Goal.ask DataClauses.datumRelation DataClauses.unitTerm value ∈ inverse →
      ∃ depthRow body out, Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals
  | [], _, found, _, inside => by
      simp only [buildConverses, Option.some.injEq] at found
      subst found
      exact absurd inside List.not_mem_nil
  | goal :: goals, inverse, found, value, inside => by
      simp only [buildConverses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, converse, converseFound, rfl⟩ := found
      rcases List.mem_append.mp inside with inLater | here
      · obtain ⟨depthRow, body, out, member⟩ := datum_of_converses laterFound inLater
        exact ⟨depthRow, body, out, List.mem_cons_of_mem _ member⟩
      · cases goal with
        | query _ => simp [buildConverse?] at converseFound
        | ask relation input output =>
            simp only [buildConverse?] at converseFound
            split_ifs at converseFound with isLift isList isUnwrap isInstantiate
            · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp converseFound
              exact absurd (Goal.ask.inj (List.mem_singleton.mp here)).1 (by decide)
            · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp converseFound
              exact absurd (Goal.ask.inj (List.mem_singleton.mp here)).1 (by decide)
            · simp only [Option.some.injEq] at converseFound
              subst converseFound
              exact absurd (Goal.ask.inj (List.mem_singleton.mp here)).1 (by decide)
            · obtain ⟨⟨function, argument⟩, split, found⟩ := Option.bind_eq_some_iff.mp converseFound
              obtain ⟨⟨depthRow, value'⟩, inner, rfl⟩ := Option.map_eq_some_iff.mp found
              simp only at inner
              subst isInstantiate
              simp only [List.mem_cons, List.not_mem_nil, or_false] at here
              rcases here with same | same
              · obtain ⟨-, -, rfl⟩ := Goal.ask.inj same
                refine ⟨depthRow, argument, output, ?_⟩
                rw [splitRow?_some split, splitRow?_some inner]
                exact List.mem_cons_self
              · exact absurd (Goal.ask.inj same).1 (by decide)

/-- **Substitutions read back**: at each instantiation of a substitution among the goals, an instance that is a term has
a value of data and a body, which instantiate to it. -/
def SubstitutionsRead (θ : ℕ → Expr) (goals : List Goal) : Prop :=
  ∀ value body out : Tm, Goal.ask instantiateRelation (triple (symTerm 0) value body) out ∈ goals →
    ∀ s : Pattern, inst θ out = encode s → ∃ v b : Pattern, inst θ value = encode v ∧ inst θ body = encode b ∧
      OrderedMatching.isData v = true ∧ instantiateBVarAt 0 v b = s

theorem SubstitutionsRead.mono {θ : ℕ → Expr} {goals smaller : List Goal} (read : SubstitutionsRead θ goals)
    (within : ∀ g ∈ smaller, g ∈ goals) : SubstitutionsRead θ smaller :=
  fun value body out member => read value body out (within _ member)

/-- **Where the converses hold, the substitutions are read back.** -/
theorem substitutionsRead_of_converses (converses : ConverseClauses program) {supply : List String}
    (data : DataClauses.DataProgram supply program) {θ : ℕ → Expr} {goals inverse : List Goal}
    (found : buildConverses goals = some inverse) (holds : ∀ g ∈ inverse, goalHolds R (Derives R program) θ g) :
    SubstitutionsRead θ goals := by
  intro value body out member s outIs
  obtain ⟨chosen, abstracted⟩ := converses_of_instantiate found member
  have chosenHolds := holds _ chosen
  simp only [goalHolds, DataClauses.unitTerm, RootRewritesOnTheStep.inst_symTerm] at chosenHolds
  obtain ⟨v, vIs, vData, -⟩ := (DataClauses.datum_iff data).mp chosenHolds
  have abstractedHolds := holds _ abstracted
  simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, vIs,
    outIs] at abstractedHolds
  obtain ⟨b, bIs, instantiated⟩ := (ScopeClauses.abstract_iff converses.abstracts 0 v s).mp abstractedHolds
  exact ⟨v, b, vIs, bIs, vData, instantiated⟩

end Converses

section ConverseModes

variable {rests avoid : List String} {sites : Pattern}

theorem lifted_goals {relation shift source fresh : ℕ}
    (isLift : relation = liftRelation ∨ relation = liftListRelation) :
    ∀ g ∈ (lifted relation shift source fresh).2, BuildGoal g := by
  intro g inside
  by_cases zero : shift = 0
  · simp [lifted, zero] at inside
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton] at inside
    subst inside
    exact .lift isLift

mutual
  /-- **An instantiation lowering asks lifts, unwraps and instantiations only.** -/
  theorem buildRow_goals : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm} {goals : List Goal},
      buildRow rests avoid sites depth next p = some (t, goals, next') → ∀ g ∈ goals, BuildGoal g
    | .fvar name, depth, next, _, _, _, lowered => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact lifted_goals (by split <;> simp)
    | .bvar _, _, _, _, _, _, lowered => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact fun _ inside => absurd inside List.not_mem_nil
    | .apply _ arguments, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRows_goals arguments found
    | .lambda _ body, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRow_goals body found
    | .multiLambda _ _ body, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRow_goals body found
    | .subst body value, depth, next, _, _, _, lowered => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, bodyGoals, _⟩, bodyFound, ⟨_, valueGoals, _⟩, valueFound, -, rfl, -⟩ := lowered
        intro g inside
        simp only [List.append_assoc, List.mem_append, List.mem_singleton] at inside
        rcases inside with inBody | inValue | rfl
        · exact buildRow_goals body bodyFound g inBody
        · exact buildRow_goals value valueFound g inValue
        · exact .instantiate
    | .collection .vec elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRows_goals elements found
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
          intro g inside
          rcases List.mem_append.mp inside with inLift | inElements
          · exact lifted_goals (.inr rfl) g inLift
          · exact buildRows_goals elements found g inElements
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRows_goals elements found
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
          intro g inside
          simp only [List.mem_cons, List.mem_append] at inside
          rcases inside with (rfl | inLift) | inElements
          · exact .unwrap
          · exact lifted_goals (.inr rfl) g inLift
          · exact buildRows_goals elements found g inElements
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
        exact buildRows_goals elements found
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨_, _, _⟩, found, -, rfl, -⟩ := lowered
          intro g inside
          simp only [List.mem_cons, List.mem_append] at inside
          rcases inside with (rfl | inLift) | inElements
          · exact .unwrap
          · exact lifted_goals (.inr rfl) g inLift
          · exact buildRows_goals elements found g inElements
        · cases lowered

  theorem buildRows_goals : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') → ∀ g ∈ goals, BuildGoal g
    | [], _, _, _, _, _, _, lowered => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact fun _ inside => absurd inside List.not_mem_nil
    | pattern :: patterns, _, _, _, _, _, _, lowered => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨_, headGoals, _⟩, headFound, ⟨_, tailGoals, _⟩, tailFound, -, rfl, -⟩ := lowered
        intro g inside
        rcases List.mem_append.mp inside with inHead | inTail
        · exact buildRow_goals pattern headFound g inHead
        · exact buildRows_goals patterns tailFound g inTail
end

theorem buildConverses_single {goal : Goal} {converse : List Goal} (found : buildConverse? goal = some converse) :
    buildConverses [goal] = some converse := by
  simp [buildConverses, found]

/-- **The converses of a lifted value read the value back from the row.** -/
theorem lifted_converses {relation shift source fresh : ℕ}
    (isLift : relation = liftRelation ∨ relation = liftListRelation) :
    ∃ inverse, buildConverses (lifted relation shift source fresh).2 = some inverse ∧
      ∀ {bound : List ℕ}, (∀ u ∈ unknowns (lifted relation shift source fresh).1, u ∈ bound) →
        InputsBound bound inverse ∧ source ∈ bound ++ inverse.flatMap goalUnknowns := by
  by_cases zero : shift = 0
  · refine ⟨[], by simp [lifted, zero, buildConverses], fun rowBound => ⟨.nil _, ?_⟩⟩
    have here := rowBound source (by simp [lifted, zero])
    simpa using here
  · rcases isLift with rfl | rfl
    · refine ⟨[.ask lowerRelation (appTerm (appTerm (symTerm 0) (numeralTerm shift)) (.var fresh)) (.var source)],
        by simp [lifted, zero, buildConverses, buildConverse?, triple, splitRow?_appTerm],
        fun rowBound => ⟨.cons (fun x inside => ?_) (.nil _), by simp [goalUnknowns]⟩⟩
      simp only [goalInputs, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
        RootRewritesOnTheStep.unknowns_numeralTerm, DemandTransformation.unknowns_unknown, List.nil_append,
        List.mem_singleton] at inside
      subst inside
      exact rowBound _ (by simp [lifted, zero])
    · refine ⟨[.ask lowerListRelation (appTerm (appTerm (symTerm 0) (numeralTerm shift)) (.var fresh))
        (.var source)], by simp [lifted, zero, buildConverses, buildConverse?, triple, splitRow?_appTerm,
          show liftListRelation ≠ liftRelation by decide],
        fun rowBound => ⟨.cons (fun x inside => ?_) (.nil _), by simp [goalUnknowns]⟩⟩
      simp only [goalInputs, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
        RootRewritesOnTheStep.unknowns_numeralTerm, DemandTransformation.unknowns_unknown, List.nil_append,
        List.mem_singleton] at inside
      subst inside
      exact rowBound _ (by simp [lifted, zero])

theorem buildRows_close : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm} {goals : List Goal},
    buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ u ∈ unknowns close, u ∈ unknowns list
  | [], _, _, _, _, _, _, lowered => by
      simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, -, -⟩ := lowered
      exact fun _ inside => inside
  | pattern :: patterns, _, _, _, _, _, _, lowered => by
      simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨⟨_, _, _⟩, -, ⟨_, _, _⟩, tailFound, rfl, -, -⟩ := lowered
      intro u inside
      simp only [RootRewritesOnTheStep.unknowns_appTerm, List.mem_append]
      exact .inr (buildRows_close patterns tailFound u inside)

/-- The converses of the instantiation of a bag's or a set's rest: the elements, the list lowered, then wrapped. -/
theorem bagRest_converses {kind : CollType} {elements : List Pattern} {restName : String} {depth next last : ℕ}
    {list : Tm} {elementGoals : List Goal}
    (elementsFound : buildRows rests avoid sites depth (next + 2) elements (lifted liftListRelation
      (shiftOf sites restName depth) (listUnknown avoid next) (listUnknown avoid (next + 1))).1 =
        some (list, elementGoals, last))
    (elementsConverses : ∀ {inverse : List Goal}, buildConverses elementGoals = some inverse →
      ∀ {bound : List ℕ}, (∀ u ∈ unknowns list, u ∈ bound) →
        InputsBound bound inverse ∧ ∀ name ∈ namesList elements, labelCode name ∈
          bound ++ inverse.flatMap goalUnknowns)
    {inverse : List Goal}
    (found : buildConverses (Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals) = some inverse)
    {bound : List ℕ} (rowBound : ∀ u ∈ unknowns (collectionTerm kind list), u ∈ bound) :
    InputsBound bound inverse ∧
      ∀ name ∈ names (.collection kind elements (some restName)), labelCode name ∈
        bound ++ inverse.flatMap goalUnknowns := by
  obtain ⟨liftInverse, liftFound, liftBound⟩ := lifted_converses (relation := liftListRelation)
    (shift := shiftOf sites restName depth) (source := listUnknown avoid next)
    (fresh := listUnknown avoid (next + 1)) (.inr rfl)
  rw [buildConverses_append] at found
  simp only [buildConverses, liftFound, buildConverse?, show unwrapRelation ≠ liftRelation by decide,
    show unwrapRelation ≠ liftListRelation by decide, ↓reduceIte, Option.bind_some, Option.map_some,
    Option.bind_eq_some_iff, Option.some.injEq] at found
  obtain ⟨elementInverse, elementInverseFound, rfl⟩ := found
  have listBound : ∀ u ∈ unknowns list, u ∈ bound := fun u inside =>
    rowBound u (by rw [CollectionMatching.unknowns_collectionTerm]; exact inside)
  obtain ⟨elementFlows, elementNamed⟩ := elementsConverses elementInverseFound listBound
  obtain ⟨liftFlows, sourceBound⟩ := liftBound (bound := bound ++ elementInverse.flatMap goalUnknowns)
    fun u inside => List.mem_append_left _ (listBound u (buildRows_close elements elementsFound u inside))
  have wrapFlows : InputsBound (bound ++ elementInverse.flatMap goalUnknowns ++ liftInverse.flatMap goalUnknowns)
      [Goal.ask wrapRelation (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next)))
        (.var (labelCode restName))] := by
    refine .cons (fun x inside => ?_) (.nil _)
    simp only [goalInputs, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
      DemandTransformation.unknowns_unknown, List.nil_append, List.mem_singleton] at inside
    subst inside
    exact sourceBound
  refine ⟨elementFlows.append (by simpa [List.flatMap_append, List.append_assoc] using liftFlows.append wrapFlows),
    fun name inside => ?_⟩
  simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
  rcases inside with inElements | rfl
  · have here := elementNamed name inElements
    simp only [List.flatMap_append, List.mem_append] at here ⊢
    tauto
  · simp [goalUnknowns]

mutual
  /-- **The converses of an instantiation are bound in order from its row, and bind the pattern's names.** -/
  theorem buildRow_converses : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm} {goals : List Goal},
      buildRow rests avoid sites depth next p = some (t, goals, next') → ∀ {inverse : List Goal},
      buildConverses goals = some inverse → ∀ {bound : List ℕ}, (∀ u ∈ unknowns t, u ∈ bound) →
      InputsBound bound inverse ∧ ∀ name ∈ names p, labelCode name ∈ bound ++ inverse.flatMap goalUnknowns
    | .fvar name, depth, next, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, -⟩ := lowered
        obtain ⟨computed, computedFound, computedBound⟩ := lifted_converses (relation := if name ∈ rests then
          liftListRelation else liftRelation) (shift := shiftOf sites name depth) (source := labelCode name)
          (fresh := listUnknown avoid next) (by split <;> simp)
        obtain rfl : inverse = computed := Option.some.inj (found.symm.trans computedFound)
        have bound' : ∀ u ∈ unknowns (lifted (if name ∈ rests then liftListRelation else liftRelation)
            (shiftOf sites name depth) (labelCode name) (listUnknown avoid next)).1, u ∈ bound := by
          intro u inside
          apply rowBound u
          split
          · rw [CollectionMatching.unknowns_vectorTerm]
            simpa [*] using inside
          · simpa [*] using inside
        obtain ⟨flows, nameBound⟩ := computedBound bound'
        refine ⟨flows, fun other inside => ?_⟩
        simp only [names, List.mem_singleton] at inside
        subst inside
        exact nameBound
    | .bvar _, _, _, _, _, _, lowered, inverse, found, bound, _ => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, -⟩ := lowered
        simp only [buildConverses, Option.some.injEq] at found
        subst found
        exact ⟨.nil bound, fun _ inside => by simp [names] at inside⟩
    | .apply _ arguments, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, argumentsFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRows_converses arguments argumentsFound found fun u inside =>
          rowBound u (by simp [RootRewritesOnTheStep.unknowns_appTerm, inside])
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .lambda _ body, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRow_converses body bodyFound found fun u inside =>
          rowBound u (by simp [RootRewritesOnTheStep.unknowns_appTerm, unknowns_toTerm, inside])
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .multiLambda _ _ body, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRow_converses body bodyFound found fun u inside =>
          rowBound u (by simp [RootRewritesOnTheStep.unknowns_appTerm, unknowns_toTerm, inside])
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .subst body value, depth, next, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, -⟩ :=
          lowered
        rw [buildConverses_append, buildConverses_single (buildConverse_instantiate _ _ _ _)] at found
        simp only [Option.bind_some, Option.map_eq_some_iff] at found
        obtain ⟨earlier, earlierFound, rfl⟩ := found
        rw [buildConverses_append] at earlierFound
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at earlierFound
        obtain ⟨valueInverse, valueInverseFound, bodyInverse, bodyInverseFound, rfl⟩ := earlierFound
        have freshBound : listUnknown avoid last ∈ bound := rowBound _ (by simp)
        have choiceFlows : InputsBound bound
            [Goal.ask DataClauses.datumRelation DataClauses.unitTerm valueRow,
              Goal.ask abstractRelation (appTerm (appTerm (symTerm 0) valueRow) (.var (listUnknown avoid last)))
                bodyRow] := by
          refine .cons (fun x inside => ?_) (.cons (fun x inside => ?_) (.nil _))
          · simp [goalInputs, DataClauses.unitTerm] at inside
          · simp only [goalInputs, RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
              DemandTransformation.unknowns_unknown, List.nil_append, List.mem_append, List.mem_singleton] at inside
            rcases inside with inValue | rfl
            · exact List.mem_append_right _ (by simp [goalUnknowns, DataClauses.unitTerm, inValue])
            · exact List.mem_append_left _ freshBound
        obtain ⟨valueFlows, valueNamed⟩ := buildRow_converses value valueFound valueInverseFound
          (bound := bound ++ [Goal.ask DataClauses.datumRelation DataClauses.unitTerm valueRow,
            Goal.ask abstractRelation (appTerm (appTerm (symTerm 0) valueRow) (.var (listUnknown avoid last)))
              bodyRow].flatMap goalUnknowns) fun u inside =>
            List.mem_append_right _ (by simp [goalUnknowns, DataClauses.unitTerm, inside])
        obtain ⟨bodyFlows, bodyNamed⟩ := buildRow_converses body bodyFound bodyInverseFound
          (bound := bound ++ [Goal.ask DataClauses.datumRelation DataClauses.unitTerm valueRow,
            Goal.ask abstractRelation (appTerm (appTerm (symTerm 0) valueRow) (.var (listUnknown avoid last)))
              bodyRow].flatMap goalUnknowns ++ valueInverse.flatMap goalUnknowns) fun u inside =>
            List.mem_append_left _ (List.mem_append_right _ (by simp [goalUnknowns, inside]))
        refine ⟨choiceFlows.append (valueFlows.append bodyFlows), fun name inside => ?_⟩
        simp only [names, List.mem_append] at inside
        rcases inside with inBody | inValue
        · have here := bodyNamed name inBody
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
        · have here := valueNamed name inValue
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
    | .collection .vec elements none, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRows_converses elements elementsFound found fun u inside =>
          rowBound u (by rw [CollectionMatching.unknowns_vectorTerm]; exact inside)
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, inverse, found, bound,
        rowBound => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          obtain ⟨liftInverse, liftFound, liftBound⟩ := lifted_converses (relation := liftListRelation)
            (shift := shiftOf sites restName depth) (source := labelCode restName)
            (fresh := listUnknown avoid next) (.inr rfl)
          rw [buildConverses_append, liftFound] at found
          simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq, exists_eq_left'] at found
          obtain ⟨elementInverse, elementInverseFound, rfl⟩ := found
          have listBound : ∀ u ∈ unknowns list, u ∈ bound := fun u inside =>
            rowBound u (by rw [CollectionMatching.unknowns_vectorTerm]; exact inside)
          obtain ⟨elementFlows, elementNamed⟩ := buildRows_converses elements elementsFound elementInverseFound
            listBound
          obtain ⟨liftFlows, restBound⟩ := liftBound (bound := bound ++ elementInverse.flatMap goalUnknowns)
            fun u inside => List.mem_append_left _ (listBound u (buildRows_close elements elementsFound u inside))
          refine ⟨elementFlows.append liftFlows, fun name inside => ?_⟩
          simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
          rcases inside with inElements | rfl
          · have here := elementNamed name inElements
            simp only [List.flatMap_append, List.mem_append] at here ⊢
            tauto
          · simp only [List.flatMap_append, List.mem_append] at restBound ⊢
            tauto
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRows_converses elements elementsFound found fun u inside =>
          rowBound u (by rw [CollectionMatching.unknowns_collectionTerm]; exact inside)
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, inverse, found, bound,
        rowBound => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_converses elementsFound
            (fun {_} inverseFound {_} listBound => buildRows_converses elements elementsFound inverseFound listBound) found
            rowBound
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, inverse, found, bound, rowBound => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        obtain ⟨flows, named⟩ := buildRows_converses elements elementsFound found fun u inside =>
          rowBound u (by rw [CollectionMatching.unknowns_collectionTerm]; exact inside)
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, inverse, found, bound,
        rowBound => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_converses elementsFound
            (fun {_} inverseFound {_} listBound => buildRows_converses elements elementsFound inverseFound listBound) found
            rowBound
        · cases lowered

  theorem buildRows_converses : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm}
      {goals : List Goal}, buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ {inverse : List Goal}, buildConverses goals = some inverse → ∀ {bound : List ℕ},
      (∀ u ∈ unknowns list, u ∈ bound) →
      InputsBound bound inverse ∧ ∀ name ∈ namesList patterns, labelCode name ∈ bound ++ inverse.flatMap goalUnknowns
    | [], _, _, _, _, _, _, lowered, inverse, found, bound, _ => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        simp only [buildConverses, Option.some.injEq] at found
        subst found
        exact ⟨.nil bound, fun _ inside => by simp [namesList] at inside⟩
    | pattern :: patterns, _, _, _, _, _, _, lowered, inverse, found, bound, listBound => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, -⟩ := lowered
        rw [buildConverses_append] at found
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
        obtain ⟨tailInverse, tailInverseFound, headInverse, headInverseFound, rfl⟩ := found
        obtain ⟨tailFlows, tailNamed⟩ := buildRows_converses patterns tailFound tailInverseFound fun u inside =>
          listBound u (by simp [RootRewritesOnTheStep.unknowns_appTerm, inside])
        obtain ⟨headFlows, headNamed⟩ := buildRow_converses pattern headFound headInverseFound
          (bound := bound ++ tailInverse.flatMap goalUnknowns) fun u inside =>
            List.mem_append_left _ (listBound u (by simp [RootRewritesOnTheStep.unknowns_appTerm, inside]))
        refine ⟨tailFlows.append headFlows, fun name inside => ?_⟩
        simp only [namesList, List.mem_append] at inside
        rcases inside with inHead | inTail
        · have here := headNamed name inHead
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
        · have here := tailNamed name inTail
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
end

end ConverseModes

/-! ## What an instance's row holds -/

section Captures

variable {R : Relations} {program : List Clause} {rests avoid : List String} {sites : Pattern}

theorem buildConverses_parts {first second : List Goal} {inverse : List Goal}
    (found : buildConverses (first ++ second) = some inverse) :
    (∃ earlier, buildConverses first = some earlier) ∧ ∃ later, buildConverses second = some later := by
  rw [buildConverses_append] at found
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
  obtain ⟨later, laterFound, earlier, earlierFound, -⟩ := found
  exact ⟨⟨earlier, earlierFound⟩, later, laterFound⟩

theorem buildRows_tail : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm} {goals : List Goal},
    buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items → ∃ rest, inst θ close = encodeList rest
  | [], _, _, _, _, _, _, lowered, θ, items, listIs => by
      simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, -, -⟩ := lowered
      exact ⟨items, listIs⟩
  | pattern :: patterns, _, _, _, _, _, _, lowered, θ, items, listIs => by
      simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨⟨_, _, _⟩, -, ⟨_, _, _⟩, tailFound, rfl, -, -⟩ := lowered
      simp only [RootRewritesOnTheStep.inst_appTerm] at listIs
      obtain ⟨_, rest, -, -, restIs⟩ := PatternRows.encodeList_cons_inv listIs
      exact buildRows_tail patterns tailFound restIs

/-- What a lifted value's goals and its row hold, when the row is a term: the source is a term too. -/
theorem lifted_captures (build : BuildClauses program) {shift source fresh : ℕ} {θ : ℕ → Expr} {s : Pattern}
    (rowIs : inst θ (lifted liftRelation shift source fresh).1 = encode s)
    (goals : ∀ g ∈ (lifted liftRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    ∃ value, θ source = encode value := by
  by_cases zero : shift = 0
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs
    exact ⟨s, rowIs⟩
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs goals
    have asked := goals _ List.mem_cons_self
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_numeralTerm, rowIs] at asked
    obtain ⟨depth, derived⟩ := asked
    exact ScopeClauses.lift_decode build.scope depth _ _ _ s derived

/-- What a lifted list's goals and its row hold, when the row is a list of terms: the source is one too. -/
theorem liftedList_captures (build : BuildClauses program) {shift source fresh : ℕ} {θ : ℕ → Expr}
    {items : List Pattern} (rowIs : inst θ (lifted liftListRelation shift source fresh).1 = encodeList items)
    (goals : ∀ g ∈ (lifted liftListRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    ∃ tail, θ source = encodeList tail := by
  by_cases zero : shift = 0
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs
    exact ⟨items, rowIs⟩
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs goals
    have asked := goals _ List.mem_cons_self
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_numeralTerm, rowIs] at asked
    obtain ⟨depth, derived⟩ := asked
    exact ScopeClauses.liftList_decode build.scope depth _ _ _ items derived

/-- What the instantiation of a bag's or a set's rest holds: its elements' names, and the rest a collection. -/
theorem bagRest_captures (build : BuildClauses program) {kind : CollType} {elements : List Pattern}
    {restName : String} {depth next last : ℕ} {list : Tm} {elementGoals : List Goal} (outside : restName ∉ rests)
    (elementsFound : buildRows rests avoid sites depth (next + 2) elements (lifted liftListRelation
      (shiftOf sites restName depth) (listUnknown avoid next) (listUnknown avoid (next + 1))).1 =
        some (list, elementGoals, last))
    (elementsCaptured : ∀ {inverse : List Goal}, buildConverses elementGoals = some inverse →
      ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
        (∀ g ∈ elementGoals, goalHolds R (Derives R program) θ g) → SubstitutionsRead θ elementGoals →
          ∀ name ∈ namesList elements, OrderedRows.Captured rests θ name)
    {inverse : List Goal}
    (found : buildConverses (Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals) = some inverse)
    {θ : ℕ → Expr} {s : Pattern} (rowIs : inst θ (collectionTerm kind list) = encode s)
    (goals : ∀ g ∈ Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals, goalHolds R (Derives R program) θ g)
    (read : SubstitutionsRead θ (Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals)) :
    ∀ name ∈ names (.collection kind elements (some restName)), OrderedRows.Captured rests θ name := by
  rw [CollectionMatching.inst_collectionTerm] at rowIs
  obtain ⟨items, -, itemsIs⟩ := encode_closed_inv rowIs
  obtain ⟨-, ⟨elementInverse, elementInverseFound⟩⟩ := buildConverses_parts found
  intro name inside
  simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
  rcases inside with inElements | rfl
  · exact elementsCaptured elementInverseFound itemsIs
      (fun g inside' => goals g (List.mem_append_right _ inside'))
      (read.mono fun _ inside' => List.mem_append_right _ inside') name inElements
  · obtain ⟨rest, restIs⟩ := buildRows_tail elements elementsFound itemsIs
    obtain ⟨tail, tailIs⟩ := liftedList_captures build restIs fun g inside' =>
      goals g (List.mem_append_left _ (List.mem_cons_of_mem _ inside'))
    have unwrapped := goals _ (List.mem_append_left _ List.mem_cons_self)
    simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      DemandTransformation.inst_unknown, tailIs] at unwrapped
    have value := CollectionMatching.unwrap_sound build.onlyUnwraps unwrapped
    unfold OrderedRows.Captured
    rw [if_neg outside]
    exact ⟨.collection kind tail none, by rw [value, encode_collection]⟩

mutual
  /-- **When an instance's row is a term and its goals hold, each of its names holds a term**, a list for a rest. -/
  theorem buildRow_captures (build : BuildClauses program) : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm}
      {goals : List Goal}, buildRow rests avoid sites depth next p = some (t, goals, next') → ∀ {inverse : List Goal},
      buildConverses goals = some inverse → ∀ {θ : ℕ → Expr} {s : Pattern}, inst θ t = encode s →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) → SubstitutionsRead θ goals →
      ∀ name ∈ names p, OrderedRows.Captured rests θ name
    | .fvar name, depth, next, _, _, _, lowered, _, _, θ, s, rowIs, goals, read, other, inside => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, -⟩ := lowered
        rw [show other = name by simpa [names] using inside]
        unfold OrderedRows.Captured
        by_cases inRests : name ∈ rests
        · rw [if_pos inRests]
          simp only [inRests, ↓reduceIte] at rowIs goals
          obtain ⟨items, itemsIs⟩ := OrderedRows.list_of_vectorTerm rowIs
          exact liftedList_captures build itemsIs goals
        · rw [if_neg inRests]
          simp only [inRests, ↓reduceIte] at rowIs goals
          exact lifted_captures build rowIs goals
    | .bvar _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, inside => by simp [names] at inside
    | .apply _ arguments, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, argumentsFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, arguments', -, -, argumentsIs⟩ := PatternRows.encode_apply_inv rowIs
        exact buildRows_captures build arguments argumentsFound found argumentsIs goals read name
          (by simpa [names] using inside)
    | .lambda _ body, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, body', -, -, bodyIs⟩ := PatternRows.encode_lambda_inv rowIs
        exact buildRow_captures build body bodyFound found bodyIs goals read name (by simpa [names] using inside)
    | .multiLambda _ _ body, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, _, body', -, -, -, bodyIs⟩ := PatternRows.encode_multiLambda_inv rowIs
        exact buildRow_captures build body bodyFound found bodyIs goals read name (by simpa [names] using inside)
    | .subst body value, depth, next, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, -⟩ :=
          lowered
        obtain ⟨⟨earlier, earlierFound⟩, -⟩ := buildConverses_parts found
        obtain ⟨⟨bodyInverse, bodyInverseFound⟩, ⟨valueInverse, valueInverseFound⟩⟩ :=
          buildConverses_parts earlierFound
        obtain ⟨v, b, valueIs, bodyIs, -, -⟩ := read _ _ _ (List.mem_append_right _ List.mem_cons_self) s rowIs
        simp only [names, List.mem_append] at inside
        rcases inside with inBody | inValue
        · exact buildRow_captures build body bodyFound bodyInverseFound bodyIs
            (fun g inside' => goals g (List.mem_append_left _ (List.mem_append_left _ inside')))
            (read.mono fun _ inside' => List.mem_append_left _ (List.mem_append_left _ inside')) name inBody
        · exact buildRow_captures build value valueFound valueInverseFound valueIs
            (fun g inside' => goals g (List.mem_append_left _ (List.mem_append_right _ inside')))
            (read.mono fun _ inside' => List.mem_append_left _ (List.mem_append_right _ inside')) name inValue
    | .collection .vec elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        obtain ⟨items, itemsIs⟩ := OrderedRows.list_of_vectorTerm rowIs
        exact buildRows_captures build elements elementsFound found itemsIs goals read name (by simpa [names] using inside)
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name,
        inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          obtain ⟨items, itemsIs⟩ := OrderedRows.list_of_vectorTerm rowIs
          obtain ⟨-, ⟨elementInverse, elementInverseFound⟩⟩ := buildConverses_parts found
          simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
          rcases inside with inElements | rfl
          · exact buildRows_captures build elements elementsFound elementInverseFound itemsIs
              (fun g inside' => goals g (List.mem_append_right _ inside'))
              (read.mono fun _ inside' => List.mem_append_right _ inside') name inElements
          · obtain ⟨rest, restIs⟩ := buildRows_tail elements elementsFound itemsIs
            unfold OrderedRows.Captured
            rw [if_pos inRests]
            exact liftedList_captures build restIs fun g inside' => goals g (List.mem_append_left _ inside')
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        rw [CollectionMatching.inst_collectionTerm] at rowIs
        obtain ⟨items, -, itemsIs⟩ := encode_closed_inv rowIs
        exact buildRows_captures build elements elementsFound found itemsIs goals read name (by simpa [names] using inside)
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, goals, read,
        name, inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_captures build outside elementsFound
            (fun {_} inverseFound {_} {_} listIs goals' read' => buildRows_captures build elements elementsFound inverseFound
              listIs goals' read') found rowIs goals read name inside
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        rw [CollectionMatching.inst_collectionTerm] at rowIs
        obtain ⟨items, -, itemsIs⟩ := encode_closed_inv rowIs
        exact buildRows_captures build elements elementsFound found itemsIs goals read name (by simpa [names] using inside)
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, goals, read,
        name, inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_captures build outside elementsFound
            (fun {_} inverseFound {_} {_} listIs goals' read' => buildRows_captures build elements elementsFound inverseFound
              listIs goals' read') found rowIs goals read name inside
        · cases lowered

  theorem buildRows_captures (build : BuildClauses program) : ∀ (patterns : List Pattern) {depth next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') → ∀ {inverse : List Goal},
      buildConverses goals = some inverse → ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) → SubstitutionsRead θ goals → ∀ name ∈ namesList patterns,
        OrderedRows.Captured rests θ name
    | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, inside => by simp [namesList] at inside
    | pattern :: patterns, _, _, _, _, _, _, lowered, _, found, θ, items, listIs, goals, read, name, inside => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, -⟩ := lowered
        obtain ⟨⟨headInverse, headInverseFound⟩, ⟨tailInverse, tailInverseFound⟩⟩ := buildConverses_parts found
        simp only [RootRewritesOnTheStep.inst_appTerm] at listIs
        obtain ⟨x, rest, -, headIs, tailIs⟩ := PatternRows.encodeList_cons_inv listIs
        simp only [namesList, List.mem_append] at inside
        rcases inside with inHead | inTail
        · exact buildRow_captures build pattern headFound headInverseFound headIs
            (fun g inside' => goals g (List.mem_append_left _ inside'))
            (read.mono fun _ inside' => List.mem_append_left _ inside') name inHead
        · exact buildRows_captures build patterns tailFound tailInverseFound tailIs
            (fun g inside' => goals g (List.mem_append_right _ inside'))
            (read.mono fun _ inside' => List.mem_append_right _ inside') name inTail
end

/-- **What an instance's row holds of a name is data**: a term of data, or a list of data for a rest. -/
def DataHeld (rests : List String) (θ : ℕ → Expr) (name : String) : Prop :=
  if name ∈ rests then ∀ tail, θ (labelCode name) = encodeList tail → OrderedMatching.isDataList tail = true
  else ∀ value, θ (labelCode name) = encode value → OrderedMatching.isData value = true

theorem buildRows_tail_data : ∀ (patterns : List Pattern) {depth next next' : ℕ} {close list : Tm}
    {goals : List Goal}, buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
        OrderedMatching.isDataList items = true →
          ∃ rest, inst θ close = encodeList rest ∧ OrderedMatching.isDataList rest = true
  | [], _, _, _, _, _, _, lowered, θ, items, listIs, data => by
      simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, -, -⟩ := lowered
      exact ⟨items, listIs, data⟩
  | pattern :: patterns, _, _, _, _, _, _, lowered, θ, items, listIs, data => by
      simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨⟨_, _, _⟩, -, ⟨_, _, _⟩, tailFound, rfl, -, -⟩ := lowered
      simp only [RootRewritesOnTheStep.inst_appTerm] at listIs
      obtain ⟨_, rest, rfl, -, restIs⟩ := PatternRows.encodeList_cons_inv listIs
      simp only [OrderedMatching.isDataList, Bool.and_eq_true] at data
      exact buildRows_tail_data patterns tailFound restIs data.2

theorem lifted_data (build : BuildClauses program) {shift source fresh : ℕ} {θ : ℕ → Expr} {s : Pattern}
    (rowIs : inst θ (lifted liftRelation shift source fresh).1 = encode s) (data : OrderedMatching.isData s = true)
    (goals : ∀ g ∈ (lifted liftRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    ∀ value, θ source = encode value → OrderedMatching.isData value = true := by
  intro value valueIs
  by_cases zero : shift = 0
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs
    rw [RootRewritesOnTheStep.encode_injective (valueIs.symm.trans rowIs)]
    exact data
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs goals
    have asked := goals _ List.mem_cons_self
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_numeralTerm, rowIs, valueIs] at asked
    have lifted := (lift_iff (R := R) build.scope 0 shift value).mp asked
    rw [← isData_liftBVars 0 shift value, ← RootRewritesOnTheStep.encode_injective lifted]
    exact data

theorem liftedList_data (build : BuildClauses program) {shift source fresh : ℕ} {θ : ℕ → Expr}
    {items : List Pattern} (rowIs : inst θ (lifted liftListRelation shift source fresh).1 = encodeList items)
    (data : OrderedMatching.isDataList items = true)
    (goals : ∀ g ∈ (lifted liftListRelation shift source fresh).2, goalHolds R (Derives R program) θ g) :
    ∀ tail, θ source = encodeList tail → OrderedMatching.isDataList tail = true := by
  intro tail tailIs
  by_cases zero : shift = 0
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs
    rw [RootRewritesOnTheStep.encodeList_inj _ _ (tailIs.symm.trans rowIs)]
    exact data
  · simp only [lifted, zero, ↓reduceIte, DemandTransformation.inst_unknown] at rowIs goals
    have asked := goals _ List.mem_cons_self
    simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, RootRewritesOnTheStep.inst_numeralTerm, rowIs, tailIs] at asked
    obtain ⟨depth, derived⟩ := asked
    have lifted := ScopeClauses.liftList_sound build.scope depth 0 shift tail _ derived
    rw [← isDataList_liftBVars 0 shift tail, ← RootRewritesOnTheStep.encodeList_inj _ _ lifted]
    exact data

/-- What the instantiation of a bag's or a set's rest holds is data: its elements' names, and the rest. -/
theorem bagRest_data (build : BuildClauses program) {kind : CollType} {elements : List Pattern}
    {restName : String} {depth next last : ℕ} {list : Tm} {elementGoals : List Goal} (outside : restName ∉ rests)
    (elementsFound : buildRows rests avoid sites depth (next + 2) elements (lifted liftListRelation
      (shiftOf sites restName depth) (listUnknown avoid next) (listUnknown avoid (next + 1))).1 =
        some (list, elementGoals, last))
    (elementsData : ∀ {inverse : List Goal}, buildConverses elementGoals = some inverse →
      ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
        OrderedMatching.isDataList items = true → (∀ g ∈ elementGoals, goalHolds R (Derives R program) θ g) →
          SubstitutionsRead θ elementGoals → ∀ name ∈ namesList elements, DataHeld rests θ name)
    {inverse : List Goal}
    (found : buildConverses (Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals) = some inverse)
    {θ : ℕ → Expr} {s : Pattern} (rowIs : inst θ (collectionTerm kind list) = encode s)
    (data : OrderedMatching.isData s = true)
    (goals : ∀ g ∈ Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals, goalHolds R (Derives R program) θ g)
    (read : SubstitutionsRead θ (Goal.ask unwrapRelation (.var (labelCode restName))
      (appTerm (symTerm (collectionCode kind)) (.var (listUnknown avoid next))) ::
        (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
          (listUnknown avoid (next + 1))).2 ++ elementGoals)) :
    ∀ name ∈ names (.collection kind elements (some restName)), DataHeld rests θ name := by
  rw [CollectionMatching.inst_collectionTerm] at rowIs
  obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
  simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
  obtain ⟨-, ⟨elementInverse, elementInverseFound⟩⟩ := buildConverses_parts found
  intro name inside
  simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
  rcases inside with inElements | same
  · exact elementsData elementInverseFound itemsIs data
      (fun g inside' => goals g (List.mem_append_right _ inside'))
      (read.mono fun _ inside' => List.mem_append_right _ inside') name inElements
  · rw [same]
    obtain ⟨rest, restIs, restData⟩ := buildRows_tail_data elements elementsFound itemsIs data
    have liftGoals : ∀ g ∈ (lifted liftListRelation (shiftOf sites restName depth) (listUnknown avoid next)
        (listUnknown avoid (next + 1))).2, goalHolds R (Derives R program) θ g :=
      fun g inside' => goals g (List.mem_append_left _ (List.mem_cons_of_mem _ inside'))
    obtain ⟨tail, tailIs⟩ := liftedList_captures build restIs liftGoals
    have tailData := liftedList_data build restIs restData liftGoals tail tailIs
    have unwrapped := goals _ (List.mem_append_left _ List.mem_cons_self)
    simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
      DemandTransformation.inst_unknown, tailIs] at unwrapped
    have value := CollectionMatching.unwrap_sound build.onlyUnwraps unwrapped
    unfold DataHeld
    rw [if_neg outside]
    intro held heldIs
    rw [value, ← encode_collection] at heldIs
    rw [RootRewritesOnTheStep.encode_injective heldIs.symm]
    simp [OrderedMatching.isData, tailData]

mutual
  /-- **When an instance's row is data and its goals hold, what it holds of each name is data.** -/
  theorem buildRow_data (build : BuildClauses program) : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm}
      {goals : List Goal}, buildRow rests avoid sites depth next p = some (t, goals, next') → ∀ {inverse : List Goal},
      buildConverses goals = some inverse → ∀ {θ : ℕ → Expr} {s : Pattern}, inst θ t = encode s →
      OrderedMatching.isData s = true → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      SubstitutionsRead θ goals → ∀ name ∈ names p, DataHeld rests θ name
    | .fvar name, depth, next, _, _, _, lowered, _, _, θ, s, rowIs, data, goals, read, other, inside => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, -⟩ := lowered
        rw [show other = name by simpa [names] using inside]
        unfold DataHeld
        by_cases inRests : name ∈ rests
        · rw [if_pos inRests]
          simp only [inRests, ↓reduceIte] at rowIs goals
          simp only [vectorTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
          obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
          simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
          exact liftedList_data build itemsIs data goals
        · rw [if_neg inRests]
          simp only [inRests, ↓reduceIte] at rowIs goals
          exact lifted_data build rowIs data goals
    | .bvar _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, inside => by simp [names] at inside
    | .apply _ arguments, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, argumentsFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, arguments', rfl, -, argumentsIs⟩ := PatternRows.encode_apply_inv rowIs
        exact buildRows_data build arguments argumentsFound found argumentsIs data goals read name
          (by simpa [names] using inside)
    | .lambda _ body, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, body', rfl, -, bodyIs⟩ := PatternRows.encode_lambda_inv rowIs
        simp only [OrderedMatching.isData, Bool.and_eq_true] at data
        exact buildRow_data build body bodyFound found bodyIs data.2 goals read name (by simpa [names] using inside)
    | .multiLambda _ _ body, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name, inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, -⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨_, _, body', rfl, -, -, bodyIs⟩ := PatternRows.encode_multiLambda_inv rowIs
        simp only [OrderedMatching.isData, Bool.and_eq_true] at data
        exact buildRow_data build body bodyFound found bodyIs data.2 goals read name (by simpa [names] using inside)
    | .subst body value, depth, next, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name, inside => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, -⟩ :=
          lowered
        obtain ⟨⟨earlier, earlierFound⟩, -⟩ := buildConverses_parts found
        obtain ⟨⟨bodyInverse, bodyInverseFound⟩, ⟨valueInverse, valueInverseFound⟩⟩ :=
          buildConverses_parts earlierFound
        obtain ⟨v, b, valueIs, bodyIs, vData, instantiated⟩ :=
          read _ _ _ (List.mem_append_right _ List.mem_cons_self) s rowIs
        have bData : OrderedMatching.isData b = true :=
          isData_of_instantiateBVarAt (replacement := v) 0 b (by rw [instantiated]; exact data)
        simp only [names, List.mem_append] at inside
        rcases inside with inBody | inValue
        · exact buildRow_data build body bodyFound bodyInverseFound bodyIs bData
            (fun g inside' => goals g (List.mem_append_left _ (List.mem_append_left _ inside')))
            (read.mono fun _ inside' => List.mem_append_left _ (List.mem_append_left _ inside')) name inBody
        · exact buildRow_data build value valueFound valueInverseFound valueIs vData
            (fun g inside' => goals g (List.mem_append_left _ (List.mem_append_right _ inside')))
            (read.mono fun _ inside' => List.mem_append_left _ (List.mem_append_right _ inside')) name inValue
    | .collection .vec elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name,
        inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        simp only [vectorTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
        obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
        simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
        exact buildRows_data build elements elementsFound found itemsIs data goals read name (by simpa [names] using inside)
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read,
        name, inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          simp only [vectorTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at rowIs
          obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
          simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
          obtain ⟨-, ⟨elementInverse, elementInverseFound⟩⟩ := buildConverses_parts found
          simp only [names, List.mem_append, Option.toList_some, List.mem_singleton] at inside
          rcases inside with inElements | rfl
          · exact buildRows_data build elements elementsFound elementInverseFound itemsIs data
              (fun g inside' => goals g (List.mem_append_right _ inside'))
              (read.mono fun _ inside' => List.mem_append_right _ inside') name inElements
          · obtain ⟨rest, restIs, restData⟩ := buildRows_tail_data elements elementsFound itemsIs data
            unfold DataHeld
            rw [if_pos inRests]
            exact liftedList_data build restIs restData fun g inside' => goals g (List.mem_append_left _ inside')
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name,
        inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        rw [CollectionMatching.inst_collectionTerm] at rowIs
        obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
        simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
        exact buildRows_data build elements elementsFound found itemsIs data goals read name (by simpa [names] using inside)
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, data,
        goals, read, name, inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_data build outside elementsFound
            (fun {_} inverseFound {_} {_} listIs listData goals' read' =>
              buildRows_data build elements elementsFound inverseFound listIs listData goals' read')
            found rowIs data goals read name inside
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, _, found, θ, s, rowIs, data, goals, read, name,
        inside => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
        rw [CollectionMatching.inst_collectionTerm] at rowIs
        obtain ⟨items, rfl, itemsIs⟩ := encode_closed_inv rowIs
        simp only [OrderedMatching.isData, Option.isNone_none, Bool.true_and] at data
        exact buildRows_data build elements elementsFound found itemsIs data goals read name (by simpa [names] using inside)
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, _, found, θ, s, rowIs, data,
        goals, read, name, inside => by
        simp only [buildRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, -⟩ := lowered
          exact bagRest_data build outside elementsFound
            (fun {_} inverseFound {_} {_} listIs listData goals' read' =>
              buildRows_data build elements elementsFound inverseFound listIs listData goals' read')
            found rowIs data goals read name inside
        · cases lowered

  theorem buildRows_data (build : BuildClauses program) : ∀ (patterns : List Pattern) {depth next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') → ∀ {inverse : List Goal},
      buildConverses goals = some inverse → ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
      OrderedMatching.isDataList items = true → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      SubstitutionsRead θ goals → ∀ name ∈ namesList patterns, DataHeld rests θ name
    | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, inside => by simp [namesList] at inside
    | pattern :: patterns, _, _, _, _, _, _, lowered, _, found, θ, items, listIs, data, goals, read, name, inside => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, -⟩ := lowered
        obtain ⟨⟨headInverse, headInverseFound⟩, ⟨tailInverse, tailInverseFound⟩⟩ := buildConverses_parts found
        simp only [RootRewritesOnTheStep.inst_appTerm] at listIs
        obtain ⟨x, rest, rfl, headIs, tailIs⟩ := PatternRows.encodeList_cons_inv listIs
        simp only [OrderedMatching.isDataList, Bool.and_eq_true] at data
        simp only [namesList, List.mem_append] at inside
        rcases inside with inHead | inTail
        · exact buildRow_data build pattern headFound headInverseFound headIs data.1
            (fun g inside' => goals g (List.mem_append_left _ inside'))
            (read.mono fun _ inside' => List.mem_append_left _ inside') name inHead
        · exact buildRows_data build patterns tailFound tailInverseFound tailIs data.2
            (fun g inside' => goals g (List.mem_append_right _ inside'))
            (read.mono fun _ inside' => List.mem_append_right _ inside') name inTail
end

end Captures

/-- **A converse mentions what its goal mentions.** -/
theorem buildConverse_unknowns {goal : Goal} {converse : List Goal} (found : buildConverse? goal = some converse) :
    ∀ u ∈ converse.flatMap goalUnknowns, u ∈ goalUnknowns goal := by
  cases goal with
  | query _ => simp [buildConverse?] at found
  | ask relation input output =>
      simp only [buildConverse?] at found
      split_ifs at found
      · obtain ⟨⟨function, argument⟩, split, rfl⟩ := Option.map_eq_some_iff.mp found
        rw [splitRow?_some split]
        intro u inside
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
          RootRewritesOnTheStep.unknowns_appTerm, List.mem_append] at inside ⊢
        tauto
      · obtain ⟨⟨function, argument⟩, split, rfl⟩ := Option.map_eq_some_iff.mp found
        rw [splitRow?_some split]
        intro u inside
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
          RootRewritesOnTheStep.unknowns_appTerm, List.mem_append] at inside ⊢
        tauto
      · simp only [Option.some.injEq] at found
        subst found
        intro u inside
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, List.mem_append] at inside ⊢
        tauto
      · obtain ⟨⟨function, argument⟩, split, found⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨⟨depthRow, value⟩, inner, rfl⟩ := Option.map_eq_some_iff.mp found
        simp only at inner
        rw [splitRow?_some split, splitRow?_some inner]
        intro u inside
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns, DataClauses.unitTerm,
          RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append,
          List.mem_append] at inside ⊢
        tauto

theorem buildConverses_unknowns : ∀ {goals inverse : List Goal}, buildConverses goals = some inverse →
    ∀ u ∈ inverse.flatMap goalUnknowns, u ∈ goals.flatMap goalUnknowns
  | [], _, found, u, inside => by
      simp only [buildConverses, Option.some.injEq] at found
      subst found
      simp at inside
  | goal :: goals, _, found, u, inside => by
      simp only [buildConverses, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨later, laterFound, converse, converseFound, rfl⟩ := found
      simp only [List.flatMap_append, List.flatMap_cons, List.mem_append] at inside ⊢
      rcases inside with inLater | here
      · exact .inr (buildConverses_unknowns laterFound u inLater)
      · exact .inl (buildConverse_unknowns converseFound u here)

/-! ## The values an instance's goals substitute -/

section Substituted

variable {R : Relations} {program : List Clause} {rests avoid : List String} {sites : Pattern}

theorem lifted_not_instantiate {relation shift source fresh : ℕ} (other : relation ≠ instantiateRelation) {x y : Tm} :
    Goal.ask instantiateRelation x y ∉ (lifted relation shift source fresh).2 := by
  intro member
  by_cases zero : shift = 0
  · simp [lifted, zero] at member
  · simp only [lifted, zero, ↓reduceIte, List.mem_singleton] at member
    exact other (Goal.ask.inj member).1.symm

mutual
  /-- **The values an instance's goals substitute are the values the instance substitutes**: each instantiation of a
  substitution among the goals has a value whose row is one of them, and each of them is the row of such a value. -/
  theorem buildRow_substituted (build : BuildClauses program) : ∀ (p : Pattern) {depth next next' : ℕ} {t : Tm}
      {goals : List Goal}, buildRow rests avoid sites depth next p = some (t, goals, next') →
      ∀ {θ : ℕ → Expr} {witness : Bindings}, (∀ name ∈ names p, Holds rests θ witness name) →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ {depthRow value body out : Tm}, Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals →
        ∃ s ∈ substValues sites witness depth p, inst θ value = encode s) ∧
      (∀ s ∈ substValues sites witness depth p, ∃ depthRow value body out,
        Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals ∧ inst θ value = encode s)
    | .fvar name, depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨fun member => absurd member (lifted_not_instantiate (by split <;> decide)), fun s inside => ?_⟩
        simp [substValues] at inside
    | .bvar _, _, _, _, _, _, lowered, _, _, _, _ => by
        simp only [buildRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨fun member => absurd member List.not_mem_nil, fun s inside => by simp [substValues] at inside⟩
    | .apply _ arguments, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, argumentsFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRows_substituted build arguments argumentsFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .lambda _ body, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRow_substituted build body bodyFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .multiLambda arity _ body, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, bodyFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRow_substituted build body bodyFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .subst body value, depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        have bodyHolds : ∀ name ∈ names body, Holds rests θ witness name :=
          fun name inside => holds name (by simp [names, inside])
        have valueHolds : ∀ name ∈ names value, Holds rests θ witness name :=
          fun name inside => holds name (by simp [names, inside])
        have bodyGoalsHold : ∀ g ∈ bodyGoals, goalHolds R (Derives R program) θ g :=
          fun g inside => goals g (List.mem_append_left _ (List.mem_append_left _ inside))
        have valueGoalsHold : ∀ g ∈ valueGoals, goalHolds R (Derives R program) θ g :=
          fun g inside => goals g (List.mem_append_left _ (List.mem_append_right _ inside))
        obtain ⟨bodyIn, bodyOut⟩ := buildRow_substituted build body bodyFound bodyHolds bodyGoalsHold
        obtain ⟨valueIn, valueOut⟩ := buildRow_substituted build value valueFound valueHolds valueGoalsHold
        have valueIs := buildRow_sound build value valueFound valueHolds valueGoalsHold
        constructor
        · intro depthRow value' body' out member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with (inBody | inValue) | same
          · obtain ⟨s, sIn, sIs⟩ := bodyIn inBody
            exact ⟨s, by simp [substValues, sIn], sIs⟩
          · obtain ⟨s, sIn, sIs⟩ := valueIn inValue
            exact ⟨s, by simp [substValues, sIn], sIs⟩
          · obtain ⟨-, rowSame, -⟩ := Goal.ask.inj same
            obtain ⟨front, -⟩ := appTerm_inj rowSame
            obtain ⟨-, rfl⟩ := appTerm_inj front
            exact ⟨_, List.mem_cons_self, valueIs⟩
        · intro s inside
          simp only [substValues, List.mem_cons, List.mem_append] at inside
          rcases inside with rfl | inBody | inValue
          · exact ⟨symTerm 0, valueRow, bodyRow, .var (listUnknown avoid last),
              List.mem_append_right _ List.mem_cons_self, valueIs⟩
          · obtain ⟨d, v, b, o, member, isS⟩ := bodyOut s inBody
            exact ⟨d, v, b, o, List.mem_append_left _ (List.mem_append_left _ member), isS⟩
          · obtain ⟨d, v, b, o, member, isS⟩ := valueOut s inValue
            exact ⟨d, v, b, o, List.mem_append_left _ (List.mem_append_right _ member), isS⟩
    | .collection .vec elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRows_substituted build elements elementsFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .collection .vec elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
          obtain ⟨elementsIn, elementsOut⟩ := buildRows_substituted build elements elementsFound
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_append_right _ inside))
          simp only [substValues]
          refine ⟨fun member => ?_, fun s inside => ?_⟩
          · rcases List.mem_append.mp member with inLift | inElements
            · exact absurd inLift (lifted_not_instantiate (by decide))
            · exact elementsIn inElements
          · obtain ⟨d, v, b, o, member, isS⟩ := elementsOut s inside
            exact ⟨d, v, b, o, List.mem_append_right _ member, isS⟩
        · cases lowered
    | .collection .hashBag elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRows_substituted build elements elementsFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .collection .hashBag elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
          obtain ⟨elementsIn, elementsOut⟩ := buildRows_substituted build elements elementsFound
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_append_right _ inside))
          simp only [substValues]
          refine ⟨fun member => ?_, fun s inside => ?_⟩
          · rcases List.mem_append.mp member with inRest | inElements
            · rcases List.mem_cons.mp inRest with same | inLift
              · exact absurd (Goal.ask.inj same).1 (by decide)
              · exact absurd inLift (lifted_not_instantiate (by decide))
            · exact elementsIn inElements
          · obtain ⟨d, v, b, o, member, isS⟩ := elementsOut s inside
            exact ⟨d, v, b, o, List.mem_append_right _ member, isS⟩
        · cases lowered
    | .collection .hashSet elements none, depth, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
        simp only [substValues]
        exact buildRows_substituted build elements elementsFound
          (fun name inside => holds name (by simpa [names] using inside)) goals
    | .collection .hashSet elements (some restName), depth, next, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, elementsFound, rfl, rfl, rfl⟩ := lowered
          obtain ⟨elementsIn, elementsOut⟩ := buildRows_substituted build elements elementsFound
            (fun name inside => holds name (by simp [names, inside]))
            (fun g inside => goals g (List.mem_append_right _ inside))
          simp only [substValues]
          refine ⟨fun member => ?_, fun s inside => ?_⟩
          · rcases List.mem_append.mp member with inRest | inElements
            · rcases List.mem_cons.mp inRest with same | inLift
              · exact absurd (Goal.ask.inj same).1 (by decide)
              · exact absurd inLift (lifted_not_instantiate (by decide))
            · exact elementsIn inElements
          · obtain ⟨d, v, b, o, member, isS⟩ := elementsOut s inside
            exact ⟨d, v, b, o, List.mem_append_right _ member, isS⟩
        · cases lowered

  theorem buildRows_substituted (build : BuildClauses program) : ∀ (patterns : List Pattern) {depth next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      buildRows rests avoid sites depth next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {witness : Bindings}, (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ {depthRow value body out : Tm}, Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals →
        ∃ s ∈ substValuesList sites witness depth patterns, inst θ value = encode s) ∧
      (∀ s ∈ substValuesList sites witness depth patterns, ∃ depthRow value body out,
        Goal.ask instantiateRelation (triple depthRow value body) out ∈ goals ∧ inst θ value = encode s)
    | [], _, _, _, _, _, _, lowered, _, _, _, _ => by
        simp only [buildRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact ⟨fun member => absurd member List.not_mem_nil, fun s inside => by simp [substValuesList] at inside⟩
    | pattern :: patterns, depth, _, _, _, _, _, lowered, θ, witness, holds, goals => by
        simp only [buildRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨headIn, headOut⟩ := buildRow_substituted build pattern headFound
          (fun name inside => holds name (by simp [namesList, inside]))
          (fun g inside => goals g (List.mem_append_left _ inside))
        obtain ⟨tailIn, tailOut⟩ := buildRows_substituted build patterns tailFound
          (fun name inside => holds name (by simp [namesList, inside]))
          (fun g inside => goals g (List.mem_append_right _ inside))
        simp only [substValuesList]
        refine ⟨fun member => ?_, fun s inside => ?_⟩
        · rcases List.mem_append.mp member with inHead | inTail
          · obtain ⟨s, sIn, sIs⟩ := headIn inHead
            exact ⟨s, List.mem_append_left _ sIn, sIs⟩
          · obtain ⟨s, sIn, sIs⟩ := tailIn inTail
            exact ⟨s, List.mem_append_right _ sIn, sIs⟩
        · rcases List.mem_append.mp inside with inHead | inTail
          · obtain ⟨d, v, b, o, member, isS⟩ := headOut s inHead
            exact ⟨d, v, b, o, List.mem_append_left _ member, isS⟩
          · obtain ⟨d, v, b, o, member, isS⟩ := tailOut s inTail
            exact ⟨d, v, b, o, List.mem_append_right _ member, isS⟩
end

end Substituted

end Mettapedia.GSLT.Compilation.Uniform.Instantiation
