import Mettapedia.OSLF.Framework.HerbrandBridge
import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mettapedia.OSLF.Framework.NativeBasis

/-!
# Finite models as certificates: tree automata with binders

A finite model of a language interprets every constructor as an operation on a finite carrier and
every binder as a map from the carrier's functions into the carrier (`FiniteModel`). Patterns,
binders and explicit substitutions included, evaluate into the carrier (`eval`). Without binders a
finite model with a set of accepting elements is a deterministic bottom-up tree automaton; with
binders, an abstraction denotes the finite function from the values of its bound variables to the
values of its body, for one variable (`lam`) or several at once (`lamMulti`).

A certificate is a finite model with a preorder on its carrier (`Certificate`), such that the left
side of every rule is below its right side under every valuation of the rule's metavariables. A
metavariable bound under binders on the left side denotes a function of their values, so the
valuations that matter are finitely many tables (`tables`, `exists_table`), and validity is a finite
check (`Certificate.valid`), which visits the tables one at a time and stops at the first that fails
(`allTables`, `allTables_eq`). The right side may use a metavariable under more binders, as nested
substitutions do: a value matched in a closed state only reads the binders above its match
(`scoped_of_matchRel`, `eval_take`).

- `eval_instantiateBVarAt`: evaluation of an explicit substitution is evaluation in the extended
  environment (the substitution lemma);
- `eval_applyBindings`, `eval_of_matchPattern`: instantiating a rule evaluates as the rule under the
  valuation its bindings give, and matching reconstructs the matched state up to evaluation;
- `step_below`, `reaches_below`: every root step of the language from a closed state, and so every
  run through closed states (`ObjectState`), goes down the preorder;
- `goal_accepted`: every instance of a goal pattern is accepted, for any bindings, including goals with
  rest variables (`{Err | ...rest}`: every bag holding `Err`), whose rests may stay unresolved
  (`eval_applyBindings_instance`);
- `cannotReach_of_check`: when no goal element lies below the value of a state, the state cannot
  reach the goals through scoped states. The check is a computation on finite lists, so the kernel
  decides it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteModels

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList liftBVarsList_eq_map instantiateBVarAt
  instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel BindingsExtends matchPattern_sound
  mergeBindings_subsumed_left mergeBindings_subsumed_right)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal mem_rootReducts)

/-! ## Environments -/

section Lists

variable {A : Type}

/-- Remove `shift` entries at position `cutoff`. -/
def dropAt (cutoff shift : ℕ) (env : List A) : List A := env.take cutoff ++ env.drop (cutoff + shift)

/-- Insert an entry at position `depth`. -/
def insertAt (depth : ℕ) (inserted : A) (env : List A) : List A := env.take depth ++ inserted :: env.drop depth

theorem getD_dropAt (env : List A) (cutoff shift index : ℕ) (fallback : A) :
    (dropAt cutoff shift env).getD index fallback =
      if cutoff ≤ index then env.getD (index + shift) fallback else env.getD index fallback := by
  unfold dropAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, List.getElem?_take,
    List.getElem?_drop]
  by_cases high : cutoff ≤ index
  · rw [if_pos high]
    by_cases inside : index < min cutoff env.length
    · omega
    · rw [if_neg inside]
      by_cases short : env.length < cutoff
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      · congr 2
        omega
  · rw [if_neg high]
    by_cases inside : index < min cutoff env.length
    · rw [if_pos inside, if_pos (by omega)]
    · rw [if_neg inside, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem dropAt_cons (cutoff shift : ℕ) (value : A) (env : List A) :
    dropAt (cutoff + 1) shift (value :: env) = value :: dropAt cutoff shift env := by
  simp [dropAt, Nat.add_right_comm]

theorem dropAt_zero (shift : ℕ) (env : List A) : dropAt 0 shift env = env.drop shift := by
  simp [dropAt]

theorem getD_insertAt (env : List A) (depth index : ℕ) (inserted fallback : A) (within : depth ≤ env.length) :
    (insertAt depth inserted env).getD index fallback =
      if index < depth then env.getD index fallback
      else if index = depth then inserted else env.getD (index - 1) fallback := by
  unfold insertAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_take, List.getElem?_take]
  rw [show min depth env.length = depth by omega]
  by_cases low : index < depth
  · rw [if_pos low, if_pos low, if_pos low]
  · rw [if_neg low, if_neg low]
    by_cases here : index = depth
    · subst here
      simp
    · rw [if_neg here, List.getElem?_cons, if_neg (by omega), List.getElem?_drop]
      congr 2
      omega

theorem insertAt_cons (depth : ℕ) (inserted value : A) (env : List A) :
    insertAt (depth + 1) inserted (value :: env) = value :: insertAt depth inserted env := by
  simp [insertAt]

theorem insertAt_zero (inserted : A) (env : List A) : insertAt 0 inserted env = inserted :: env := by
  simp [insertAt]

theorem dropAt_append (cutoff shift : ℕ) (front env : List A) :
    dropAt (cutoff + front.length) shift (front ++ env) = front ++ dropAt cutoff shift env := by
  simp [dropAt, List.take_append, List.drop_append, List.take_of_length_le (show front.length ≤ cutoff + front.length by omega),
    List.drop_eq_nil_of_le (show front.length ≤ cutoff + shift + front.length by omega), Nat.add_right_comm]

theorem insertAt_append (depth : ℕ) (inserted : A) (front env : List A) :
    insertAt (depth + front.length) inserted (front ++ env) = front ++ insertAt depth inserted env := by
  simp [insertAt, List.take_append, List.drop_append, List.take_of_length_le (show front.length ≤ depth + front.length by omega),
    List.drop_eq_nil_of_le (show front.length ≤ depth + front.length by omega)]

end Lists

/-! ## Finite models and evaluation -/

/-- **A finite model of a language**: an operation for every constructor label, and an
interpretation of abstractions; ill-formed patterns go to `junk`. -/
structure FiniteModel (A : Type) where
  junk : A
  lam : (A → A) → A
  lamMulti : (arity : ℕ) → ((Fin arity → A) → A) → A := fun _ _ => junk
  /-- The empty collection of each kind. -/
  collectionUnit : CollType → A := fun _ => junk
  /-- Adding an element to a collection of each kind. -/
  collectionJoin : CollType → A → A → A := fun _ _ _ => junk
  operation : String → List A → A

/-- A valuation of metavariables: a metavariable under binders denotes a function of their values. -/
abbrev Valuation (A : Type) := String → List A → A

variable {A : Type} (model : FiniteModel A)

/-- The value a collection starts from: its rest variable, or the empty bag. -/
def restValue (valuation : Valuation A) (env : List A) (kind : CollType) : Option String → A
  | some name => valuation name env
  | none => model.collectionUnit kind

mutual
/-- **Evaluate a pattern** in an environment of bound-variable values. -/
def eval (valuation : Valuation A) : List A → Pattern → A
  | env, .bvar index => env.getD index model.junk
  | env, .fvar name => valuation name env
  | env, .apply label arguments => model.operation label (evalList valuation env arguments)
  | env, .lambda _ body => model.lam fun value => eval valuation (value :: env) body
  | env, .multiLambda arity _ body =>
      model.lamMulti arity fun values => eval valuation (List.ofFn values ++ env) body
  | env, .subst body replacement => eval valuation (eval valuation env replacement :: env) body
  | env, .collection kind elements rest =>
      (evalList valuation env elements).foldr (model.collectionJoin kind) (restValue model valuation env kind rest)

def evalList (valuation : Valuation A) : List A → List Pattern → List A
  | _, [] => []
  | env, pattern :: patterns => eval valuation env pattern :: evalList valuation env patterns
end

theorem evalList_eq_map (valuation : Valuation A) (env : List A) :
    ∀ patterns : List Pattern, evalList model valuation env patterns = patterns.map (eval model valuation env)
  | [] => rfl
  | pattern :: patterns => by
    simp only [evalList, List.map_cons, evalList_eq_map valuation env patterns]

/-- The valuation of states, which have no metavariables. -/
def stateValuation : Valuation A := fun _ _ => model.junk

/-- **The value of a state.** -/
def value (state : Pattern) : A := eval model (stateValuation model) [] state

/-- A valuation that does not depend on the environment. -/
def Independent (valuation : Valuation A) : Prop := ∀ name first second, valuation name first = valuation name second

theorem stateValuation_independent : Independent (stateValuation model) := fun _ _ _ => rfl

/-! ## Shifting and the substitution lemma -/

section Substitution

variable {model} {valuation : Valuation A} (independent : Independent valuation)
include independent

theorem eval_liftBVars (pattern : Pattern) :
    ∀ (cutoff shift : ℕ) (env : List A),
      eval model valuation env (liftBVars cutoff shift pattern) = eval model valuation (dropAt cutoff shift env) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift env
    simp only [liftBVars]
    by_cases high : index ≥ cutoff
    · rw [if_pos high]
      simp only [eval]
      rw [getD_dropAt, if_pos high]
    · rw [if_neg high]
      simp only [eval]
      rw [getD_dropAt, if_neg high]
  | hfvar name => intro cutoff shift env; exact independent name _ _
  | happly label arguments ih =>
    intro cutoff shift env
    simp only [liftBVars, eval, evalList_eq_map, liftBVarsList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member cutoff shift env
  | hlambda name body ih =>
    intro cutoff shift env
    simp only [liftBVars, eval]
    congr 1
    funext entry
    rw [ih (cutoff + 1) shift (entry :: env), dropAt_cons]
  | hmultiLambda arity names body ih =>
    intro cutoff shift env
    simp only [liftBVars, eval]
    congr 1
    funext values
    have shifted := dropAt_append cutoff shift (List.ofFn values) env
    rw [List.length_ofFn] at shifted
    rw [ih (cutoff + arity) shift, shifted]
  | hsubst body replacement bodyIh replacementIh =>
    intro cutoff shift env
    simp only [liftBVars, eval]
    rw [replacementIh cutoff shift env, bodyIh (cutoff + 1) shift, dropAt_cons]
  | hcollection kind elements rest ih =>
    intro cutoff shift env
    simp only [liftBVars, eval, evalList_eq_map, liftBVarsList_eq_map, List.map_map]
    congr 1
    · cases rest with
      | none => rfl
      | some name => exact independent name _ _
    · exact List.map_congr_left fun element member => ih element member cutoff shift env

/-- **The substitution lemma**: eliminating a bound level evaluates as inserting the value of the
replacement into the environment. -/
theorem eval_instantiateBVarAt (replacement : Pattern) (body : Pattern) :
    ∀ (depth : ℕ) (env : List A), depth ≤ env.length →
      eval model valuation env (instantiateBVarAt depth replacement body) =
        eval model valuation (insertAt depth (eval model valuation (env.drop depth) replacement) env) body := by
  induction body using Pattern.inductionOn with
  | hbvar index =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval]
    rw [getD_insertAt env depth index _ _ within]
    by_cases low : index < depth
    · rw [if_pos low, if_pos low]
      simp only [eval]
    · rw [if_neg low, if_neg low]
      by_cases here : index = depth
      · rw [if_pos here, if_pos here, eval_liftBVars independent, dropAt_zero]
      · rw [if_neg here, if_neg here]
        simp only [eval]
  | hfvar name =>
    intro depth env _
    rw [instantiateBVarAt]
    exact independent name _ _
  | happly label arguments ih =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval, evalList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member depth env within
  | hlambda name body ih =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval]
    congr 1
    funext entry
    rw [ih (depth + 1) (entry :: env) (by simpa using within), insertAt_cons, List.drop_succ_cons]
  | hmultiLambda arity names body ih =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval]
    congr 1
    funext values
    have inserted := insertAt_append depth (eval model valuation (env.drop depth) replacement) (List.ofFn values) env
    rw [List.length_ofFn] at inserted
    have dropped : (List.ofFn values ++ env).drop (depth + arity) = env.drop depth := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by simp)]
      simp
    rw [ih (depth + arity) (List.ofFn values ++ env) (by simp; omega), dropped, inserted]
  | hsubst body nested bodyIh nestedIh =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval]
    rw [nestedIh depth env within, bodyIh (depth + 1) _ (by simpa using within), insertAt_cons,
      List.drop_succ_cons]
  | hcollection kind elements rest ih =>
    intro depth env within
    rw [instantiateBVarAt]
    simp only [eval, evalList_eq_map, List.map_map]
    congr 1
    · cases rest with
      | none => rfl
      | some name => exact independent name _ _
    · exact List.map_congr_left fun element member => ih element member depth env within

theorem eval_instantiateBVar (replacement body : Pattern) (env : List A) :
    eval model valuation env (instantiateBVar replacement body) =
      eval model valuation (eval model valuation env replacement :: env) body := by
  unfold instantiateBVar
  rw [eval_instantiateBVarAt independent replacement body 0 env (Nat.zero_le _), insertAt_zero, List.drop_zero]

/-- **Locality**: a pattern whose bound variables are in scope at a depth reads only that many
entries of the environment. -/
theorem eval_take (pattern : Pattern) :
    ∀ (depth : ℕ) (env : List A), pattern.isWellScopedAt depth = true →
      eval model valuation env pattern = eval model valuation (env.take depth) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
    simp only [eval, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos inScope]
  | hfvar name => intro _ _ _; exact independent name _ _
  | happly label arguments ih =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
      at inScope
    simp only [eval, evalList_eq_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member depth env (inScope argument member)
  | hlambda name body ih =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [eval]
    congr 1
    funext entry
    rw [ih (depth + 1) (entry :: env) inScope, List.take_succ_cons]
  | hmultiLambda arity names body ih =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [eval]
    congr 1
    funext values
    rw [ih (depth + arity) _ inScope, List.take_append, List.take_of_length_le (by simp)]
    simp
  | hsubst body replacement bodyIh replacementIh =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
    simp only [eval]
    rw [bodyIh (depth + 1) _ inScope.1, List.take_succ_cons, replacementIh depth env inScope.2]
  | hcollection kind elements rest ih =>
    intro depth env inScope
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
      at inScope
    simp only [eval, evalList_eq_map]
    congr 1
    · cases rest with
      | none => rfl
      | some name => exact independent name _ _
    · exact List.map_congr_left fun element member => ih element member depth env (inScope element member)

end Substitution

/-! ## Instantiating and matching rules -/

/-- The valuation that bindings give: a bound metavariable denotes the value of its binding. -/
def bindingValuation (bindings : Bindings) : Valuation A := fun name env =>
  match bindings.find? (·.1 == name) with
  | some (_, bound) => eval model (stateValuation model) env bound
  | none => model.junk

mutual
/-- The rest variables of a pattern, with the kind of their collection. -/
def restVars : Pattern → List (String × CollType)
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ arguments => restVarsList arguments
  | .lambda _ body => restVars body
  | .multiLambda _ _ body => restVars body
  | .subst body replacement => restVars body ++ restVars replacement
  | .collection kind elements rest =>
      restVarsList elements ++ (match rest with | some name => [(name, kind)] | none => [])

def restVarsList : List Pattern → List (String × CollType)
  | [] => []
  | pattern :: patterns => restVars pattern ++ restVarsList patterns
end

theorem restVarsList_eq : ∀ patterns : List Pattern, restVarsList patterns = patterns.flatMap restVars
  | [] => rfl
  | pattern :: patterns => by simp only [restVarsList, List.flatMap_cons, restVarsList_eq patterns]

/-- Every rest variable is bound to a closed collection of its kind. -/
def RestsBound (bindings : Bindings) (pattern : Pattern) : Prop :=
  ∀ entry ∈ restVars pattern, ∃ bound, bindings.find? (·.1 == entry.1) = some (entry.1, .collection entry.2 bound none)

theorem applyBindings_collection_none (bindings : Bindings) (kind : CollType) (elements : List Pattern) :
    applyBindings bindings (.collection kind elements none) =
      .collection kind (elements.map (applyBindings bindings)) none := by
  rw [applyBindings]
  simp

theorem applyBindings_collection_some {bindings : Bindings} {kind : CollType} {elements bound : List Pattern}
    {name : String} (found : bindings.find? (·.1 == name) = some (name, .collection kind bound none)) :
    applyBindings bindings (.collection kind elements (some name)) =
      .collection kind (elements.map (applyBindings bindings) ++ bound) none := by
  rw [applyBindings]
  simp [found]

theorem eval_collection (valuation : Valuation A) (env : List A) (kind : CollType) (elements : List Pattern) :
    eval model valuation env (.collection kind elements none) =
      (elements.map (eval model valuation env)).foldr (model.collectionJoin kind) (model.collectionUnit kind) := by
  simp only [eval, evalList_eq_map, restValue]

/-- **Instantiating a pattern evaluates as the pattern under the valuation of the bindings**, when its
rest variables are bound to collections. -/
theorem eval_applyBindings (bindings : Bindings) (pattern : Pattern) (bound : RestsBound bindings pattern) :
    ∀ env : List A, eval model (stateValuation model) env (applyBindings bindings pattern) =
      eval model (bindingValuation model bindings) env pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro env; rw [applyBindings]; rfl
  | hfvar name =>
    intro env
    rw [applyBindings]
    cases found : bindings.find? (·.1 == name) with
    | none => simp only [eval, bindingValuation, found]; rfl
    | some entry => simp only [eval, bindingValuation, found]
  | happly label arguments ih =>
    intro env
    rw [applyBindings]
    simp only [eval, evalList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member (fun entry inside => bound entry (by
      simp only [restVars, restVarsList_eq, List.mem_flatMap]
      exact ⟨argument, member, inside⟩)) env
  | hlambda name body ih =>
    intro env
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext entry
    exact ih (fun entry inside => bound entry (by simpa [restVars] using inside)) (entry :: env)
  | hmultiLambda arity names body ih =>
    intro env
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext values
    exact ih (fun entry inside => bound entry (by simpa [restVars] using inside)) (List.ofFn values ++ env)
  | hsubst body replacement bodyIh replacementIh =>
    intro env
    rw [applyBindings]
    simp only [eval]
    rw [eval_instantiateBVar (stateValuation_independent model),
      replacementIh (fun entry inside => bound entry (by simp [restVars, inside])) env,
      bodyIh (fun entry inside => bound entry (by simp [restVars, inside]))]
  | hcollection kind elements rest ih =>
    intro env
    have mapped : elements.map (fun element => eval model (stateValuation model) env (applyBindings bindings element)) =
        elements.map (eval model (bindingValuation model bindings) env) :=
      List.map_congr_left fun element member => ih element member (fun entry inside => bound entry (by
        simp only [restVars, restVarsList_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨element, member, inside⟩)) env
    cases rest with
    | none =>
      rw [applyBindings_collection_none]
      simp only [eval, evalList_eq_map, restValue, List.map_map, Function.comp_def]
      rw [mapped]
    | some name =>
      obtain ⟨boundElements, found⟩ := bound (name, kind) (by simp [restVars])
      rw [applyBindings_collection_some found]
      simp only [eval, evalList_eq_map, restValue, List.map_append, List.foldr_append, List.map_map,
        Function.comp_def]
      rw [mapped]
      simp only [bindingValuation, found, eval, evalList_eq_map, restValue]

theorem find?_singleton (name : String) (value : Pattern) :
    ([(name, value)] : Bindings).find? (·.1 == name) = some (name, value) := by
  simp [List.find?]

/-- The valuation of an instance of a goal, given the kinds of its rest variables: a metavariable
denotes the value of its binding; a rest variable denotes the value its collection continues with,
the fold of the collection it is bound to, or `junk` when it stays unresolved. -/
def instanceValuation (bindings : Bindings) (kinds : List (String × CollType)) : Valuation A := fun name env =>
  match kinds.find? (·.1 == name) with
  | some (_, kind) =>
      match bindings.find? (·.1 == name) with
      | some (_, .collection boundKind bound none) =>
          if boundKind == kind then
            (bound.map (eval model (stateValuation model) env)).foldr (model.collectionJoin kind) (model.collectionUnit kind)
          else model.junk
      | _ => model.junk
  | none => bindingValuation model bindings name env

/-- **Every instance of a pattern evaluates as the pattern under a valuation**, for any bindings, when
each rest variable has one kind and no rest variable is also a metavariable. -/
theorem eval_applyBindings_instance (bindings : Bindings) (kinds : List (String × CollType)) (pattern : Pattern)
    (rests : ∀ entry ∈ restVars pattern, kinds.find? (·.1 == entry.1) = some entry)
    (plain : ∀ name ∈ Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern, kinds.find? (·.1 == name) = none) :
    ∀ env : List A, eval model (stateValuation model) env (applyBindings bindings pattern) =
      eval model (instanceValuation model bindings kinds) env pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro env; rw [applyBindings]; rfl
  | hfvar name =>
    intro env
    have notRest := plain name (by rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]; simp)
    rw [applyBindings]
    cases found : bindings.find? (·.1 == name) with
    | none => simp only [eval, instanceValuation, notRest, bindingValuation, found]; rfl
    | some entry => simp only [eval, instanceValuation, notRest, bindingValuation, found]
  | happly label arguments ih =>
    intro env
    rw [applyBindings]
    simp only [eval, evalList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member
      (fun entry inside => rests entry (by
        simp only [restVars, restVarsList_eq, List.mem_flatMap]
        exact ⟨argument, member, inside⟩))
      (fun name inside => plain name (by
        rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
        exact List.mem_flatMap.mpr ⟨argument, member, inside⟩)) env
  | hlambda name body ih =>
    intro env
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext entry
    exact ih (fun entry inside => rests entry (by simpa [restVars] using inside))
      (fun name inside => plain name (by rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]; exact inside))
      (entry :: env)
  | hmultiLambda arity names body ih =>
    intro env
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext values
    exact ih (fun entry inside => rests entry (by simpa [restVars] using inside))
      (fun name inside => plain name (by rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]; exact inside))
      (List.ofFn values ++ env)
  | hsubst body replacement bodyIh replacementIh =>
    intro env
    rw [applyBindings]
    simp only [eval]
    rw [eval_instantiateBVar (stateValuation_independent model),
      replacementIh (fun entry inside => rests entry (by simp [restVars, inside]))
        (fun name inside => plain name (by
          rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]; exact List.mem_append_right _ inside)) env,
      bodyIh (fun entry inside => rests entry (by simp [restVars, inside]))
        (fun name inside => plain name (by
          rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]; exact List.mem_append_left _ inside))]
  | hcollection kind elements rest ih =>
    intro env
    have mapped : elements.map (fun element => eval model (stateValuation model) env (applyBindings bindings element)) =
        elements.map (eval model (instanceValuation model bindings kinds) env) :=
      List.map_congr_left fun element member => ih element member
        (fun entry inside => rests entry (by
          simp only [restVars, restVarsList_eq, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨element, member, inside⟩))
        (fun name inside => plain name (by
          rw [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
          exact List.mem_flatMap.mpr ⟨element, member, inside⟩)) env
    cases rest with
    | none =>
      rw [applyBindings_collection_none]
      simp only [eval, evalList_eq_map, restValue, List.map_map, Function.comp_def]
      rw [mapped]
    | some name =>
      have kindOf := rests (name, kind) (by simp [restVars])
      rw [applyBindings]
      simp only [eval, evalList_eq_map, restValue, instanceValuation, kindOf]
      rw [List.map_append, List.foldr_append, List.map_map, Function.comp_def, mapped]
      congr 1
      cases found : List.find? (fun entry => entry.1 == name) bindings with
      | none => simp [stateValuation]
      | some entry =>
        obtain ⟨_, bound⟩ := entry
        cases bound with
        | collection boundKind bound boundRest =>
          cases boundRest with
          | none =>
            by_cases same : boundKind = kind
            · subst same
              simp
            · simp [same, stateValuation]
          | some _ => simp [stateValuation]
        | _ => simp [stateValuation]

/-- Every entry of merged bindings comes from one of the two. -/
theorem mem_of_mergeBindings : ∀ {first second merged : Bindings}, mergeBindings first second = some merged →
    ∀ entry ∈ merged, entry ∈ first ∨ entry ∈ second
  | first, [], merged, merge, entry, member => by
    simp only [mergeBindings, List.foldlM, Option.pure_def, Option.some.injEq] at merge
    subst merge
    exact Or.inl member
  | first, (name, value) :: rest, merged, merge, entry, member => by
    simp only [mergeBindings, List.foldlM] at merge
    cases found : first.find? (·.1 == name) with
    | none =>
      simp only [found] at merge
      change mergeBindings ((name, value) :: first) rest = some merged at merge
      rcases mem_of_mergeBindings merge entry member with inFirst | inRest
      · rcases List.mem_cons.mp inFirst with rfl | old
        · exact Or.inr List.mem_cons_self
        · exact Or.inl old
      · exact Or.inr (List.mem_cons_of_mem _ inRest)
    | some existing =>
      obtain ⟨_, existingValue⟩ := existing
      by_cases same : existingValue = value
      · simp only [found, same, beq_self_eq_true, ↓reduceIte] at merge
        change mergeBindings first rest = some merged at merge
        rcases mem_of_mergeBindings merge entry member with inFirst | inRest
        · exact Or.inl inFirst
        · exact Or.inr (List.mem_cons_of_mem _ inRest)
      · simp [found, same] at merge

/-- **Left-commutativity** of the join of every unordered collection kind: what matching modulo
permutation needs. Vectors are matched in order and need nothing. -/
def LeftCommutes : Prop :=
  ∀ kind, kind ≠ .vec → ∀ first second rest : A,
    model.collectionJoin kind first (model.collectionJoin kind second rest) =
      model.collectionJoin kind second (model.collectionJoin kind first rest)

/-- The elements a rest variable is bound to, or none for no rest variable. -/
def RestBound (bindings : Bindings) (kind : CollType) : Option String → List Pattern → Prop
  | none, bound => bound = []
  | some name, bound => bindings.find? (·.1 == name) = some (name, .collection kind bound none)

theorem objects_of_list : ∀ {patterns : List Pattern}, isObjectPatternList patterns = true →
    ∀ pattern ∈ patterns, isObjectPattern pattern = true
  | [], _, _, member => by cases member
  | head :: tail, objects, pattern, member => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    rcases List.mem_cons.mp member with rfl | later
    · exact objects.1
    · exact objects_of_list objects.2 pattern later

theorem list_of_objects : ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, isObjectPattern pattern = true) →
    isObjectPatternList patterns = true
  | [], _ => rfl
  | head :: tail, objects => by
    simp only [isObjectPatternList, Bool.and_eq_true]
    exact ⟨objects head List.mem_cons_self, list_of_objects fun pattern member => objects pattern (List.mem_cons_of_mem _ member)⟩

mutual
/-- **Matching reconstructs the matched object up to evaluation**, under every extension of the
bindings; bags are matched modulo permutation, which the left-commutativity of the join of each
unordered kind absorbs. -/
theorem eval_of_matchRel (comm : LeftCommutes model) :
    ∀ {pattern state : Pattern} {bindings : Bindings}, MatchRel pattern state bindings → isObjectPattern state = true →
      ∀ extended : Bindings, BindingsExtends bindings extended → ∀ env : List A,
        eval model (stateValuation model) env (applyBindings extended pattern) =
          eval model (stateValuation model) env state
  | _, state, _, @MatchRel.fvar name _, _, extended, extension, env => by
    rw [applyBindings.eq_def]
    simp only
    rw [extension name state (by simp [List.find?])]
  | _, _, _, .bvar, _, _, _, _ => by rw [applyBindings.eq_def]
  | _, _, _, .apply arguments _, object, extended, extension, env => by
    simp only [isObjectPattern] at object
    rw [applyBindings]
    simp only [eval]
    rw [evalList_eq_map, evalList_eq_map]
    exact congrArg _ (evalList_of_matchArgsRel comm arguments object extended extension env)
  | _, _, _, .lambda body, object, extended, extension, env => by
    simp only [isObjectPattern] at object
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext entry
    exact eval_of_matchRel comm body object extended extension (entry :: env)
  | _, _, _, .multiLambda body, object, extended, extension, env => by
    simp only [isObjectPattern] at object
    rw [applyBindings]
    simp only [eval]
    congr 1
    funext values
    exact eval_of_matchRel comm body object extended extension (List.ofFn values ++ env)
  | _, _, _, .collection (rest := rest) notVec bag, object, extended, extension, env => by
    simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
    obtain ⟨restNone, elementsObject⟩ := object
    subst restNone
    obtain ⟨bound, restBound, equation⟩ := evalBag_of_matchBagRel comm bag notVec extended extension elementsObject env
    rw [eval_collection]
    cases rest with
    | none =>
      cases restBound
      rw [applyBindings_collection_none, eval_collection, List.map_map]
      simpa using equation
    | some name =>
      rw [applyBindings_collection_some restBound, eval_collection]
      exact equation
  | _, _, _, .vector arguments, object, extended, extension, env => by
    simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
    obtain ⟨restNone, elementsObject⟩ := object
    subst restNone
    rw [applyBindings_collection_none, eval_collection, eval_collection, List.map_map,
      ← evalList_of_matchArgsRel comm arguments elementsObject extended extension env, List.map_map]
  | _, _, _, .vectorRest (rv := name) prefixMatch merged, object, extended, extension, env => by
    simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
    obtain ⟨restNone, elementsObject⟩ := object
    subst restNone
    have found := extension name _ (mergeBindings_subsumed_right merged (find?_singleton _ _))
    rw [applyBindings_collection_some found, eval_collection, eval_collection, List.map_append,
      evalList_of_matchArgsRel comm prefixMatch
        (list_of_objects fun pattern member => objects_of_list elementsObject pattern (List.mem_of_mem_take member))
        extended (fun name bound found =>
          extension name bound (mergeBindings_subsumed_left merged found)) env,
      ← List.map_append, List.take_append_drop]
  | _, _, _, .subst _ _ _, object, _, _, _ => by simp [isObjectPattern] at object

theorem evalList_of_matchArgsRel (comm : LeftCommutes model) : ∀ {patterns states : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns states bindings → isObjectPatternList states = true →
      ∀ extended : Bindings, BindingsExtends bindings extended →
        ∀ env : List A, (patterns.map (applyBindings extended)).map (eval model (stateValuation model) env) =
          states.map (eval model (stateValuation model) env)
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons head tail merged, objects, extended, extension, env => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    simp only [List.map_cons]
    rw [eval_of_matchRel comm head objects.1 extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) env,
      evalList_of_matchArgsRel comm tail objects.2 extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) env]

theorem evalBag_of_matchBagRel (comm : LeftCommutes model) :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {states : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind states bindings → kind ≠ .vec → ∀ extended : Bindings,
        BindingsExtends bindings extended → isObjectPatternList states = true → ∀ env : List A,
          ∃ bound, RestBound extended kind rest bound ∧
            ((patterns.map (applyBindings extended) ++ bound).map (eval model (stateValuation model) env)).foldr
                (model.collectionJoin kind) (model.collectionUnit kind) =
              (states.map (eval model (stateValuation model) env)).foldr (model.collectionJoin kind)
                (model.collectionUnit kind)
  | _, _, _, _, _, .nilNoRest, _, _, _, _, _ => ⟨[], rfl, rfl⟩
  | _, _, _, states, _, .nilRest (rv := name), _, extended, extension, _, _ =>
    ⟨states, extension name _ (find?_singleton _ _), by simp⟩
  | _, _, kind, states, _, MatchBagRel.cons index below head tail merged, notVec, extended, extension, objects, env => by
    have headObject := objects_of_list objects _ (List.getElem_mem below)
    have tailObjects : isObjectPatternList (states.eraseIdx index) = true :=
      list_of_objects fun pattern member => objects_of_list objects pattern (List.mem_of_mem_eraseIdx member)
    obtain ⟨bound, restBound, equation⟩ := evalBag_of_matchBagRel comm tail notVec extended (fun name bound found =>
      extension name bound (mergeBindings_subsumed_right merged found)) tailObjects env
    refine ⟨bound, restBound, ?_⟩
    have headValue := eval_of_matchRel comm head headObject extended (fun name bound found =>
      extension name bound (mergeBindings_subsumed_left merged found)) env
    simp only [List.map_cons, List.cons_append, List.foldr_cons]
    rw [equation, headValue, ← List.foldr_cons (f := model.collectionJoin kind), ← List.map_cons]
    exact List.Perm.foldr_eq' ((List.getElem_cons_eraseIdx_perm below).map _)
      (fun first _ second _ rest => comm kind notVec second first rest) _
end

theorem eval_of_matchPattern (comm : LeftCommutes model) {pattern state : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern pattern state) (object : isObjectPattern state = true)
    (bound : RestsBound bindings pattern) (env : List A) :
    eval model (bindingValuation model bindings) env pattern = eval model (stateValuation model) env state := by
  rw [← eval_applyBindings model bindings pattern bound]
  exact eval_of_matchRel model comm (matchPattern_sound matched) object bindings (fun _ _ found => found) env

mutual
/-- **Matching binds every rest variable to a closed collection of its kind.** -/
theorem restsBound_of_matchRel : ∀ {pattern state : Pattern} {bindings : Bindings}, MatchRel pattern state bindings →
    ∀ extended : Bindings, BindingsExtends bindings extended → RestsBound extended pattern
  | _, _, _, .fvar, _, _ => fun _ inside => by simp [restVars] at inside
  | _, _, _, .bvar, _, _ => fun _ inside => by simp [restVars] at inside
  | _, _, _, .apply arguments _, extended, extension => fun entry inside =>
    restsBoundList_of_matchArgsRel arguments extended extension entry (by simpa [restVars] using inside)
  | _, _, _, .lambda body, extended, extension => fun entry inside =>
    restsBound_of_matchRel body extended extension entry (by simpa [restVars] using inside)
  | _, _, _, .multiLambda body, extended, extension => fun entry inside =>
    restsBound_of_matchRel body extended extension entry (by simpa [restVars] using inside)
  | _, _, _, .collection _ bag, extended, extension => restsBoundBag_of_matchBagRel bag extended extension
  | _, _, _, .vector arguments, extended, extension => fun entry inside =>
    restsBoundList_of_matchArgsRel arguments extended extension entry (by simpa [restVars] using inside)
  | _, _, _, .vectorRest (rv := name) prefixMatch merged, extended, extension => fun entry inside => by
    simp only [restVars, List.mem_append, List.mem_singleton] at inside
    rcases inside with inElements | rfl
    · exact restsBoundList_of_matchArgsRel prefixMatch extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) entry inElements
    · exact ⟨_, extension name _ (mergeBindings_subsumed_right merged (find?_singleton _ _))⟩
  | _, _, _, .subst body replacement merged, extended, extension => fun entry inside => by
    simp only [restVars, List.mem_append] at inside
    rcases inside with inBody | inReplacement
    · exact restsBound_of_matchRel body extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) entry inBody
    · exact restsBound_of_matchRel replacement extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) entry inReplacement

theorem restsBoundList_of_matchArgsRel : ∀ {patterns states : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns states bindings → ∀ extended : Bindings, BindingsExtends bindings extended →
      ∀ entry ∈ restVarsList patterns, ∃ bound,
        extended.find? (·.1 == entry.1) = some (entry.1, .collection entry.2 bound none)
  | _, _, _, .nil, _, _ => fun _ inside => by simp [restVarsList] at inside
  | _, _, _, .cons head tail merged, extended, extension => fun entry inside => by
    simp only [restVarsList, List.mem_append] at inside
    rcases inside with inHead | inTail
    · exact restsBound_of_matchRel head extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) entry inHead
    · exact restsBoundList_of_matchArgsRel tail extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) entry inTail

theorem restsBoundBag_of_matchBagRel :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {states : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind states bindings → ∀ extended : Bindings, BindingsExtends bindings extended →
        RestsBound extended (.collection kind patterns rest)
  | _, _, _, _, _, .nilNoRest, _, _ => fun _ inside => by simp [restVars, restVarsList] at inside
  | _, _, _, _, _, .nilRest (rv := name), extended, extension => fun entry inside => by
    simp only [restVars, restVarsList, List.nil_append, List.mem_singleton] at inside
    subst inside
    exact ⟨_, extension name _ (find?_singleton _ _)⟩
  | _, _, _, _, _, MatchBagRel.cons _ _ head tail merged, extended, extension => fun entry inside => by
    simp only [restVars, restVarsList, List.mem_append] at inside
    rcases inside with (inHead | inTail) | inRest
    · exact restsBound_of_matchRel head extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) entry inHead
    · exact restsBoundBag_of_matchBagRel tail extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) entry (by
          simp only [restVars, List.mem_append]; exact Or.inl (by simpa [restVarsList_eq] using inTail))
    · exact restsBoundBag_of_matchBagRel tail extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) entry (by
          simp only [restVars, List.mem_append]; exact Or.inr inRest)
end

/-! ## Valuations as finite tables -/

mutual
/-- The metavariable occurrences of a pattern, each with the number of binders above it; a rest
variable occurs where its collection is. -/
def occurrences : ℕ → Pattern → List (String × ℕ)
  | _, .bvar _ => []
  | depth, .fvar name => [(name, depth)]
  | depth, .apply _ arguments => occurrencesList depth arguments
  | depth, .lambda _ body => occurrences (depth + 1) body
  | depth, .multiLambda arity _ body => occurrences (depth + arity) body
  | depth, .subst body replacement => occurrences (depth + 1) body ++ occurrences depth replacement
  | depth, .collection _ elements rest =>
      occurrencesList depth elements ++ (match rest with | some name => [(name, depth)] | none => [])

def occurrencesList : ℕ → List Pattern → List (String × ℕ)
  | _, [] => []
  | depth, pattern :: patterns => occurrences depth pattern ++ occurrencesList depth patterns
end

theorem occurrencesList_eq (depth : ℕ) :
    ∀ patterns : List Pattern, occurrencesList depth patterns = patterns.flatMap (occurrences depth)
  | [] => rfl
  | pattern :: patterns => by simp only [occurrencesList, List.flatMap_cons, occurrencesList_eq depth patterns]

mutual
/-- **Matched values are in scope**: matching a state whose bound variables are in scope binds each
metavariable to a value in scope at the depth of its occurrence. -/
theorem scoped_of_matchRel : ∀ {pattern state : Pattern} {bindings : Bindings}, MatchRel pattern state bindings →
    ∀ extended : Bindings, BindingsExtends bindings extended → ∀ depth : ℕ, state.isWellScopedAt depth = true →
      ∀ entry ∈ occurrences depth pattern, ∃ bound, extended.find? (·.1 == entry.1) = some (entry.1, bound) ∧
        bound.isWellScopedAt entry.2 = true
  | _, state, _, @MatchRel.fvar name _, extended, extension, depth, inScope, entry, inside => by
    simp only [occurrences, List.mem_singleton] at inside
    subst inside
    exact ⟨state, extension name state (by simp [List.find?]), inScope⟩
  | _, _, _, .bvar, _, _, _, _, _, inside => by simp [occurrences] at inside
  | _, _, _, .apply arguments _, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [occurrences] at inside
    exact scopedList_of_matchArgsRel arguments extended extension depth inScope entry inside
  | _, _, _, .lambda body, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [occurrences] at inside
    exact scoped_of_matchRel body extended extension (depth + 1) inScope entry inside
  | _, _, _, .multiLambda body, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [occurrences] at inside
    exact scoped_of_matchRel body extended extension _ inScope entry inside
  | _, _, _, .collection _ bag, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [occurrences] at inside
    exact scopedBag_of_matchBagRel bag extended extension depth inScope entry inside
  | _, _, _, .vector arguments, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    simp only [occurrences, List.append_nil] at inside
    exact scopedList_of_matchArgsRel arguments extended extension depth inScope entry inside
  | _, _, _, .vectorRest (rv := name) prefixMatch merged, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt] at inScope
    rw [Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
    simp only [occurrences, List.mem_append, List.mem_singleton] at inside
    rcases inside with inElements | rfl
    · exact scopedList_of_matchArgsRel prefixMatch extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) depth
        ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mpr fun pattern member =>
          inScope pattern (List.mem_of_mem_take member)) entry inElements
    · refine ⟨_, extension name _ (mergeBindings_subsumed_right merged (find?_singleton _ _)), ?_⟩
      simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
      exact fun pattern member => inScope pattern (List.mem_of_mem_drop member)
  | _, _, _, .subst body replacement merged, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
    simp only [occurrences, List.mem_append] at inside
    rcases inside with inBody | inReplacement
    · exact scoped_of_matchRel body extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) (depth + 1) inScope.1 entry inBody
    · exact scoped_of_matchRel replacement extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) depth inScope.2 entry inReplacement

theorem scopedList_of_matchArgsRel : ∀ {patterns states : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns states bindings → ∀ extended : Bindings, BindingsExtends bindings extended →
      ∀ depth : ℕ, Pattern.isWellScopedListAt depth states = true →
        ∀ entry ∈ occurrencesList depth patterns, ∃ bound, extended.find? (·.1 == entry.1) = some (entry.1, bound) ∧
          bound.isWellScopedAt entry.2 = true
  | _, _, _, .nil, _, _, _, _, _, inside => by simp [occurrencesList] at inside
  | _, _, _, .cons head tail merged, extended, extension, depth, inScope, entry, inside => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
    simp only [occurrencesList, List.mem_append] at inside
    rcases inside with inHead | inTail
    · exact scoped_of_matchRel head extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) depth inScope.1 entry inHead
    · exact scopedList_of_matchArgsRel tail extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) depth inScope.2 entry inTail

theorem scopedBag_of_matchBagRel :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {states : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind states bindings → ∀ extended : Bindings, BindingsExtends bindings extended →
        ∀ depth : ℕ, Pattern.isWellScopedListAt depth states = true →
          ∀ entry ∈ occurrencesList depth patterns ++ (match rest with | some name => [(name, depth)] | none => []),
            ∃ bound, extended.find? (·.1 == entry.1) = some (entry.1, bound) ∧ bound.isWellScopedAt entry.2 = true
  | _, _, _, _, _, .nilNoRest, _, _, _, _, _, inside => by simp [occurrencesList] at inside
  | _, _, _, _, _, .nilRest (rv := name), extended, extension, depth, inScope, entry, inside => by
    simp only [occurrencesList, List.nil_append, List.mem_singleton] at inside
    subst inside
    exact ⟨_, extension name _ (find?_singleton _ _), by simpa [Pattern.isWellScopedAt] using inScope⟩
  | _, _, _, _, _, .cons index below head tail merged, extended, extension, depth, inScope, entry, inside => by
    rw [Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
    simp only [occurrencesList, List.append_assoc, List.mem_append] at inside
    rcases inside with inHead | inTail
    · exact scoped_of_matchRel head extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_left merged found)) depth
        (inScope _ (List.getElem_mem below)) entry inHead
    · exact scopedBag_of_matchBagRel tail extended (fun name bound found =>
        extension name bound (mergeBindings_subsumed_right merged found)) depth
        ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mpr fun pattern member =>
          inScope pattern (List.mem_of_mem_eraseIdx member)) entry (List.mem_append.mpr inTail)
end

/-- **Evaluation reads a valuation only at its occurrences**: valuations that agree on environments
of each occurrence's depth evaluate alike. -/
theorem eval_congr {first second : Valuation A} (pattern : Pattern) :
    ∀ env : List A, (∀ entry ∈ occurrences env.length pattern, ∀ inner : List A, inner.length = entry.2 →
        first entry.1 inner = second entry.1 inner) →
      eval model first env pattern = eval model second env pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _; rfl
  | hfvar name =>
    intro env agree
    exact agree (name, env.length) (by simp [occurrences]) env rfl
  | happly label arguments ih =>
    intro env agree
    simp only [eval, evalList_eq_map]
    congr 1
    refine List.map_congr_left fun argument member => ih argument member env fun entry inside => ?_
    exact agree entry (by
      simp only [occurrences, occurrencesList_eq, List.mem_flatMap]
      exact ⟨argument, member, inside⟩)
  | hlambda name body ih =>
    intro env agree
    simp only [eval]
    congr 1
    funext entry
    exact ih (entry :: env) fun occurrence inside => agree occurrence (by simpa [occurrences] using inside)
  | hmultiLambda arity names body ih =>
    intro env agree
    simp only [eval]
    congr 1
    funext values
    exact ih (List.ofFn values ++ env) fun occurrence inside =>
      agree occurrence (by simpa [occurrences, Nat.add_comm] using inside)
  | hsubst body replacement bodyIh replacementIh =>
    intro env agree
    simp only [eval]
    rw [replacementIh env fun occurrence inside =>
      agree occurrence (by simp only [occurrences, List.mem_append]; exact Or.inr inside)]
    exact bodyIh _ fun occurrence inside =>
      agree occurrence (by simp only [occurrences, List.mem_append]; exact Or.inl (by simpa using inside))
  | hcollection kind elements rest ih =>
    intro env agree
    simp only [eval, evalList_eq_map]
    congr 1
    · cases rest with
      | none => rfl
      | some name => exact agree (name, env.length) (by simp [occurrences]) env rfl
    · exact List.map_congr_left fun element member => ih element member env fun entry inside =>
        agree entry (by
          simp only [occurrences, occurrencesList_eq, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨element, member, inside⟩)

section Tables

variable [DecidableEq A] (elements : List A)

/-- All environments of a length. -/
def vectors : ℕ → List (List A)
  | 0 => [[]]
  | length + 1 => (vectors length).flatMap fun vector => elements.map (· :: vector)

omit [DecidableEq A] in
theorem mem_vectors (complete : ∀ entry : A, entry ∈ elements) :
    ∀ (length : ℕ) (vector : List A), vector ∈ vectors elements length ↔ vector.length = length
  | 0, vector => by cases vector <;> simp [vectors]
  | length + 1, [] => by simp [vectors]
  | length + 1, head :: tail => by
    simp only [vectors, List.mem_flatMap, List.mem_map, List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨vector, member, entry, _, same⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      exact (mem_vectors complete length vector).mp member
    · intro same
      exact ⟨tail, (mem_vectors complete length tail).mpr same, head, complete head, rfl⟩

/-- A table: for each metavariable, its depth and its values on the environments of that depth. -/
abbrev Table (A : Type) := List (String × ℕ × List A)

/-- The valuation a table gives. -/
def tableValuation (table : Table A) : Valuation A := fun name env =>
  match table.find? (·.1 == name) with
  | some (_, depth, outputs) => outputs.getD ((vectors elements depth).idxOf (env.take depth)) model.junk
  | none => model.junk

/-- **Every table for metavariables at given depths.** -/
def tables : List (String × ℕ) → List (Table A)
  | [] => [[]]
  | (name, depth) :: rest =>
      (vectors elements (vectors elements depth).length).flatMap fun outputs =>
        (tables rest).map ((name, depth, outputs) :: ·)

/-- **Every table passes a check**, the tables visited one at a time, stopping at the first that fails, without
listing them all. -/
def allTables : (Table A → Bool) → List (String × ℕ) → Bool
  | check, [] => check []
  | check, (name, depth) :: rest =>
      (vectors elements (vectors elements depth).length).all fun outputs =>
        allTables (fun table => check ((name, depth, outputs) :: table)) rest

omit [DecidableEq A] in
/-- **Visiting the tables one at a time is checking the list of them all.** -/
theorem allTables_eq : ∀ (check : Table A → Bool) (spec : List (String × ℕ)),
    allTables elements check spec = (tables elements spec).all check
  | check, [] => by simp [allTables, tables]
  | check, (name, depth) :: rest => by
    simp only [allTables, tables, List.all_flatMap, List.all_map, Function.comp_def, allTables_eq _ rest]

omit [DecidableEq A] in
theorem getD_map_idxOf [DecidableEq A] {domain : List (List A)} {vector : List A} (member : vector ∈ domain)
    (function : List A → A) (fallback : A) :
    (domain.map function).getD (domain.idxOf vector) fallback = function vector := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf member]
  rfl

/-- **The tables realize every valuation** on the environments of each metavariable's depth; a table
reads a deeper environment through its first entries. -/
theorem exists_table (complete : ∀ entry : A, entry ∈ elements) (valuation : Valuation A) :
    ∀ spec : List (String × ℕ), (spec.map Prod.fst).Nodup →
      ∃ table ∈ tables elements spec, ∀ entry ∈ spec, ∀ env : List A, entry.2 ≤ env.length →
        tableValuation model elements table entry.1 env = valuation entry.1 (env.take entry.2)
  | [], _ => ⟨[], by simp [tables], fun _ member => by simp at member⟩
  | (name, depth) :: rest, distinct => by
    simp only [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨table, member, realizes⟩ := exists_table complete valuation rest distinct.2
    let outputs := (vectors elements depth).map (valuation name)
    refine ⟨(name, depth, outputs) :: table, ?_, ?_⟩
    · simp only [tables, List.mem_flatMap, List.mem_map]
      exact ⟨outputs, (mem_vectors elements complete _ outputs).mpr (by simp [outputs]), table, member, rfl⟩
    · intro entry inside env length
      rcases List.mem_cons.mp inside with rfl | later
      · simp only [tableValuation, List.find?_cons, beq_self_eq_true]
        exact getD_map_idxOf ((mem_vectors elements complete depth _).mpr (by simp; omega)) _ _
      · have different : (name == entry.1) = false := by
          rw [beq_eq_false_iff_ne]
          intro same
          apply distinct.1
          rw [same]
          exact List.mem_map_of_mem later
        have skip := realizes entry later env length
        simp only [tableValuation, List.find?_cons, different] at skip ⊢
        exact skip

end Tables

/-- The first depth of every metavariable, each once. -/
def firstDepths : List (String × ℕ) → List (String × ℕ)
  | [] => []
  | (name, depth) :: rest => (name, depth) :: (firstDepths rest).filter (·.1 != name)

theorem mem_of_mem_firstDepths : ∀ {occurrences : List (String × ℕ)} {entry : String × ℕ},
    entry ∈ firstDepths occurrences → entry ∈ occurrences
  | [], _, inside => by simp [firstDepths] at inside
  | (name, depth) :: rest, entry, inside => by
    simp only [firstDepths, List.mem_cons, List.mem_filter] at inside
    rcases inside with same | ⟨later, _⟩
    · exact same ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_firstDepths later)

theorem firstDepths_keys : ∀ occurrences : List (String × ℕ), ((firstDepths occurrences).map Prod.fst).Nodup
  | [] => List.nodup_nil
  | (name, depth) :: rest => by
    simp only [firstDepths, List.map_cons, List.nodup_cons, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq]
    refine ⟨fun ⟨entry, ⟨_, different⟩, same⟩ => different same, ?_⟩
    exact (firstDepths_keys rest).sublist (List.filter_sublist.map Prod.fst)

/-! ## Certificates -/

/-- **A certificate**: a finite model over a listed carrier, and a preorder on it that every rule
goes down. -/
structure Certificate (A : Type) [DecidableEq A] where
  elements : List A
  complete : ∀ entry : A, entry ∈ elements
  model : FiniteModel A
  below : A → A → Bool

variable [DecidableEq A]

/-- The metavariables of a rule's left side with their depths. -/
def ruleSpec (rule : RewriteRule) : List (String × ℕ) := firstDepths (occurrences 0 rule.left)

/-- The shape a rule check needs: each metavariable occurs at one depth on the left side, and the
right side uses only those metavariables, under at least as many binders. -/
def ruleShape (rule : RewriteRule) : Bool :=
  (occurrences 0 rule.left).all (fun entry => entry ∈ ruleSpec rule) &&
    (occurrences 0 rule.right).all fun entry =>
      (ruleSpec rule).any fun home => home.1 == entry.1 && decide (home.2 ≤ entry.2)

/-- The right side uses only rest variables its left side binds, with their kinds. -/
def restsCovered (rule : RewriteRule) : Bool := (restVars rule.right).all (· ∈ restVars rule.left)

/-- **The states of a run**: object patterns (no explicit substitution, closed collections) whose bound
variables are in scope. -/
def ObjectState (state : Pattern) : Prop := state.isWellScopedAt 0 = true ∧ isObjectPattern state = true

namespace Certificate

variable (certificate : Certificate A)

/-- A rule goes down the preorder under every table. -/
def ruleCheck (rule : RewriteRule) : Bool :=
  ruleShape rule && restsCovered rule &&
    allTables certificate.elements (fun table =>
      certificate.below
        (eval certificate.model (tableValuation certificate.model certificate.elements table) [] rule.left)
        (eval certificate.model (tableValuation certificate.model certificate.elements table) [] rule.right))
      (ruleSpec rule)

/-- The join of every unordered collection kind is left-commutative. -/
def commutes : Bool :=
  [CollType.hashBag, CollType.hashSet].all fun kind =>
    certificate.elements.all fun first => certificate.elements.all fun second => certificate.elements.all fun rest =>
      certificate.model.collectionJoin kind first (certificate.model.collectionJoin kind second rest) ==
        certificate.model.collectionJoin kind second (certificate.model.collectionJoin kind first rest)

/-- The relation is a preorder and the join of every unordered collection kind is left-commutative. -/
def preorderValid : Bool :=
  certificate.elements.all (fun entry => certificate.below entry entry) &&
    (certificate.elements.all fun first => certificate.elements.all fun second =>
      certificate.elements.all fun third =>
        !(certificate.below first second && certificate.below second third) || certificate.below first third) &&
    certificate.commutes

/-- **Validity**: the relation is a preorder, every unordered collection join is left-commutative, and every rule goes
down the preorder. -/
def valid (language : LanguageDef) : Bool :=
  certificate.preorderValid && language.rewrites.all certificate.ruleCheck

variable {certificate} {language : LanguageDef}

theorem preorder_refl (checked : certificate.preorderValid = true) (entry : A) : certificate.below entry entry = true := by
  simp only [preorderValid, Bool.and_eq_true, List.all_eq_true] at checked
  exact checked.1.1 entry (certificate.complete entry)

theorem preorder_commutes (checked : certificate.preorderValid = true) : LeftCommutes certificate.model := by
  simp only [preorderValid, commutes, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
  intro kind notVec first second rest
  have unordered : kind ∈ [CollType.hashBag, CollType.hashSet] := by cases kind <;> simp_all
  exact checked.2 kind unordered first (certificate.complete first) second (certificate.complete second)
    rest (certificate.complete rest)

theorem preorder_trans (checked : certificate.preorderValid = true) {first second third : A}
    (low : certificate.below first second = true) (lower : certificate.below second third = true) :
    certificate.below first third = true := by
  simp only [preorderValid, Bool.and_eq_true, List.all_eq_true] at checked
  have := checked.1.2 first (certificate.complete first) second (certificate.complete second) third
    (certificate.complete third)
  simp only [low, lower, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact this

theorem preorderValid_of_valid (checked : certificate.valid language = true) : certificate.preorderValid = true := by
  simp only [valid, Bool.and_eq_true] at checked
  exact checked.1

theorem leftCommutes (checked : certificate.valid language = true) : LeftCommutes certificate.model :=
  preorder_commutes (preorderValid_of_valid checked)

theorem rule_checked (checked : certificate.valid language = true) {rule : RewriteRule} (member : rule ∈ language.rewrites) :
    certificate.ruleCheck rule = true := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at checked
  exact checked.2 rule member

/-- **Every valuation of a checked rule goes down the preorder**, when it reads each metavariable
through the binders of its left occurrence. -/
theorem rule_below (checked : certificate.valid language = true) {rule : RewriteRule}
    (member : rule ∈ language.rewrites) (valuation : Valuation A)
    (local_ : ∀ home ∈ ruleSpec rule, ∀ env : List A, home.2 ≤ env.length →
      valuation home.1 env = valuation home.1 (env.take home.2)) :
    certificate.below (eval certificate.model valuation [] rule.left)
      (eval certificate.model valuation [] rule.right) = true := by
  have ruleChecked := rule_checked checked member
  simp only [ruleCheck, ruleShape, Bool.and_eq_true, allTables_eq, List.all_eq_true, decide_eq_true_eq] at ruleChecked
  obtain ⟨⟨⟨leftHomes, rightHomes⟩, _⟩, tablesChecked⟩ := ruleChecked
  obtain ⟨table, tableMember, realizes⟩ := exists_table certificate.model certificate.elements
    certificate.complete valuation (ruleSpec rule) (firstDepths_keys _)
  have agree : ∀ side : Pattern,
      (∀ entry ∈ occurrences 0 side, ∃ home ∈ ruleSpec rule, home.1 = entry.1 ∧ home.2 ≤ entry.2) →
      eval certificate.model valuation [] side =
        eval certificate.model (tableValuation certificate.model certificate.elements table) [] side :=
    fun side homes => eval_congr certificate.model side [] fun entry inside inner length => by
      obtain ⟨home, homeMember, sameName, shallow⟩ := homes entry inside
      rw [← sameName, local_ home homeMember inner (by omega), realizes home homeMember inner (by omega)]
  rw [agree rule.left fun entry inside => ⟨entry, leftHomes entry inside, rfl, le_refl _⟩,
    agree rule.right fun entry inside => by
      obtain ⟨home, homeMember, fits⟩ := List.any_eq_true.mp (rightHomes entry inside)
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at fits
      exact ⟨home, homeMember, fits.1, fits.2⟩]
  exact tablesChecked table tableMember

/-- **Every root step from a scoped state goes down the preorder.** -/
theorem step_below (checked : certificate.valid language = true) {source target : Pattern}
    (inScope : ObjectState source)
    (step : target ∈ Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction.rootReducts language source) :
    certificate.below (value certificate.model source) (value certificate.model target) = true := by
  obtain ⟨rule, member, bindings, matched, rfl⟩ := mem_rootReducts.mp step
  have leftBound := restsBound_of_matchRel (matchPattern_sound matched) bindings (fun _ _ found => found)
  have covered : restsCovered rule = true := by
    have ruleChecked := rule_checked checked member
    simp only [ruleCheck, Bool.and_eq_true] at ruleChecked
    exact ruleChecked.1.2
  have rightBound : RestsBound bindings rule.right := fun entry inside =>
    leftBound entry (by simpa using List.all_eq_true.mp covered entry inside)
  unfold value
  rw [← eval_of_matchPattern certificate.model (leftCommutes checked) matched inScope.2 leftBound,
    eval_applyBindings certificate.model bindings rule.right rightBound]
  refine rule_below checked member _ fun home homeMember env shallow => ?_
  obtain ⟨bound, found, boundInScope⟩ := scoped_of_matchRel (matchPattern_sound matched) bindings
    (fun _ _ found => found) 0 inScope.1 home (mem_of_mem_firstDepths homeMember)
  simp only [bindingValuation, found]
  exact eval_take (stateValuation_independent certificate.model) bound home.2 env boundInScope

/-- A semantics goes down the preorder when each of its steps from an object state does. -/
def GoesDown (steps : ReductionSpan Pattern) : Prop :=
  ∀ event : steps.Edge, ObjectState (steps.source event) →
    certificate.below (value certificate.model (steps.source event)) (value certificate.model (steps.target event)) = true

/-- **The root steps go down.** -/
theorem rootGoesDown (checked : certificate.valid language = true) : certificate.GoesDown (languageSpan language) :=
  fun event inScope => step_below checked inScope event.2

/-- **Every run through object states goes down the preorder**, for a semantics that goes down. -/
theorem reaches_below (preorder : certificate.preorderValid = true) {steps : ReductionSpan Pattern}
    (down : certificate.GoesDown steps) {goal : Pattern → Prop} {state : Pattern}
    (reaches : Reaches (between steps ObjectState) goal state) :
    ∃ reached, goal reached ∧ certificate.below (value certificate.model state) (value certificate.model reached) = true := by
  induction reaches with
  | goal atGoal => exact ⟨_, atGoal, preorder_refl preorder _⟩
  | step event _ ih =>
    obtain ⟨reached, atGoal, low⟩ := ih
    exact ⟨reached, atGoal, preorder_trans preorder (down event.1 event.2.1) low⟩

/-! ## Goals and the verdict -/

/-- Each rest variable of a goal has one kind, and no rest variable is also a metavariable. -/
def goalRoles (goal : Pattern) : Bool :=
  (restVars goal).all (fun entry => (restVars goal).find? (·.1 == entry.1) == some entry) &&
    (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars goal).all fun name => ((restVars goal).find? (·.1 == name)).isNone

/-- Every instance of a goal pattern is accepted; a rest variable stands for the rest of its collection,
whatever it is bound to. -/
def goalCheck (accept : A → Bool) (goal : Pattern) : Bool :=
  goalRoles goal &&
  (occurrences 0 goal).all (fun entry => entry ∈ firstDepths (occurrences 0 goal)) &&
    (tables certificate.elements (firstDepths (occurrences 0 goal))).all fun table =>
      accept (eval certificate.model (tableValuation certificate.model certificate.elements table) [] goal)

theorem goal_accepted {accept : A → Bool} {goal : Pattern} (checked : certificate.goalCheck accept goal = true)
    (bindings : Bindings) : accept (value certificate.model (applyBindings bindings goal)) = true := by
  simp only [goalCheck, goalRoles, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Option.isNone_iff_eq_none] at checked
  obtain ⟨⟨⟨rests, plain⟩, sameDepths⟩, tablesChecked⟩ := checked
  obtain ⟨table, tableMember, realizes⟩ := exists_table certificate.model certificate.elements
    certificate.complete (instanceValuation certificate.model bindings (restVars goal)) _ (firstDepths_keys _)
  unfold value
  rw [eval_applyBindings_instance certificate.model bindings (restVars goal) goal rests plain,
    eval_congr certificate.model
    (second := tableValuation certificate.model certificate.elements table) goal [] fun entry inside inner length => by
    rw [realizes entry (sameDepths entry inside) inner (by omega), List.take_of_length_le (by omega)]]
  exact tablesChecked table tableMember

/-- No accepted element lies below a value. -/
def apart (accept : A → Bool) (start : A) : Bool :=
  certificate.elements.all fun entry => !(certificate.below start entry && accept entry)

/-- **No run through object states reaches an accepted value**, for a semantics that goes down, when no
accepted element lies below the value of the state. -/
theorem not_reachesAccepted_of_apart (preorder : certificate.preorderValid = true) {steps : ReductionSpan Pattern}
    (down : certificate.GoesDown steps) {accept : A → Bool} {state : Pattern}
    (apartChecked : certificate.apart accept (value certificate.model state) = true) :
    ¬ Reaches (between steps ObjectState) (fun reached => accept (value certificate.model reached) = true) state := by
  intro reaches
  obtain ⟨reached, accepted, low⟩ := reaches_below preorder down reaches
  have := List.all_eq_true.mp apartChecked _ (certificate.complete (value certificate.model reached))
  simp [low, accepted] at this

/-- **No run through object states reaches the goals**, for a semantics that goes down, when every goal
instance is accepted and no accepted element lies below the value of the state. -/
theorem not_reaches_of_apart (preorder : certificate.preorderValid = true) {steps : ReductionSpan Pattern}
    (down : certificate.GoesDown steps) {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (goalsChecked : goals.all (certificate.goalCheck accept) = true)
    (apartChecked : certificate.apart accept (value certificate.model state) = true) :
    ¬ Reaches (between steps ObjectState) (Goal goals) state := by
  intro reaches
  obtain ⟨reached, ⟨goal, goalMember, bindings, rfl⟩, low⟩ := reaches_below preorder down reaches
  have accepted := goal_accepted (List.all_eq_true.mp goalsChecked goal goalMember) bindings
  have := List.all_eq_true.mp apartChecked _
    (certificate.complete (value certificate.model (applyBindings bindings goal)))
  simp [low, accepted] at this

/-- **Decide that a state cannot reach the goals**: the certificate is valid, every goal instance is
accepted, and no accepted element lies below the value of the state. -/
def cannotReach (language : LanguageDef) (goals : List Pattern) (accept : A → Bool) (state : Pattern) : Bool :=
  certificate.valid language && goals.all (certificate.goalCheck accept) &&
    certificate.apart accept (value certificate.model state)

theorem cannotReach_of_valid {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (valid : certificate.valid language = true) (goalsChecked : goals.all (certificate.goalCheck accept) = true)
    (apartChecked : certificate.apart accept (value certificate.model state) = true) :
    ¬ Reaches (between (languageSpan language) ObjectState) (Goal goals) state :=
  certificate.not_reaches_of_apart (preorderValid_of_valid valid) (rootGoesDown valid) goalsChecked apartChecked

theorem cannotReach_of_check {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReach language goals accept state = true) :
    ¬ Reaches (between (languageSpan language) ObjectState) (Goal goals) state := by
  simp only [cannotReach, Bool.and_eq_true] at checked
  exact cannotReach_of_valid checked.1.1 checked.1.2 checked.2

/-- **Decide that a state never reaches an accepted value**: the accepted elements are a native type the
model selects. -/
def cannotReachAccepted (language : LanguageDef) (accept : A → Bool) (state : Pattern) : Bool :=
  certificate.valid language && certificate.apart accept (value certificate.model state)

theorem cannotReachAccepted_of_check {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReachAccepted language accept state = true) :
    ¬ Reaches (between (languageSpan language) ObjectState) (fun reached => accept (value certificate.model reached) = true)
      state := by
  simp only [cannotReachAccepted, Bool.and_eq_true] at checked
  exact certificate.not_reachesAccepted_of_apart (preorderValid_of_valid checked.1) (rootGoesDown checked.1) checked.2

/-- The runs of a language through scoped states, as a presentation for the basis: one sort, no
constructors. -/
def runsPresentation (language : LanguageDef) :
    NativeBasis.Presentation Unit () (fun _ => Empty) where
  Carrier _ := Pattern
  span := between (languageSpan language) ObjectState
  operation := fun empty => nomatch empty

/-- **A verdict is the falsity of a basis formula**: the reachability term of the basis, at the goals,
is false at the state. -/
theorem not_reach_of_check {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReach language goals accept state = true) :
    ¬ NativeBasis.apply (runsPresentation language) NativeBasis.reach (Goal goals) state := by
  intro holds
  exact cannotReach_of_check checked
    ((congrFun (NativeBasis.denote_reach (runsPresentation language) (Goal goals)) state).mp holds)

end Certificate

end Mettapedia.OSLF.Framework.FiniteModels
