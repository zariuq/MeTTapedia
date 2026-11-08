import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampInference
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Constructors

/-!
# General open formals against ground typing stamps

A child stamp is interned only when all of its inferred types are ground.
Consequently, a function row's type variables can be represented by a partial
map to ground type terms. Successful argument matches extend that map; they
cannot overwrite an earlier binding. This module instantiates the ordered
stamp driver for arbitrary nested and repeated formal variables, rather than
a one-variable control service.

Nested `%Undefined%` occurrences are independent wildcards. Expected-side
`Atom` and the SpaceType/Space bridge are top-level type-matcher cases. The
existing driver's metatype branch still checks the value's kind before this
matcher is called. A missing ground result is a cache-publication decline,
not a claim that the type inference has no answer.

The represented type syntax is the existing `Ty`: variables, symbols and
applications. Numeric literals and arithmetic normalization in native type
expressions are not represented here. No numeric value is encoded as a symbol
to hide that remaining correspondence obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundStampMatcher

abbrev Ground := Ty Empty
abbrev Env := String → Option Ground

def empty : Env := fun _ => none

def value (env : Env) (x : String) : Ty String :=
  (env x).map Ty.lift |>.getD (.var x)

def apply (env : Env) (type_ : Ty String) : Ty String := type_.bind (value env)

mutual
def close : Ty String → Option Ground
  | .var _ => none
  | .sym s => some (.sym s)
  | .app ts => (closeList ts).map Ty.app

def closeList : List (Ty String) → Option (List Ground)
  | [] => some []
  | t :: ts => (close t).bind fun g => (closeList ts).map (g :: ·)
end

@[simp] theorem lift_app (ts : List Ground) :
    (Ty.app ts).lift = (Ty.app (ts.map Ty.lift) : Ty String) := by
  rw [Ty.lift, Ty.map_app]
  rfl

mutual
theorem close_lift : ∀ t : Ground, close t.lift = some t
  | .var x => nomatch x
  | .sym _ => rfl
  | .app ts => by
      rw [lift_app, close]
      rw [closeList_lift]
      rfl

theorem closeList_lift : ∀ ts : List Ground, closeList (ts.map Ty.lift) = some ts
  | [] => rfl
  | t :: ts => by simp [closeList, close_lift, closeList_lift ts]
end

mutual
theorem close_sound : ∀ (t : Ty String) (g : Ground), close t = some g → g.lift = t
  | .var _, _, h => by cases h
  | .sym _, _, h => by cases h; rfl
  | .app ts, g, h => by
      cases hs : closeList ts with
      | none => simp [close, hs] at h
      | some gs =>
          have eq : Ty.app gs = g := by simpa [close, hs] using h
          subst g
          rw [lift_app, closeList_sound ts gs hs]

theorem closeList_sound : ∀ (ts : List (Ty String)) (gs : List Ground),
    closeList ts = some gs → gs.map Ty.lift = ts
  | [], _, h => by cases h; rfl
  | t :: ts, gs, h => by
      cases ht : close t with
      | none => simp [closeList, ht] at h
      | some g =>
          cases hs : closeList ts with
          | none => simp [closeList, ht, hs] at h
          | some rest =>
              have eq : g :: rest = gs := by simpa [closeList, ht, hs] using h
              subst gs
              simp only [List.map_cons, close_sound t g ht, closeList_sound ts rest hs]
end

@[simp] theorem apply_lift (env : Env) (t : Ground) : apply env t.lift = t.lift :=
  Ty.bind_lift (value env) t

@[simp] theorem value_some {env : Env} {x : String} {t : Ground} (h : env x = some t) :
    value env x = t.lift := by simp [value, h]

@[simp] theorem value_none {env : Env} {x : String} (h : env x = none) :
    value env x = .var x := by simp [value, h]

/-- Stored ground assignments are retained through later matches. -/
def Extends (before after : Env) : Prop :=
  ∀ x t, before x = some t → after x = some t

theorem Extends.refl (env : Env) : Extends env env := fun _ _ h => h

theorem Extends.trans {a b c : Env} (ab : Extends a b) (bc : Extends b c) : Extends a c :=
  fun x t h => bc x t (ab x t h)

theorem Extends.bindFresh (env : Env) (x : String) (t : Ground) (fresh : env x = none) :
    Extends env (Function.update env x (some t)) := by
  intro y u hy
  by_cases same : y = x
  · subst y
    rw [fresh] at hy
    cases hy
  · simpa [Function.update_of_ne same] using hy

mutual
/-- Ground structural compatibility with nested independent wildcards. -/
def compatible : Ground → Ground → Bool
  | .var x, _ => nomatch x
  | _, .var x => nomatch x
  | .sym a, .sym b => a == "%Undefined%" || b == "%Undefined%" || a == b
  | .sym a, .app _ => a == "%Undefined%"
  | .app _, .sym b => b == "%Undefined%"
  | .app as, .app bs => compatibleList as bs

def compatibleList : List Ground → List Ground → Bool
  | [], [] => true
  | a :: as, b :: bs => compatible a b && compatibleList as bs
  | _, _ => false
end

mutual
/-- Structural matching preserves the first assignment of each row variable.
Nested wildcard checks are performed before binding a variable. -/
def matchPattern (env : Env) : Ground → Ty String → Option Env
  | actual, .var x =>
      if actual = undefinedTy then some env
      else match env x with
        | none => some (Function.update env x (some actual))
        | some previous => if compatible actual previous then some env else none
  | actual, .sym s =>
      if actual = undefinedTy ∨ s = "%Undefined%" then some env
      else match actual with
        | .var x => nomatch x
        | .sym t => if s = t then some env else none
        | .app _ => none
  | actual, .app ps =>
      if actual = undefinedTy then some env
      else match actual with
        | .var x => nomatch x
        | .sym _ => none
        | .app ts => matchPatterns env ts ps

def matchPatterns (env : Env) : List Ground → List (Ty String) → Option Env
  | [], [] => some env
  | t :: ts, p :: ps => (matchPattern env t p).bind fun next => matchPatterns next ts ps
  | _, _ => none
end

mutual
/-- A successful structural match never overwrites retained row bindings. -/
theorem matchPattern_extends : ∀ (p : Ty String) (actual : Ground) (env next : Env),
    matchPattern env actual p = some next → Extends env next
  | .var x, actual, env, next, h => by
      by_cases wild : actual = undefinedTy
      · have eq : env = next := by simpa [matchPattern, wild] using h
        subst next
        exact Extends.refl env
      · cases old : env x with
        | none =>
            have eq : Function.update env x (some actual) = next := by
              simpa [matchPattern, wild, old] using h
            subst next
            exact Extends.bindFresh env x actual old
        | some previous =>
            by_cases ok : compatible actual previous = true
            · have eq : env = next := by simpa [matchPattern, wild, old, ok] using h
              subst next
              exact Extends.refl env
            · simp [matchPattern, wild, old, ok] at h
  | .sym s, actual, env, next, h => by
      cases actual with
      | var x => exact x.elim
      | app ts =>
          by_cases wild : s = "%Undefined%"
          · have eq : env = next := by simpa [matchPattern, undefinedTy, wild] using h
            subst next
            exact Extends.refl env
          · simp [matchPattern, undefinedTy, wild] at h
      | sym t =>
          by_cases wild : t = "%Undefined%" ∨ s = "%Undefined%"
          · have eq : env = next := by simpa [matchPattern, undefinedTy, wild] using h
            subst next
            exact Extends.refl env
          ·
            by_cases same : s = t
            · have eq : env = next := by simpa [matchPattern, undefinedTy, wild, same] using h
              subst next
              exact Extends.refl env
            · simp [matchPattern, undefinedTy, wild, same] at h
  | .app ps, actual, env, next, h => by
      by_cases wild : actual = undefinedTy
      · subst actual
        have eq : env = next := by simpa [matchPattern, undefinedTy] using h
        subst next
        exact Extends.refl env
      · cases actual with
        | var x => exact x.elim
        | sym _ => simp [matchPattern, wild] at h
        | app ts => exact matchPatterns_extends ps ts env next (by simpa [matchPattern, wild] using h)

theorem matchPatterns_extends : ∀ (ps : List (Ty String)) (ts : List Ground) (env next : Env),
    matchPatterns env ts ps = some next → Extends env next
  | [], [], env, next, h => by cases h; exact Extends.refl env
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | p :: ps, t :: ts, env, next, h => by
      cases first : matchPattern env t p with
      | none => simp [matchPatterns, first] at h
      | some middle =>
          have tail : matchPatterns middle ts ps = some next := by simpa [matchPatterns, first] using h
          exact (matchPattern_extends p t env middle first).trans
            (matchPatterns_extends ps ts middle next tail)
end

mutual
/-- Operational ground-pattern matching. A fresh variable is bound once;
subsequent occurrences test compatibility with the retained ground binding. -/
inductive Matches : Env → Ground → Ty String → Env → Prop where
  | actualWildcard (env : Env) (p : Ty String) : Matches env undefinedTy p env
  | formalWildcard (env : Env) (actual : Ground) : Matches env actual undefinedTy env
  | fresh {env : Env} {x : String} {actual : Ground}
      (notWildcard : actual ≠ undefinedTy) (unset : env x = none) :
      Matches env actual (.var x) (Function.update env x (some actual))
  | bound {env : Env} {x : String} {actual previous : Ground}
      (set : env x = some previous) (accepts : compatible actual previous = true) :
      Matches env actual (.var x) env
  | symbol (env : Env) (s : String) : Matches env (.sym s) (.sym s) env
  | app {env next : Env} {actuals : List Ground} {patterns : List (Ty String)}
      (parts : MatchesList env actuals patterns next) :
      Matches env (.app actuals) (.app patterns) next

inductive MatchesList : Env → List Ground → List (Ty String) → Env → Prop where
  | nil (env : Env) : MatchesList env [] [] env
  | cons {env middle next : Env} {a : Ground} {as : List Ground}
      {p : Ty String} {ps : List (Ty String)}
      (head : Matches env a p middle) (tail : MatchesList middle as ps next) :
      MatchesList env (a :: as) (p :: ps) next
end

mutual
theorem Matches.sound : ∀ {env next : Env} {actual : Ground} {p : Ty String},
    Matches env actual p next → matchPattern env actual p = some next
  | _, _, _, _, .actualWildcard env p => by
      cases p <;> simp [matchPattern, undefinedTy]
  | _, _, _, _, .formalWildcard env actual => by
      cases actual with
      | var x => exact x.elim
      | sym s => simp [matchPattern, undefinedTy]
      | app ts => simp [matchPattern, undefinedTy]
  | _, _, _, _, .fresh notWildcard unset => by simp [matchPattern, notWildcard, unset]
  | _, _, actual, _, .bound set accepts => by
      by_cases wild : actual = undefinedTy <;> simp [matchPattern, wild, set, accepts]
  | _, _, _, _, .symbol env s => by simp [matchPattern, undefinedTy]
  | _, _, _, _, .app parts => by
      simp only [matchPattern, undefinedTy, reduceCtorEq, if_false]
      exact MatchesList.sound parts

theorem MatchesList.sound : ∀ {env next : Env} {actuals : List Ground} {patterns : List (Ty String)},
    MatchesList env actuals patterns next → matchPatterns env actuals patterns = some next
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .cons head tail => by
      simp only [matchPatterns, Matches.sound head]
      exact MatchesList.sound tail
end

mutual
theorem Matches.complete : ∀ (p : Ty String) (actual : Ground) (env next : Env),
    matchPattern env actual p = some next → Matches env actual p next
  | .var x, actual, env, next, h => by
      by_cases wild : actual = undefinedTy
      · subst actual
        have eq : env = next := by simpa [matchPattern] using h
        subst next
        exact .actualWildcard env _
      · cases old : env x with
        | none =>
            have eq : Function.update env x (some actual) = next := by
              simpa [matchPattern, wild, old] using h
            subst next
            exact .fresh wild old
        | some previous =>
            by_cases ok : compatible actual previous = true
            · have eq : env = next := by simpa [matchPattern, wild, old, ok] using h
              subst next
              exact .bound old ok
            · simp [matchPattern, wild, old, ok] at h
  | .sym s, actual, env, next, h => by
      cases actual with
      | var x => exact x.elim
      | app ts =>
          by_cases wild : s = "%Undefined%"
          · subst s
            have eq : env = next := by simpa [matchPattern, undefinedTy] using h
            subst next
            exact .formalWildcard env _
          · simp [matchPattern, undefinedTy, wild] at h
      | sym t =>
          by_cases left : t = "%Undefined%"
          · subst t
            have eq : env = next := by simpa [matchPattern, undefinedTy] using h
            subst next
            exact .actualWildcard env _
          · by_cases right : s = "%Undefined%"
            · subst s
              have eq : env = next := by simpa [matchPattern, undefinedTy] using h
              subst next
              exact .formalWildcard env _
            · by_cases same : s = t
              · subst t
                have eq : env = next := by simpa [matchPattern, undefinedTy, left, right] using h
                subst next
                exact .symbol env s
              · simp [matchPattern, undefinedTy, left, right, same] at h
  | .app ps, actual, env, next, h => by
      by_cases wild : actual = undefinedTy
      · subst actual
        have eq : env = next := by simpa [matchPattern, undefinedTy] using h
        subst next
        exact .actualWildcard env _
      · cases actual with
        | var x => exact x.elim
        | sym _ => simp [matchPattern, wild] at h
        | app ts => exact .app (MatchesList.complete ps ts env next
            (by simpa [matchPattern, wild] using h))

theorem MatchesList.complete : ∀ (ps : List (Ty String)) (ts : List Ground) (env next : Env),
    matchPatterns env ts ps = some next → MatchesList env ts ps next
  | [], [], env, next, h => by cases h; exact .nil env
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | p :: ps, t :: ts, env, next, h => by
      cases first : matchPattern env t p with
      | none => simp [matchPatterns, first] at h
      | some middle =>
          have tail : matchPatterns middle ts ps = some next := by simpa [matchPatterns, first] using h
          exact .cons (Matches.complete p t env middle first)
            (MatchesList.complete ps ts middle next tail)
end

theorem matchPattern_iff (env next : Env) (actual : Ground) (p : Ty String) :
    matchPattern env actual p = some next ↔ Matches env actual p next :=
  ⟨Matches.complete p actual env next, Matches.sound⟩

theorem Matches.preserves {env next : Env} {actual : Ground} {p : Ty String}
    (run : Matches env actual p next) : Extends env next :=
  matchPattern_extends p actual env next run.sound

/-- Rename the row-local variable namespace, leaving ground payloads alone. -/
def renameEnv (ren : String ≃ String) (env : Env) : Env := fun x => env (ren.symm x)

@[simp] theorem renameEnv_apply (ren : String ≃ String) (env : Env) (x : String) :
    renameEnv ren env (ren x) = env x := by simp [renameEnv]

@[simp] theorem renameEnv_empty (ren : String ≃ String) : renameEnv ren empty = empty := rfl

theorem renameEnv_update (ren : String ≃ String) (env : Env) (x : String) (t : Ground) :
    renameEnv ren (Function.update env x (some t)) =
      Function.update (renameEnv ren env) (ren x) (some t) := by
  funext y
  by_cases h : y = ren x
  · subst y
    simp [renameEnv]
  · have hs : ren.symm y ≠ x := by
      intro eq
      apply h
      simpa using congrArg ren eq
    simp [renameEnv, Function.update_of_ne h, Function.update_of_ne hs]

@[simp] theorem renameEnv_inverse (ren : String ≃ String) (env : Env) :
    renameEnv ren.symm (renameEnv ren env) = env := by
  funext x
  simp [renameEnv]

@[simp] theorem map_inverse (ren : String ≃ String) (p : Ty String) :
    (p.map ren).map ren.symm = p := by
  rw [Ty.map_map]
  have eq : (ren.symm : String → String) ∘ ren = id := by funext x; simp
  rw [eq, Ty.map_id']

mutual
theorem Matches.rename (ren : String ≃ String) :
    ∀ {env next : Env} {actual : Ground} {p : Ty String}, Matches env actual p next →
      Matches (renameEnv ren env) actual (p.map ren) (renameEnv ren next)
  | _, _, _, _, .actualWildcard env p => .actualWildcard _ _
  | _, _, _, _, .formalWildcard env actual => .formalWildcard _ _
  | env, _, actual, _, @Matches.fresh _ x _ notWildcard unset => by
      rw [Ty.map_var, renameEnv_update]
      exact .fresh notWildcard (by simpa using unset)
  | _, _, _, _, .bound set accepts => .bound (by simpa using set) accepts
  | _, _, _, _, .symbol env s => .symbol _ _
  | _, _, _, _, .app parts => by
      rw [Ty.map_app]
      exact .app (MatchesList.rename ren parts)

theorem MatchesList.rename (ren : String ≃ String) :
    ∀ {env next : Env} {actuals : List Ground} {patterns : List (Ty String)},
      MatchesList env actuals patterns next →
      MatchesList (renameEnv ren env) actuals (patterns.map (Ty.map ren)) (renameEnv ren next)
  | _, _, _, _, .nil env => .nil _
  | _, _, _, _, .cons head tail => .cons (Matches.rename ren head) (MatchesList.rename ren tail)
end

/-- Freshening a row changes only the names of its private assignments. -/
theorem matchPattern_rename (ren : String ≃ String) (env : Env) (actual : Ground) (p : Ty String) :
    matchPattern (renameEnv ren env) actual (p.map ren) =
      (matchPattern env actual p).map (renameEnv ren) := by
  cases original : matchPattern env actual p with
  | some next =>
      exact (Matches.rename ren (Matches.complete p actual env next original)).sound
  | none =>
      cases changed : matchPattern (renameEnv ren env) actual (p.map ren) with
      | none => rfl
      | some next =>
          have back := (Matches.rename ren.symm
            (Matches.complete (p.map ren) actual _ next changed)).sound
          simp only [renameEnv_inverse, map_inverse, original] at back
          cases back

theorem apply_rename (ren : String ≃ String) (env : Env) (p : Ty String) :
    apply (renameEnv ren env) (p.map ren) = (apply env p).map ren := by
  unfold apply
  rw [Ty.bind_map, Ty.map, Ty.bind_bind]
  apply Ty.bind_congr
  intro x _
  cases old : env x with
  | none => simp [Function.comp, value, old, renameEnv]
  | some ground => simp [Function.comp, value, old, renameEnv, Ty.bind_lift]

mutual
theorem close_rename (ren : String → String) : ∀ p : Ty String, close (p.map ren) = close p
  | .var _ => rfl
  | .sym _ => rfl
  | .app ps => by rw [Ty.map_app]; simp only [close, closeList_rename]

theorem closeList_rename (ren : String → String) : ∀ ps : List (Ty String),
    closeList (ps.map (Ty.map ren)) = closeList ps
  | [] => rfl
  | p :: ps => by simp only [List.map_cons, closeList, close_rename, closeList_rename]
end

/-- Ground publication is independent of the row's fresh variable names. -/
theorem close_apply_rename (ren : String ≃ String) (env : Env) (range : Ty String) :
    close (apply (renameEnv ren env) (range.map ren)) = close (apply env range) := by
  rw [apply_rename, close_rename]

def isSpace {V : Type} : Ty V → Bool
  | .app [.sym name, _] => name == "Space"
  | _ => false

theorem isSpace_map {V W : Type} (ren : V → W) : ∀ p : Ty V, isSpace (p.map ren) = isSpace p
  | .var _ => rfl
  | .sym _ => rfl
  | .app [] => rfl
  | .app [head] => by cases head <;> rfl
  | .app [head, _] => by cases head <;> simp [Ty.map_app, isSpace]
  | .app (_ :: _ :: _ :: _) => by simp [Ty.map_app, isSpace]

theorem map_beq_sym (ren : String → String) (p : Ty String) (s : String) :
    (p.map ren == .sym s) = (p == .sym s) := by cases p <;> rfl

def spaceBridge (actual : Ground) (formal : Ty String) : Bool :=
  (actual == .sym "SpaceType" && isSpace formal) ||
    (formal == .sym "SpaceType" && isSpace actual)

theorem spaceBridge_map (ren : String → String) (actual : Ground) (formal : Ty String) :
    spaceBridge actual (formal.map ren) = spaceBridge actual formal := by
  simp only [spaceBridge, isSpace_map, map_beq_sym]

/-- Top-level cases of the type matcher; nested matching has only the
Undefined wildcard rule, as the structural worklist does. -/
def matchType (env : Env) (actual : Ground) (formal : Ty String) : Option Env :=
  if formal == .sym "Atom" || spaceBridge actual formal then some env
  else matchPattern env actual formal

theorem matchType_extends {env next : Env} {actual : Ground} {formal : Ty String}
    (h : matchType env actual formal = some next) : Extends env next := by
  unfold matchType at h
  split at h
  · cases h; exact Extends.refl env
  · exact matchPattern_extends formal actual env next h

theorem matchType_rename (ren : String ≃ String) (env : Env) (actual : Ground) (p : Ty String) :
    matchType (renameEnv ren env) actual (p.map ren) =
      (matchType env actual p).map (renameEnv ren) := by
  simp only [matchType, map_beq_sym, spaceBridge_map]
  split
  · rfl
  · exact matchPattern_rename ren env actual p

/-- Instantiate the shared ordered driver. Non-ground actual typings decline
this service; they are not silently coerced into the ground-stamp profile. -/
def matcher : StampInference.Matcher Env where
  initial := empty
  apply := apply
  unify := fun env actual formal => (close actual).bind fun ground => matchType env ground formal
  normalize := id

theorem matcher_unify_extends {env next : Env} {actual formal : Ty String}
    (h : matcher.unify env actual formal = some next) : Extends env next := by
  cases closed : close actual with
  | none => simp [matcher, closed] at h
  | some ground =>
      exact matchType_extends (by simpa [matcher, closed] using h)

theorem matcher_unify_rename (ren : String ≃ String) (env : Env) (actual formal : Ty String) :
    matcher.unify (renameEnv ren env) actual (formal.map ren) =
      (matcher.unify env actual formal).map (renameEnv ren) := by
  cases closed : close actual with
  | none => simp [matcher, closed]
  | some ground => simpa [matcher, closed] using matchType_rename ren env ground formal

/-- The ordered driver retains all assignments made by earlier arguments,
including when a later argument is checked only by its metatype. -/
theorem checks_preserve {env next : Env} {params : List (Ty String)} {args : List StampInference.Stamp}
    (run : StampInference.Checks matcher params args env next) : Extends env next := by
  induction run with
  | done env => exact Extends.refl env
  | kindPass _ _ ih => exact ih
  | choice _ _ _ _ _ _ selected _ ih => exact (matcher_unify_extends selected).trans ih

theorem metaCheck_map (ren : String → String) (p : Ty String) (kind : String) :
    StampInference.metaCheck (p.map ren) kind = StampInference.metaCheck p kind := by
  cases p <;> rfl

theorem firstResult_map {A B C : Type} (f : A → Option B) (g : B → C) (xs : List A) :
    StampInference.firstResult (fun x => (f x).map g) xs =
      (StampInference.firstResult f xs).map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [StampInference.firstResult, h, ih]

theorem firstChoice_rename (ren : String ≃ String) (env : Env) (formal : Ty String)
    (actuals : List (Ty String)) :
    StampInference.firstResult (fun actual => matcher.unify (renameEnv ren env) actual (formal.map ren))
        actuals =
      (StampInference.firstResult (fun actual => matcher.unify env actual formal) actuals).map
        (renameEnv ren) := by
  have functions : (fun actual => matcher.unify (renameEnv ren env) actual (formal.map ren)) =
      (fun actual => (matcher.unify env actual formal).map (renameEnv ren)) := by
    funext actual
    exact matcher_unify_rename ren env actual formal
  rw [functions, firstResult_map]

/-- Whole-row first-match selection transports the same private environment
through every argument. Renaming never reorders or retries candidates. -/
theorem checkArgs_rename (ren : String ≃ String) (params : List (Ty String)) :
    ∀ (args : List StampInference.Stamp) (env : Env),
      StampInference.checkArgs matcher (params.map (Ty.map ren)) args (renameEnv ren env) =
        (StampInference.checkArgs matcher params args env).map (renameEnv ren) := by
  induction params with
  | nil => intro args env; cases args <;> rfl
  | cons p params ih =>
      intro args env
      cases args with
      | nil => rfl
      | cons a args =>
          have cast : matcher.apply (renameEnv ren env) (p.map ren) =
              (matcher.apply env p).map ren := apply_rename ren env p
          simp only [List.map_cons, StampInference.checkArgs, cast, metaCheck_map]
          cases mode : StampInference.metaCheck (matcher.apply env p) a.kind with
          | some accepted =>
              cases accepted with
              | false => rfl
              | true => exact ih args env
          | none =>
              rw [firstChoice_rename]
              cases chosen : StampInference.firstResult
                  (fun actual => matcher.unify env actual (matcher.apply env p)) a.types with
              | none => rfl
              | some next => exact ih args next

/-- Each row starts with a fresh private map, and the returned type is the
range instantiated by the one committed argument traversal. -/
theorem rowResult_sound (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) {answer : Ty String}
    (h : StampInference.rowResult matcher args (arrow params range) = some answer) :
    ∃ env : Env, StampInference.Checks matcher params args empty env ∧ answer = apply env range := by
  rw [StampInference.rowResult, arrowSplit_arrow] at h
  change (StampInference.checkArgs matcher params args empty).map (fun env => apply env range) =
    some answer at h
  cases checked : StampInference.checkArgs matcher params args empty with
  | none => simp [checked] at h
  | some env =>
      have same : apply env range = answer := by simpa [checked] using h
      exact ⟨env, (StampInference.checkArgs_iff_checks matcher params args empty env).mp checked, same.symm⟩

theorem rowResult_rename (ren : String ≃ String) (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) :
    StampInference.rowResult matcher args (arrow (params.map (Ty.map ren)) (range.map ren)) =
      (StampInference.rowResult matcher args (arrow params range)).map (Ty.map ren) := by
  simp only [StampInference.rowResult, arrowSplit_arrow]
  change (StampInference.checkArgs matcher (params.map (Ty.map ren)) args empty).map
      (fun env => apply env (range.map ren)) =
    ((StampInference.checkArgs matcher params args empty).map (fun env => apply env range)).map (Ty.map ren)
  have renamed := checkArgs_rename ren params args empty
  rw [renameEnv_empty] at renamed
  rw [renamed]
  cases checked : StampInference.checkArgs matcher params args empty with
  | none => rfl
  | some env =>
      simp only [Option.map_some]
      rw [apply_rename]

/-- Publication is distinct from inference: an inferred open type has no
ground cache payload and must follow the uncached route. -/
def publish (answer : Ty String) : Option Ground := close answer

theorem published_exact {answer : Ty String} {ground : Ground} (h : publish answer = some ground) :
    ground.lift = answer := close_sound answer ground h

/-- The empty answer list is a valid ground stamp. An open answer makes the
whole publication decline, without discarding the inference's other answers. -/
def publishList (answers : List (Ty String)) : Option (List Ground) := closeList answers

theorem publishedList_exact {answers : List (Ty String)} {ground : List Ground}
    (h : publishList answers = some ground) : ground.map Ty.lift = answers :=
  closeList_sound answers ground h

theorem publishedList_count {answers : List (Ty String)} {ground : List Ground}
    (h : publishList answers = some ground) : ground.length = answers.length := by
  have lengths := congrArg List.length (publishedList_exact h)
  simpa using lengths

def rowPublication (params : List (Ty String)) (range : Ty String) (args : List StampInference.Stamp) :
    Option Ground := (StampInference.rowResult matcher args (arrow params range)).bind publish

theorem rowPublication_sound (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) {ground : Ground}
    (h : rowPublication params range args = some ground) :
    ∃ env : Env, StampInference.Checks matcher params args empty env ∧ ground.lift = apply env range := by
  unfold rowPublication at h
  cases inferred : StampInference.rowResult matcher args (arrow params range) with
  | none => simp [inferred] at h
  | some answer =>
      have closed : publish answer = some ground := by simpa [inferred] using h
      obtain ⟨env, checked, same⟩ := rowResult_sound params range args inferred
      exact ⟨env, checked, (published_exact closed).trans same⟩

/-- Published ranges have no row-private names, regardless of freshening. -/
theorem rowPublication_rename (ren : String ≃ String) (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) :
    rowPublication (params.map (Ty.map ren)) (range.map ren) args = rowPublication params range args := by
  unfold rowPublication
  rw [rowResult_rename]
  cases inferred : StampInference.rowResult matcher args (arrow params range) with
  | none => rfl
  | some answer => exact close_rename ren answer

/-- Shape-key eligibility concerns inferred child typings, not merely the
absence of variables in the child values. -/
def groundInputs (args : List StampInference.Stamp) : Bool :=
  args.all fun arg => (publishList arg.types).isSome

theorem groundInputs_types {args : List StampInference.Stamp} (h : groundInputs args = true)
    {arg : StampInference.Stamp} (member : arg ∈ args) :
    ∃ types : List Ground, types.map Ty.lift = arg.types := by
  have closed : (publishList arg.types).isSome = true := List.all_eq_true.mp h arg member
  cases published : publishList arg.types with
  | none => simp [published] at closed
  | some types => exact ⟨types, publishedList_exact published⟩

/-- A fast transition offer. `none` requests uncached inference; it is not
the empty typing list and must not be interpreted as a type failure. -/
def cachedRow (params : List (Ty String)) (range : Ty String) (args : List StampInference.Stamp) :
    Option Ground := if groundInputs args then rowPublication params range args else none

theorem cachedRow_sound (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) {ground : Ground} (h : cachedRow params range args = some ground) :
    groundInputs args = true ∧ ∃ env : Env,
      StampInference.Checks matcher params args empty env ∧ ground.lift = apply env range := by
  unfold cachedRow at h
  split at h
  · exact ⟨‹_›, rowPublication_sound params range args h⟩
  · cases h

theorem cachedRow_rename (ren : String ≃ String) (params : List (Ty String)) (range : Ty String)
    (args : List StampInference.Stamp) :
    cachedRow (params.map (Ty.map ren)) (range.map ren) args = cachedRow params range args := by
  simp only [cachedRow, rowPublication_rename]

/-- Publish the complete ordered node result, including a legitimate empty
typing list. An open member prevents publication of the entire list. -/
def cachedNode (rows : List (Ty String)) (args : List StampInference.Stamp) : Option (List Ground) :=
  if groundInputs args then publishList (StampInference.inferRows matcher rows args).types else none

theorem cachedNode_exact (rows : List (Ty String)) (args : List StampInference.Stamp)
    {ground : List Ground} (h : cachedNode rows args = some ground) :
    groundInputs args = true ∧ ground.map Ty.lift = (StampInference.inferRows matcher rows args).types := by
  unfold cachedNode at h
  split at h
  · exact ⟨‹_›, publishedList_exact h⟩
  · cases h

namespace Controls

def number : Ground := .sym "Number"
def string : Ground := .sym "String"
def list (t : Ground) : Ground := .app [.sym "List", t]
def pair (a b : Ground) : Ground := .app [.sym "Pair", a, b]
def input (types : List Ground) : StampInference.Stamp := ⟨"Symbol", types.map Ty.lift⟩

def nestedParams : List (Ty String) :=
  [.app [.sym "Pair", .var "a", .var "b"], .app [.sym "List", .var "a"]]
def nestedRange : Ty String := .app [.sym "Pair", .var "b", .var "a"]

/-- Two independently bound row variables, nested matching and a retained
cross-argument constraint determine the instantiated result. -/
theorem arbitrary_nested_variables :
    cachedRow nestedParams nestedRange [input [pair number string], input [list number]] =
      some (pair string number) := by cbv

theorem repeated_variable_conflict :
    cachedRow [.app [.sym "Pair", .var "a", .var "a"]] (.var "a")
      [input [pair number string]] = none := by cbv

theorem retained_cross_argument_conflict :
    cachedRow nestedParams nestedRange [input [pair number string], input [list string]] = none := by cbv

/-- The first argument commits Number; later failure does not retry String. -/
theorem greedy_choice_has_no_backtrack :
    cachedRow [.var "a", .var "a"] (.var "a")
        [input [number, string], input [string]] = none ∧
      cachedRow [.var "a", .var "a"] (.var "a")
        [input [string, number], input [string]] = some string := by cbv

/-- Repeated candidate occurrences do not turn first-match argument checking
into enumeration of all candidate bindings. -/
theorem duplicate_candidate_is_one_choice :
    cachedRow [.var "a"] (.var "a") [input [number, number]] = some number := by cbv

theorem nested_wildcard_then_binding :
    cachedRow [.app [.sym "List", .var "a"], .var "a"] (.var "a")
      [input [list undefinedTy], input [number]] = some number := by cbv

/-- The wildcard did not bind `a`. Inference keeps its open result; only
ground-cache publication declines. -/
theorem open_result_is_uncached_not_rejected :
    StampInference.rowResult matcher [input [list undefinedTy]]
        (arrow [.app [.sym "List", .var "a"]] (.var "a")) = some (.var "a") ∧
      cachedRow [.app [.sym "List", .var "a"]] (.var "a")
        [input [list undefinedTy]] = none := by cbv

theorem open_child_typing_declines :
    groundInputs [⟨"Symbol", [.app [.sym "List", .var "x"]]⟩] = false ∧
      cachedRow [.var "a"] (.var "a")
        [⟨"Symbol", [.app [.sym "List", .var "x"]]⟩] = none := by cbv

theorem atom_top_is_not_nested_top :
    matchType empty number (.sym "Atom") = some empty ∧
      matchType empty (list number) (.app [.sym "List", .sym "Atom"]) = none := by cbv

theorem space_bridge_top_level :
    matchType empty (.sym "SpaceType") (.app [.sym "Space", .var "discipline"]) = some empty ∧
      matchType empty (.app [.sym "Space", .sym "Bag"]) (.sym "SpaceType") = some empty ∧
      matchType empty (.app [.sym "Box", .sym "SpaceType"])
        (.app [.sym "Box", .app [.sym "Space", .sym "Bag"]]) = none := by cbv

def freshNames : String ≃ String := Equiv.swap "a" "fresh:a"

theorem renamed_row_same_ground_answer :
    cachedRow (nestedParams.map (Ty.map freshNames)) (nestedRange.map freshNames)
      [input [pair number string], input [list number]] = some (pair string number) := by
  rw [cachedRow_rename]
  exact arbitrary_nested_variables

/-- Each declaration must start with its own private binding map. -/
theorem row_scope_isolation :
    cachedRow [.var "a"] (.var "a") [input [number]] = some number ∧
      cachedRow [.var "a"] (.var "a") [input [string]] = some string ∧
      matchType (Function.update empty "a" (some number)) string (.var "a") = none := by cbv

theorem empty_stamp_can_be_published : publishList [] = some [] := rfl

theorem publication_preserves_order_and_repeats :
    publishList [string.lift, number.lift, string.lift] = some [string, number, string] := by cbv

/-- Completed absence is cacheable; it is distinct from an uncached offer. -/
theorem ill_typed_node_has_empty_stamp :
    cachedNode [arrow [.sym "Number"] (.sym "Number")] [input [string]] = some [] := by cbv

theorem node_preserves_duplicate_rows :
    cachedNode [arrow [.var "a"] (.var "a"), arrow [.sym "Atom"] (.sym "Number")]
      [input [number]] = some [number, number] := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundStampMatcher
