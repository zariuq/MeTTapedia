import Mettapedia.Languages.ProcessCalculi.CCS.Recursive
import Mettapedia.Languages.ProcessCalculi.CCS.Reflection

/-!
# The rule firing of CCS with recursion, by occurrence

An independent specification of the rules of `ccsRecCalc` in an environment of definitions (`RecRawStep`), by
occurrence index:

- a reaction selects two components of a parallel composition, an action among the guards the first offers and the
  co-action on the same name among the guards the second offers, and releases both continuations into the
  composition;
- a silent step selects a silent guard among those a component offers and leaves its continuation;
- a step happens inside a parallel composition and under a restriction.

A sum offers its summands and a call the summands of its body (`offers`), so a reaction of two sums is CCS's, and a
call reacts through its body: it is unfolded when one of its body's guards is taken. The authored rules fire exactly
as the specification says (`step_iff_raw`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (binary_match_iff)

/-- **The firing of CCS with recursion, by occurrence.** -/
inductive RecRawStep (definitions : List Definition) : Pattern → Pattern → Prop where
  /-- `(a.P + M) | (~a.Q + N) | R ⟶ P | Q | R`, each side offered by a sum or by a call's body. -/
  | react {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      {guards guards' : List Pattern} (k : ℕ) (hk : k < guards.length) (l : ℕ) (hl : l < guards'.length)
      (name continuation continuation' : Pattern)
      (first : offers definitions elements[i] = some guards)
      (second : offers definitions (elements.eraseIdx i)[j] = some guards')
      (acting : guards[k] = .apply "CAct" [name, continuation])
      (coacting : guards'[l] = .apply "CCoAct" [name, continuation']) :
      RecRawStep definitions (.collection .hashBag elements tail)
        (.collection .hashBag (continuation :: continuation' :: (elements.eraseIdx i).eraseIdx j) none)
  /-- `τ.P + M ⟶ P`, offered by a sum or by a call's body. -/
  | tau {source : Pattern} {guards : List Pattern} (k : ℕ) (hk : k < guards.length) (continuation : Pattern)
      (offered : offers definitions source = some guards) (silent : guards[k] = .apply "CTau" [continuation]) :
      RecRawStep definitions source continuation
  /-- A step inside a parallel composition. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {target : Pattern}
      (inner : RecRawStep definitions elements[i] target) :
      RecRawStep definitions (.collection .hashBag elements tail)
        (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- A step under a restriction. -/
  | res (binder : Option String) {source target : Pattern} (inner : RecRawStep definitions source target) :
      RecRawStep definitions (.apply "CNu" [.lambda binder source]) (.apply "CNu" [.lambda none target])

/-! ## Offers -/

/-- The sum of a list of guards. -/
def sumOf (guards : List Pattern) : Pattern := .apply "CSum" [.collection .hashBag guards none]

theorem offers_sum (definitions : List Definition) (guards : List Pattern) (tail : Option String) :
    offers definitions (.apply "CSum" [.collection .hashBag guards tail]) = some guards := rfl

theorem offers_call (definitions : List Definition) (name args : Pattern) :
    offers definitions (.apply "CCall" [name, args]) = body definitions name args := rfl

/-- A component that offers guards is a sum or a call. -/
theorem offers_cases {definitions : List Definition} {component : Pattern} {guards : List Pattern}
    (offered : offers definitions component = some guards) :
    (∃ tail, component = .apply "CSum" [.collection .hashBag guards tail]) ∨
      ∃ name args, component = .apply "CCall" [name, args] ∧ body definitions name args = some guards := by
  unfold offers at offered
  split at offered
  · cases offered
    exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, rfl, offered⟩
  · cases offered

/-! ## Matching the call rules -/

theorem call_match_iff (nameVar argsVar : String) (distinct : nameVar ≠ argsVar) (target : Pattern)
    (bindings : Bindings) :
    MatchRel (callPattern nameVar argsVar) target bindings ↔
      ∃ name args, target = .apply "CCall" [name, args] ∧ bindings = [(argsVar, args), (nameVar, name)] :=
  binary_match_iff "CCall" nameVar argsVar distinct target bindings

theorem offering_binary (guard first second others : String) :
    offering guard [first, second] others =
      .apply "CSum" [.collection .hashBag [.apply guard [.fvar first, .fvar second]] (some others)] := rfl

theorem offering_tau : offering "CTau" ["p"] "m" = ccsTauRewrite.left := rfl

/-- The bindings of a call reacting by its body's action. -/
def callActBindings (channel continuation' name args : Pattern) (others' rest : List Pattern) : Bindings :=
  [("a", channel), ("q", continuation'), ("n", .collection .hashBag others' none),
    ("rest", .collection .hashBag rest none), ("A", args), ("K", name)]

theorem callAct_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel callActRewrite.left source bindings ↔
      ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
        (hj : j < (elements.eraseIdx i).length) (name args : Pattern) (guards' : List Pattern)
        (sumTail' : Option String) (l : ℕ) (hl : l < guards'.length) (channel continuation' : Pattern),
        source = .collection .hashBag elements tail ∧ elements[i] = .apply "CCall" [name, args] ∧
          (elements.eraseIdx i)[j] = .apply "CSum" [.collection .hashBag guards' sumTail'] ∧
          guards'[l] = .apply "CCoAct" [channel, continuation'] ∧
          bindings = callActBindings channel continuation' name args (guards'.eraseIdx l)
            ((elements.eraseIdx i).eraseIdx j) := by
  constructor
  · intro matched
    simp only [callActRewrite] at matched
    cases matched with
    | collection _ bag =>
      cases bag with
      | cons i hi first remaining mergedFirst =>
        obtain ⟨name, args, atFirst, rfl⟩ := (call_match_iff "K" "A" (by decide) _ _).mp first
        cases remaining with
        | cons j hj second last mergedSecond =>
          rw [offering_binary] at second
          obtain ⟨guards', sumTail', l, hl, channel, continuation', atSecond, atCoaction, rfl⟩ :=
            (sum_match_iff "CCoAct" "a" "q" "n" (by decide) (by decide) _ _).mp second
          cases last
          simp [mergeBindings, List.find?] at mergedSecond
          subst mergedSecond
          simp [mergeBindings, List.find?] at mergedFirst
          subst mergedFirst
          exact ⟨_, _, i, hi, j, hj, name, args, guards', sumTail', l, hl, channel, continuation', rfl, atFirst,
            atSecond, atCoaction, rfl⟩
  · rintro ⟨elements, tail, i, hi, j, hj, name, args, guards', sumTail', l, hl, channel, continuation', rfl, atFirst,
      atSecond, atCoaction, rfl⟩
    have firstMatch := (call_match_iff "K" "A" (by decide) _ _).mpr ⟨name, args, rfl, rfl⟩
    have secondMatch := (sum_match_iff "CCoAct" "a" "q" "n" (by decide) (by decide) _ _).mpr
      ⟨guards', sumTail', l, hl, channel, continuation', rfl, atCoaction, rfl⟩
    rw [← atFirst] at firstMatch
    rw [← atSecond, ← offering_binary] at secondMatch
    exact .collection (by decide) (.cons i hi firstMatch
      (MatchBagRel.cons (bs := [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
          ("n", .collection .hashBag (guards'.eraseIdx l) none), ("q", continuation'), ("a", channel)]) j hj
        secondMatch .nilRest (by simp [mergeBindings, List.find?]))
      (by simp [mergeBindings, List.find?, callActBindings]))

/-- The bindings of a sum's action reacting with a call's body's co-action. -/
def callCoActBindings (channel continuation name args : Pattern) (others rest : List Pattern) : Bindings :=
  [("K", name), ("A", args), ("rest", .collection .hashBag rest none), ("m", .collection .hashBag others none),
    ("p", continuation), ("a", channel)]

theorem callCoAct_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel callCoActRewrite.left source bindings ↔
      ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
        (hj : j < (elements.eraseIdx i).length) (guards : List Pattern) (sumTail : Option String) (k : ℕ)
        (hk : k < guards.length) (channel continuation name args : Pattern),
        source = .collection .hashBag elements tail ∧
          elements[i] = .apply "CSum" [.collection .hashBag guards sumTail] ∧
          guards[k] = .apply "CAct" [channel, continuation] ∧
          (elements.eraseIdx i)[j] = .apply "CCall" [name, args] ∧
          bindings = callCoActBindings channel continuation name args (guards.eraseIdx k)
            ((elements.eraseIdx i).eraseIdx j) := by
  constructor
  · intro matched
    simp only [callCoActRewrite] at matched
    cases matched with
    | collection _ bag =>
      cases bag with
      | cons i hi first remaining mergedFirst =>
        rw [offering_binary] at first
        obtain ⟨guards, sumTail, k, hk, channel, continuation, atFirst, atAction, rfl⟩ :=
          (sum_match_iff "CAct" "a" "p" "m" (by decide) (by decide) _ _).mp first
        cases remaining with
        | cons j hj second last mergedSecond =>
          obtain ⟨name, args, atSecond, rfl⟩ := (call_match_iff "K" "A" (by decide) _ _).mp second
          cases last
          simp [mergeBindings, List.find?] at mergedSecond
          subst mergedSecond
          simp [mergeBindings, List.find?] at mergedFirst
          subst mergedFirst
          exact ⟨_, _, i, hi, j, hj, guards, sumTail, k, hk, channel, continuation, name, args, rfl, atFirst,
            atAction, atSecond, rfl⟩
  · rintro ⟨elements, tail, i, hi, j, hj, guards, sumTail, k, hk, channel, continuation, name, args, rfl, atFirst,
      atAction, atSecond, rfl⟩
    have firstMatch := (sum_match_iff "CAct" "a" "p" "m" (by decide) (by decide) _ _).mpr
      ⟨guards, sumTail, k, hk, channel, continuation, rfl, atAction, rfl⟩
    have secondMatch := (call_match_iff "K" "A" (by decide) _ _).mpr ⟨name, args, rfl, rfl⟩
    rw [← atFirst, ← offering_binary] at firstMatch
    rw [← atSecond] at secondMatch
    exact .collection (by decide) (.cons i hi firstMatch
      (MatchBagRel.cons (bs := [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
          ("A", args), ("K", name)]) j hj secondMatch .nilRest (by simp [mergeBindings, List.find?]))
      (by simp [mergeBindings, List.find?, callCoActBindings]))

/-- The bindings of two calls reacting through their bodies. -/
def callCallBindings (name args name' args' : Pattern) (rest : List Pattern) : Bindings :=
  [("L", name'), ("B", args'), ("rest", .collection .hashBag rest none), ("A", args), ("K", name)]

theorem callCall_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel callCallRewrite.left source bindings ↔
      ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
        (hj : j < (elements.eraseIdx i).length) (name args name' args' : Pattern),
        source = .collection .hashBag elements tail ∧ elements[i] = .apply "CCall" [name, args] ∧
          (elements.eraseIdx i)[j] = .apply "CCall" [name', args'] ∧
          bindings = callCallBindings name args name' args' ((elements.eraseIdx i).eraseIdx j) := by
  constructor
  · intro matched
    simp only [callCallRewrite] at matched
    cases matched with
    | collection _ bag =>
      cases bag with
      | cons i hi first remaining mergedFirst =>
        obtain ⟨name, args, atFirst, rfl⟩ := (call_match_iff "K" "A" (by decide) _ _).mp first
        cases remaining with
        | cons j hj second last mergedSecond =>
          obtain ⟨name', args', atSecond, rfl⟩ := (call_match_iff "L" "B" (by decide) _ _).mp second
          cases last
          simp [mergeBindings, List.find?] at mergedSecond
          subst mergedSecond
          simp [mergeBindings, List.find?] at mergedFirst
          subst mergedFirst
          exact ⟨_, _, i, hi, j, hj, name, args, name', args', rfl, atFirst, atSecond, rfl⟩
  · rintro ⟨elements, tail, i, hi, j, hj, name, args, name', args', rfl, atFirst, atSecond, rfl⟩
    have firstMatch := (call_match_iff "K" "A" (by decide) _ _).mpr ⟨name, args, rfl, rfl⟩
    have secondMatch := (call_match_iff "L" "B" (by decide) _ _).mpr ⟨name', args', rfl, rfl⟩
    rw [← atFirst] at firstMatch
    rw [← atSecond] at secondMatch
    exact .collection (by decide) (.cons i hi firstMatch
      (MatchBagRel.cons (bs := [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
          ("B", args'), ("L", name')]) j hj secondMatch .nilRest (by simp [mergeBindings, List.find?]))
      (by simp [mergeBindings, List.find?, callCallBindings]))

/-! ## The body as a relation -/

theorem builtin_body (language : LanguageDef) (request : List Pattern) :
    builtinRelationTuples language "Body" request = [] := rfl

theorem mergeBindings_nil (bindings : Bindings) : mergeBindings bindings [] = some bindings := rfl

/-- The relation's arguments matched against an answer of the environment: the constant and the arguments are the
bound ones, and the offered pattern is matched against the answer's sum. -/
theorem matchRelationArgs_body {seed : Bindings} {nameVar argsVar : String} {offer name args offered : Pattern}
    (notVar : ∀ x, offer ≠ .fvar x) (nameBound : seed.lookup nameVar = some name)
    (argsBound : seed.lookup argsVar = some args) :
    matchRelationArgs seed [.fvar nameVar, .fvar argsVar, offer] [name, args, offered] =
      (((matchPattern offer offered).flatMap fun extension =>
        match mergeBindings seed extension with
        | none => []
        | some _ => [extension]).filterMap (mergeBindings [])).filterMap (mergeBindings []) := by
  have offerArgument : ∀ bindings value, matchRelationArgument bindings offer value = matchPattern offer value := by
    intro bindings value
    cases offer with
    | fvar x => exact absurd rfl (notVar x)
    | _ => rfl
  have last : ∀ extension : Bindings, (match mergeBindings seed extension with
      | none => ([] : List Bindings)
      | some extended => List.filterMap (fun tailBindings => mergeBindings extension tailBindings)
          (matchRelationArgs extended [] [])) =
      (match mergeBindings seed extension with
      | none => []
      | some _ => [extension]) := by
    intro extension
    cases mergeBindings seed extension with
    | none => rfl
    | some extended =>
        simp only
        rw [matchRelationArgs]
        rfl
  rw [matchRelationArgs, matchRelationArgument, nameBound]
  simp only [↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil, mergeBindings_nil]
  rw [matchRelationArgs, matchRelationArgument, argsBound]
  simp only [↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil, mergeBindings_nil]
  rw [matchRelationArgs, offerArgument]
  exact congrArg (fun list => List.filterMap (mergeBindings []) (List.filterMap (mergeBindings []) list))
    (congrArg (fun function => List.flatMap function (matchPattern offer offered)) (funext last))

/-- **A query of a call's body**: the environment answers with the sum of its guards, and the offered pattern is
matched against that sum, its new bindings merged in. -/
theorem mem_bodyQuery {definitions : List Definition} {seed result : Bindings} {nameVar argsVar : String}
    {offer name args : Pattern} (notVar : ∀ x, offer ≠ .fvar x)
    (nameBound : seed.lookup nameVar = some name) (argsBound : seed.lookup argsVar = some args)
    (nameApplied : applyBindings seed (.fvar nameVar) = name) (argsApplied : applyBindings seed (.fvar argsVar) = args) :
    result ∈ relationQueryStep (definitionsEnv definitions) ccsRecCalc seed "Body" [.fvar nameVar, .fvar argsVar, offer] ↔
      ∃ guards extension once twice, body definitions name args = some guards ∧
        extension ∈ matchPattern offer (sumOf guards) ∧ (mergeBindings seed extension).isSome ∧
        mergeBindings [] extension = some once ∧ mergeBindings [] once = some twice ∧
        mergeBindings seed twice = some result := by
  have tuples : (definitionsEnv definitions).tuples "Body"
      (List.map (applyBindings seed) [.fvar nameVar, .fvar argsVar, offer]) =
        match body definitions name args with
        | some guards => [[name, args, sumOf guards]]
        | none => [] := by
    simp only [List.map_cons, List.map_nil, nameApplied, argsApplied]
    rfl
  unfold relationQueryStep
  simp only [builtin_body, List.nil_append, tuples]
  cases found : body definitions name args with
  | none => simp
  | some guards =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filterMap,
        matchRelationArgs_body notVar nameBound argsBound, List.mem_flatMap]
      constructor
      · rintro ⟨twice, ⟨once, ⟨extension, ⟨extension', member, inner⟩, onceMerged⟩, twiceMerged⟩, merged⟩
        cases seedMerge : mergeBindings seed extension' with
        | none => simp [seedMerge] at inner
        | some extended =>
            simp only [seedMerge, List.mem_singleton] at inner
            subst inner
            exact ⟨guards, extension, once, twice, rfl, member, by simp [seedMerge], onceMerged, twiceMerged, merged⟩
      · rintro ⟨guards', extension, once, twice, same, member, seedMerge, onceMerged, twiceMerged, merged⟩
        cases same
        obtain ⟨extended, extendedIs⟩ := Option.isSome_iff_exists.mp seedMerge
        exact ⟨twice, ⟨once, ⟨extension, ⟨extension, member, by simp [extendedIs]⟩, onceMerged⟩, twiceMerged⟩,
          merged⟩

/-! ## What the call rules' queries give -/

theorem offering_notVar (guard : String) (arguments : List String) (others : String) :
    ∀ x, offering guard arguments others ≠ .fvar x := by
  intro x equal
  cases equal

/-- **The silent query**: the body offers a silent guard, and its continuation is bound. -/
theorem callTau_premise {definitions : List Definition} {name args : Pattern} {result : Bindings} :
    result ∈ engineBasePremises (definitionsEnv definitions) ccsRecCalc [("A", args), ("K", name)]
        (.relationQuery "Body" [.fvar "K", .fvar "A", offering "CTau" ["p"] "m"]) ↔
      ∃ (guards : List Pattern) (k : ℕ) (hk : k < guards.length) (continuation : Pattern),
        body definitions name args = some guards ∧ guards[k] = .apply "CTau" [continuation] ∧
        result = [("p", continuation), ("m", .collection .hashBag (guards.eraseIdx k) none), ("A", args),
          ("K", name)] := by
  change result ∈ relationQueryStep _ _ _ _ _ ↔ _
  rw [mem_bodyQuery (name := name) (args := args) (offering_notVar _ _ _) rfl rfl
    (by simp [applyBindings, List.find?]) (by simp [applyBindings, List.find?])]
  constructor
  · rintro ⟨guards, extension, once, twice, found, member, -, onceMerged, twiceMerged, merged⟩
    rw [offering_tau] at member
    obtain ⟨guards', sumTail, k, hk, continuation, sumIs, silent, rfl⟩ :=
      (tau_match_iff _ _).mp (matchPattern_iff_matchRel.mp member)
    cases sumIs
    simp [tauBindings, mergeBindings, List.find?] at onceMerged
    subst onceMerged
    simp [mergeBindings, List.find?] at twiceMerged
    subst twiceMerged
    simp [mergeBindings, List.find?] at merged
    exact ⟨guards, k, hk, continuation, found, silent, merged.symm⟩
  · rintro ⟨guards, k, hk, continuation, found, silent, rfl⟩
    refine ⟨guards, tauBindings continuation (guards.eraseIdx k),
      [("p", continuation), ("m", .collection .hashBag (guards.eraseIdx k) none)],
      tauBindings continuation (guards.eraseIdx k), found, ?_, by simp [tauBindings, mergeBindings, List.find?],
      by simp [tauBindings, mergeBindings, List.find?], by simp [tauBindings, mergeBindings, List.find?],
      by simp [tauBindings, mergeBindings, List.find?]⟩
    rw [offering_tau]
    exact matchPattern_iff_matchRel.mpr ((tau_match_iff _ _).mpr ⟨guards, none, k, hk, continuation, rfl, silent, rfl⟩)

/-- The bindings a binary guard of a sum adds. -/
theorem binary_extension {guard nameVar continuationVar othersVar : String} (distinct : nameVar ≠ continuationVar)
    (fresh : othersVar ≠ continuationVar ∧ othersVar ≠ nameVar) {guards : List Pattern} {extension : Bindings}
    (member : extension ∈ matchPattern (offering guard [nameVar, continuationVar] othersVar) (sumOf guards)) :
    ∃ (k : ℕ) (hk : k < guards.length) (channel continuation : Pattern),
      guards[k] = .apply guard [channel, continuation] ∧
      extension = [(othersVar, .collection .hashBag (guards.eraseIdx k) none), (continuationVar, continuation),
        (nameVar, channel)] := by
  rw [offering_binary] at member
  obtain ⟨guards', sumTail, k, hk, channel, continuation, sumIs, atGuard, rfl⟩ :=
    (sum_match_iff guard nameVar continuationVar othersVar distinct fresh _ _).mp (matchPattern_iff_matchRel.mp member)
  cases sumIs
  exact ⟨k, hk, channel, continuation, atGuard, rfl⟩

theorem binary_member {guard nameVar continuationVar othersVar : String} (distinct : nameVar ≠ continuationVar)
    (fresh : othersVar ≠ continuationVar ∧ othersVar ≠ nameVar) {guards : List Pattern} {k : ℕ} (hk : k < guards.length)
    {channel continuation : Pattern} (atGuard : guards[k] = .apply guard [channel, continuation]) :
    [(othersVar, .collection .hashBag (guards.eraseIdx k) none), (continuationVar, continuation), (nameVar, channel)] ∈
      matchPattern (offering guard [nameVar, continuationVar] othersVar) (sumOf guards) := by
  rw [offering_binary]
  exact matchPattern_iff_matchRel.mpr ((sum_match_iff guard nameVar continuationVar othersVar distinct fresh _ _).mpr
    ⟨guards, none, k, hk, channel, continuation, rfl, atGuard, rfl⟩)

/-- **The action query**: a call's body offers the action on the channel its partner's co-action names. -/
theorem callAct_premise {definitions : List Definition} {channel continuation' name args : Pattern}
    {others' rest : List Pattern} {result : Bindings} :
    result ∈ engineBasePremises (definitionsEnv definitions) ccsRecCalc
        (callActBindings channel continuation' name args others' rest)
        (.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"]) ↔
      ∃ (guards : List Pattern) (k : ℕ) (hk : k < guards.length) (continuation : Pattern),
        body definitions name args = some guards ∧ guards[k] = .apply "CAct" [channel, continuation] ∧
        result = ("p", continuation) :: ("m", .collection .hashBag (guards.eraseIdx k) none) ::
          callActBindings channel continuation' name args others' rest := by
  change result ∈ relationQueryStep _ _ _ _ _ ↔ _
  rw [mem_bodyQuery (name := name) (args := args) (offering_notVar _ _ _) rfl rfl
    (by simp [applyBindings, List.find?, callActBindings]) (by simp [applyBindings, List.find?, callActBindings])]
  constructor
  · rintro ⟨guards, extension, once, twice, found, member, -, onceMerged, twiceMerged, merged⟩
    obtain ⟨k, hk, channel', continuation, acting, rfl⟩ := binary_extension (by decide) (by decide) member
    simp [mergeBindings, List.find?] at onceMerged
    subst onceMerged
    simp [mergeBindings, List.find?] at twiceMerged
    subst twiceMerged
    simp [mergeBindings, List.find?, callActBindings] at merged
    obtain ⟨rfl, rfl⟩ := merged
    exact ⟨guards, k, hk, continuation, found, acting, rfl⟩
  · rintro ⟨guards, k, hk, continuation, found, acting, rfl⟩
    exact ⟨guards, [("m", .collection .hashBag (guards.eraseIdx k) none), ("p", continuation), ("a", channel)],
      [("a", channel), ("p", continuation), ("m", .collection .hashBag (guards.eraseIdx k) none)],
      [("m", .collection .hashBag (guards.eraseIdx k) none), ("p", continuation), ("a", channel)], found,
      binary_member (by decide) (by decide) hk acting,
      by simp [mergeBindings, List.find?, callActBindings], by simp [mergeBindings, List.find?],
      by simp [mergeBindings, List.find?], by simp [mergeBindings, List.find?, callActBindings]⟩

/-- **The co-action query**: a call's body offers the co-action on the channel its partner's action names. -/
theorem callCoAct_premise {definitions : List Definition} {channel continuation name args : Pattern}
    {others rest : List Pattern} {result : Bindings} :
    result ∈ engineBasePremises (definitionsEnv definitions) ccsRecCalc
        (callCoActBindings channel continuation name args others rest)
        (.relationQuery "Body" [.fvar "K", .fvar "A", offering "CCoAct" ["a", "q"] "n"]) ↔
      ∃ (guards : List Pattern) (l : ℕ) (hl : l < guards.length) (continuation' : Pattern),
        body definitions name args = some guards ∧ guards[l] = .apply "CCoAct" [channel, continuation'] ∧
        result = ("q", continuation') :: ("n", .collection .hashBag (guards.eraseIdx l) none) ::
          callCoActBindings channel continuation name args others rest := by
  change result ∈ relationQueryStep _ _ _ _ _ ↔ _
  rw [mem_bodyQuery (name := name) (args := args) (offering_notVar _ _ _) rfl rfl
    (by simp [applyBindings, List.find?, callCoActBindings]) (by simp [applyBindings, List.find?, callCoActBindings])]
  constructor
  · rintro ⟨guards, extension, once, twice, found, member, -, onceMerged, twiceMerged, merged⟩
    obtain ⟨l, hl, channel', continuation', coacting, rfl⟩ := binary_extension (by decide) (by decide) member
    simp [mergeBindings, List.find?] at onceMerged
    subst onceMerged
    simp [mergeBindings, List.find?] at twiceMerged
    subst twiceMerged
    simp [mergeBindings, List.find?, callCoActBindings] at merged
    obtain ⟨rfl, rfl⟩ := merged
    exact ⟨guards, l, hl, continuation', found, coacting, rfl⟩
  · rintro ⟨guards, l, hl, continuation', found, coacting, rfl⟩
    exact ⟨guards, [("n", .collection .hashBag (guards.eraseIdx l) none), ("q", continuation'), ("a", channel)],
      [("a", channel), ("q", continuation'), ("n", .collection .hashBag (guards.eraseIdx l) none)],
      [("n", .collection .hashBag (guards.eraseIdx l) none), ("q", continuation'), ("a", channel)], found,
      binary_member (by decide) (by decide) hl coacting,
      by simp [mergeBindings, List.find?, callCoActBindings], by simp [mergeBindings, List.find?],
      by simp [mergeBindings, List.find?], by simp [mergeBindings, List.find?, callCoActBindings]⟩

/-- The bindings after the first call's query: the channel, its action's continuation and the other guards. -/
def callCallFirstBindings (channel continuation name args name' args' : Pattern) (others rest : List Pattern) :
    Bindings :=
  ("a", channel) :: ("p", continuation) :: ("m", .collection .hashBag others none) ::
    callCallBindings name args name' args' rest

/-- **The first call's query**: its body offers an action, whose channel is bound. -/
theorem callCallFirst_premise {definitions : List Definition} {name args name' args' : Pattern}
    {rest : List Pattern} {result : Bindings} :
    result ∈ engineBasePremises (definitionsEnv definitions) ccsRecCalc (callCallBindings name args name' args' rest)
        (.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"]) ↔
      ∃ (guards : List Pattern) (k : ℕ) (hk : k < guards.length) (channel continuation : Pattern),
        body definitions name args = some guards ∧ guards[k] = .apply "CAct" [channel, continuation] ∧
        result = callCallFirstBindings channel continuation name args name' args' (guards.eraseIdx k) rest := by
  change result ∈ relationQueryStep _ _ _ _ _ ↔ _
  rw [mem_bodyQuery (name := name) (args := args) (offering_notVar _ _ _) rfl rfl
    (by simp [applyBindings, List.find?, callCallBindings]) (by simp [applyBindings, List.find?, callCallBindings])]
  constructor
  · rintro ⟨guards, extension, once, twice, found, member, -, onceMerged, twiceMerged, merged⟩
    obtain ⟨k, hk, channel, continuation, acting, rfl⟩ := binary_extension (by decide) (by decide) member
    simp [mergeBindings, List.find?] at onceMerged
    subst onceMerged
    simp [mergeBindings, List.find?] at twiceMerged
    subst twiceMerged
    simp [mergeBindings, List.find?, callCallBindings] at merged
    exact ⟨guards, k, hk, channel, continuation, found, acting, by
      simp [← merged, callCallFirstBindings, callCallBindings]⟩
  · rintro ⟨guards, k, hk, channel, continuation, found, acting, rfl⟩
    exact ⟨guards, [("m", .collection .hashBag (guards.eraseIdx k) none), ("p", continuation), ("a", channel)],
      [("a", channel), ("p", continuation), ("m", .collection .hashBag (guards.eraseIdx k) none)],
      [("m", .collection .hashBag (guards.eraseIdx k) none), ("p", continuation), ("a", channel)], found,
      binary_member (by decide) (by decide) hk acting,
      by simp [mergeBindings, List.find?, callCallBindings], by simp [mergeBindings, List.find?],
      by simp [mergeBindings, List.find?], by simp [mergeBindings, List.find?, callCallBindings, callCallFirstBindings]⟩

/-- **The second call's query**: its body offers the co-action on the first's channel. -/
theorem callCallSecond_premise {definitions : List Definition} {channel continuation name args name' args' : Pattern}
    {others rest : List Pattern} {result : Bindings} :
    result ∈ engineBasePremises (definitionsEnv definitions) ccsRecCalc
        (callCallFirstBindings channel continuation name args name' args' others rest)
        (.relationQuery "Body" [.fvar "L", .fvar "B", offering "CCoAct" ["a", "q"] "n"]) ↔
      ∃ (guards : List Pattern) (l : ℕ) (hl : l < guards.length) (continuation' : Pattern),
        body definitions name' args' = some guards ∧ guards[l] = .apply "CCoAct" [channel, continuation'] ∧
        result = ("q", continuation') :: ("n", .collection .hashBag (guards.eraseIdx l) none) ::
          callCallFirstBindings channel continuation name args name' args' others rest := by
  change result ∈ relationQueryStep _ _ _ _ _ ↔ _
  rw [mem_bodyQuery (name := name') (args := args') (offering_notVar _ _ _) rfl rfl
    (by simp [applyBindings, List.find?, callCallFirstBindings, callCallBindings])
    (by simp [applyBindings, List.find?, callCallFirstBindings, callCallBindings])]
  constructor
  · rintro ⟨guards, extension, once, twice, found, member, -, onceMerged, twiceMerged, merged⟩
    obtain ⟨l, hl, channel', continuation', coacting, rfl⟩ := binary_extension (by decide) (by decide) member
    simp [mergeBindings, List.find?] at onceMerged
    subst onceMerged
    simp [mergeBindings, List.find?] at twiceMerged
    subst twiceMerged
    simp [mergeBindings, List.find?, callCallFirstBindings, callCallBindings] at merged
    obtain ⟨rfl, rfl⟩ := merged
    exact ⟨guards, l, hl, continuation', found, coacting, by simp [callCallFirstBindings, callCallBindings]⟩
  · rintro ⟨guards, l, hl, continuation', found, coacting, rfl⟩
    exact ⟨guards, [("n", .collection .hashBag (guards.eraseIdx l) none), ("q", continuation'), ("a", channel)],
      [("a", channel), ("q", continuation'), ("n", .collection .hashBag (guards.eraseIdx l) none)],
      [("n", .collection .hashBag (guards.eraseIdx l) none), ("q", continuation'), ("a", channel)], found,
      binary_member (by decide) (by decide) hl coacting,
      by simp [mergeBindings, List.find?, callCallFirstBindings, callCallBindings], by simp [mergeBindings, List.find?],
      by simp [mergeBindings, List.find?],
      by simp [mergeBindings, List.find?, callCallFirstBindings, callCallBindings]⟩

/-! ## What the call rules leave -/

theorem callTau_apply_exact {language : LanguageDef} (continuation name args : Pattern) (others : List Pattern) :
    applyBindingsForRule language callTauRewrite
        [("p", continuation), ("m", .collection .hashBag others none), ("A", args), ("K", name)] = continuation := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [callTauRewrite, applyBindings]

theorem callAct_apply_exact {language : LanguageDef} (continuation channel continuation' name args : Pattern)
    (others others' rest : List Pattern) :
    applyBindingsForRule language callActRewrite
        (("p", continuation) :: ("m", .collection .hashBag others none) ::
          callActBindings channel continuation' name args others' rest) =
      .collection .hashBag (continuation :: continuation' :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [callActRewrite, applyBindings, callActBindings]

theorem callCoAct_apply_exact {language : LanguageDef} (continuation' channel continuation name args : Pattern)
    (others' others rest : List Pattern) :
    applyBindingsForRule language callCoActRewrite
        (("q", continuation') :: ("n", .collection .hashBag others' none) ::
          callCoActBindings channel continuation name args others rest) =
      .collection .hashBag (continuation :: continuation' :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [callCoActRewrite, applyBindings, callCoActBindings]

theorem callCall_apply_exact {language : LanguageDef} (continuation' channel continuation name args name' args' : Pattern)
    (others' others rest : List Pattern) :
    applyBindingsForRule language callCallRewrite
        (("q", continuation') :: ("n", .collection .hashBag others' none) ::
          callCallFirstBindings channel continuation name args name' args' others rest) =
      .collection .hashBag (continuation :: continuation' :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [callCallRewrite, applyBindings, callCallFirstBindings, callCallBindings]

/-! ## Adequacy -/

section Adequacy

variable {definitions : List Definition}

theorem raw_of_stepAt {fuel : ℕ} {source target : Pattern}
    (step : StepAt (engineBasePremises (definitionsEnv definitions)) ccsRecCalc fuel source target) :
    RecRawStep definitions source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [ccsRecCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨elements, tail, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, name, continuation,
          continuation', rfl, atFirst, atSecond, atAction, atCoaction, rfl⟩ := (react_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [react_apply_exact] at result
        cases result
        exact .react i hi j hj k hk l hl name continuation continuation' (by rw [atFirst]; rfl)
          (by rw [atSecond]; rfl) atAction atCoaction
      · obtain ⟨guards, sumTail, k, hk, continuation, rfl, atSilent, rfl⟩ := (tau_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [tau_apply_exact] at result
        subst result
        exact .tau k hk _ rfl atSilent
      · change MatchRel (.collection .hashBag [.fvar "S"] (some "rest")) source initial at matchRel
        obtain ⟨elements, tail, i, hi, rfl, rfl⟩ := par_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate),
                ("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [parCong_apply_exact] at result
            cases result
            exact .par i hi (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · change MatchRel (.apply "CNu" [.lambda none (.fvar "S")]) source initial at matchRel
        obtain ⟨binder, body', rfl, rfl⟩ := restriction_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate), ("S", body')] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [resCong_apply_exact] at result
            cases result
            exact .res binder (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · change MatchRel (callPattern "K" "A") source initial at matchRel
        obtain ⟨name, args, rfl, rfl⟩ := (call_match_iff "K" "A" (by decide) _ _).mp matchRel
        change PremisesAt _ _ _ _ [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CTau" ["p"] "m"]] _
          at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | relationQuery member =>
            obtain ⟨guards, k, hk, continuation, found, silent, rfl⟩ := callTau_premise.mp member
            rw [callTau_apply_exact] at result
            subst result
            exact .tau k hk continuation found silent
      · obtain ⟨elements, tail, i, hi, j, hj, name, args, guards', sumTail', l, hl, channel, continuation', rfl,
          atFirst, atSecond, atCoaction, rfl⟩ := (callAct_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"]] _
          at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | relationQuery member =>
            obtain ⟨guards, k, hk, continuation, found, acting, rfl⟩ := callAct_premise.mp member
            rw [callAct_apply_exact] at result
            cases result
            exact .react i hi j hj k hk l hl channel continuation continuation'
              (by rw [atFirst]; exact (offers_call _ _ _).trans found) (by rw [atSecond]; rfl) acting atCoaction
      · obtain ⟨elements, tail, i, hi, j, hj, guards, sumTail, k, hk, channel, continuation, name, args, rfl, atFirst,
          atAction, atSecond, rfl⟩ := (callCoAct_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _
          [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CCoAct" ["a", "q"] "n"]] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | relationQuery member =>
            obtain ⟨guards', l, hl, continuation', found, coacting, rfl⟩ := callCoAct_premise.mp member
            rw [callCoAct_apply_exact] at result
            cases result
            exact .react i hi j hj k hk l hl channel continuation continuation' (by rw [atFirst]; rfl)
              (by rw [atSecond]; exact (offers_call _ _ _).trans found) atAction coacting
      · obtain ⟨elements, tail, i, hi, j, hj, name, args, name', args', rfl, atFirst, atSecond, rfl⟩ :=
          (callCall_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"],
          .relationQuery "Body" [.fvar "L", .fvar "B", offering "CCoAct" ["a", "q"] "n"]] _ at premises
        cases premises with
        | cons first remaining =>
          cases remaining with
          | cons second last =>
            cases last
            cases first with
            | relationQuery member =>
              obtain ⟨guards, k, hk, channel, continuation, found, acting, rfl⟩ := callCallFirst_premise.mp member
              cases second with
              | relationQuery member' =>
                obtain ⟨guards', l, hl, continuation', found', coacting, rfl⟩ := callCallSecond_premise.mp member'
                rw [callCall_apply_exact] at result
                cases result
                exact .react i hi j hj k hk l hl channel continuation continuation'
                  (by rw [atFirst]; exact (offers_call _ _ _).trans found)
                  (by rw [atSecond]; exact (offers_call _ _ _).trans found') acting coacting

/-- **Every firing of the authored rules is a firing of the specification.** -/
theorem raw_of_step {source target : Pattern}
    (step : Step (engineBasePremises (definitionsEnv definitions)) ccsRecCalc source target) :
    RecRawStep definitions source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact raw_of_stepAt bounded

/-- **Every firing of the specification is a firing of the authored rules.** -/
theorem step_of_raw {source target : Pattern} (step : RecRawStep definitions source target) :
    Step (engineBasePremises (definitionsEnv definitions)) ccsRecCalc source target := by
  induction step with
  | @react elements tail i hi j hj guards guards' k hk l hl name continuation continuation' first second acting
      coacting =>
    rcases offers_cases first with ⟨sumTail, atFirst⟩ | ⟨callName, callArgs, atFirst, foundFirst⟩ <;>
      rcases offers_cases second with ⟨sumTail', atSecond⟩ | ⟨callName', callArgs', atSecond, foundSecond⟩
    · refine ⟨1, .rule (rule := ccsReactRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_ (.nil _)
        (react_apply_exact name continuation continuation' (guards.eraseIdx k) (guards'.eraseIdx l)
          ((elements.eraseIdx i).eraseIdx j))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((react_match_iff _ _).mpr
        ⟨_, _, i, hi, j, hj, _, _, _, _, k, hk, l, hl, name, continuation, continuation', rfl, atFirst, atSecond,
          acting, coacting, rfl⟩)
    · refine ⟨1, .rule (rule := callCoActRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_
        (.cons (.relationQuery (callCoAct_premise.mpr ⟨guards', l, hl, continuation', foundSecond, coacting, rfl⟩))
          (.nil _))
        (callCoAct_apply_exact continuation' name continuation callName' callArgs' (guards'.eraseIdx l)
          (guards.eraseIdx k) ((elements.eraseIdx i).eraseIdx j))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((callCoAct_match_iff _ _).mpr
        ⟨_, _, i, hi, j, hj, guards, sumTail, k, hk, name, continuation, callName', callArgs', rfl, atFirst, acting,
          atSecond, rfl⟩)
    · refine ⟨1, .rule (rule := callActRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_
        (.cons (.relationQuery (callAct_premise.mpr ⟨guards, k, hk, continuation, foundFirst, acting, rfl⟩))
          (.nil _))
        (callAct_apply_exact continuation name continuation' callName callArgs (guards.eraseIdx k)
          (guards'.eraseIdx l) ((elements.eraseIdx i).eraseIdx j))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((callAct_match_iff _ _).mpr
        ⟨_, _, i, hi, j, hj, callName, callArgs, guards', sumTail', l, hl, name, continuation', rfl, atFirst,
          atSecond, coacting, rfl⟩)
    · refine ⟨1, .rule (rule := callCallRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_
        (.cons (.relationQuery (callCallFirst_premise.mpr ⟨guards, k, hk, name, continuation, foundFirst, acting, rfl⟩))
          (.cons (.relationQuery (callCallSecond_premise.mpr ⟨guards', l, hl, continuation', foundSecond, coacting,
            rfl⟩)) (.nil _)))
        (callCall_apply_exact continuation' name continuation callName callArgs callName' callArgs'
          (guards'.eraseIdx l) (guards.eraseIdx k) ((elements.eraseIdx i).eraseIdx j))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((callCall_match_iff _ _).mpr
        ⟨_, _, i, hi, j, hj, callName, callArgs, callName', callArgs', rfl, atFirst, atSecond, rfl⟩)
  | @tau source guards k hk continuation offered silent =>
    rcases offers_cases offered with ⟨sumTail, rfl⟩ | ⟨name, args, rfl, found⟩
    · refine ⟨1, .rule (rule := ccsTauRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_ (.nil _)
        (tau_apply_exact continuation (guards.eraseIdx k))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((tau_match_iff _ _).mpr ⟨_, _, k, hk, continuation, rfl, silent, rfl⟩)
    · refine ⟨1, .rule (rule := callTauRewrite) (by rw [ccsRecCalc_rewrites]; simp) ?_
        (.cons (.relationQuery (callTau_premise.mpr ⟨guards, k, hk, continuation, found, silent, rfl⟩)) (.nil _))
        (callTau_apply_exact continuation name args (guards.eraseIdx k))⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((call_match_iff "K" "A" (by decide) _ _).mpr ⟨name, args, rfl, rfl⟩)
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := ccsParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) ?_ ?_ ?_ (parCong_apply_exact _ _ _)⟩
    · rw [ccsRecCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.collection (by decide) (.cons i hi .fvar .nilRest rfl))
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _
  | @res binder source target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := ccsResCongRewrite)
      (initialBindings := [("S", source)]) (finalBindings := [("T", target), ("S", source)])
      ?_ ?_ ?_ (resCong_apply_exact source target)⟩
    · rw [ccsRecCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

/-- **The authored rules of CCS with recursion fire exactly as the specification says**, in the environment of
the definitions. -/
theorem step_iff_raw (source target : Pattern) :
    Step (engineBasePremises (definitionsEnv definitions)) ccsRecCalc source target ↔
      RecRawStep definitions source target :=
  ⟨raw_of_step, step_of_raw⟩

end Adequacy

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
