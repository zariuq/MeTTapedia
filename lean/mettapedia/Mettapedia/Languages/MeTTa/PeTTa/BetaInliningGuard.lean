import Mettapedia.Languages.MeTTa.PeTTa.BetaInliningSuperpose
import Mettapedia.Languages.MeTTa.PeTTa.BetaInliningControls

/-!
# A head pattern inlined as a case

A one-equation function whose head argument is a constructor pattern, `(= (f p) body)`,
is a guarded entry: the call matches `p` against the argument's value and runs the body
under the pattern's bindings, or answers nothing. Inlined as `(case $a ((p' body')))`,
where `p'` and `body'` rename the pattern's variables apart from the caller's environment,
it has the same observations beneath every continuation (`beta_case`). The head's test
becomes the case's test; no premise asks for the head to be distinct variables.

Matching a renamed pattern on top of the caller's environment binds the renamed variables
over the caller's bindings and decides as the original match does (`matchValue_lift`), and
a successful match binds every variable of the pattern (`matchValue_binds`).

Controls: a constant head `(z 0)` tests as `(case $u ((0 yes)))` does; a constructor head
with variables agrees with its case once the variables are renamed apart; without renaming
apart, the caller's binding of `$q` captures the pattern's `$q` and the case answers
nothing (`Controls.pair_head_case_captured`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInliningGuard

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program)
open Eval
open DeclarativeSpec (Transition Runs)
open Mettapedia.Languages.MeTTa.TypeSchemeActivation (rename freeVars)
open BetaInlining
open BetaInliningSuperpose

/-- Bindings carried to renamed names. -/
def lift (names : String → String) (bindings : Subst) : Subst :=
  bindings.map fun binding => (names binding.1, binding.2)

theorem lookup_append (first second : Subst) (name : String) :
    Subst.lookup (first ++ second) name =
      (Subst.lookup first name).or (Subst.lookup second name) := by
  induction first with
  | nil => simp [Subst.lookup]
  | cons binding rest ih =>
      obtain ⟨key, value⟩ := binding
      by_cases same : key = name
      · subst same; simp [Subst.lookup, List.find?]
      · have different : (key == name) = false := by simp [same]
        simp only [List.cons_append, lookup_cons, if_neg same]
        exact ih

/-- The variables a renaming must keep apart. -/
def Injective (names : String → String) (vars : List String) : Prop :=
  ∀ x ∈ vars, ∀ y ∈ vars, names x = names y → x = y

theorem lookup_lift {names : String → String} {vars : List String}
    (injective : Injective names vars) :
    ∀ (bindings : Subst), (∀ binding ∈ bindings, binding.1 ∈ vars) →
      ∀ x ∈ vars, Subst.lookup (lift names bindings) (names x) = Subst.lookup bindings x
  | [], _, _, _ => rfl
  | ⟨key, value⟩ :: rest, domain, x, member => by
      have keyIn : key ∈ vars := domain ⟨key, value⟩ List.mem_cons_self
      have tail := lookup_lift injective rest
        (fun binding found => domain binding (List.mem_cons_of_mem _ found)) x member
      simp only [lift, List.map_cons] at tail ⊢
      rw [lookup_cons, lookup_cons]
      by_cases same : key = x
      · subst same; simp
      · have renamedDifferent : names key ≠ names x :=
          fun equal => same (injective key keyIn x member equal)
        rw [if_neg renamedDifferent, if_neg same]
        exact tail

/-- What matching on top of a lifted environment keeps: every binding is of a variable in
`vars`, and every variable bound before stays bound to the same value. -/
def Domain (vars : List String) (bindings : Subst) : Prop := ∀ binding ∈ bindings, binding.1 ∈ vars

theorem lift_cons (names : String → String) (key : String) (value : Atom) (rest : Subst) :
    lift names ((key, value) :: rest) = (names key, value) :: lift names rest := rfl

section Lift

variable {names : String → String} {vars : List String} {caller : Subst}
  (injective : Injective names vars)
  (fresh : ∀ x ∈ vars, Subst.lookup caller (names x) = none)

include injective fresh

theorem lookup_lifted (acc : Subst) (domain : Domain vars acc) (x : String) (member : x ∈ vars) :
    Subst.lookup (lift names acc ++ caller) (names x) = Subst.lookup acc x := by
  rw [lookup_append, lookup_lift injective acc domain x member, fresh x member]
  cases Subst.lookup acc x <;> rfl

theorem matchAtom_lift :
    ∀ (p : Atom), Within vars p → ∀ (acc : Subst), Domain vars acc → ∀ (v : Atom),
      matchAtom (lift names acc ++ caller) (rename names p) v =
        (matchAtom acc p v).map (fun bound => lift names bound ++ caller) ∧
      ∀ bound, matchAtom acc p v = some bound → Domain vars bound := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, Within vars item) → ∀ (acc : Subst), Domain vars acc → ∀ values,
      matchAtom.matchAtomList (lift names acc ++ caller) (items.map (rename names)) values =
        (matchAtom.matchAtomList acc items values).map (fun bound => lift names bound ++ caller) ∧
      ∀ bound, matchAtom.matchAtomList acc items values = some bound → Domain vars bound) with
  | symbol s =>
      intro _ acc domain v
      refine ⟨?_, ?_⟩
      · cases v <;> simp [matchAtom]
      · intro bound matched
        cases v <;> simp [matchAtom] at matched
        all_goals simp_all
  | grounded g =>
      intro _ acc domain v
      refine ⟨?_, ?_⟩
      · cases v <;> simp [matchAtom]
      · intro bound matched
        cases v <;> simp [matchAtom] at matched
        all_goals simp_all
  | var x =>
      intro within acc domain v
      have member : x ∈ vars := within x (by simp [freeVars])
      have lifted := lookup_lifted injective fresh acc domain x member
      simp only [rename_var, matchAtom, lifted]
      cases found : Subst.lookup acc x with
      | some existing =>
          refine ⟨?_, ?_⟩
          · by_cases same : (v == existing) = true <;> simp [same]
          · intro bound matched
            by_cases same : (v == existing) = true <;> simp [same] at matched
            subst matched
            exact domain
      | none =>
          refine ⟨by simp [lift_cons], ?_⟩
          intro bound matched
          simp only [Option.some.injEq] at matched
          subst matched
          intro binding found
          rcases List.mem_cons.mp found with rfl | found
          · exact member
          · exact domain binding found
  | expression items ih =>
      intro within acc domain v
      have each := ih (within_expression.mp within) acc domain
      cases v with
      | expression values =>
          simp only [rename_expression, matchAtom]
          exact each values
      | var _ | symbol _ | grounded _ => simp [matchAtom]
  | nil =>
      rename_i _ acc domain values
      cases values <;> simp_all [matchAtom.matchAtomList]
  | cons head tail ihHead ihTail =>
      rename_i within acc domain values
      have headWithin := within head List.mem_cons_self
      have tailWithin : ∀ item ∈ tail, Within vars item :=
        fun item member => within item (List.mem_cons_of_mem _ member)
      cases values with
      | nil => simp [matchAtom.matchAtomList]
      | cons value rest =>
          simp only [List.map_cons, matchAtom.matchAtomList]
          obtain ⟨headEq, headDomain⟩ := ihHead headWithin acc domain value
          rw [headEq]
          cases matched : matchAtom acc head value with
          | none => simp
          | some middle =>
              have middleDomain := headDomain middle matched
              obtain ⟨tailEq, tailDomain⟩ := ihTail tailWithin middle middleDomain rest
              simp only [Option.map_some]
              exact ⟨tailEq, tailDomain⟩

theorem matchValue_lift :
    ∀ (p : Atom), Within vars p → ∀ (acc : Subst), Domain vars acc → ∀ (v : Atom),
      SpaceSemantics.matchValue (lift names acc ++ caller) (rename names p) v =
        (SpaceSemantics.matchValue acc p v).map (fun bound => lift names bound ++ caller) ∧
      ∀ bound, SpaceSemantics.matchValue acc p v = some bound → Domain vars bound := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, Within vars item) →
      (∀ item ∈ items, ∀ (acc : Subst), Domain vars acc → ∀ v,
        SpaceSemantics.matchValue (lift names acc ++ caller) (rename names item) v =
          (SpaceSemantics.matchValue acc item v).map (fun bound => lift names bound ++ caller) ∧
        ∀ bound, SpaceSemantics.matchValue acc item v = some bound → Domain vars bound) ∧
      ∀ (acc : Subst), Domain vars acc → ∀ values,
        SpaceSemantics.matchValue.matchValues (lift names acc ++ caller)
            (items.map (rename names)) values =
          (SpaceSemantics.matchValue.matchValues acc items values).map
            (fun bound => lift names bound ++ caller) ∧
        ∀ bound, SpaceSemantics.matchValue.matchValues acc items values = some bound →
          Domain vars bound) with
  | symbol s =>
      intro within acc domain v
      rw [matchValue_atomic _ _ _ (by simp), rename_symbol, matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_symbol] using matchAtom_lift injective fresh (.symbol s) within acc domain v
  | grounded g =>
      intro within acc domain v
      rw [matchValue_atomic _ _ _ (by simp), rename_grounded, matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_grounded] using
        matchAtom_lift injective fresh (.grounded g) within acc domain v
  | var x =>
      intro within acc domain v
      rw [matchValue_atomic _ _ _ (by simp), rename_var, matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_var] using matchAtom_lift injective fresh (.var x) within acc domain v
  | expression items ih =>
      intro within acc domain v
      obtain ⟨eachItem, eachList⟩ := ih (within_expression.mp within)
      by_cases isCons : ∃ first rest, items = [.symbol "cons", first, rest]
      · obtain ⟨first, rest, rfl⟩ := isCons
        simp only [rename_expression, List.map_cons, List.map_nil, rename_symbol]
        by_cases shape : ∃ head tail, v = .expression (head :: tail)
        · obtain ⟨head, tail, rfl⟩ := shape
          rw [matchValue_cons_cons, matchValue_cons_cons]
          obtain ⟨firstEq, firstDomain⟩ := eachItem first (by simp) acc domain head
          rw [firstEq]
          cases matched : SpaceSemantics.matchValue acc first head with
          | none => simp
          | some middle =>
              obtain ⟨restEq, restDomain⟩ :=
                eachItem rest (by simp) middle (firstDomain middle matched) (.expression tail)
              simp only [Option.map_some, Option.bind_some]
              exact ⟨restEq, restDomain⟩
        · have other : ∀ head tail, v ≠ .expression (head :: tail) :=
            fun head tail same => shape ⟨head, tail, same⟩
          rw [matchValue_cons_other _ _ _ _ other, matchValue_cons_other _ _ _ _ other]
          simp
      · have notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest] := by
          intro first rest same
          exact isCons ⟨first, rest, same⟩
        have renamedNotCons := not_cons_rename names notCons
        simp only [rename_expression]
        cases v with
        | expression values =>
            rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ notCons,
              SpaceSemantics.matchValue_expression_of_not_cons _ _ _ renamedNotCons]
            exact eachList acc domain values
        | var _ | symbol _ | grounded _ =>
            rw [matchValue_expression_nonexpression _ _ _ (by simp) notCons,
              matchValue_expression_nonexpression _ _ _ (by simp) renamedNotCons]
            simp
  | nil =>
      refine ⟨by simp, fun acc domain values => ?_⟩
      cases values <;> simp_all [SpaceSemantics.matchValue.matchValues]
  | cons head tail ihHead ihTail =>
      rename_i within
      have headWithin := within head List.mem_cons_self
      have tailWithin : ∀ item ∈ tail, Within vars item :=
        fun item member => within item (List.mem_cons_of_mem _ member)
      obtain ⟨tailItems, tailList⟩ := ihTail tailWithin
      refine ⟨?_, fun acc domain values => ?_⟩
      · intro item member acc domain v
        rcases List.mem_cons.mp member with rfl | member
        · exact ihHead headWithin acc domain v
        · exact tailItems item member acc domain v
      · cases values with
        | nil => simp [SpaceSemantics.matchValue.matchValues]
        | cons value rest =>
            simp only [List.map_cons, SpaceSemantics.matchValue.matchValues, bind, Option.bind]
            obtain ⟨headEq, headDomain⟩ := ihHead headWithin acc domain value
            rw [headEq]
            cases matched : SpaceSemantics.matchValue acc head value with
            | none => simp
            | some middle =>
                obtain ⟨restEq, restDomain⟩ := tailList middle (headDomain middle matched) rest
                simp only [Option.map_some]
                exact ⟨restEq, restDomain⟩

end Lift

/-! ## A successful match binds the pattern's variables -/

/-- A match keeps every binding it starts from and binds every variable of the pattern. -/
theorem matchAtom_binds :
    ∀ (p : Atom) (acc : Subst) (v : Atom) (bound : Subst), matchAtom acc p v = some bound →
      (∀ x w, Subst.lookup acc x = some w → Subst.lookup bound x = some w) ∧
      ∀ x ∈ freeVars p, (Subst.lookup bound x).isSome := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    ∀ (acc : Subst) (values : List Atom) (bound : Subst),
      matchAtom.matchAtomList acc items values = some bound →
      (∀ x w, Subst.lookup acc x = some w → Subst.lookup bound x = some w) ∧
      ∀ x ∈ items.flatMap freeVars, (Subst.lookup bound x).isSome) with
  | symbol s =>
      intro acc v bound matched
      cases v <;> simp [matchAtom] at matched
      all_goals (obtain ⟨_, rfl⟩ := matched; simp [freeVars])
  | grounded g =>
      intro acc v bound matched
      cases v <;> simp [matchAtom] at matched
      all_goals (obtain ⟨_, rfl⟩ := matched; simp [freeVars])
  | var x =>
      intro acc v bound matched
      simp only [matchAtom] at matched
      cases found : Subst.lookup acc x with
      | some existing =>
          rw [found] at matched
          by_cases same : (v == existing) = true <;> simp [same] at matched
          subst matched
          exact ⟨fun _ _ h => h, by simp [freeVars, found]⟩
      | none =>
          rw [found] at matched
          simp only [Option.some.injEq] at matched
          subst matched
          refine ⟨fun y w h => ?_, by simp [freeVars, lookup_cons]⟩
          rw [lookup_cons]
          by_cases same : x = y
          · subst same; rw [found] at h; cases h
          · rw [if_neg same]; exact h
  | expression items ih =>
      intro acc v bound matched
      cases v with
      | expression values =>
          simp only [matchAtom] at matched
          obtain ⟨keeps, covers⟩ := ih acc values bound matched
          exact ⟨keeps, by simpa [freeVars] using covers⟩
      | var _ | symbol _ | grounded _ => simp [matchAtom] at matched
  | nil =>
      rename_i acc values bound matched
      cases values <;> simp [matchAtom.matchAtomList] at matched
      subst matched
      exact ⟨fun _ _ h => h, by simp⟩
  | cons head tail ihHead ihTail =>
      rename_i acc values bound matched
      cases values with
      | nil => simp [matchAtom.matchAtomList] at matched
      | cons value rest =>
          simp only [matchAtom.matchAtomList] at matched
          cases headMatched : matchAtom acc head value with
          | none => rw [headMatched] at matched; cases matched
          | some middle =>
              rw [headMatched] at matched
              obtain ⟨keepsHead, coversHead⟩ := ihHead acc value middle headMatched
              obtain ⟨keepsTail, coversTail⟩ := ihTail middle rest bound matched
              refine ⟨fun x w h => keepsTail x w (keepsHead x w h), ?_⟩
              intro x member
              simp only [List.flatMap_cons, List.mem_append] at member
              rcases member with member | member
              · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (coversHead x member)
                simp [keepsTail x w hw]
              · exact coversTail x member

theorem matchValue_binds :
    ∀ (p : Atom) (acc : Subst) (v : Atom) (bound : Subst),
      SpaceSemantics.matchValue acc p v = some bound →
      (∀ x w, Subst.lookup acc x = some w → Subst.lookup bound x = some w) ∧
      ∀ x ∈ freeVars p, (Subst.lookup bound x).isSome := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, ∀ (acc : Subst) (v : Atom) (bound : Subst),
      SpaceSemantics.matchValue acc item v = some bound →
      (∀ x w, Subst.lookup acc x = some w → Subst.lookup bound x = some w) ∧
      ∀ x ∈ freeVars item, (Subst.lookup bound x).isSome) ∧
    ∀ (acc : Subst) (values : List Atom) (bound : Subst),
      SpaceSemantics.matchValue.matchValues acc items values = some bound →
      (∀ x w, Subst.lookup acc x = some w → Subst.lookup bound x = some w) ∧
      ∀ x ∈ items.flatMap freeVars, (Subst.lookup bound x).isSome) with
  | symbol s =>
      intro acc v bound matched
      rw [matchValue_atomic _ _ _ (by simp)] at matched
      exact matchAtom_binds _ acc v bound matched
  | grounded g =>
      intro acc v bound matched
      rw [matchValue_atomic _ _ _ (by simp)] at matched
      exact matchAtom_binds _ acc v bound matched
  | var x =>
      intro acc v bound matched
      rw [matchValue_atomic _ _ _ (by simp)] at matched
      exact matchAtom_binds _ acc v bound matched
  | expression items ih =>
      intro acc v bound matched
      obtain ⟨eachItem, eachList⟩ := ih
      by_cases isCons : ∃ first rest, items = [.symbol "cons", first, rest]
      · obtain ⟨first, rest, rfl⟩ := isCons
        by_cases shape : ∃ head tail, v = .expression (head :: tail)
        · obtain ⟨head, tail, rfl⟩ := shape
          rw [matchValue_cons_cons] at matched
          cases firstMatched : SpaceSemantics.matchValue acc first head with
          | none => rw [firstMatched] at matched; cases matched
          | some middle =>
              rw [firstMatched] at matched
              simp only [Option.bind_some] at matched
              obtain ⟨keepsFirst, coversFirst⟩ := eachItem first (by simp) acc head middle firstMatched
              obtain ⟨keepsRest, coversRest⟩ :=
                eachItem rest (by simp) middle (.expression tail) bound matched
              refine ⟨fun x w h => keepsRest x w (keepsFirst x w h), ?_⟩
              intro x member
              simp only [freeVars, List.flatMap_cons, List.flatMap_nil, List.mem_append,
                List.append_nil] at member
              rcases member with member | member | member
              · simp at member
              · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (coversFirst x member)
                simp [keepsRest x w hw]
              · exact coversRest x member
        · have other : ∀ head tail, v ≠ .expression (head :: tail) :=
            fun head tail same => shape ⟨head, tail, same⟩
          rw [matchValue_cons_other _ _ _ _ other] at matched
          cases matched
      · have notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest] := by
          intro first rest same
          exact isCons ⟨first, rest, same⟩
        cases v with
        | expression values =>
            rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ notCons] at matched
            obtain ⟨keeps, covers⟩ := eachList acc values bound matched
            exact ⟨keeps, by simpa [freeVars] using covers⟩
        | var _ | symbol _ | grounded _ =>
            rw [matchValue_expression_nonexpression _ _ _ (by simp) notCons] at matched
            cases matched
  | nil =>
      refine ⟨by simp, fun acc values bound matched => ?_⟩
      cases values <;> simp [SpaceSemantics.matchValue.matchValues] at matched
      subst matched
      exact ⟨fun _ _ h => h, by simp⟩
  | cons head tail ihHead ihTail =>
      obtain ⟨tailItems, tailList⟩ := ihTail
      refine ⟨?_, fun acc values bound matched => ?_⟩
      · intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact ihHead
        · exact tailItems item member
      · cases values with
        | nil => simp [SpaceSemantics.matchValue.matchValues] at matched
        | cons value rest =>
            simp only [SpaceSemantics.matchValue.matchValues, bind, Option.bind] at matched
            cases headMatched : SpaceSemantics.matchValue acc head value with
            | none => rw [headMatched] at matched; cases matched
            | some middle =>
                rw [headMatched] at matched
                obtain ⟨keepsHead, coversHead⟩ := ihHead acc value middle headMatched
                obtain ⟨keepsTail, coversTail⟩ := tailList middle rest bound matched
                refine ⟨fun x w h => keepsTail x w (keepsHead x w h), ?_⟩
                intro x member
                simp only [List.flatMap_cons, List.mem_append] at member
                rcases member with member | member
                · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (coversHead x member)
                  simp [keepsTail x w hw]
                · exact coversTail x member

/-! ## The head as a case -/

theorem clauses_of_single (program : Program) (f : String) (arguments : List Atom) (body : Atom)
    (single : program.equations.filter (fun equation => equation.head == f) =
      [⟨f, arguments, body⟩]) (values : List Atom) :
    clauses program f values =
      ((SpaceSemantics.matchValue.matchValues [] arguments values).map
        fun bound => Control.evaluate bound body).toList := by
  unfold clauses
  have rewritten := filterMap_ite_eq_filter (fun equation : SpaceSemantics.Equation =>
      equation.head = f)
    (fun equation => (SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
      fun bindings => Control.evaluate bindings equation.body)
    program.equations
  rw [rewritten]
  have sameFilter : (fun equation : SpaceSemantics.Equation => decide (equation.head = f)) =
      (fun equation => equation.head == f) := by
    funext equation
    by_cases same : equation.head = f <;> simp [same]
  rw [sameFilter, single]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases (SpaceSemantics.matchValue.matchValues [] arguments values) <;> rfl

theorem matchValues_single (pattern value : Atom) :
    SpaceSemantics.matchValue.matchValues [] [pattern] [value] =
      SpaceSemantics.matchValue [] pattern value := by
  simp only [SpaceSemantics.matchValue.matchValues, bind, Option.bind]
  cases SpaceSemantics.matchValue [] pattern value <;> rfl

theorem matchValue_single (pattern value : Atom) :
    SpaceSemantics.matchValue [] (.expression [pattern]) (.expression [value]) =
      SpaceSemantics.matchValue [] pattern value := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by intro first rest same; simp at same)]
  simp only [SpaceSemantics.matchValue.matchValues, bind, Option.bind]
  cases SpaceSemantics.matchValue [] pattern value <;> rfl

/-- **The head as a case.** A call of a one-equation function whose head argument is any
pattern is equivalent beneath every continuation to a case on the argument with one row:
the pattern and the body, their variables renamed apart from the caller's environment. -/
theorem beta_case (program : Program) (f : String) (pattern body : Atom) (a : String)
    (names : String → String)
    (single : program.equations.filter (fun equation => equation.head == f) =
      [⟨f, [pattern], body⟩])
    (closed : Within (freeVars pattern) body)
    (injective : Injective names (freeVars pattern))
    (notPrimitive : StdLib.known f = false) (notIO : ioHead f = false)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (caller : Subst) (fresh : ∀ x ∈ freeVars pattern, Subst.lookup caller (names x) = none) :
    Equivalent program (.evaluate caller (.expression [.symbol f, .var a]))
      (.evaluate caller (.expression [.symbol "case", .var a,
        .expression [.expression [rename names pattern, rename names body]]])) := by
  intro state frames input output
  set value := applySubst caller (.var a) with valueDef
  have callable : (ioHead f || StdLib.known f || program.equations.any (·.head == f)) = true := by
    have member : (⟨f, [pattern], body⟩ : SpaceSemantics.Equation) ∈
        program.equations.filter (fun equation => equation.head == f) := by
      rw [single]; simp
    have found := List.mem_filter.mp member
    simp only [List.any_eq_true, Bool.or_eq_true]
    exact .inr ⟨_, found.1, found.2⟩
  have callPath := call_reaches_clauses program f [a] callable notPrimitive notIO ordinary
    (by simp [arities, single]) caller state frames input output
  rw [clauses_of_single program f [pattern] body single] at callPath
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.zero_add,
    matchValues_single] at callPath
  have patternWithin : Within (freeVars pattern) pattern := fun _ member => member
  obtain ⟨lifted, _⟩ := matchValue_lift injective fresh pattern patternWithin [] (by simp [Domain]) value
  have selected : SpaceSemantics.selectCase caller value
      [(rename names pattern, rename names body)] =
      (SpaceSemantics.matchValue [] pattern value).map
        (fun bound => (lift names bound ++ caller, rename names body)) := by
    simp only [lift, List.map_nil, List.nil_append] at lifted
    simp only [SpaceSemantics.selectCase, lifted]
    cases SpaceSemantics.matchValue [] pattern value <;> rfl
  have casePath : (theory program).MultiStep
      ⟨state, .evaluate caller (.expression [.symbol "case", .var a,
        .expression [.expression [rename names pattern, rename names body]]]), frames, input,
        output⟩
      ⟨state, .sequence ((SpaceSemantics.matchValue [] pattern value).map
          (fun bound => Control.evaluate (lift names bound ++ caller) (rename names body))).toList [],
        frames, input, output⟩ := by
    refine .step (Transition.case_enter (cases := [(rename names pattern, rename names body)])
      rfl rfl) (.step (Transition.value_variable rfl) (.step (Transition.case_return rfl rfl) ?_))
    have shape : ([applySubst caller (.var a)].filterMap fun value =>
        (SpaceSemantics.selectCase caller value [(rename names pattern, rename names body)]).map
          fun (bound, body) => Control.evaluate bound body) =
        ((SpaceSemantics.matchValue [] pattern value).map
          (fun bound => Control.evaluate (lift names bound ++ caller) (rename names body))).toList := by
      simp only [List.filterMap_cons, List.filterMap_nil, ← valueDef, selected]
      cases SpaceSemantics.matchValue [] pattern value <;> rfl
    rw [shape]
    exact .refl _
  refine (sameObservations_of_path callPath).trans
    ((transparent_sequences program 1 frames state _ input output).trans
      (SameObservations.trans ?_ (sameObservations_of_path casePath).symm))
  cases matched : SpaceSemantics.matchValue [] pattern value with
  | none => exact SameObservations.refl program _
  | some bound =>
      have domain := (matchValue_lift injective fresh pattern patternWithin [] (by simp [Domain])
        value).2 bound matched
      have covers := (matchValue_binds pattern [] value bound matched).2
      have agree : Agree bound (lift names bound ++ caller) names (freeVars pattern) := by
        intro x member
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (covers x member)
        exact ⟨w, hw, by rw [lookup_lifted injective fresh bound domain x member, hw]⟩
      exact sequence_equivalent program
        (.cons (evaluate_equivalent program agree body closed) .nil) [] state frames input output

/-! ## Controls -/

namespace Controls

open BetaInliningControls (answersOf)

private def int (value : Int) : Atom := .grounded (.int value)
private def sym (name : String) : Atom := .symbol name
private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

/-- `(= (z 0) yes)`: a constant head. -/
def constantHead : Program where
  equations := [⟨"z", [int 0], sym "yes"⟩]
  declarations := []

/-- The head's test: `(let $u 0 (z $u))` gives `yes`, `(let $u 1 (z $u))` nothing, as
does the case `(case $u ((0 yes)))` for each. -/
theorem constant_head_call : answersOf (evaluate constantHead 64 Effects.empty
    (call "let" [.var "u", int 0, call "z" [.var "u"]])) = some [sym "yes"] ∧
    answersOf (evaluate constantHead 64 Effects.empty
      (call "let" [.var "u", int 1, call "z" [.var "u"]])) = some [] := by
  constructor <;> decide +kernel

theorem constant_head_case : answersOf (evaluate constantHead 64 Effects.empty
    (call "let" [.var "u", int 0, call "case" [.var "u",
      .expression [.expression [int 0, sym "yes"]]]])) = some [sym "yes"] ∧
    answersOf (evaluate constantHead 64 Effects.empty
      (call "let" [.var "u", int 1, call "case" [.var "u",
        .expression [.expression [int 0, sym "yes"]]]])) = some [] := by
  constructor <;> decide +kernel

/-- `(= (second (pair $p $q)) $q)`: a constructor head with variables. -/
def pairHead : Program where
  equations := [⟨"second", [call "pair" [.var "p", .var "q"]], .var "q"⟩]
  declarations := []

/-- With the caller binding `$q` to 7, the call `(second $u)` on `(pair 1 2)` gives 2, and
so does the case with the pattern's variables renamed apart, `(pair $p1 $q1)`. -/
theorem pair_head_call : answersOf (evaluate pairHead 64 Effects.empty
    (call "let" [.var "q", int 7, call "let" [.var "u", call "pair" [int 1, int 2],
      call "second" [.var "u"]]])) = some [int 2] := by
  decide +kernel

theorem pair_head_case_renamed : answersOf (evaluate pairHead 64 Effects.empty
    (call "let" [.var "q", int 7, call "let" [.var "u", call "pair" [int 1, int 2],
      call "case" [.var "u",
        .expression [.expression [call "pair" [.var "p1", .var "q1"], .var "q1"]]]]])) =
      some [int 2] := by
  decide +kernel

/-- Negative: without renaming apart, the case's `$q` is the caller's, bound to 7, and the
case answers nothing. -/
theorem pair_head_case_captured : answersOf (evaluate pairHead 64 Effects.empty
    (call "let" [.var "q", int 7, call "let" [.var "u", call "pair" [int 1, int 2],
      call "case" [.var "u",
        .expression [.expression [call "pair" [.var "p", .var "q"], .var "q"]]]]])) =
      some [] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.BetaInliningGuard
