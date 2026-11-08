/-!
# Declared types of applications: the design choices and their trade-offs

Hyperon Experimental gives an application `(h a₁ … aₙ)` a type in two ways.

* A declaration `(: (h a₁ … aₙ) T)` in the space states a fact about the
  expression itself.
* The application rule: a function type `(: h (-> A₁ … Aₙ R))` whose
  argument types `Aᵢ` the arguments have gives the application the type `R`.

The type checker (`get-type`, `check_type`, argument checks) uses both. The
evaluator admits an application whose head has function types only by the
application rule. So `(: (Human Socrates) TrueProp)` makes the checker accept
`(proof-id (Human Socrates))` for `(: proof-id (-> TrueProp TrueProp))`, while
evaluation rejects the argument with `(BadType TrueProp Prop)`. The checker
also lets a declaration type `(Human Time)` although `Time` is no `Entity`.

This file states the candidate policies for reconciling the two judgments and
proves which properties each one has:

| policy | `Agree` | `NoMasking` | `Refines` | `Preserves` | `MonotoneInRules` |
|---|---|---|---|---|---|
| `stock` (HE today) | no | no | no | yes | yes |
| `ignoreDeclarations` | yes | yes | no | yes | yes |
| `checkArgumentsFirst` | no | yes | no | yes | yes |
| `trustDeclarations` | yes | yes | yes | no | yes |
| `valuesOnly` | yes | yes | yes | yes | no |

`refine_preserve_monotone_incompatible` proves that no policy whatsoever has
the last three properties together, so every policy that makes the checker
and evaluation agree gives up one of them. `get-type` faces a second forced
choice (`reflect_reportAgrees_noMasking_incompatible`): it cannot report every
declaration, agree with evaluation, and refuse ill-typed applications at once.
`reflectDeclarations` is `ignoreDeclarations` with a `get-type` that keeps
reporting the declarations.

HE already trusts declarations on applications of heads without function
types (tuples) before rewriting them: `tuple_declarations_trusted_before_rewriting`.

Model scope. Terms are ground: no type variables, no `%Undefined%`, no
meta-types, no subtyping, and no tuple types computed from element types.
Equations are ground and are read as one rewrite step; arguments are taken
as already evaluated. Type matching is syntactic equality. The properties
are properties of this model of the two judgments, not of the Rust code.
-/

namespace Mettapedia.Languages.MeTTa.HE.DeclaredApplicationTypes

/-! ## Terms and theories -/

/-- Ground atoms: symbols, and applications of a symbol head. -/
inductive Term where
  | sym : String → Term
  | app : String → List Term → Term

/-- A typing theory: declarations, function types of heads, and equations. -/
structure Theory where
  /-- `(: e T)` -/
  decl : Term → Term → Prop
  /-- `(: h (-> A₁ … Aₙ R))` -/
  arrow : String → List Term → Term → Prop
  /-- `(= lhs rhs)` -/
  rule : Term → Term → Prop

/-- The head has at least one function type. -/
def Theory.HasArrow (Γ : Theory) (h : String) : Prop :=
  ∃ As R, Γ.arrow h As R

/-- No equation rewrites `e`: evaluation returns `e` itself, so `e` is data. -/
def Theory.NormalForm (Γ : Theory) (e : Term) : Prop :=
  ∀ e', ¬ Γ.rule e e'

/-- The theory with additional equations. -/
def Theory.withRules (Γ : Theory) (extra : Term → Term → Prop) : Theory :=
  { Γ with rule := fun a b => Γ.rule a b ∨ extra a b }

/-! ## The typing judgment, parameterized by a declaration rule -/

/-- When a declaration may give its type to an application whose head has
function types. -/
structure DeclarationRule where
  /-- Declarations count at all. -/
  allow : Bool
  /-- Only when some function type of the head accepts the arguments. -/
  checkArgs : Bool
  /-- Only when no equation rewrites the application. -/
  normalOnly : Bool

/-- HE's checker today: every declaration counts. -/
def DeclarationRule.permissive : DeclarationRule := ⟨true, false, false⟩
/-- Declarations never type an application of a head with function types. -/
def DeclarationRule.ignored : DeclarationRule := ⟨false, false, false⟩
/-- A declaration counts once the arguments are well typed. -/
def DeclarationRule.checked : DeclarationRule := ⟨true, true, false⟩
/-- A declaration counts for a well-typed application that is a value. -/
def DeclarationRule.values : DeclarationRule := ⟨true, true, true⟩

mutual
/-- `Typed Γ r e T`: `e` has type `T` when declarations on applications are
admitted by `r`. -/
inductive Typed (Γ : Theory) (r : DeclarationRule) : Term → Term → Prop where
  | sym {s T} : Γ.decl (.sym s) T → Typed Γ r (.sym s) T
  /-- A head without function types forms a tuple, typed by declarations. -/
  | tuple {h args T} : ¬ Γ.HasArrow h → Γ.decl (.app h args) T →
      Typed Γ r (.app h args) T
  | declUnchecked {h args T} : Γ.HasArrow h → r.allow = true →
      r.checkArgs = false → (r.normalOnly = true → Γ.NormalForm (.app h args)) →
      Γ.decl (.app h args) T → Typed Γ r (.app h args) T
  | declChecked {h args As R T} : r.allow = true → Γ.arrow h As R →
      ArgsTyped Γ r args As → (r.normalOnly = true → Γ.NormalForm (.app h args)) →
      Γ.decl (.app h args) T → Typed Γ r (.app h args) T
  /-- The application rule. -/
  | app {h args As R} : Γ.arrow h As R → ArgsTyped Γ r args As →
      Typed Γ r (.app h args) R

/-- Arguments and their expected types, pointwise. -/
inductive ArgsTyped (Γ : Theory) (r : DeclarationRule) : List Term → List Term → Prop where
  | nil : ArgsTyped Γ r [] []
  | cons {a as A As} : Typed Γ r a A → ArgsTyped Γ r as As →
      ArgsTyped Γ r (a :: as) (A :: As)
end

/-- The checker's judgment in HE today, and the reference notion "`e` has
type `T`" used to state preservation. -/
abbrev HasType (Γ : Theory) : Term → Term → Prop := Typed Γ .permissive

/-- HE's evaluator: an application of a head with function types is admitted
at `T` only by a function type returning `T`, its arguments checked by the
judgment of `r`; any other atom is cast by its types. -/
def HeadAdmit (Γ : Theory) (r : DeclarationRule) : Term → Term → Prop
  | .sym s, T => Typed Γ r (.sym s) T
  | .app h args, T =>
      (∃ As, Γ.arrow h As T ∧ ArgsTyped Γ r args As) ∨
      (¬ Γ.HasArrow h ∧ Typed Γ r (.app h args) T)

/-! ## Policies -/

/-- A reconciliation policy: the checker's judgment in an evaluated position,
what evaluation admits, and what `get-type` reports. -/
structure Policy where
  check : Theory → Term → Term → Prop
  admit : Theory → Term → Term → Prop
  report : Theory → Term → Term → Prop

/-- HE today. -/
def Policy.stock : Policy where
  check Γ := Typed Γ .permissive
  admit Γ := HeadAdmit Γ .permissive
  report Γ := Typed Γ .permissive

/-- Delete declarations on applications of heads with function types. -/
def Policy.ignoreDeclarations : Policy where
  check Γ := Typed Γ .ignored
  admit Γ := Typed Γ .ignored
  report Γ := Typed Γ .ignored

/-- Like `ignoreDeclarations`, but `get-type` still reports declarations. -/
def Policy.reflectDeclarations : Policy where
  check Γ := Typed Γ .ignored
  admit Γ := Typed Γ .ignored
  report Γ e T := Γ.decl e T ∨ Typed Γ .ignored e T

/-- Keep a declaration in the checker only when the arguments are well
typed; evaluation unchanged. -/
def Policy.checkArgumentsFirst : Policy where
  check Γ := Typed Γ .checked
  admit Γ := HeadAdmit Γ .checked
  report Γ := Typed Γ .checked

/-- Evaluation honours a declaration on a well-typed application. -/
def Policy.trustDeclarations : Policy where
  check Γ := Typed Γ .checked
  admit Γ := Typed Γ .checked
  report Γ := Typed Γ .checked

/-- A declaration counts for a well-typed application only while no
equation rewrites it: a computation is typed by its head, a value also by
its declarations. -/
def Policy.valuesOnly : Policy where
  check Γ := Typed Γ .values
  admit Γ := Typed Γ .values
  report Γ := Typed Γ .values

/-! ## Properties -/

/-- Whatever the checker accepts at `T` in an evaluated position, evaluation
admits at `T`. -/
def Agree (P : Policy) : Prop :=
  ∀ Γ e T, P.check Γ e T → P.admit Γ e T

/-- The checker accepts an application of a head with function types only
when some function type of the head accepts its arguments. -/
def NoMasking (P : Policy) : Prop :=
  ∀ Γ h args T, Γ.HasArrow h → P.check Γ (.app h args) T →
    ∃ As R, Γ.arrow h As R ∧ ArgsTyped Γ .permissive args As

/-- The arguments are well typed without any declaration on an application. -/
def PlainArgs (Γ : Theory) (h : String) (args : List Term) : Prop :=
  ∃ As R, Γ.arrow h As R ∧ ArgsTyped Γ .ignored args As

/-- A declaration on a well-typed application that no equation rewrites is
honoured by evaluation. -/
def Refines (P : Policy) : Prop :=
  ∀ Γ h args T, Γ.NormalForm (.app h args) → PlainArgs Γ h args →
    Γ.decl (.app h args) T → P.admit Γ (.app h args) T

/-- Equations preserve the types the application rule gives. -/
def Theory.RulesPreserveApplicationTypes (Γ : Theory) : Prop :=
  ∀ h args rhs, Γ.rule (.app h args) rhs → ∀ As R, Γ.arrow h As R →
    ArgsTyped Γ .permissive args As → HasType Γ rhs R

/-- Admission is honest for computations: when equations preserve the
application rule's types, a rewrite of an admitted application of a head with
function types has the type it was admitted at. -/
def Preserves (P : Policy) : Prop :=
  ∀ Γ, Γ.RulesPreserveApplicationTypes → ∀ h args T rhs, Γ.HasArrow h →
    P.admit Γ (.app h args) T → Γ.rule (.app h args) rhs → HasType Γ rhs T

/-- Adding equations never withdraws an admission. -/
def MonotoneInRules (P : Policy) : Prop :=
  ∀ Γ extra e T, P.admit Γ e T → P.admit (Γ.withRules extra) e T

/-- `get-type` reports every declaration. -/
def Reflects (P : Policy) : Prop :=
  ∀ Γ e T, Γ.decl e T → P.report Γ e T

/-- What `get-type` reports, evaluation admits. -/
def ReportAgrees (P : Policy) : Prop :=
  ∀ Γ e T, P.report Γ e T → P.admit Γ e T

/-- Evaluation admits an application of a head with function types only when
some function type of the head accepts its arguments. -/
def AdmitNoMasking (P : Policy) : Prop :=
  ∀ Γ h args T, Γ.HasArrow h → P.admit Γ (.app h args) T →
    ∃ As R, Γ.arrow h As R ∧ ArgsTyped Γ .permissive args As

/-! ## Structural lemmas -/

mutual
/-- Every judgment is contained in the permissive one. -/
theorem Typed.toPermissive {Γ : Theory} {r : DeclarationRule} :
    ∀ {e T}, Typed Γ r e T → HasType Γ e T
  | _, _, .sym d => .sym d
  | _, _, .tuple n d => .tuple n d
  | _, _, .declUnchecked ha _ _ _ d => .declUnchecked ha rfl rfl (fun h => nomatch h) d
  | _, _, .declChecked _ arr _ _ d =>
      .declUnchecked ⟨_, _, arr⟩ rfl rfl (fun h => nomatch h) d
  | _, _, .app arr args => .app arr (ArgsTyped.toPermissive args)

theorem ArgsTyped.toPermissive {Γ : Theory} {r : DeclarationRule} :
    ∀ {as As}, ArgsTyped Γ r as As → ArgsTyped Γ .permissive as As
  | _, _, .nil => .nil
  | _, _, .cons t ts => .cons (Typed.toPermissive t) (ArgsTyped.toPermissive ts)
end

mutual
/-- A judgment without declarations on applications holds under every rule. -/
theorem Typed.ofIgnored {Γ : Theory} {r : DeclarationRule} :
    ∀ {e T}, Typed Γ .ignored e T → Typed Γ r e T
  | _, _, .sym d => .sym d
  | _, _, .tuple n d => .tuple n d
  | _, _, .declUnchecked _ allow _ _ _ => nomatch allow
  | _, _, .declChecked allow _ _ _ _ => nomatch allow
  | _, _, .app arr args => .app arr (ArgsTyped.ofIgnored args)

theorem ArgsTyped.ofIgnored {Γ : Theory} {r : DeclarationRule} :
    ∀ {as As}, ArgsTyped Γ .ignored as As → ArgsTyped Γ r as As
  | _, _, .nil => .nil
  | _, _, .cons t ts => .cons (Typed.ofIgnored t) (ArgsTyped.ofIgnored ts)
end

mutual
/-- A rule that does not look at equations is unaffected by adding some. -/
theorem Typed.withRules {Γ : Theory} {r : DeclarationRule} (hr : r.normalOnly = false)
    (extra : Term → Term → Prop) :
    ∀ {e T}, Typed Γ r e T → Typed (Γ.withRules extra) r e T
  | _, _, .sym d => .sym d
  | _, _, .tuple n d => .tuple n d
  | _, _, .declUnchecked ha allow ca _ d =>
      .declUnchecked ha allow ca (fun h => by rw [hr] at h; cases h) d
  | _, _, .declChecked allow arr args _ d =>
      .declChecked allow arr (ArgsTyped.withRules hr extra args)
        (fun h => by rw [hr] at h; cases h) d
  | _, _, .app arr args => .app arr (ArgsTyped.withRules hr extra args)

theorem ArgsTyped.withRules {Γ : Theory} {r : DeclarationRule} (hr : r.normalOnly = false)
    (extra : Term → Term → Prop) :
    ∀ {as As}, ArgsTyped Γ r as As → ArgsTyped (Γ.withRules extra) r as As
  | _, _, .nil => .nil
  | _, _, .cons t ts => .cons (Typed.withRules hr extra t) (ArgsTyped.withRules hr extra ts)
end

theorem HeadAdmit.withRules {Γ : Theory} {r : DeclarationRule} (hr : r.normalOnly = false)
    (extra : Term → Term → Prop) :
    ∀ {e T}, HeadAdmit Γ r e T → HeadAdmit (Γ.withRules extra) r e T
  | .sym _, _, h => Typed.withRules hr extra h
  | .app _ _, _, .inl ⟨As, arr, args⟩ => .inl ⟨As, arr, ArgsTyped.withRules hr extra args⟩
  | .app _ _, _, .inr ⟨n, t⟩ => .inr ⟨n, Typed.withRules hr extra t⟩

/-- Under a rule that checks arguments or ignores declarations, a typed
application of a head with function types has well-typed arguments. -/
theorem Typed.args_of_hasArrow {Γ : Theory} {r : DeclarationRule}
    (hr : r.allow = false ∨ r.checkArgs = true) {h args T}
    (ha : Γ.HasArrow h) (t : Typed Γ r (.app h args) T) :
    ∃ As R, Γ.arrow h As R ∧ ArgsTyped Γ .permissive args As := by
  cases t with
  | tuple n _ => exact absurd ha n
  | declUnchecked _ allow ca _ _ =>
      rcases hr with hr | hr
      · rw [hr] at allow; cases allow
      · rw [hr] at ca; cases ca
  | declChecked _ arr args _ _ => exact ⟨_, _, arr, args.toPermissive⟩
  | app arr args => exact ⟨_, _, arr, args.toPermissive⟩

/-- An application typed without declarations is typed by the application
rule. -/
theorem Typed.ignored_app {Γ : Theory} {h args T} (ha : Γ.HasArrow h)
    (t : Typed Γ .ignored (.app h args) T) :
    ∃ As, Γ.arrow h As T ∧ ArgsTyped Γ .ignored args As := by
  cases t with
  | tuple n _ => exact absurd ha n
  | declUnchecked _ allow _ _ _ => cases allow
  | declChecked allow _ _ _ _ => cases allow
  | app arr args => exact ⟨_, arr, args⟩

/-! ## The witnesses -/

private abbrev s (name : String) : Term := .sym name
private abbrev socrates : Term := .app "Human" [s "Socrates"]
private abbrev time : Term := .app "Human" [s "Time"]

/-- `(: Socrates Entity) (: Time NotEntity) (: p Prop)
(: Human (-> Entity Prop)) (: proof-id (-> TrueProp TrueProp))
(: (Human Socrates) TrueProp) (: (Human Time) Prop)`, no equations. -/
def humans : Theory where
  decl e T :=
    (e = s "Socrates" ∧ T = s "Entity") ∨ (e = s "Time" ∧ T = s "NotEntity") ∨
    (e = s "p" ∧ T = s "Prop") ∨ (e = socrates ∧ T = s "TrueProp") ∨
    (e = time ∧ T = s "Prop")
  arrow h As R :=
    (h = "Human" ∧ As = [s "Entity"] ∧ R = s "Prop") ∨
    (h = "proof-id" ∧ As = [s "TrueProp"] ∧ R = s "TrueProp")
  rule _ _ := False

/-- `humans` with the equation `(= (Human Socrates) p)`. -/
def humansRewritten : Theory :=
  humans.withRules fun a b => a = socrates ∧ b = s "p"

theorem humans_hasArrow_human : humans.HasArrow "Human" :=
  ⟨_, _, .inl ⟨rfl, rfl, rfl⟩⟩

theorem humansRewritten_hasArrow_human : humansRewritten.HasArrow "Human" :=
  humans_hasArrow_human

theorem humans_socrates_entity {r : DeclarationRule} :
    ArgsTyped humans r [s "Socrates"] [s "Entity"] :=
  .cons (.sym (.inl ⟨rfl, rfl⟩)) .nil

theorem humans_plainArgs_socrates : PlainArgs humans "Human" [s "Socrates"] :=
  ⟨_, _, .inl ⟨rfl, rfl, rfl⟩, humans_socrates_entity⟩

theorem humans_normal_socrates : humans.NormalForm socrates :=
  fun _ h => h

/-- Only the application rule's `Prop` and the declared `TrueProp` type
`(Human Socrates)`; a function type of `Human` returns `Prop`. -/
theorem human_arrow {Γ : Theory} (hΓ : Γ.arrow = humans.arrow) {As R}
    (arr : Γ.arrow "Human" As R) : As = [s "Entity"] ∧ R = s "Prop" := by
  rw [hΓ] at arr
  rcases arr with ⟨_, hAs, hR⟩ | ⟨h, _, _⟩
  · exact ⟨hAs, hR⟩
  · exact absurd h (by decide)

/-- `Time` has no type `Entity`, under any rule, with any equations. -/
theorem time_not_entity {Γ : Theory} (hΓ : Γ.decl = humans.decl) {r : DeclarationRule} :
    ¬ Typed Γ r (s "Time") (s "Entity") := by
  intro t
  cases t with
  | sym d =>
      rw [hΓ] at d
      simp [humans] at d

/-- `p` has no type `TrueProp`. -/
theorem p_not_trueProp {Γ : Theory} (hΓ : Γ.decl = humans.decl) {r : DeclarationRule} :
    ¬ Typed Γ r (s "p") (s "TrueProp") := by
  intro t
  cases t with
  | sym d =>
      rw [hΓ] at d
      simp [humans] at d

/-- The application rule does not give `(Human Socrates)` the type
`TrueProp`. -/
theorem socrates_no_trueProp_arrow {Γ : Theory} (hΓ : Γ.arrow = humans.arrow) {As} :
    ¬ Γ.arrow "Human" As (s "TrueProp") := by
  intro arr
  have := (human_arrow hΓ arr).2
  simp at this

theorem headAdmit_socrates_trueProp {Γ : Theory} (hΓ : Γ.arrow = humans.arrow)
    {r : DeclarationRule} : ¬ HeadAdmit Γ r socrates (s "TrueProp") := by
  rintro (⟨As, arr, _⟩ | ⟨n, _⟩)
  · exact socrates_no_trueProp_arrow hΓ arr
  · exact n ⟨_, _, by rw [hΓ]; exact .inl ⟨rfl, rfl, rfl⟩⟩

theorem ignored_socrates_trueProp {Γ : Theory} (hΓ : Γ.arrow = humans.arrow)
    (ha : Γ.HasArrow "Human") : ¬ Typed Γ .ignored socrates (s "TrueProp") := by
  intro t
  obtain ⟨As, arr, _⟩ := Typed.ignored_app ha t
  exact socrates_no_trueProp_arrow hΓ arr

/-! ## HE today -/

/-- The checker accepts `(Human Socrates)` at `TrueProp` by its declaration;
evaluation rejects it. -/
theorem stock_not_agree : ¬ Agree .stock := by
  intro h
  have check : Policy.stock.check humans socrates (s "TrueProp") :=
    .declUnchecked humans_hasArrow_human rfl rfl (fun h => nomatch h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  exact headAdmit_socrates_trueProp rfl (h _ _ _ check)

/-- The declaration `(: (Human Time) Prop)` hides that `Time` is no `Entity`. -/
theorem stock_not_noMasking : ¬ NoMasking .stock := by
  intro h
  have check : Policy.stock.check humans time (s "Prop") :=
    .declUnchecked humans_hasArrow_human rfl rfl (fun h => nomatch h)
      (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))
  obtain ⟨As, R, arr, args⟩ := h _ _ _ _ humans_hasArrow_human check
  obtain ⟨rfl, _⟩ := human_arrow rfl arr
  cases args with
  | cons t _ => exact time_not_entity rfl t

theorem stock_not_refines : ¬ Refines .stock := fun h =>
  headAdmit_socrates_trueProp rfl
    (h humans "Human" [s "Socrates"] (s "TrueProp") humans_normal_socrates
      humans_plainArgs_socrates (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))

/-- Evaluation by the head's function types is honest. -/
theorem headAdmit_preserves {r : DeclarationRule} {Γ : Theory}
    (hΓ : Γ.RulesPreserveApplicationTypes) {h args T rhs} (ha : Γ.HasArrow h)
    (adm : HeadAdmit Γ r (.app h args) T) (rw : Γ.rule (.app h args) rhs) : HasType Γ rhs T := by
  rcases adm with ⟨As, arr, args⟩ | ⟨n, _⟩
  · exact hΓ h _ rhs rw As T arr args.toPermissive
  · exact absurd ha n

theorem stock_preserves : Preserves .stock :=
  fun _ hΓ _ _ _ _ ha adm rw => headAdmit_preserves hΓ ha adm rw

theorem stock_monotoneInRules : MonotoneInRules .stock :=
  fun _ extra _ _ adm => HeadAdmit.withRules rfl extra adm

/-- `(: (c d) (C D)) (: x X) (= (c d) x)`, and no function types. -/
def tuples : Theory where
  decl e T := (e = .app "c" [s "d"] ∧ T = .app "C" [s "D"]) ∨ (e = s "x" ∧ T = s "X")
  arrow _ _ _ := False
  rule a b := a = .app "c" [s "d"] ∧ b = s "x"

/-- HE today already admits a declared tuple before rewriting it, and the
rewrite need not have the declared type. -/
theorem tuple_declarations_trusted_before_rewriting :
    tuples.RulesPreserveApplicationTypes ∧
      Policy.stock.admit tuples (.app "c" [s "d"]) (.app "C" [s "D"]) ∧
      tuples.rule (.app "c" [s "d"]) (s "x") ∧ ¬ HasType tuples (s "x") (.app "C" [s "D"]) := by
  refine ⟨fun _ _ _ _ _ _ arr _ => arr.elim, ?_, ⟨rfl, rfl⟩, ?_⟩
  · exact .inr ⟨fun ⟨_, _, arr⟩ => arr, .tuple (fun ⟨_, _, arr⟩ => arr) (.inl ⟨rfl, rfl⟩)⟩
  · intro t
    cases t with
    | sym d => simp [tuples] at d

/-! ## Ignoring declarations -/

theorem ignoreDeclarations_agree : Agree .ignoreDeclarations := fun _ _ _ h => h

theorem ignoreDeclarations_noMasking : NoMasking .ignoreDeclarations :=
  fun _ _ _ _ ha t => Typed.args_of_hasArrow (.inl rfl) ha t

theorem ignoreDeclarations_not_refines : ¬ Refines .ignoreDeclarations := fun h =>
  ignored_socrates_trueProp rfl humans_hasArrow_human
    (h humans "Human" [s "Socrates"] (s "TrueProp") humans_normal_socrates
      humans_plainArgs_socrates (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))

theorem ignoreDeclarations_preserves : Preserves .ignoreDeclarations := by
  intro Γ hΓ h args T rhs ha adm rw
  obtain ⟨As, arr, args⟩ := Typed.ignored_app ha adm
  exact hΓ h _ rhs rw As T arr args.toPermissive

theorem ignoreDeclarations_monotoneInRules : MonotoneInRules .ignoreDeclarations :=
  fun _ extra _ _ adm => Typed.withRules rfl extra adm

theorem ignoreDeclarations_not_reflects : ¬ Reflects .ignoreDeclarations := fun h =>
  ignored_socrates_trueProp rfl humans_hasArrow_human
    (h humans socrates (s "TrueProp") (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))

theorem reflectDeclarations_reflects : Reflects .reflectDeclarations :=
  fun _ _ _ d => .inl d

theorem reflectDeclarations_not_reportAgrees : ¬ ReportAgrees .reflectDeclarations := fun h =>
  ignored_socrates_trueProp rfl humans_hasArrow_human
    (h humans socrates (s "TrueProp") (.inl (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))))

/-! ## Checking arguments first -/

theorem checkArgumentsFirst_not_agree : ¬ Agree .checkArgumentsFirst := by
  intro h
  have check : Policy.checkArgumentsFirst.check humans socrates (s "TrueProp") :=
    .declChecked rfl (.inl ⟨rfl, rfl, rfl⟩) humans_socrates_entity (fun h => nomatch h)
      (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  exact headAdmit_socrates_trueProp rfl (h _ _ _ check)

theorem checkArgumentsFirst_noMasking : NoMasking .checkArgumentsFirst :=
  fun _ _ _ _ ha t => Typed.args_of_hasArrow (.inr rfl) ha t

theorem checkArgumentsFirst_not_refines : ¬ Refines .checkArgumentsFirst := fun h =>
  headAdmit_socrates_trueProp rfl
    (h humans "Human" [s "Socrates"] (s "TrueProp") humans_normal_socrates
      humans_plainArgs_socrates (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))

theorem checkArgumentsFirst_preserves : Preserves .checkArgumentsFirst :=
  fun _ hΓ _ _ _ _ ha adm rw => headAdmit_preserves hΓ ha adm rw

theorem checkArgumentsFirst_monotoneInRules : MonotoneInRules .checkArgumentsFirst :=
  fun _ extra _ _ adm => HeadAdmit.withRules rfl extra adm

/-! ## Trusting declarations -/

theorem trustDeclarations_agree : Agree .trustDeclarations := fun _ _ _ h => h

theorem trustDeclarations_noMasking : NoMasking .trustDeclarations :=
  fun _ _ _ _ ha t => Typed.args_of_hasArrow (.inr rfl) ha t

theorem trustDeclarations_refines : Refines .trustDeclarations := by
  intro Γ h args T _ ⟨As, R, arr, args⟩ d
  exact .declChecked rfl arr (ArgsTyped.ofIgnored args) (fun h => nomatch h) d

/-- The equations of `humansRewritten` preserve the application rule's types. -/
theorem humansRewritten_preserves_application_types :
    humansRewritten.RulesPreserveApplicationTypes := by
  intro h args rhs rw As R arr _
  rcases rw with rw | ⟨hl, hr⟩
  · exact rw.elim
  · cases hl
    subst hr
    obtain ⟨_, rfl⟩ := human_arrow rfl arr
    exact .sym (.inr (.inr (.inl ⟨rfl, rfl⟩)))

/-- A declaration admits `(Human Socrates)` at `TrueProp`, and its equation
rewrites it to `p`, which is only a `Prop`. -/
theorem trustDeclarations_not_preserves : ¬ Preserves .trustDeclarations := by
  intro h
  have adm : Policy.trustDeclarations.admit humansRewritten socrates (s "TrueProp") :=
    .declChecked rfl (.inl ⟨rfl, rfl, rfl⟩) (.cons (.sym (.inl ⟨rfl, rfl⟩)) .nil)
      (fun h => nomatch h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  exact p_not_trueProp (Γ := humansRewritten) rfl
    (h _ humansRewritten_preserves_application_types _ _ _ _ humansRewritten_hasArrow_human adm
      (.inr ⟨rfl, rfl⟩))

theorem trustDeclarations_monotoneInRules : MonotoneInRules .trustDeclarations :=
  fun _ extra _ _ adm => Typed.withRules rfl extra adm

/-! ## Declarations for values only -/

theorem valuesOnly_agree : Agree .valuesOnly := fun _ _ _ h => h

theorem valuesOnly_noMasking : NoMasking .valuesOnly :=
  fun _ _ _ _ ha t => Typed.args_of_hasArrow (.inr rfl) ha t

theorem valuesOnly_refines : Refines .valuesOnly := by
  intro Γ h args T normal ⟨As, R, arr, args⟩ d
  exact .declChecked rfl arr (ArgsTyped.ofIgnored args) (fun _ => normal) d

theorem valuesOnly_preserves : Preserves .valuesOnly := by
  intro Γ hΓ h args T rhs ha adm rw
  cases adm with
  | tuple n _ => exact absurd ha n
  | declUnchecked _ _ ca _ _ => cases ca
  | declChecked _ _ _ normal _ => exact absurd rw (normal rfl rhs)
  | app arr args => exact hΓ h _ rhs rw _ T arr args.toPermissive

/-- Adding `(= (Human Socrates) p)` makes `(Human Socrates)` a computation, and
its declaration stops counting. -/
theorem valuesOnly_not_monotoneInRules : ¬ MonotoneInRules .valuesOnly := by
  intro h
  have adm : Policy.valuesOnly.admit humans socrates (s "TrueProp") :=
    .declChecked rfl (.inl ⟨rfl, rfl, rfl⟩) humans_socrates_entity
      (fun _ => humans_normal_socrates) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have adm' := h humans (fun a b => a = socrates ∧ b = s "p") _ _ adm
  cases adm' with
  | tuple n _ => exact n humansRewritten_hasArrow_human
  | declUnchecked _ _ ca _ _ => cases ca
  | declChecked _ _ _ normal _ => exact normal rfl (s "p") (.inr ⟨rfl, rfl⟩)
  | app arr _ => exact socrates_no_trueProp_arrow (Γ := humansRewritten) rfl arr

/-! ## The trade-offs -/

/-- No policy honours declarations on values, stays honest for computations,
and keeps its admissions when equations are added. -/
theorem refine_preserve_monotone_incompatible (P : Policy) :
    ¬ (Refines P ∧ Preserves P ∧ MonotoneInRules P) := by
  rintro ⟨refines, preserves, monotone⟩
  have adm := refines humans "Human" [s "Socrates"] (s "TrueProp") humans_normal_socrates
    humans_plainArgs_socrates (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have adm' := monotone humans (fun a b => a = socrates ∧ b = s "p") _ _ adm
  exact p_not_trueProp (Γ := humansRewritten) rfl
    (preserves _ humansRewritten_preserves_application_types _ _ _ _
      humansRewritten_hasArrow_human adm' (.inr ⟨rfl, rfl⟩))

/-- `get-type` cannot report every declaration, agree with evaluation, and
have evaluation refuse ill-typed applications. -/
theorem reflect_reportAgrees_noMasking_incompatible (P : Policy) :
    ¬ (Reflects P ∧ ReportAgrees P ∧ AdmitNoMasking P) := by
  rintro ⟨reflects, agrees, noMasking⟩
  have report := reflects humans time (s "Prop") (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))
  obtain ⟨As, R, arr, args⟩ := noMasking _ _ _ _ humans_hasArrow_human (agrees _ _ _ report)
  obtain ⟨rfl, _⟩ := human_arrow rfl arr
  cases args with
  | cons t _ => exact time_not_entity rfl t

end Mettapedia.Languages.MeTTa.HE.DeclaredApplicationTypes
