import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.WellFormed

/-!
# The surface: MeTTa text, declarations, and the elaborations that insert holding and running

**Text** is data of the MeTTa signature `MSig`: symbols, integers, tuples `(f a₁ … aₙ)`, an object
binder `lam` (so text has binders, and equations may have second-order patterns under it), and two
marks, `(hold a)` and `(run a)`. A *position* is an argument of a tuple whose head is a symbol. A
position is *annotated* when its text is a mark.

**What elaboration decides** (`Params`, never fixed here):
* the strategy at each undeclared position: data, by value, by name, or by need (`strategy`, a function of
  the head and the position, so mixtures by position are instances);
* `heldRuns`: whether held text (a parameter declared `Atom`) runs when it reaches a position that
  wants a value, or stays data;
* `heldResultComputes`: whether the body of an equation of a function declared with a held result is
  computed or returned as written.

Declarations (`Decl`) give a type to each parameter and to the result; the type discipline
(`Typing`) says which types hold and what a value type admits. Declared value types are checked
(`check`); held types pass text as written.

**The elaboration** (`elabText`) reads text at a position that wants a value: a mark decides by
itself; an unannotated argument is decided by its declaration, or else by the strategy; a variable
is decided by how its parameter was passed. Every reading is this one function at different
parameters; only unannotated positions consult them (`Annotated`, and the law in `Laws`). The
program's reading of text as code at run time (`reading`, the program's `reflect`) is the same
function, with every variable taken as a value and its arrows at sites below `[2, k]`, where `k` is
past every code site of a name of the text it reads (`freshIndex`). So the arrows of code made at run
time never rename a name of the text they read (`ElaborationHygiene.reading_hygienic`); a reading that
put them at the same sites at every run would (`ExampleCapture`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

/-! ## The MeTTa signature -/

/-- Operators of MeTTa text (one sort). -/
inductive MOp : Unit → Type where
  | sym (name : String) : MOp ()
  | num (value : Int) : MOp ()
  | tup (length : ℕ) : MOp ()
  | lam : MOp ()
  | hold : MOp ()
  | run : MOp ()

/-- Arities: symbols and numbers are constants, a tuple has its elements, `lam` binds one variable
in its body, the marks have one argument. -/
def MOp.arity : {s : Unit} → MOp s → List (List Unit × Unit)
  | _, .sym _ => []
  | _, .num _ => []
  | _, .tup n => List.replicate n ([], ())
  | _, .lam => [([()], ())]
  | _, .hold => [([], ())]
  | _, .run => [([], ())]

/-- **The MeTTa signature** with an object binder. -/
abbrev MSig : Signature := ⟨Unit, MOp, MOp.arity⟩

/-- An injective code of the operators. -/
def MOp.code : {s : Unit} → MOp s → String ⊕ Int ⊕ ℕ ⊕ ℕ
  | _, .sym n => .inl n
  | _, .num k => .inr (.inl k)
  | _, .tup n => .inr (.inr (.inl n))
  | _, .lam => .inr (.inr (.inr 0))
  | _, .hold => .inr (.inr (.inr 1))
  | _, .run => .inr (.inr (.inr 2))

theorem MOp.code_injective {s : Unit} : Function.Injective (MOp.code (s := s)) := by
  intro a b same
  cases a <;> cases b <;> simp_all [MOp.code]

instance (s : Unit) : DecidableEq (MOp s) := MOp.code_injective.decidableEq

/-- The empty family of names: closed readings. -/
def noNames : Empty → MetaArity MSig := fun impossible => nomatch impossible

/-- Keys of names in MeTTa programs: a site (a path), an index, an arity. -/
structure MKey where
  site : List ℕ
  index : ℕ
  arity : MetaArity MSig
  deriving DecidableEq

/-- The key system of MeTTa programs. -/
abbrev mkeys : Keys MSig := ⟨MKey, List ℕ, MKey.site, MKey.arity, inferInstance⟩

/-- MeTTa data with names. -/
abbrev MData := Data mkeys [] ()

/-- Closed MeTTa data. -/
abbrev MClosed := Term MSig [] ()

/-- A symbol. -/
def sym (name : String) : MData := .op (.inl (.sym name)) .nil

/-- An integer. -/
def num (value : Int) : MData := .op (.inl (.num value)) .nil

/-- The elements of a tuple. -/
def tupleArgs : (ts : List MData) → Args (signature MSig (fam mkeys)) (List.replicate ts.length ([], ())) []
  | [] => .nil
  | t :: ts => .cons t (tupleArgs ts)

/-- A tuple. -/
def tuple (ts : List MData) : MData := .op (.inl (.tup ts.length)) (tupleArgs ts)

/-- The mark `(hold a)`. -/
def hold (a : MData) : MData := .op (.inl .hold) (.cons a .nil)

/-- The mark `(run a)`. -/
def run (a : MData) : MData := .op (.inl .run) (.cons a .nil)

/-- A first-order name of a site, unopened. -/
def mvar (site : List ℕ) (index : ℕ) : MData :=
  .op (.inr (.mk ⟨[], ⟨site, index, ([], ())⟩⟩)) .nil

/-- Closed versions. -/
def csym (name : String) : MClosed := .op (.sym name) .nil
def cnum (value : Int) : MClosed := .op (.num value) .nil
def ctupleArgs : (ts : List MClosed) → Args MSig (List.replicate ts.length ([], ())) []
  | [] => .nil
  | t :: ts => .cons t (ctupleArgs ts)
def ctuple (ts : List MClosed) : MClosed := .op (.tup ts.length) (ctupleArgs ts)

/-! ## Types, declarations, parameters -/

/-- Surface types: the unknown type, held text, held text of a stated type, and value types. -/
inductive MTy where
  | undefined
  | atom
  | code (name : String)
  | value (name : String)
  deriving DecidableEq

/-- Held types pass text as written. -/
def MTy.held : MTy → Bool
  | .atom => true
  | .code _ => true
  | _ => false

/-- A type discipline for the surface: what each type admits of a closed value, with its laws (the
unknown type and the held types admit everything; checks are made only at value types). -/
structure Typing where
  admits : MTy → MClosed → Prop
  admits_undefined : ∀ g, admits .undefined g
  admits_held : ∀ T g, T.held = true → admits T g

/-- The discipline as the core asks it. -/
def Typing.discipline (τ : Typing) : Discipline MSig [] () := ⟨MTy, τ.admits⟩

/-- **The trivial discipline**: every type admits everything. -/
def untyped : Typing := ⟨fun _ _ => True, fun _ => trivial, fun _ _ _ => trivial⟩

/-- **A real discipline**: `Number` admits integers, `Bool` admits `True` and `False`; other value
types are open (they admit everything). -/
def numbers : Typing where
  admits
    | .value "Number", g => ∃ k, g = cnum k
    | .value "Bool", g => g = csym "True" ∨ g = csym "False"
    | _, _ => True
  admits_undefined _ := trivial
  admits_held T g held := by
    cases T with
    | undefined => trivial
    | atom => trivial
    | code _ => trivial
    | value name => simp [MTy.held] at held

/-- A declaration `(: f (-> T₁ … Tₙ R))`. -/
structure Decl where
  head : String
  params : List MTy
  result : MTy
  deriving DecidableEq

/-- The declaration of a head, if any (the first). -/
def declOf (decls : List Decl) (f : String) : Option Decl := decls.find? fun d => d.head == f

/-- **Declarations are consistent**: two declarations of one head agree on the arity and on which
parameters and result hold (so no position is held under one declaration and evaluated under
another). Their value types may differ (an overloaded head); the elaboration reads the first
declaration of a head, so for such heads it depends on the order of the declarations
(`LawDeclarations.overloaded_order`), and for unambiguous ones it does not
(`LawDeclarations.elaborate_perm_decls`). -/
def DeclarationsConsistent (decls : List Decl) : Prop :=
  ∀ d ∈ decls, ∀ d' ∈ decls, d.head = d'.head →
    d.params.map MTy.held = d'.params.map MTy.held ∧ d.result.held = d'.result.held

instance (decls : List Decl) : Decidable (DeclarationsConsistent decls) := by
  unfold DeclarationsConsistent; infer_instance

/-- How an undeclared position is passed. -/
inductive Mode where
  | data
  | value
  | name
  | need
  deriving DecidableEq

/-- **The parameters of the reference semantics.** -/
structure Params where
  strategy : String → ℕ → Mode
  heldRuns : Bool
  heldResultComputes : Bool

/-- How a variable was passed, which decides what it does at a position that wants a value. -/
inductive VarMode where
  | value
  | held
  | name
  | need
  deriving DecidableEq

/-! ## Viewing text -/

/-- Text as the elaboration reads it. -/
inductive View where
  | holdMark (orig inside : MData)
  | runMark (orig : MData) (inner : View)
  | var (orig : MData) (name : Name mkeys)
  | symbol (orig : MData) (name : String)
  | call (orig : MData) (head : String) (args : List View)
  | inert (orig : MData)
  | other (orig : MData)

/-- The text a view was read from. -/
def View.orig : View → MData
  | .holdMark o _ => o
  | .runMark o _ => o
  | .var o _ => o
  | .symbol o _ => o
  | .call o _ _ => o
  | .inert o => o
  | .other o => o

/-- A term at a context that is empty, as text. -/
def atTop {Δ : Ctx MSig} {s : Unit} (h : Δ = []) (t : Term (signature MSig (fam mkeys)) Δ s) : MData := by
  subst h
  exact t

mutual
/-- Read text at the empty context (the proof `h` lets the reading recurse structurally). -/
def viewAtWith (activateHeld skipHold : Bool) {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) (h : Δ = []) : View :=
  match t with
  | .op (.inl .hold) (.cons u .nil) =>
      if skipHold then viewAtWith activateHeld false u ((List.nil_append Δ).trans h)
      else .holdMark (atTop h t) (atTop ((List.nil_append Δ).trans h) u)
  | .op (.inl .run) (.cons u .nil) => .runMark (atTop h t) (viewAtWith activateHeld activateHeld u ((List.nil_append Δ).trans h))
  | .op (.inl (.tup _)) args =>
      match viewArgsAtWith activateHeld args h with
      | .symbol _ f :: rest => .call (atTop h t) f rest
      | _ => .other (atTop h t)
  | .op (.inl (.sym f)) _ => .symbol (atTop h t) f
  | .op (.inr (.mk x)) _ => .var (atTop h t) x
  | _ => .inert (atTop h t)

/-- Read the elements of a tuple; elements under binders are not positions. -/
def viewArgsAtWith (activateHeld : Bool) {as : List (List Unit × Unit)} {Δ : Ctx MSig}
    (args : Args (signature MSig (fam mkeys)) as Δ) (h : Δ = []) : List View :=
  match args with
  | .nil => []
  | .cons (bs := bs) hd tl =>
      if hb : bs = [] then viewAtWith activateHeld false hd (by subst hb; exact h) :: viewArgsAtWith activateHeld tl h
      else viewArgsAtWith activateHeld tl h
end

abbrev viewAt {Δ : Ctx MSig} {s : Unit} := @viewAtWith false false Δ s
abbrev viewArgsAt {as : List (List Unit × Unit)} {Δ : Ctx MSig} := @viewArgsAtWith false as Δ

/-- Read text. -/
def view (t : MData) : View := viewAt t rfl

/-! ## Elaboration -/

variable (π : Params) (decls : List Decl)

/-- The let-bound name of the position at `site`. -/
def slot (site : List ℕ) : MData := mvar site 0

/-- A variable at a position that wants a value. -/
def varAt (mode : VarMode) (x : MData) : Comp mkeys [] () MTy :=
  match mode with
  | .value => .ret x
  | .held => if π.heldRuns then .run x else .ret x
  | .name => .run x
  | .need => .force x

/-- How the argument at position `i` of `f` is passed. -/
inductive Pass where
  | text (datum : MData)
  | evaluate (check : Option MTy)
  | byName
  | byNeed

/-- The passing of an argument: a mark decides; else the declaration; else the strategy. -/
def passOf (f : String) (i : ℕ) (a : View) : Pass :=
  match a with
  | .holdMark _ u => .text u
  | .runMark _ _ => .evaluate none
  | _ =>
    match declOf decls f with
    | some d =>
        match d.params[i]? with
        | some T => if T.held then .text a.orig else
            match T with
            | .undefined => match π.strategy f i with
                | .data => .text a.orig
                | .value => .evaluate none
                | .name => .byName
                | .need => .byNeed
            | _ => .evaluate (some T)
        | none => match π.strategy f i with
            | .data => .text a.orig
            | .value => .evaluate none
            | .name => .byName
            | .need => .byNeed
    | none => match π.strategy f i with
        | .data => .text a.orig
        | .value => .evaluate none
        | .name => .byName
        | .need => .byNeed

/-- The call of `f` on its passed arguments, checked against a declared value result. -/
def finish (f : String) (args : List MData) : Comp mkeys [] () MTy :=
  match declOf decls f with
  | some d => if d.result.held || d.result == .undefined then .apply (tuple (sym f :: args))
      else .check d.result (.apply (tuple (sym f :: args)))
  | none => .apply (tuple (sym f :: args))

mutual
/-- **Text at a position that wants a value.** `modes` says how each variable was passed; `path` makes
the sites of the inserted arrows distinct. -/
def elabText (modes : Name mkeys → VarMode) (path : List ℕ) : View → Comp mkeys [] () MTy
  | .holdMark _ u => .ret u
  | .runMark _ inner =>
      match inner with
      | .var o _ => .run o
      | other => elabText modes path other
  | .var o x => varAt π (modes x) o
  | .symbol o _ => .apply o
  | .call _ f args => elabArgs modes path f 0 args []
  | .inert o => .ret o
  | .other o => .apply o

/-- The arguments of a call, left to right; `done` holds the passed data so far, newest first. -/
def elabArgs (modes : Name mkeys → VarMode) (path : List ℕ) (f : String) (i : ℕ) :
    List View → List MData → Comp mkeys [] () MTy
  | [], done => finish decls f done.reverse
  | a :: rest, done =>
      match passOf π decls f i a with
      | .text u => elabArgs modes path f (i + 1) rest (u :: done)
      | .byName => elabArgs modes path f (i + 1) rest (a.orig :: done)
      | .evaluate none =>
          .let_ (path ++ [i]) (slot (path ++ [i])) (elabText modes (path ++ [i]) a)
            (elabArgs modes path f (i + 1) rest (slot (path ++ [i]) :: done))
      | .evaluate (some T) =>
          .let_ (path ++ [i]) (slot (path ++ [i])) (.check T (elabText modes (path ++ [i]) a))
            (elabArgs modes path f (i + 1) rest (slot (path ++ [i]) :: done))
      | .byNeed =>
          .delay (path ++ [i]) (slot (path ++ [i])) (elabText modes (path ++ [i]) a)
            (elabArgs modes path f (i + 1) rest (slot (path ++ [i]) :: done))
end

/-! ## Surface programs -/

/-- Surface computations: text at a value position, and the language's constructs. -/
inductive SComp where
  | text (t : MData)
  | let_ (site : List ℕ) (pattern : MData) (bound body : SComp)
  | choice (left right : SComp)
  | fail
  | query (space pattern : MData) (body : SComp)
  | add (space atom : MData) (body : SComp)
  | remove (space atom : MData) (body : SComp)
  | new (site : List ℕ) (handle : MData) (body : SComp)

/-- Elaborate a surface computation; let-bound names are values. -/
def elabComp (modes : Name mkeys → VarMode) (path : List ℕ) (source : SComp)
    (readText : MData → View := view) : Comp mkeys [] () MTy :=
  match source with
  | .text t => elabText π decls modes path (readText t)
  | .let_ s p c k => .let_ s p (elabComp modes (path ++ [0]) c readText) (elabComp modes (path ++ [1]) k readText)
  | .choice c d => .choice (elabComp modes (path ++ [0]) c readText) (elabComp modes (path ++ [1]) d readText)
  | .fail => .fail
  | .query sp p k => .query sp p (elabComp modes (path ++ [0]) k readText)
  | .add sp t k => .add sp t (elabComp modes (path ++ [0]) k readText)
  | .remove sp t k => .remove sp t (elabComp modes (path ++ [0]) k readText)
  | .new s x k => .new s x (elabComp modes (path ++ [0]) k readText)

/-- A surface equation `(= (f p₁ … pₙ) body)` at its site. -/
structure SEquation where
  site : List ℕ
  head : String
  params : List MData
  body : SComp

/-- How the parameter at position `i` of `f` is passed, for the variables it binds. -/
def paramMode (f : String) (i : ℕ) : VarMode :=
  match passOf π decls f i (.inert (sym "")) with
  | .text _ => .held
  | .evaluate _ => .value
  | .byName => .name
  | .byNeed => .need

/-- The modes of the variables of an equation's parameters (a variable of no parameter is a value). -/
def paramModes (e : SEquation) (x : Name mkeys) : VarMode :=
  match (e.params.zipIdx.find? fun pi => decide (x ∈ support pi.1)) with
  | some (_, i) => paramMode π decls e.head i
  | none => .value

/-- The body of an equation: an explicit mark decides; a held result returns unannotated text as
written unless the reading computes it. -/
def elabBody (e : SEquation) : Comp mkeys [] () MTy :=
  match e.body with
  | .text t =>
      match view t with
      | .holdMark _ u => .ret u
      | .runMark _ inner => elabText π decls (paramModes π decls e) (1 :: e.site) (.runMark t inner)
      | v =>
          match declOf decls e.head with
          | some d => if d.result.held && !π.heldResultComputes then .ret t
              else elabText π decls (paramModes π decls e) (1 :: e.site) v
          | none => elabText π decls (paramModes π decls e) (1 :: e.site) v
  | b => elabComp π decls (paramModes π decls e) (1 :: e.site) b

/-- An elaborated equation. -/
def elabEquation (e : SEquation) : Equation mkeys [] () MTy :=
  ⟨e.site, tuple (sym e.head :: e.params), elabBody π decls e⟩

/-- A surface program: declarations and equations. -/
structure SProgram where
  decls : List Decl
  equations : List SEquation

/-! ## Reading text as code at run time -/

/-- How far a name's site reaches into the code sites `[2, k, …]`: `k + 1` there, `0` elsewhere. -/
def codeIndex (x : Name mkeys) : ℕ :=
  match x.key.site with
  | 2 :: k :: _ => k + 1
  | _ => 0

/-- **An index past every code site of the names of a text.** -/
def freshIndex (t : MData) : ℕ := ((support t).map codeIndex).foldr max 0

/-- **The reading of text as code at run time**: the elaboration with every variable a value, its
arrows at sites below `[2, freshIndex t]`, which no name of the text has. -/
def reading (t : MData) : Comp mkeys [] () MTy :=
  elabText π decls (fun _ => .value) [2, freshIndex t] (view t)

/-- **The elaborated program** under the parameters: its equations, and the reading of text as code at
run time. -/
def elaborate (P : SProgram) : Program mkeys [] () MTy :=
  ⟨P.equations.map (elabEquation π P.decls), reading π P.decls⟩

/-- A query: elaborated at the sites below `[3]`, its variables values. -/
def elabQuery (P : SProgram) (q : SComp) : Comp mkeys [] () MTy :=
  elabComp π P.decls (fun _ => .value) [3] q

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration
