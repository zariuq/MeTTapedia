import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EntryToQuery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundFragment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ExpressionTriangle

/-!
# Read words over a whole run

H2 compared one firing with one request: HE's equation query reads `regionRows (eqRegion …)` of
the program, PeTTa's complete call request reads the rows of its call region, each row with its
position (`ReadWordTriangle.read_word_triangle`). Here HE's whole run from its entry configuration
through the equation query (`EntryToQuery`) is compared with PeTTa's request word, with the same
observation: for each firing, the positioned rows it reads, and the region its complete
observation guards.

**What is compared.**

* *Rows, with order and multiplicity*: the concatenation, in firing order, of the positioned rows
  each firing reads (`heRows`), against the rows of PeTTa's complete call request (`pettaRows`),
  both in store order, each positioned row once.
* *Guards*: the region each firing observes completely. A region of no row is vacuous; a region
  that holds no row of the program but could hold one is an absence guard.

## Results

* `whole_run_rows` (**agreement on rows**): on the literal-head ground fragment of flat calls
  (`(f a₁ … aₙ)` of data atoms, every equation of the program with a literal left side, no
  declaration of `f` or of an `aᵢ`), HE's whole-run rows are exactly PeTTa's request rows. HE makes
  `8n + 6` firings before the query (`entryWord_length`, `n` arguments), each reading no row.
* `whole_run_guards` (**the exact difference**): every row an HE firing before the query guards is
  a declaration `(: a T)` of an atom `a` of the call, PeTTa's call request guards no declaration,
  and HE's entry guard is not vacuous: it holds `(: f T)` for every `T`. So the words differ by
  HE's absence guards over the call's declarations: the type-directed entry (the declarations of
  `f` and of the arguments, observed together) and one cast guard per atom of the call (`f` again,
  and each argument; a grounded argument's guard is vacuous).
* `declaration_race`: the difference is observable. A commit that adds `(: f T)` spoils HE's entry
  firing, while it commutes with PeTTa's call request, whose region it leaves unchanged.
* `Double.double_whole_run`: H2's tied instance completed. On `{(p a), (= (double 4) 8)}` HE's run
  from `ExpressionTriangle.entry` reaches the query, its fourteen firings before the query read no
  row, the query reads `(= (double 4) 8)` at position `1`, and PeTTa's run of the translation is
  the one request reading that row.

## Controls

* `separating_controls`: H2's two separating programs are kept: a variable-headed equation (HE
  answers `8`, PeTTa makes no request) and a `cons` list view in a head (PeTTa answers `5`, HE does
  not reduce). Both lie outside the fragment.
* `Double.double_declaration_race`: `(: double Number)` lands in HE's entry guard of `(double 4)`
  and outside PeTTa's call region.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace WholeRunWords

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (annotationType?)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst.typeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Frame Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings (rowSupply Row requests selectAt
  selectAt_located)
open MeTTaCalculus.OccurrenceCommits
open HEOnTheStep (Cell)
open ServiceFootprints EntryToQuery

/-! ## The two words -/

/-- **HE's whole-run read word**, from the entry through the equation query, under HE's raw lookup:
for each firing in order, the positioned rows it reads. -/
def heRows (atoms : List Atom) (f : String) (args : List Atom) : List (List (Atom × ℕ)) :=
  (entryWord rawDeclared f args ++
      [eqRegion [Atom.undefinedType] (.expression (.symbol f :: args)) Bindings.empty]).map
    fun ρ => regionRows ρ atoms

/-- **PeTTa's read word** for the call: its complete call request, H2's observation. -/
def pettaRows (atoms : List Atom) (f : String) (args : List Atom) : List (Atom × ℕ) :=
  (completeCall rowSupply f args (Row.load 0 atoms)).selection.read.map
    fun row => (row.atom, row.serial)

theorem tupleWord_length (D : DeclaredLookup) :
    ∀ (atom : Atom) (rest : List Atom), (tupleWord D (atom :: rest)).length = 8 * rest.length + 3
  | _, [] => rfl
  | atom, next :: rest => by
      simp only [tupleWord, List.length_append, List.length_cons, List.length_nil,
        tupleWord_length D next rest]
      omega

/-- **HE makes `8n + 6` firings before the query** for a call with `n` arguments. -/
theorem entryWord_length (D : DeclaredLookup) (f : String) (args : List Atom) :
    (entryWord D f args).length = 8 * args.length + 6 := by
  simp only [entryWord, List.length_cons, List.length_append, tupleWord_length D,
    List.length_nil]

theorem data_closed {a : Atom} (data : DataAtom a) : TypeSubst.typeVars a = [] := by
  cases data <;> rfl

/-- **Agreement on rows.** On the literal-head ground fragment of flat calls, HE's whole-run rows,
from the entry through the query, are PeTTa's request rows, in the same order and multiplicity; HE
makes `8n + 7` firings, and none before the query reads a row. -/
theorem whole_run_rows {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, DataAtom a)
    (undeclared : ∀ a ∈ Atom.symbol f :: args, ∀ row ∈ atoms, typeRegion a row = false)
    (program : ∀ row ∈ atoms, GroundFragment.LiteralHeads row) :
    (heRows atoms f args).flatten = pettaRows atoms f args ∧
      (heRows atoms f args).length = 8 * args.length + 7 ∧
      ∀ ρ ∈ entryWord rawDeclared f args, regionRows ρ atoms = [] := by
  have before := entry_rows_empty (atoms := atoms) undeclared
  have query : regionRows (eqRegion [Atom.undefinedType] (.expression (.symbol f :: args))
      Bindings.empty) atoms = pettaRows atoms f args :=
    GroundFragment.footprints_coincide atoms [Atom.undefinedType]
      (fun value member => data_closed (data value (List.mem_cons_of_mem _ member)))
      Completed.Frame.empty.certified.satisfiable program
  refine ⟨?_, ?_, before⟩
  · have empty : ((entryWord rawDeclared f args).map fun ρ => regionRows ρ atoms).flatten = [] := by
      apply List.flatten_eq_nil_iff.mpr
      intro rows member
      obtain ⟨ρ, inWord, rfl⟩ := List.mem_map.mp member
      exact before ρ inWord
    simp only [heRows, List.map_append, List.flatten_append, empty, List.nil_append, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, query]
  · simp only [heRows, List.length_map, List.length_append, entryWord_length, List.length_cons,
      List.length_nil]

/-! ## The guards -/

/-- A row of a type region is a declaration. -/
theorem typeRegion_declaration {a row : Atom} (inside : typeRegion a row = true) :
    ∃ type, row = .expression [.symbol ":", a, type] := by
  cases a with
  | symbol name =>
      obtain ⟨type, found⟩ := Option.isSome_iff_exists.mp inside
      exact ⟨type, Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType?_eq_some_iff.mp found⟩
  | var name => simp [typeRegion] at inside
  | grounded value => simp [typeRegion] at inside
  | expression children =>
      cases children with
      | nil => simp [typeRegion] at inside
      | cons head tail =>
          obtain ⟨type, found⟩ := Option.isSome_iff_exists.mp inside
          exact ⟨type, Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType?_eq_some_iff.mp found⟩

/-- Declarations of `f` are in `f`'s type region. -/
theorem declaration_typeRegion (f : String) (type : Atom) :
    typeRegion (.symbol f) (.expression [.symbol ":", .symbol f, type]) = true := by
  show (annotationType? (.symbol f) (.expression [.symbol ":", .symbol f, type])).isSome = true
  rw [Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType?_eq_some_iff.mpr rfl]
  rfl

/-- The declaration rows of the atoms of a call. -/
def Declares (f : String) (args : List Atom) (row : Atom) : Prop :=
  ∃ a ∈ Atom.symbol f :: args, typeRegion a row = true

/-- **The exact difference, as guards.** Every row a firing of HE's run before the query guards is
a declaration of an atom of the call; PeTTa's call request guards no declaration; and HE's entry
guard holds every declaration of `f`. -/
theorem whole_run_guards (f : String) (args : List Atom) :
    (∀ ρ ∈ entryWord rawDeclared f args, ∀ row, ρ row = true → Declares f args row) ∧
      (∀ row, Declares f args row → pettaCallRegion f args row = false) ∧
      ∀ type, interpretRegion rawDeclared (.expression (.symbol f :: args))
        (.expression [.symbol ":", .symbol f, type]) = true := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ member row inside
    simp only [entryWord, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with rfl | inTuple | rfl | rfl
    · change (typeRegion (.symbol f) row || (typeRegion (.symbol f) row ||
        args.any fun argument => typeRegion argument row)) = true at inside
      simp only [Bool.or_eq_true, List.any_eq_true] at inside
      rcases inside with head | head | ⟨a, member, found⟩
      · exact ⟨_, List.mem_cons_self, head⟩
      · exact ⟨_, List.mem_cons_self, head⟩
      · exact ⟨a, List.mem_cons_of_mem _ member, found⟩
    · rcases tupleWord_mem _ _ inTuple with rfl | ⟨a, inValues, rfl⟩
      · cases inside
      · exact ⟨a, inValues, inside⟩
    · cases inside
    · cases inside
  · rintro row ⟨a, _, inside⟩
    obtain ⟨type, rfl⟩ := typeRegion_declaration inside
    exact pettaCallRegion_not_equation (LiveEquations.equationOfRow_declaration a type)
  · intro type
    change (typeRegion (.symbol f) _ || _) = true
    rw [declaration_typeRegion]
    rfl

/-! ## The race on the guard -/

/-- **The difference is observable.** A commit that makes the row `(: f T)` spoils HE's entry firing
of the call (its observation guards `f`'s declarations), and the same declaration, added as a fresh
row of PeTTa's store, commutes with PeTTa's complete call request and leaves its region unchanged. -/
theorem declaration_race {C F A : Type} {f : String} {args : List Atom} (type : Atom)
    {sel : Selection (RowCell Atom C F A × ℕ)}
    {d : Commit (RowCell Atom C F A × ℕ) (RowCell Atom C F A)} {o : RowCell Atom C F A × ℕ}
    {position : ℕ} (made : o ∈ d.made)
    (labelled : o.1 = Cell.world (.expression [.symbol ":", .symbol f, type], position))
    (atoms : List Atom) (serial : ℕ)
    (fresh : (⟨serial, .self, .expression [.symbol ":", .symbol f, type]⟩ : Row) ∉
      (Row.load 0 atoms).toFinset) :
    Spoils Prod.fst d (PredicateQueryAdmission.commit sel
      [observation (interpretRegion rawDeclared (.expression (.symbol f :: args))) sel] ()) ∧
      Independent rowSupply.located (completeCall rowSupply f args (Row.load 0 atoms)).commit
        (Commit.makeOne ⟨serial, .self, .expression [.symbol ":", .symbol f, type]⟩ :
          Commit Row Atom) ∧
      regionOf rowSupply.located
          (fire (Row.load 0 atoms).toFinset
            (Commit.makeOne ⟨serial, .self, .expression [.symbol ":", .symbol f, type]⟩ :
              Commit Row Atom))
          (selectAt .self (pettaCallRegion f args)) =
        regionOf rowSupply.located (Row.load 0 atoms).toFinset
          (selectAt .self (pettaCallRegion f args)) := by
  have inside := (whole_run_guards f args).2.2 type
  have notCall : pettaCallRegion f args (.expression [.symbol ":", .symbol f, type]) = false :=
    (whole_run_guards f args).2.1 _ ⟨_, List.mem_cons_self, declaration_typeRegion f type⟩
  have outside : selectAt .self (pettaCallRegion f args)
      (rowSupply.located (⟨serial, .self, .expression [.symbol ":", .symbol f, type]⟩ : Row)) =
        false := by
    rw [selectAt_located]
    simp [rowSupply, notCall]
  have commutes := add_outside_region_commutes rowSupply.located
    (region := selectAt .self (pettaCallRegion f args)) fresh outside
  refine ⟨rowStep_spoiled_by_make_inside made labelled inside, ?_, commutes.2.2.2.2⟩
  rw [readRequest_commit]
  exact commutes.1

/-! ## Controls: H2's separating programs -/

/-- **H2's two separating programs, kept as controls.** A variable-headed equation `(= ($h 4) 8)`:
HE answers `8`, PeTTa makes no request and answers `(double 4)`. A `cons` list view in a head
`(= (f (cons 1 (2))) 5)`: PeTTa's region of `(f (1 2))` holds it and PeTTa answers `5`; HE's region
leaves it out and HE answers `(f (1 2))`. Neither program is in the literal-head fragment. -/
theorem separating_controls (live : List Atom) (incoming : Bindings) :
    ((Mettapedia.Languages.MeTTa.HE.evalAtom (Space.ofList [Instance.variableHead])
        HEOnTheStep.NamedDifferences.plus Instance.doubleFour Atom.undefinedType Bindings.empty
          40).map Prod.fst = [Instance.eight] ∧
      Streaming.values (Streaming.advance Instance.noFunctions 30
        (Streaming.enter { state := NamedSpaces.Store.new [Instance.variableHead] [] }
          Instance.doubleFour)) = [Instance.doubleFour] ∧
      requests rowSupply Instance.noFunctions 30
        (Streaming.enter { state := NamedSpaces.Store.new [Instance.variableHead] [] }
          Instance.doubleFour) (Row.load 0 [Instance.variableHead]) = [] ∧
      pettaCallRegion "double" [.grounded (.int 4)] Instance.variableHead = false) ∧
    (pettaCallRegion "f" [.expression [.grounded (.int 1), .grounded (.int 2)]]
        GroundFragment.Controls.consRow = true ∧
      eqRegion live GroundFragment.Controls.callList incoming GroundFragment.Controls.consRow =
        false ∧
      Streaming.values (Streaming.advance GroundFragment.Controls.consRegistry 30
        (Streaming.enter { state := NamedSpaces.Store.new [GroundFragment.Controls.consRow] [] }
          GroundFragment.Controls.callList)) = [.grounded (.int 5)] ∧
      (Mettapedia.Languages.MeTTa.HE.evalAtom (Space.ofList [GroundFragment.Controls.consRow])
        HEOnTheStep.NamedDifferences.plus GroundFragment.Controls.callList Atom.undefinedType
          Bindings.empty 40).map Prod.fst = [GroundFragment.Controls.callList]) :=
  ⟨Instance.variable_head_distinguishes, GroundFragment.Controls.cons_view_distinguishes live incoming⟩

/-! ## The tied instance: `(double 4)` -/

namespace Double

open Instance (doubleFour eight doubleEight program registry)
open RunsAsFirings.Controls (shape)

/-- HE's grounded dispatch with no host operation: every authored function goes to its equations. -/
def noHost : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

theorem noHost_double : ¬ noHost.executable (.symbol "double") := fun impossible => impossible

theorem double_data : ∀ a ∈ Atom.symbol "double" :: [Atom.grounded (.int 4)], DataAtom a := by
  intro a member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .symbol (by decide) (by decide)
  · exact .grounded _

theorem double_undeclared :
    ∀ a ∈ Atom.symbol "double" :: [Atom.grounded (.int 4)], ∀ row ∈ program,
      typeRegion a row = false := by
  intro a member row inProgram
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at inProgram
  rcases member with rfl | rfl <;> rcases inProgram with rfl | rfl <;> decide +kernel

theorem double_fragment : ∀ row ∈ program, GroundFragment.LiteralHeads row := by
  intro row member lhs rhs same
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp [RunsAsFirings.Controls.p] at same
  · cases same
    exact SpaceSemantics.Literal.constructor "double" [.grounded (.int 4)] (by decide)
      (fun item member => by
        simp only [List.mem_singleton] at member
        subst member
        exact SpaceSemantics.Literal.grounded _)

/-- **H2's tied instance over the whole run.** From H2's entry configuration of `(double 4)` on
`{(p a), (= (double 4) 8)}`, with HE's raw lookup, any policy and a dispatch for which `double` is
no host operation (`noHost` is one): HE's machine reaches the call with fourteen firings, none
reading a row; the equation query fires and reads `(= (double 4) 8)` at position `1`; HE's
whole-run rows are that row; and PeTTa's run of the translation is the one request reading it. -/
theorem double_whole_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "double")) (policy : Policy) :
    Traced rawDeclared dispatch policy (entry program doubleFour)
        (callConfig program "double" [.grounded (.int 4)])
        (entryWord rawDeclared "double" [.grounded (.int 4)]) ∧
      (entryWord rawDeclared "double" [.grounded (.int 4)]).length = 14 ∧
      (∀ ρ ∈ entryWord rawDeclared "double" [.grounded (.int 4)], regionRows ρ program = []) ∧
      (∃ works, HEStep dispatch rawDeclared.lookup policy
          (callConfig program "double" [.grounded (.int 4)])
          (queryTarget program "double" [.grounded (.int 4)] works) ∧
        regionRows (heRegionD rawDeclared policy
            (callConfig program "double" [.grounded (.int 4)]).control
            (queryTarget program "double" [.grounded (.int 4)] works).control) program =
          [(doubleEight, 1)]) ∧
      (heRows program "double" [.grounded (.int 4)]).flatten = [(doubleEight, 1)] ∧
      (pettaWord registry program doubleFour 30).map shape =
        [([], [⟨1, .self, doubleEight⟩], [])] := by
  have untyped : (Space.ofList program).atoms.filter (typeRegion (.symbol "double")) = [] := by
    decide +kernel
  have notInstruction :
      Minimal.embeddedInstruction (.expression [.symbol "double", .grounded (.int 4)]) = false := by
    decide +kernel
  obtain ⟨_, traced, works, _, fires, region⟩ :=
    entry_reaches_equation_query (dispatch := dispatch) (policy := policy) rawDeclared raw_answers
      double_data untyped notHost notInstruction
  have rows := whole_run_rows double_data double_undeclared double_fragment
  have petta : pettaRows program "double" [.grounded (.int 4)] = [(doubleEight, 1)] :=
    (Instance.triangle_double []).2.1
  refine ⟨traced, (entryWord_length _ _ _).trans rfl, rows.2.2, ⟨works, fires, ?_⟩,
    rows.1.trans petta,
    (Tied.double_expression_triangle (dispatch := dispatch) (lookup := Completed.rawLookup)
      (policy := policy)).2.1⟩
  rw [region]
  exact Tied.region_rows_any [Atom.undefinedType] Completed.Frame.empty

/-- `(: double Number)`. -/
def declareDouble : Atom := .expression [.symbol ":", .symbol "double", .symbol "Number"]

/-- **The declaration race on `(double 4)`.** `(: double Number)` is inside HE's entry guard of
`(double 4)` and outside PeTTa's call region; added as the fresh row `2` of PeTTa's store it
commutes with PeTTa's call request, while a commit making it spoils HE's entry firing. -/
theorem double_declaration_race {C F A : Type} {sel : Selection (RowCell Atom C F A × ℕ)}
    {d : Commit (RowCell Atom C F A × ℕ) (RowCell Atom C F A)} {o : RowCell Atom C F A × ℕ}
    (made : o ∈ d.made) (labelled : o.1 = Cell.world (declareDouble, 2)) :
    interpretRegion rawDeclared doubleFour declareDouble = true ∧
      pettaCallRegion "double" [.grounded (.int 4)] declareDouble = false ∧
      Spoils Prod.fst d (PredicateQueryAdmission.commit sel
        [observation (interpretRegion rawDeclared doubleFour) sel] ()) ∧
      Independent rowSupply.located
        (completeCall rowSupply "double" [.grounded (.int 4)] (Row.load 0 program)).commit
        (Commit.makeOne ⟨2, .self, declareDouble⟩ : Commit Row Atom) := by
  have fresh : (⟨2, .self, declareDouble⟩ : Row) ∉ (Row.load 0 program).toFinset := by
    decide +kernel
  have race := declaration_race (args := [.grounded (.int 4)]) (sel := sel) (.symbol "Number") made
    labelled program 2 fresh
  exact ⟨(whole_run_guards "double" [.grounded (.int 4)]).2.2 _, by decide +kernel, race.1, race.2.1⟩

end Double

#print axioms tupleWord_length
#print axioms entryWord_length
#print axioms whole_run_rows
#print axioms whole_run_guards
#print axioms declaration_race
#print axioms separating_controls
#print axioms Double.double_whole_run
#print axioms Double.double_declaration_race

end WholeRunWords

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
