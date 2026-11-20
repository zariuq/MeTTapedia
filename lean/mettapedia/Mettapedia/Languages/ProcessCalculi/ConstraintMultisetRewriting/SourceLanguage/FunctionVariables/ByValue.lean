import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Hosted
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleTwiceAsWritten
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.ExampleUnknownHead

/-!
# The elaboration by value, beside `Elaboration.elaborate`

`elaborateByValue` and `elabQueryByValue` are the elaboration of surface programs and queries under the
clause by value: a tuple whose head is not a symbol has its head read as a position that wants a value
and each argument evaluated at its own arrow (`Clause.byValue`). `Elaboration.elaborate` is unchanged
and is the same construction under the clause that calls such a tuple as it stands
(`elaborateH_asWritten`).

**Where the two agree** (`elaborateByValue_agrees`, `elabQueryByValue_agrees`): on every program and query
in which no tuple with a head that is not a symbol stands at a position the reading reaches
(`SSymbolHeaded`), under every reading and every declaration. The instances are the program of `inc`
alone and the query `(twice inc Z)` (`inc_agrees`, `twice_query_agrees`).

**Where they differ** (`twice_compared`): on the text

```
(= (inc $n) (S $n))
(= (twice $f $x) ($f ($f $x)))
!(twice inc Z)
```

the elaborated programs differ (`twice_programs_differ`), a quiescent run of the elaboration by value
ends with the bag `{(S (S Z))}`, and a quiescent run of `Elaboration.elaborate`'s program ends with the
bag `{(S (inc Z))}`.

**On the run theorems of the translation** (`byValue_runs_forward`, `byValue_answers_hosted`,
`byValue_runs_reflected`): for a program without declarations, read by value, whose bodies are text
without `run` marks and whose equations are scoped under `Elaboration.elaborate`, every run of the
elaboration by value and a query text corresponds to runs of the step, both ways, with the answers of
every reached configuration those of a frontier reached by the step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Elaboration
open Hosting

/-! ## The definition -/

/-- **The elaborated program by value**: `Elaboration.elaborate` with the clause by value for tuples
whose head is not a symbol. -/
abbrev elaborateByValue (π : Params) (P : SProgram) : Program mkeys [] () MTy := elaborateH .byValue π P

/-- **A query by value.** -/
abbrev elabQueryByValue (π : Params) (P : SProgram) (q : SComp) : Comp mkeys [] () MTy :=
  elabQueryH .byValue π P q

/-! ## Where the two elaborations agree -/

/-- No tuple with a head that is not a symbol stands at a position the reading of the surface
computation reaches. -/
def SSymbolHeaded : SComp → Prop
  | .text t => SymbolHeaded (hview t)
  | .let_ _ _ c k => SSymbolHeaded c ∧ SSymbolHeaded k
  | .choice c d => SSymbolHeaded c ∧ SSymbolHeaded d
  | .fail => True
  | .query _ _ k => SSymbolHeaded k
  | .add _ _ k => SSymbolHeaded k
  | .remove _ _ k => SSymbolHeaded k
  | .new _ _ k => SSymbolHeaded k

theorem elabCompH_eq (cl : Clause) (π : Params) (decls : List Decl) (modes : Name mkeys → VarMode) :
    (path : List ℕ) → (c : SComp) → SSymbolHeaded c →
      elabCompH cl π decls modes path c = elabComp π decls modes path c
  | path, .text t, headed => by
      simp only [elabCompH, elabComp]
      rw [← forget_hview t]
      exact elabH_eq cl π decls modes path (hview t) (.inr headed)
  | path, .let_ s p c k, ⟨hc, hk⟩ => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) c hc,
        elabCompH_eq cl π decls modes (path ++ [1]) k hk]
  | path, .choice c d, ⟨hc, hd⟩ => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) c hc,
        elabCompH_eq cl π decls modes (path ++ [1]) d hd]
  | _, .fail, _ => rfl
  | path, .query sp p k, hk => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) k hk]
  | path, .add sp t k, hk => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) k hk]
  | path, .remove sp t k, hk => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) k hk]
  | path, .new s x k, hk => by
      simp only [elabCompH, elabComp, elabCompH_eq cl π decls modes (path ++ [0]) k hk]

/-- An equation whose body has no such tuple elaborates as `Elaboration.elabEquation` does, under every
clause. -/
theorem elabEquationH_eq (cl : Clause) (π : Params) (decls : List Decl) (e : SEquation)
    (headed : SSymbolHeaded e.body) : elabEquationH cl π decls e = elabEquation π decls e := by
  unfold elabEquationH elabEquation elabBodyH elabBody
  congr 1
  rcases e with ⟨site, head, params, body⟩
  cases body with
  | text t =>
      dsimp only
      have headed' : SymbolHeaded (hview t) := headed
      rw [← forget_hview t]
      generalize hview t = v at headed' ⊢
      have same := fun (modes : Name mkeys → VarMode) (path : List ℕ) =>
        elabH_eq cl π decls modes path v (.inr headed')
      cases v with
      | holdMark o u => rfl
      | runMark o inner => exact elabH_eq cl π decls _ _ (.runMark t inner) (.inr headed')
      | var o x => simp only [same, HView.forget]; rfl
      | symbol o f => simp only [same, HView.forget]; rfl
      | call o f args => simp only [same, HView.forget]; rfl
      | inert o => simp only [same, HView.forget]; rfl
      | other o elements => simp only [same, HView.forget]; rfl
  | let_ s p c k => exact elabCompH_eq cl π decls _ _ _ headed
  | choice c d => exact elabCompH_eq cl π decls _ _ _ headed
  | fail => rfl
  | query sp p k => exact elabCompH_eq cl π decls _ _ _ headed
  | add sp t k => exact elabCompH_eq cl π decls _ _ _ headed
  | remove sp t k => exact elabCompH_eq cl π decls _ _ _ headed
  | new s x k => exact elabCompH_eq cl π decls _ _ _ headed

/-- **Every clause gives `Elaboration.elaborate`'s program** when no equation's body has a tuple with a
head that is not a symbol at a position the reading reaches. -/
theorem elaborateH_eq (cl : Clause) (π : Params) (P : SProgram)
    (headed : ∀ e ∈ P.equations, SSymbolHeaded e.body) : elaborateH cl π P = elaborate π P := by
  simp only [elaborateH, elaborate]
  congr 1
  exact List.map_congr_left fun e member => elabEquationH_eq cl π P.decls e (headed e member)

/-- **Where the two elaborations of programs agree.** -/
theorem elaborateByValue_agrees (π : Params) (P : SProgram)
    (headed : ∀ e ∈ P.equations, SSymbolHeaded e.body) : elaborateByValue π P = elaborate π P :=
  elaborateH_eq .byValue π P headed

/-- **Where the two elaborations of queries agree.** -/
theorem elabQueryByValue_agrees (π : Params) (P : SProgram) (q : SComp) (headed : SSymbolHeaded q) :
    elabQueryByValue π P q = elabQuery π P q :=
  elabCompH_eq .byValue π P.decls _ [3] q headed

mutual
/-- No tuple with a head that is not a symbol at a reached position: decided. -/
def decSymbolHeaded : (v : HView) → Decidable (SymbolHeaded v)
  | .holdMark _ _ => isTrue trivial
  | .runMark _ inner => decSymbolHeaded inner
  | .var _ _ => isTrue trivial
  | .symbol _ _ => isTrue trivial
  | .call _ _ args => decSymbolHeadedArgs args
  | .inert _ => isTrue trivial
  | .other _ [] => isTrue trivial
  | .other _ (_ :: _) => isFalse (by simp [SymbolHeaded])

def decSymbolHeadedArgs : (args : List HView) → Decidable (SymbolHeaded.SymbolHeadedArgs args)
  | [] => isTrue trivial
  | a :: rest =>
      letI := decSymbolHeaded a
      letI := decSymbolHeadedArgs rest
      inferInstanceAs (Decidable (_ ∧ _))
end

instance (v : HView) : Decidable (SymbolHeaded v) := decSymbolHeaded v

/-- The program of `inc` alone: the two elaborations agree on it. -/
theorem inc_agrees :
    elaborateByValue ExampleTwice.byValue ExampleUnknownHead.surface =
      elaborate ExampleTwice.byValue ExampleUnknownHead.surface :=
  elaborateByValue_agrees _ _
    (List.forall_mem_cons.mpr ⟨show SymbolHeaded _ by decide, fun _ member => nomatch member⟩)

/-- The query `(twice inc Z)`: the two elaborations agree on it. -/
theorem twice_query_agrees :
    elabQueryByValue ExampleTwice.byValue ExampleTwice.surface (.text (tuple [sym "twice", sym "inc", sym "Z"])) =
      elabQuery ExampleTwice.byValue ExampleTwice.surface (.text (tuple [sym "twice", sym "inc", sym "Z"])) :=
  elabQueryByValue_agrees _ _ _ (show SymbolHeaded _ by decide)

/-! ## Where they differ -/

open ExampleTwice in
/-- **The two elaborations make different programs of the text of `twice`**: the body of `twice` is not
text without a tuple whose head is not a symbol. -/
theorem twice_programs_differ :
    (elaborateByValue byValue surface).equations ≠ (elaborate byValue surface).equations := by
  rw [show (elaborateByValue byValue surface).equations = [incE, twiceE] from program_eq,
    ← ExampleTwiceAsWritten.program_is_elaborate, ExampleTwiceAsWritten.program_eq]
  intro same
  have atTwice := congrArg Equation.rhs (List.cons.inj (List.cons.inj same).2).1
  simp [twiceE, ExampleTwiceAsWritten.twiceE] at atTwice

open ExampleTwice in
/-- **The text of `twice` under the two elaborations.** A quiescent run of the elaboration by value ends
with the bag `{(S (S Z))}`; a quiescent run of `Elaboration.elaborate`'s program ends with the bag
`{(S (inc Z))}`; the two bags differ. -/
theorem twice_compared :
    (∃ C : Config mkeys [] () MTy,
      Runs D (elaborateByValue byValue surface) supply
        (Config.initial sp
          (elabQueryByValue byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])))) C ∧
      Config.Quiescent (D := D) (elaborateByValue byValue surface) supply C ∧
      Config.answers (D := D) C = {{ctuple [csym "S", ctuple [csym "S", csym "Z"]]}}) ∧
    (∃ C : Config mkeys [] () MTy,
      Runs D (elaborate byValue surface) supply
        (Config.initial sp (elabQuery byValue surface (.text (tuple [sym "twice", sym "inc", sym "Z"])))) C ∧
      Config.Quiescent (D := D) (elaborate byValue surface) supply C ∧
      Config.answers (D := D) C = {{ctuple [csym "S", ctuple [csym "inc", csym "Z"]]}}) ∧
    ({{ctuple [csym "S", ctuple [csym "S", csym "Z"]]}} : Multiset (Set MClosed)) ≠
      {{ctuple [csym "S", ctuple [csym "inc", csym "Z"]]}} := by
  refine ⟨runs_answers, ?_, fun same => ExampleTwiceAsWritten.bags_differ same.symm⟩
  rw [← ExampleTwiceAsWritten.program_is_elaborate]
  exact ExampleTwiceAsWritten.runs_answers

/-! ## On the run theorems of the translation -/

variable (N : Nodes MSig [] ()) (τ : Typing) (supply : ℕ → MClosed)
  (spaces : MClosed → Multiset (Row mkeys [] ())) (π : Params)

/-- **Every source run of a program by value is followed by runs of the step.** -/
theorem byValue_runs_forward (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram)
    (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {C : Config mkeys [] () MTy}
    (runs : Runs τ.discipline (elaborateByValue π P) supply
      (Config.initial spaces (elabQueryByValue π P (.text t))) C) :
    ∃ L, ArrowFrontier (D := τ.discipline) N (elaborateByValue π P) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (elaborateByValue π P))
        (Hosting.start N (elaborateByValue π P) (elabQueryByValue π P (.text t))) x.2.1 :=
  static_runs_forward .byValue π N τ supply spaces byValue_faithful byValue_arrows byValue P noDecls texts
    present t names valued runs

/-- **The answers of every configuration a source run of a program by value reaches, as a bag, are those
of a frontier reached by the step.** -/
theorem byValue_answers_hosted (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram)
    (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {C : Config mkeys [] () MTy}
    (runs : Runs τ.discipline (elaborateByValue π P) supply
      (Config.initial spaces (elabQueryByValue π P (.text t))) C) :
    ∃ L : Multiset (Branch mkeys [] () τ.discipline.Ty × HostState MSig × ℕ),
      C.answers (D := τ.discipline) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (elaborateByValue π P))
        (Hosting.start N (elaborateByValue π P) (elabQueryByValue π P (.text t))) x.2.1 :=
  static_answers .byValue π N τ supply spaces byValue_faithful byValue_arrows byValue P noDecls texts present
    t names valued runs

/-- **Every run of the step from the translation's start of a program by value is a source run.** -/
theorem byValue_runs_reflected (byValue : ∀ f i, π.strategy f i = .value) (P : SProgram)
    (noDecls : P.decls = [])
    (texts : ∀ e ∈ P.equations, ∃ t, e.body = .text t ∧ ValueTextH (paramModes π [] e) (hview t))
    (present : ∀ e ∈ P.equations, (elabEquation π [] e).Scoped) (t : MData)
    (names : NamesIn (κ := mkeys) [[3]] t) (valued : ValueTextH (fun _ => .value) (hview t))
    {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N (elaborateByValue π P))
      (Hosting.start N (elaborateByValue π P) (elabQueryByValue π P (.text t))) s) :
    ∃ (C : Config mkeys [] () MTy) (b : Branch mkeys [] () MTy) (a : ℕ),
      Runs τ.discipline (elaborateByValue π P) supply
          (Config.initial spaces (elabQueryByValue π P (.text t))) C ∧
        b ∈ C.branches ∧ Represents N (elaborateByValue π P) C.world.scope b s a ∧ ArrowBranch b :=
  static_runs_reflected .byValue π N τ supply spaces byValue_faithful byValue_arrows byValue P noDecls texts
    present t names valued run

#print axioms elaborateH_eq
#print axioms elaborateByValue_agrees
#print axioms elabQueryByValue_agrees
#print axioms inc_agrees
#print axioms twice_query_agrees
#print axioms twice_programs_differ
#print axioms twice_compared
#print axioms byValue_runs_forward
#print axioms byValue_answers_hosted
#print axioms byValue_runs_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
