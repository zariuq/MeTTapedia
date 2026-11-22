import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Laws that do not depend on the parameters

* **Spaces are unordered** (`initial_perm`): two initial spaces that list the same rows in different
  orders are the same configuration, because a space is a multiset of rows; so every run and every bag
  of answers is the same. This holds by the representation, not by a theorem about moves.
* **Annotated text does not consult the reading** (`elabText_annotated`): at a position that wants a
  value, the elaboration of annotated text is the same for every reading and every way the variables
  were passed. For programs (`elabEquation_annotated`, `elabComp_annotated`): a surface program whose
  bodies are annotated elaborates to the same equations under every reading.
* **A move of one reading is a move of another** (`move_transfer`, `step_transfer`, `runs_transfer`,
  `runs_transfer_along`) when the two programs have the same equations and read the same way the texts
  their runs actually reflect: a `run` reflects its datum dereferenced by a most general solution of
  the alternative's store (`RunsOnly`), so the readings need to agree on those texts only. It applies
  to its example: the annotated program's run under one reading is carried to every other
  (`ExampleTransfer.annotated_runs_transferred`). The control is `ExampleHeld` (the unannotated
  program, whose two readings give different bags).
* **The elaboration never runs a computed value** (`values_never_run`): without explicit `run` marks,
  every datum the elaboration of a position makes run is a variable that was passed as text (held or by
  name); a variable that holds a computed value is only returned. This is a statement about the
  elaboration only: a `run` at run time dereferences its text through the store, and a computed value
  that sits inside held text is read as code again when that text runs (`ExampleRunsAgain`).
* **Answers do not see names** (`answers_rename`): renaming every alternative's store and value by a
  renaming that has an inverse keeps the bag of answers (`reads_rename`, `solvable_rename`).
* **A program is a bag of equations** (`move_perm`, `step_perm`, `runs_perm`): the runs of a program are
  the runs of every permutation of its equations; so union of programs commutes up to runs
  (`runs_union_comm`, for programs that read text the same way) and is associative (`union_assoc`).
  The alternatives an `apply` makes form a multiset, so this too holds by the representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

/-! ## Spaces are unordered -/

/-- Rows listed in two orders give the same initial configuration. -/
theorem initial_perm {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}
    (spaces : Term S Γ star → Multiset (Row κ Γ star)) (h : Term S Γ star) {l l' : List (Row κ Γ star)}
    (perm : l.Perm l') (q : Comp κ Γ star Ty) :
    Config.initial (setSpace spaces h ↑l) q = Config.initial (setSpace spaces h ↑l') q := by
  rw [Multiset.coe_eq_coe.mpr perm]

/-! ## Annotated text -/

/-- Text at a position that wants a value is **annotated** when every position in it is marked and
no variable stands unmarked where a value is wanted. -/
def Annotated : View → Prop
  | .holdMark _ _ => True
  | .runMark _ inner => match inner with
      | .var _ _ => True
      | other => Annotated other
  | .var _ _ => False
  | .symbol _ _ => True
  | .call _ _ args => AnnotatedArgs args
  | .inert _ => True
  | .other _ => True
where
  /-- Every argument is a mark, annotated inside. -/
  AnnotatedArgs : List View → Prop
    | [] => True
    | .holdMark _ _ :: rest => AnnotatedArgs rest
    | .runMark o inner :: rest => Annotated (.runMark o inner) ∧ AnnotatedArgs rest
    | _ :: _ => False

mutual
theorem elabText_annotated (π π' : Params) (decls : List Decl) (modes modes' : Name mkeys → VarMode)
    (path : List ℕ) : (v : View) → Annotated v →
      elabText π decls modes path v = elabText π' decls modes' path v
  | .holdMark _ _, _ => rfl
  | .runMark _ inner, annotated => by
      cases inner with
      | var o x => rfl
      | holdMark o u => rfl
      | runMark o i => exact elabText_annotated π π' decls modes modes' path (.runMark o i) annotated
      | symbol o f => rfl
      | call o f args => exact elabText_annotated π π' decls modes modes' path (.call o f args) annotated
      | inert o => rfl
      | other o => rfl
  | .var _ _, annotated => absurd annotated (by simp [Annotated])
  | .symbol _ _, _ => rfl
  | .call _ f args, annotated => by
      simp only [elabText]
      exact elabArgs_annotated π π' decls modes modes' path f 0 args [] annotated
  | .inert _, _ => rfl
  | .other _, _ => rfl

theorem elabArgs_annotated (π π' : Params) (decls : List Decl) (modes modes' : Name mkeys → VarMode)
    (path : List ℕ) (f : String) : (i : ℕ) → (args : List View) → (done : List MData) →
      Annotated.AnnotatedArgs args →
        elabArgs π decls modes path f i args done = elabArgs π' decls modes' path f i args done
  | _, [], _, _ => rfl
  | i, .holdMark o u :: rest, done, annotated => by
      simp only [elabArgs, passOf]
      exact elabArgs_annotated π π' decls modes modes' path f (i + 1) rest (u :: done) annotated
  | i, .runMark o inner :: rest, done, annotated => by
      simp only [elabArgs, passOf]
      rw [elabText_annotated π π' decls modes modes' (path ++ [i]) (.runMark o inner) annotated.1,
        elabArgs_annotated π π' decls modes modes' path f (i + 1) rest (slot (path ++ [i]) :: done) annotated.2]
  | _, .var _ _ :: _, _, annotated => absurd annotated (by simp [Annotated.AnnotatedArgs])
  | _, .symbol _ _ :: _, _, annotated => absurd annotated (by simp [Annotated.AnnotatedArgs])
  | _, .call _ _ _ :: _, _, annotated => absurd annotated (by simp [Annotated.AnnotatedArgs])
  | _, .inert _ :: _, _, annotated => absurd annotated (by simp [Annotated.AnnotatedArgs])
  | _, .other _ :: _, _, annotated => absurd annotated (by simp [Annotated.AnnotatedArgs])
end

/-- A surface computation all of whose text is annotated. -/
def SAnnotated : SComp → Prop
  | .text t => Annotated (view t)
  | .let_ _ _ c k => SAnnotated c ∧ SAnnotated k
  | .choice c d => SAnnotated c ∧ SAnnotated d
  | .fail => True
  | .query _ _ k => SAnnotated k
  | .add _ _ k => SAnnotated k
  | .remove _ _ k => SAnnotated k
  | .new _ _ k => SAnnotated k

theorem elabComp_annotated (π π' : Params) (decls : List Decl) (modes modes' : Name mkeys → VarMode) :
    (path : List ℕ) → (c : SComp) → SAnnotated c →
      elabComp π decls modes path c = elabComp π' decls modes' path c
  | path, .text t, annotated => elabText_annotated π π' decls modes modes' path (view t) annotated
  | path, .let_ s p c k, ⟨hc, hk⟩ => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) c hc,
        elabComp_annotated π π' decls modes modes' (path ++ [1]) k hk]
  | path, .choice c d, ⟨hc, hd⟩ => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) c hc,
        elabComp_annotated π π' decls modes modes' (path ++ [1]) d hd]
  | _, .fail, _ => rfl
  | path, .query sp p k, hk => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) k hk]
  | path, .add sp t k, hk => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) k hk]
  | path, .remove sp t k, hk => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) k hk]
  | path, .new s x k, hk => by
      simp only [elabComp]
      rw [elabComp_annotated π π' decls modes modes' (path ++ [0]) k hk]

/-- An equation body is annotated: a marked root, or (when the result is not held) annotated text,
or annotated constructs. -/
def BodyAnnotated (decls : List Decl) (e : SEquation) : Prop :=
  match e.body with
  | .text t =>
      match view t with
      | .holdMark _ _ => True
      | .runMark o inner => Annotated (.runMark o inner)
      | v => Annotated v ∧ ∀ d, declOf decls e.head = some d → d.result.held = false
  | b => SAnnotated b

/-- **Annotated equations elaborate the same way under every reading.** -/
theorem elabEquation_annotated (π π' : Params) (decls : List Decl) (e : SEquation)
    (annotated : BodyAnnotated decls e) : elabEquation π decls e = elabEquation π' decls e := by
  unfold elabEquation elabBody
  unfold BodyAnnotated at annotated
  congr 1
  rcases e with ⟨site, head, params, body⟩
  dsimp only at annotated ⊢
  cases body with
  | text t =>
      dsimp only at annotated ⊢
      cases hv : view t with
      | holdMark o u => rfl
      | runMark o inner =>
          rw [hv] at annotated
          dsimp only at annotated
          have moved : Annotated (View.runMark t inner) := by
            cases inner <;> simp_all [Annotated]
          exact elabText_annotated π π' decls _ _ _ (.runMark t inner) moved
      | var o x =>
          rw [hv] at annotated
          dsimp only at annotated
          exact absurd annotated.1 (by simp [Annotated])
      | symbol o f =>
          rw [hv] at annotated
          dsimp only at annotated
          cases hd : declOf decls head with
          | none => rfl
          | some d =>
              simp only [annotated.2 d hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              rfl
      | call o f args =>
          rw [hv] at annotated
          dsimp only at annotated
          cases hd : declOf decls head with
          | none => exact elabText_annotated π π' decls _ _ _ _ annotated.1
          | some d =>
              simp only [annotated.2 d hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact elabText_annotated π π' decls _ _ _ _ annotated.1
      | inert o =>
          rw [hv] at annotated
          dsimp only at annotated
          cases hd : declOf decls head with
          | none => rfl
          | some d =>
              simp only [annotated.2 d hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              rfl
      | other o =>
          rw [hv] at annotated
          dsimp only at annotated
          cases hd : declOf decls head with
          | none => rfl
          | some d =>
              simp only [annotated.2 d hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              rfl
  | let_ s p c k => exact elabComp_annotated π π' decls _ _ _ _ annotated
  | choice c d => exact elabComp_annotated π π' decls _ _ _ _ annotated
  | fail => rfl
  | query sp p k => exact elabComp_annotated π π' decls _ _ _ _ annotated
  | add sp t k => exact elabComp_annotated π π' decls _ _ _ _ annotated
  | remove sp t k => exact elabComp_annotated π π' decls _ _ _ _ annotated
  | new s x k => exact elabComp_annotated π π' decls _ _ _ _ annotated

/-- **A fully annotated surface program has the same elaborated equations under every reading.** -/
theorem elaborate_annotated_equations (π π' : Params) (P : SProgram)
    (annotated : ∀ e ∈ P.equations, BodyAnnotated P.decls e) :
    (elaborate π P).equations = (elaborate π' P).equations := by
  simp only [elaborate]
  apply List.map_congr_left
  intro e member
  exact elabEquation_annotated π π' P.decls e (annotated e member)

/-- **And the same elaborated query.** -/
theorem elabQuery_annotated (π π' : Params) (P : SProgram) (q : SComp) (annotated : SAnnotated q) :
    elabQuery π P q = elabQuery π' P q :=
  elabComp_annotated π π' P.decls _ _ [3] q annotated

/-! ## A computed value never runs again -/

/-- The data a computation runs as code (`run`) or forces (`force`). -/
def reruns {Ty : Type} : Comp mkeys [] () Ty → List MData
  | .ret _ => []
  | .apply _ => []
  | .run t => [t]
  | .let_ _ _ c k => reruns c ++ reruns k
  | .choice c d => reruns c ++ reruns d
  | .fail => []
  | .query _ _ k => reruns k
  | .add _ _ k => reruns k
  | .remove _ _ k => reruns k
  | .new _ _ k => reruns k
  | .check _ k => reruns k
  | .delay _ _ c k => reruns c ++ reruns k
  | .force x => [x]

/-- Text with no explicit `run` mark, all of whose variables hold computed values. -/
def ValueText (modes : Name mkeys → VarMode) : View → Prop
  | .holdMark _ _ => True
  | .runMark _ _ => False
  | .var _ x => modes x = .value
  | .symbol _ _ => True
  | .call _ _ args => ValueArgs modes args
  | .inert _ => True
  | .other _ => True
where
  ValueArgs (modes : Name mkeys → VarMode) : List View → Prop
    | [] => True
    | a :: rest => ValueText modes a ∧ ValueArgs modes rest

mutual
/-- **A computed value never runs again**: the elaboration of text without explicit `run` marks,
whose variables hold computed values, runs nothing and forces nothing. -/
theorem values_never_run (π : Params) (decls : List Decl) (modes : Name mkeys → VarMode) (path : List ℕ) :
    (v : View) → ValueText modes v → reruns (elabText π decls modes path v) = []
  | .holdMark _ _, _ => rfl
  | .runMark _ _, valued => absurd valued (by simp [ValueText])
  | .var o x, valued => by
      simp only [ValueText] at valued
      simp only [elabText, varAt, valued]
      rfl
  | .symbol _ _, _ => rfl
  | .call _ f args, valued => by
      simp only [elabText]
      exact valueArgs_never_run π decls modes path f 0 args [] valued
  | .inert _, _ => rfl
  | .other _, _ => rfl

theorem valueArgs_never_run (π : Params) (decls : List Decl) (modes : Name mkeys → VarMode)
    (path : List ℕ) (f : String) : (i : ℕ) → (args : List View) → (done : List MData) →
      ValueText.ValueArgs modes args → reruns (elabArgs π decls modes path f i args done) = []
  | _, [], done, _ => by
      simp only [elabArgs, finish]
      split
      · split <;> rfl
      · rfl
  | i, a :: rest, done, ⟨first, others⟩ => by
      simp only [elabArgs]
      split
      · exact valueArgs_never_run π decls modes path f (i + 1) rest _ others
      · exact valueArgs_never_run π decls modes path f (i + 1) rest _ others
      · simp only [reruns, values_never_run π decls modes (path ++ [i]) a first,
          valueArgs_never_run π decls modes path f (i + 1) rest _ others, List.append_nil]
      · simp only [reruns, values_never_run π decls modes (path ++ [i]) a first,
          valueArgs_never_run π decls modes path f (i + 1) rest _ others, List.append_nil]
      · simp only [reruns, values_never_run π decls modes (path ++ [i]) a first,
          valueArgs_never_run π decls modes path f (i + 1) rest _ others, List.append_nil]
end

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

/-! ## Answers do not see names -/

/-- A store renamed. -/
def renameStore (ρ : Assignment (fam κ) (fam κ)) (K : List (Constraint κ Γ star)) : List (Constraint κ Γ star) :=
  K.map fun e => (instantiate ρ e.1, instantiate ρ e.2)

theorem models_renameStore {X : Type} {target : X → MetaArity S} (σ : Assignment (fam κ) target)
    (ρ : Assignment (fam κ) (fam κ)) (K : List (Constraint κ Γ star)) :
    Models σ (renameStore ρ K) ↔ Models (Assignment.compose σ ρ) K := by
  constructor
  · intro solved e member
    have := solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    simpa only [Assignment.instantiate_compose] using this
  · intro solved e member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    have := solved original inside
    simpa only [Assignment.instantiate_compose] using this

/-- **Readings do not depend on names**: renaming a store and a datum by a renaming that has an inverse
keeps every reading. -/
theorem reads_rename {ρ ρ' : Assignment (fam κ) (fam κ)} (inverse : Assignment.compose ρ' ρ = generator (fam κ))
    (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (g : Term S Γ star) :
    Reads (renameStore ρ K) (instantiate ρ t) g ↔ Reads K t g := by
  constructor
  · rintro ⟨X, target, σ, solved, read⟩
    refine ⟨X, target, Assignment.compose σ ρ, (models_renameStore σ ρ K).mp solved, ?_⟩
    rw [Assignment.instantiate_compose]
    exact read
  · rintro ⟨X, target, σ, solved, read⟩
    have back : Assignment.compose (Assignment.compose σ ρ') ρ = σ := by
      rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
    have solved' : Models (Assignment.compose (Assignment.compose σ ρ') ρ) K := by rw [back]; exact solved
    refine ⟨X, target, Assignment.compose σ ρ', (models_renameStore _ ρ K).mpr solved', ?_⟩
    rw [← Assignment.instantiate_compose, back]
    exact read

theorem solvable_rename {ρ ρ' : Assignment (fam κ) (fam κ)} (inverse : Assignment.compose ρ' ρ = generator (fam κ))
    (K : List (Constraint κ Γ star)) : Solvable (renameStore ρ K) ↔ Solvable K := by
  constructor
  · rintro ⟨X, target, σ, solved⟩
    exact ⟨X, target, Assignment.compose σ ρ, (models_renameStore σ ρ K).mp solved⟩
  · rintro ⟨X, target, σ, solved⟩
    have back : Assignment.compose (Assignment.compose σ ρ') ρ = σ := by
      rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
    have solved' : Models (Assignment.compose (Assignment.compose σ ρ') ρ) K := by rw [back]; exact solved
    exact ⟨X, target, Assignment.compose σ ρ', (models_renameStore _ ρ K).mpr solved'⟩

/-- An alternative whose store and value are renamed. -/
def renameAnswering {Ty : Type} (ρ : Assignment (fam κ) (fam κ)) (b : Branch κ Γ star Ty) : Branch κ Γ star Ty :=
  ⟨renameStore ρ b.store, match b.focus with
    | .value t => .value (instantiate ρ t)
    | other => other, b.frames, b.pending⟩

/-- **The bag of answers does not depend on names**: renaming every alternative's store and value by
a renaming with an inverse keeps the bag. -/
theorem answers_rename {D : Discipline S Γ star} {ρ ρ' : Assignment (fam κ) (fam κ)}
    (inverse : Assignment.compose ρ' ρ = generator (fam κ)) (C : Config κ Γ star D.Ty) :
    Config.answers (⟨C.world, C.branches.map (renameAnswering ρ)⟩ : Config κ Γ star D.Ty) = C.answers := by
  classical
  simp only [Config.answers]
  rw [Multiset.filter_map, Multiset.map_map]
  have samePred : Multiset.filter ((fun b : Branch κ Γ star D.Ty => b.Finished ∧ Solvable b.store) ∘
      renameAnswering ρ) C.branches = Multiset.filter (fun b => b.Finished ∧ Solvable b.store) C.branches := by
    apply Multiset.filter_congr
    intro b _
    rcases b with ⟨K, focus, frames, pending⟩
    simp only [Function.comp, renameAnswering, Branch.Finished, solvable_rename inverse K]
    cases focus <;> simp
  rw [samePred]
  apply Multiset.map_congr rfl
  intro b _
  rcases b with ⟨K, focus, frames, pending⟩
  ext g
  cases focus with
  | value t =>
      simp only [Function.comp, renameAnswering, Branch.answer, Set.mem_ofPred_eq, Focus.value.injEq,
        exists_eq_left']
      exact reads_rename inverse K t g
  | eval c => simp [Function.comp, renameAnswering, Branch.answer]
  | refused t T => simp [Function.comp, renameAnswering, Branch.answer]

/-! ## Moves transfer between readings -/

/-- **A move of one program is a move of another** with the same equations that reads the text the
move runs the same way: the text a `run` reflects is its datum dereferenced by a most general solution
of the alternative's store, so the two readings need to agree on those texts only. -/
theorem move_transfer {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (moved : Move D P supply w b w' bs) (equations : P.equations = P'.equations)
    (reads : ∀ t θ, b.focus = .eval (.run t) → Principal b.store θ →
      P.reflect (instantiate θ t) = P'.reflect (instantiate θ t)) :
    Move D P' supply w b w' bs := by
  cases moved with
  | ret => exact .ret _ _ _ _ _
  | apply K t fs ps matched =>
      have same : P.equations.map (callBranch D w.scope K t fs ps) =
          P'.equations.map (callBranch D w.scope K t fs ps) := by rw [equations]
      rw [same]
      exact .apply _ _ _ _ _ (equations ▸ matched)
  | unmatched K t fs ps none => exact .unmatched _ _ _ _ _ (equations ▸ none)
  | run K t fs ps θ principal =>
      rw [reads t θ rfl principal]
      exact .run _ _ _ _ _ θ principal
  | letStart => exact .letStart _ _ _ _ _ _ _ _
  | letBind => exact .letBind _ _ _ _ _ _ _ _
  | choice => exact .choice _ _ _ _ _ _
  | fail => exact .fail _ _ _ _
  | query K sp p k fs ps h addressed => exact .query _ _ _ _ _ _ _ h addressed
  | add K sp t k fs ps h addressed => exact .add _ _ _ _ _ _ _ h addressed
  | remove K sp t k fs ps h addressed r rest split fits =>
      exact .remove _ _ _ _ _ _ _ h addressed r rest split fits
  | removeAbsent K sp t k fs ps h addressed none => exact .removeAbsent _ _ _ _ _ _ _ h addressed none
  | new => exact .new _ _ _ _ _ _ _
  | checkStart => exact .checkStart _ _ _ _ _ _
  | admitted K v T fs ps all => exact .admitted _ _ _ _ _ _ all
  | refused K v T fs ps none => exact .refused _ _ _ _ _ _ none
  | delay => exact .delay _ _ _ _ _ _ _ _
  | forcePending K x cell c fs before after bound => exact .forcePending _ _ _ _ _ _ _ _ bound
  | forceDone K x fs ps none => exact .forceDone _ _ _ _ _ none
  | memo => exact .memo _ _ _ _ _ _

/-- **The texts a configuration can reflect at its next move**: for every alternative about to run a
datum `t`, every most general solution of its store dereferences `t` into `A`. (A dead alternative's
store has no solution, so it constrains nothing.) -/
def RunsOnly {Ty : Type} (C : Config κ Γ star Ty) (A : Data κ Γ star → Prop) : Prop :=
  ∀ b ∈ C.branches, ∀ t, b.focus = .eval (.run t) → ∀ θ, Principal b.store θ → A (instantiate θ t)

/-- A configuration with no alternative about to run reflects nothing. -/
theorem runsOnly_of_none {Ty : Type} {C : Config κ Γ star Ty} {A : Data κ Γ star → Prop}
    (none : ∀ b ∈ C.branches, ∀ t, b.focus ≠ .eval (.run t)) : RunsOnly C A :=
  fun b member t focus => absurd focus (none b member t)

/-- **A step transfers** between two programs with the same equations when the texts its
configuration can reflect lie where the two readings agree. -/
theorem step_transfer {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {C C' : Config κ Γ star D.Ty} (step : Step D P supply C C') (equations : P.equations = P'.equations)
    {A : Data κ Γ star → Prop} (agree : ∀ t, A t → P.reflect t = P'.reflect t) (only : RunsOnly C A) :
    Step D P' supply C C' := by
  cases step with
  | move w w' b rest bs live moved =>
      exact .move w w' b rest bs live (move_transfer moved equations
        (fun t θ focus principal => agree _ (only b (Multiset.mem_cons_self _ _) t focus θ principal)))

/-- **A run transfers along itself**: when every configuration of the run reflects, at its next move,
only text where the two readings agree, the run is a run of the other program. -/
theorem runs_transfer_along {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty}
    {supply : ℕ → Term S Γ star} {C C' : Config κ Γ star D.Ty} (equations : P.equations = P'.equations)
    {A : Data κ Γ star → Prop} (agree : ∀ t, A t → P.reflect t = P'.reflect t)
    (runs : Relation.ReflTransGen (fun C₁ C₂ => Step D P supply C₁ C₂ ∧ RunsOnly C₁ A) C C') :
    Runs D P' supply C C' := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_transfer step.1 equations agree step.2)

/-- **Runs transfer** between two programs with the same equations, when every configuration the run
reaches reflects only text where the two readings agree. -/
theorem runs_transfer {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {C C' : Config κ Γ star D.Ty} (runs : Runs D P supply C C') (equations : P.equations = P'.equations)
    {A : Data κ Γ star → Prop} (agree : ∀ t, A t → P.reflect t = P'.reflect t)
    (only : ∀ C'', Runs D P supply C C'' → RunsOnly C'' A) : Runs D P' supply C C' := by
  induction runs with
  | refl => exact .refl
  | tail before step ih => exact ih.tail (step_transfer step equations agree (only _ before))

/-! ## A program is a bag of equations -/

/-- **The order of equations is unobservable**: a move of a program is a move of every program whose
equations are a permutation of its own and which reads text the same way. -/
theorem move_perm {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (moved : Move D P supply w b w' bs) (perm : P.equations.Perm P'.equations)
    (reflect : P.reflect = P'.reflect) : Move D P' supply w b w' bs := by
  cases moved with
  | ret => exact .ret _ _ _ _ _
  | apply K t fs ps matched =>
      have same : ((P.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
          Multiset (Branch κ Γ star D.Ty)) = (P'.equations.map (callBranch D w.scope K t fs ps) : List _) :=
        Multiset.coe_eq_coe.mpr (perm.map _)
      rw [same]
      obtain ⟨e, member, live⟩ := matched
      exact .apply _ _ _ _ _ ⟨e, perm.subset member, live⟩
  | unmatched K t fs ps none =>
      exact .unmatched _ _ _ _ _ (fun e member => none e (perm.symm.subset member))
  | run K t fs ps θ principal =>
      rw [reflect]
      exact .run _ _ _ _ _ θ principal
  | letStart => exact .letStart _ _ _ _ _ _ _ _
  | letBind => exact .letBind _ _ _ _ _ _ _ _
  | choice => exact .choice _ _ _ _ _ _
  | fail => exact .fail _ _ _ _
  | query K sp p k fs ps h addressed => exact .query _ _ _ _ _ _ _ h addressed
  | add K sp t k fs ps h addressed => exact .add _ _ _ _ _ _ _ h addressed
  | remove K sp t k fs ps h addressed r rest split fits =>
      exact .remove _ _ _ _ _ _ _ h addressed r rest split fits
  | removeAbsent K sp t k fs ps h addressed none => exact .removeAbsent _ _ _ _ _ _ _ h addressed none
  | new => exact .new _ _ _ _ _ _ _
  | checkStart => exact .checkStart _ _ _ _ _ _
  | admitted K v T fs ps all => exact .admitted _ _ _ _ _ _ all
  | refused K v T fs ps none => exact .refused _ _ _ _ _ _ none
  | delay => exact .delay _ _ _ _ _ _ _ _
  | forcePending K x cell c fs before after bound => exact .forcePending _ _ _ _ _ _ _ _ bound
  | forceDone K x fs ps none => exact .forceDone _ _ _ _ _ none
  | memo => exact .memo _ _ _ _ _ _

theorem step_perm {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {C C' : Config κ Γ star D.Ty} (step : Step D P supply C C') (perm : P.equations.Perm P'.equations)
    (reflect : P.reflect = P'.reflect) : Step D P' supply C C' := by
  cases step with
  | move w w' b rest bs live moved => exact .move w w' b rest bs live (move_perm moved perm reflect)

/-- **The runs of a program are the runs of every permutation of its equations**: the same
configurations, hence the same bags of answers. -/
theorem runs_perm {D : Discipline S Γ star} {P P' : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {C C' : Config κ Γ star D.Ty} (runs : Runs D P supply C C') (perm : P.equations.Perm P'.equations)
    (reflect : P.reflect = P'.reflect) : Runs D P' supply C C' := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_perm step perm reflect)

/-- **Union of programs commutes** up to runs, for programs that read text the same way. -/
theorem runs_union_comm {D : Discipline S Γ star} {P Q : Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
    {C C' : Config κ Γ star D.Ty} (runs : Runs D (P.union Q) supply C C') (reflect : P.reflect = Q.reflect) :
    Runs D (Q.union P) supply C C' :=
  runs_perm runs List.perm_append_comm reflect

/-- **Union of programs is associative**, on the nose. -/
theorem union_assoc {Ty : Type} (P Q R : Program κ Γ star Ty) :
    (P.union Q).union R = P.union (Q.union R) := by
  simp [Program.union, List.append_assoc]

#print axioms initial_perm
#print axioms elabText_annotated
#print axioms elabEquation_annotated
#print axioms elaborate_annotated_equations
#print axioms move_transfer
#print axioms step_transfer
#print axioms runs_transfer_along
#print axioms runs_transfer
#print axioms values_never_run
#print axioms answers_rename
#print axioms runs_perm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws
