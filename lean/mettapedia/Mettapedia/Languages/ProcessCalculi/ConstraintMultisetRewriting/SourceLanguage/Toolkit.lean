import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration

/-!
# Tools for computing runs of MeTTa programs in the core

Names of the MeTTa key system, tuples at any context, how instantiation reads names, single steps,
and how the answers of a configuration are read off.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-! ## Names and data -/

/-- A first-order name at its scopes. -/
abbrev fo (scopes site : List ℕ) (index : ℕ) : Name mkeys := ⟨scopes, ⟨site, index, ([], ())⟩⟩

/-- A one-parameter name at its scopes. -/
abbrev ho (scopes site : List ℕ) (index : ℕ) : Name mkeys := ⟨scopes, ⟨site, index, ([()], ())⟩⟩

/-- A first-order name as a datum. -/
def foD (scopes site : List ℕ) (index : ℕ) : MData := .op (.inr (.mk (fo scopes site index))) .nil

/-- A one-parameter name applied to a datum. -/
def hoD {Δ : Ctx MSig} (scopes site : List ℕ) (index : ℕ) (a : Term (signature MSig (fam mkeys)) Δ ()) :
    Term (signature MSig (fam mkeys)) Δ () :=
  .op (.inr (.mk (ho scopes site index))) (.cons a .nil)

/-- Tuples at any context and over any family. -/
def tupleArgsAt {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} :
    (ts : List (Term (signature MSig target) Δ ())) →
      Args (signature MSig target) (List.replicate ts.length ([], ())) Δ
  | [] => .nil
  | t :: ts => .cons t (tupleArgsAt ts)

def tupleAt {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig}
    (ts : List (Term (signature MSig target) Δ ())) : Term (signature MSig target) Δ () :=
  .op (.inl (.tup ts.length)) (tupleArgsAt ts)

def symAt {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} (name : String) :
    Term (signature MSig target) Δ () := .op (.inl (.sym name)) .nil

/-- `(lam x. body)` over any family. -/
def lamAt {X : Type} {target : X → MetaArity MSig} (body : Term (signature MSig target) [()] ()) :
    Term (signature MSig target) [] () := .op (.inl .lam) (.cons body .nil)

/-- The bound variable of a `lam` body. -/
def bv {X : Type} {target : X → MetaArity MSig} : Term (signature MSig target) [()] () := .var .zero

/-! ## Instantiation reads names -/

theorem argsToSub_nil {X : Type} {target : X → MetaArity MSig} :
    (argsToSub (S := signature MSig target) (bs := []) (Γ := []) .nil) = fun _ v => .var v := by
  funext s v
  cases v

theorem argsToSub_bv {X : Type} {target : X → MetaArity MSig} :
    (argsToSub (S := signature MSig target) (bs := [()]) (Γ := [()]) (.cons bv .nil)) = fun _ v => .var v := by
  funext s v
  cases v with
  | zero => rfl
  | succ w => cases w

@[simp] theorem instantiate_foD {X : Type} {target : X → MetaArity MSig}
    (σ : Assignment (fam mkeys) target) (scopes site : List ℕ) (index : ℕ) :
    instantiate σ (foD scopes site index) = σ (fo scopes site index) := by
  change bind (argsToSub (S := signature MSig target) (bs := []) (Γ := []) .nil) (σ (fo scopes site index)) = _
  rw [argsToSub_nil, bind_id]

/-- A one-parameter name applied to the bound variable reads as its image. -/
theorem instantiate_hoD_bv {X : Type} {target : X → MetaArity MSig}
    (σ : Assignment (fam mkeys) target) (scopes site : List ℕ) (index : ℕ) :
    instantiate σ (hoD scopes site index (bv (target := fam mkeys))) = σ (ho scopes site index) := by
  change bind (argsToSub (S := signature MSig target) (bs := [()]) (Γ := [()]) (.cons bv .nil))
    (σ (ho scopes site index)) = _
  rw [argsToSub_bv, bind_id]

/-- A one-parameter name applied to a datum reads as its image with the parameter substituted. -/
theorem instantiate_hoD {X : Type} {target : X → MetaArity MSig}
    (σ : Assignment (fam mkeys) target) (scopes site : List ℕ) (index : ℕ) (a : MData) :
    instantiate σ (hoD scopes site index a) =
      bind (argsToSub (S := signature MSig target) (bs := [()]) (Γ := []) (.cons (instantiate σ a) .nil))
        (σ (ho scopes site index)) := rfl

/-! ## Injectivity of the term formers -/

theorem op_inj {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} {o : MOp ()}
    {a b : Args (signature MSig target) (MOp.arity o) Δ}
    (h : (Term.op (Sum.inl o) a : Term (signature MSig target) Δ ()) = Term.op (Sum.inl o) b) : a = b := by
  injection h

theorem tuple2_inj {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig}
    {a b a' b' : Term (signature MSig target) Δ ()} (h : tupleAt [a, b] = tupleAt [a', b']) :
    a = a' ∧ b = b' := by
  obtain ⟨ha, hrest⟩ := Args.cons.inj (op_inj h)
  exact ⟨ha, (Args.cons.inj hrest).1⟩

theorem tuple3_inj {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig}
    {a b c a' b' c' : Term (signature MSig target) Δ ()} (h : tupleAt [a, b, c] = tupleAt [a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨ha, hrest⟩ := Args.cons.inj (op_inj h)
  obtain ⟨hb, hrest'⟩ := Args.cons.inj hrest
  exact ⟨ha, hb, (Args.cons.inj hrest').1⟩

theorem lamAt_inj {X : Type} {target : X → MetaArity MSig}
    {a a' : Term (signature MSig target) [()] ()} (h : lamAt a = lamAt a') : a = a' :=
  (Args.cons.inj (op_inj h)).1

/-- A datum determined by a store stays determined by a longer live store. -/
theorem Determines.extend {K L : List (Constraint mkeys [] ())} {t : MData} {g : MClosed}
    (determined : Determines K t g) (live : Solvable (K ++ L)) : Determines (K ++ L) t g :=
  ⟨live, fun target σ solved => determined.2 target σ ((models_append σ K L).mp solved).1⟩

/-! ## Solutions given by a table of first-order names -/

/-- Bind the first-order names of a table to data; every other name to itself. -/
def bindNames (table : List ((List ℕ × List ℕ × ℕ) × MData)) : Assignment (fam mkeys) (fam mkeys) := fun x =>
  match x with
  | ⟨scopes, ⟨site, index, ([], ())⟩⟩ =>
      match table.lookup (scopes, site, index) with
      | some d => d
      | none => generator (fam mkeys) ⟨scopes, ⟨site, index, ([], ())⟩⟩
  | x => generator (fam mkeys) x

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (found : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at found
  | cons p rest ih =>
      obtain ⟨a', b'⟩ := p
      by_cases same : a = a'
      · subst same
        simp [List.lookup] at found
        subst found
        exact List.mem_cons.mpr (Or.inl rfl)
      · have different : (a == a') = false := by simpa using same
        simp [List.lookup, different] at found
        exact List.mem_cons.mpr (Or.inr (ih found))

/-- **Principal from a table**: a table that solves the store, each of whose entries the store
entails, gives an idempotent most general solution. -/
theorem principal_bindNames {K : List (Constraint mkeys [] ())}
    {table : List ((List ℕ × List ℕ × ℕ) × MData)}
    (solved : Models (bindNames table) K)
    (entailed : ∀ entry ∈ table, ∀ {X : Type} (target : X → MetaArity MSig)
      (σ : Assignment (fam mkeys) target),
        Models σ K → σ (fo entry.1.1 entry.1.2.1 entry.1.2.2) = instantiate σ entry.2) :
    Principal K (bindNames table) := by
  refine ⟨solved, fun target σ models name => ?_⟩
  rcases name with ⟨scopes, ⟨site, index, ⟨Δ, u⟩⟩⟩
  cases u
  cases Δ with
  | cons head tail => exact instantiate_generator σ _
  | nil =>
      show instantiate σ (match table.lookup (scopes, site, index) with
        | some d => d
        | none => generator (fam mkeys) ⟨scopes, ⟨site, index, ([], ())⟩⟩) = _
      cases found : table.lookup (scopes, site, index) with
      | none => exact instantiate_generator σ _
      | some d =>
          exact ((entailed _ (mem_of_lookup found)) target σ models).symm

/-- Close the first-order names of a table by closed data; every other name by `fallback`. -/
def closeNames (table : List ((List ℕ × List ℕ × ℕ) × MClosed)) (fallback : MClosed) :
    Assignment (fam mkeys) noNames := fun x =>
  Rigid.includeTerm noNames (match x with
    | ⟨scopes, ⟨site, index, ([], ())⟩⟩ => (table.lookup (scopes, site, index)).getD fallback
    | ⟨_, ⟨_, _, (_, _)⟩⟩ => rename (Γ := []) (fun _ impossible => nomatch impossible) fallback)

/-- Two tuples of different lengths are never made equal. -/
theorem tuple_length_ne {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target)
    {ts ts' : List MData} (different : ts.length ≠ ts'.length) :
    instantiate σ (tuple ts) ≠ instantiate σ (tuple ts') := by
  intro same
  change (Term.op (Sum.inl (MOp.tup ts.length)) _ : Term (signature MSig target) [] ()) =
    Term.op (Sum.inl (MOp.tup ts'.length)) _ at same
  injection same with _ _ hop _
  simp at hop
  exact different hop

/-- A store holding two tuples of different lengths equated is dead. -/
theorem dead_of_length {K : List (Constraint mkeys [] ())} {ts ts' : List MData}
    (member : (tuple ts, tuple ts') ∈ K) (different : ts.length ≠ ts'.length) : ¬ Solvable K := by
  rintro ⟨X, target, σ, solved⟩
  exact tuple_length_ne σ different (solved _ member)

instance (σ : Assignment (fam mkeys) noNames) (K : List (Constraint mkeys [] ())) : Decidable (Models σ K) := by
  unfold Models; infer_instance

instance (σ : Assignment (fam mkeys) (fam mkeys)) (K : List (Constraint mkeys [] ())) : Decidable (Models σ K) := by
  unfold Models; infer_instance

/-- The empty store is live. -/
theorem live_nil : Solvable ([] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, fun x => Rigid.includeTerm noNames
    (rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a") : Term MSig x.key.arity.1 ()),
    fun e member => by cases member⟩

/-! ## Steps on one alternative -/

variable {D : Discipline MSig [] ()} {P : Program mkeys [] () D.Ty} {supply : ℕ → MClosed}

/-! The lemmas below are the generic ones of `Semantics` at the MeTTa key system, stated so that
their implicit arguments are found from MeTTa data. -/

theorem step_one {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (live : Solvable b.store) (moved : Move D P supply w b w' bs) :
    Step D P supply ⟨w, {b}⟩ ⟨w', bs⟩ :=
  Step.single live moved

/-! ## Reading answers off -/

theorem answers_cons_finished {w : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {rest : Multiset (Branch mkeys [] () D.Ty)} (finished : b.Finished) (live : Solvable b.store) :
    Config.answers (⟨w, b ::ₘ rest⟩ : Config mkeys [] () D.Ty) =
      b.answer ::ₘ Config.answers (⟨w, rest⟩ : Config mkeys [] () D.Ty) :=
  Config.answers_cons_of_finished finished live

theorem answers_cons_dead {w : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {rest : Multiset (Branch mkeys [] () D.Ty)} (dead : ¬ Solvable b.store) :
    Config.answers (⟨w, b ::ₘ rest⟩ : Config mkeys [] () D.Ty) =
      Config.answers (⟨w, rest⟩ : Config mkeys [] () D.Ty) :=
  Config.answers_cons_of_dead dead

theorem answers_zero {w : World mkeys [] ()} :
    Config.answers (⟨w, 0⟩ : Config mkeys [] () D.Ty) = 0 :=
  Config.answers_of_zero

theorem answers_singleton {w : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    (finished : b.Finished) (live : Solvable b.store) :
    Config.answers (⟨w, {b}⟩ : Config mkeys [] () D.Ty) = {b.answer} :=
  Config.answers_of_finished finished live

theorem answers_singleton_dead {w : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    (dead : ¬ Solvable b.store) : Config.answers (⟨w, {b}⟩ : Config mkeys [] () D.Ty) = 0 :=
  Config.answers_of_dead dead

/-- The answer of a finished alternative whose value is determined. -/
theorem answer_of_determines {b : Branch mkeys [] () D.Ty} {t : MData} {g : MClosed}
    (focus : b.focus = .value t) (determined : Determines b.store t g) : b.answer = {g} :=
  Branch.answer_of_determines focus determined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
