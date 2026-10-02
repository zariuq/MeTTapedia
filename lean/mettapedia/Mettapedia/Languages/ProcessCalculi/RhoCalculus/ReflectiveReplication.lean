import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# Replication through reflection: Lawvere's fixed point in rho

Meredith and Radestock (2005, Section 3) define replication without a
replication primitive:

  `D(x) = x(y).(x[y] | *y)`,   `!P = x⌈D(x) | P⌉ | D(x)`.

The duplicator `D(x)` receives a quoted process on `x`, sends the same name on
again and runs it.  In the canonical Lean rho the output `x!(Q)` is the lift
`x⌈Q⌉` (communication substitutes the quote of the normalised payload), and the
name output `x[y]` is written `x!(*y)`: under communication the bound drop
collapses to the received process (`semanticCommSubst_collapses_bound_drop`),
so the continuation sends exactly the process it received.

**Unfolding** (`replicate_unfold`): `!P ⇝ !P | P` for every process `P`, one
communication followed by structural rearrangement.  The encoding "runs away"
(`replicate_runs_forever`): it has an infinite reduction sequence.

**The Lawvere reading** (`duplicator_represents`, `replication_fixedPoint`).
Let a code `c` run on an argument code `a` by `run c a = x!(a) | c`: the
argument is sent as code and `c` runs beside it.  For the endomap
`f X = X | P`, the code `D(x) | P` represents the diagonal composite
`a ↦ f (run a a) = (x!(a) | a) | P` up to one reduction step, for every
argument code `a`.  This is the point-surjectivity the diagonal needs: the
duplicator turns any received code into a running process (by drop) while
keeping the code available (by resending it).  The diagonal step then gives
the fixed point `run c c ⇝ run c c | P` for `c = D(x) | P`, which is
`!P | P` up to structural congruence.  Without drop the received code can
only be used as a channel; the negative control is in `DropFreeTermination`.

The channel hypothesis `ChannelInert x` says that normalising `x` does not
produce the bound name of the communication; every closed name satisfies it,
in particular `@0` (`atZero_channelInert`).

**Bookkeeping, choice-free.**  `normalize_sc` shows that the normaliser used
by communication is structurally congruent to the identity on names,
processes and lists, following the normaliser's own recursion; `substName_eq`
and `substNameMark_eq` give the name substitution in closed form.  With them
every theorem here depends on `propext` and `Quot.sound` only.

**Scope.**  The results concern the canonical relation `Reduces` (COMM, closed
under structural congruence and parallel contexts) on raw patterns, for every
process `P` and every channel satisfying `ChannelInert`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Logic.Diagonal

/-! ## The construction -/

/-- Parallel composition as a bag. -/
abbrev par (processes : List Pattern) : Pattern := .collection .hashBag processes none

/-- The body of the duplicator: `x!(*y) | *y`, with `y` the bound name. -/
def duplicatorBody (x : Pattern) : Pattern :=
  par [.apply "POutput" [x, .apply "PDrop" [.bvar 0]], .apply "PDrop" [.bvar 0]]

/-- **The duplicator** `D(x) = for (y ← x) (x!(*y) | *y)`. -/
def duplicator (x : Pattern) : Pattern :=
  .apply "PInput" [x, .lambda none (duplicatorBody x)]

/-- **Replication through reflection**: `!P = x!(D(x) | P) | D(x)`. -/
def replicate (x P : Pattern) : Pattern :=
  par [.apply "POutput" [x, par [duplicator x, P]], duplicator x]

/-- The channel is not the bound name of a communication after
normalisation, so substitution leaves it as its normal form. -/
def ChannelInert (x : Pattern) : Prop :=
  semanticNormalizeName x ≠ .bvar 0

/-- The closed name `@0`. -/
def atZero : Pattern := .apply "NQuote" [.apply "PZero" []]

theorem atZero_channelInert : ChannelInert atZero := by
  intro normalizedIsBound
  cases normalizedIsBound

/-! ## Structural congruence bookkeeping

The normalisation used by communication is structurally congruent to the
identity.  The canonical rho proves this with a classical case split; the
proof below follows the recursion of the normaliser (its functional induction
principle), so it uses no choice. -/

private theorem sc_trans {a b c : Pattern} (first : a ≡ b) (second : b ≡ c) : a ≡ c :=
  StructuralCongruence.trans _ _ _ first second

private theorem sc_symm {a b : Pattern} (h : a ≡ b) : b ≡ a :=
  StructuralCongruence.symm _ _ h

private theorem sc_apply_one (f : String) {a a' : Pattern} (ha : a ≡ a') :
    StructuralCongruence (.apply f [a]) (.apply f [a']) := by
  refine StructuralCongruence.apply_cong f [a] [a'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact ha
  | n + 1, h₁ => exact absurd (Nat.lt_of_succ_lt_succ h₁) (Nat.not_lt_zero n)

private theorem sc_apply_two (f : String) {a a' b b' : Pattern} (ha : a ≡ a') (hb : b ≡ b') :
    StructuralCongruence (.apply f [a, b]) (.apply f [a', b']) := by
  refine StructuralCongruence.apply_cong f [a, b] [a', b'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact ha
  | 1, _ => exact hb
  | n + 2, h₁ =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h₁)) (Nat.not_lt_zero n)

private theorem sc_par_two {a a' b b' : Pattern} (ha : a ≡ a') (hb : b ≡ b') :
    par [a, b] ≡ par [a', b'] := by
  refine StructuralCongruence.par_cong [a, b] [a', b'] rfl ?_
  intro i h₁ _
  match i, h₁ with
  | 0, _ => exact ha
  | 1, _ => exact hb
  | n + 2, h₁ =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h₁)) (Nat.not_lt_zero n)

/-- Pointwise structural congruence of two lists of equal length. -/
def ListCongruent (first second : List Pattern) : Prop :=
  first.length = second.length ∧
    ∀ i (h₁ : i < first.length) (h₂ : i < second.length),
      first.get ⟨i, h₁⟩ ≡ second.get ⟨i, h₂⟩

/-- **Normalisation is structural congruence**, for names, processes and
lists, choice-free. -/
theorem normalize_sc :
    (∀ name, semanticNormalizeName name ≡ name) ∧
      (∀ process, semanticNormalizeProc process ≡ process) ∧
        (∀ processes, ListCongruent (semanticNormalizeProcList processes) processes) := by
  refine semanticNormalizeName.mutual_induct
    (fun name => semanticNormalizeName name ≡ name)
    (fun process => semanticNormalizeProc process ≡ process)
    (fun processes => ListCongruent (semanticNormalizeProcList processes) processes)
    ?nameBvar ?nameFvar ?nameQuoteDrop ?nameQuote ?nameOther
    ?bvar ?fvar ?output ?input ?drop ?quote ?lambda ?multiLambda ?subst ?collection ?other
    ?nil ?cons
  case nameBvar => intro n; rw [semanticNormalizeName.eq_1]; exact .refl _
  case nameFvar => intro x; rw [semanticNormalizeName.eq_2]; exact .refl _
  case nameQuoteDrop =>
    intro n ih
    rw [semanticNormalizeName.eq_3]
    exact sc_trans ih (sc_symm (StructuralCongruence.quote_drop n))
  case nameQuote =>
    intro p notDrop ih
    rw [semanticNormalizeName.eq_4 p notDrop]
    exact sc_apply_one "NQuote" ih
  case nameOther =>
    intro n notBvar notFvar notQuoteDrop notQuote
    rw [semanticNormalizeName.eq_5 n notBvar notFvar notQuoteDrop notQuote]
    exact .refl _
  case bvar => intro n; rw [semanticNormalizeProc.eq_1]; exact .refl _
  case fvar => intro x; rw [semanticNormalizeProc.eq_2]; exact .refl _
  case output =>
    intro n q ihName ihPayload
    rw [semanticNormalizeProc.eq_3]
    exact sc_apply_two "POutput" ihName ihPayload
  case input =>
    intro n body ihName ihBody
    rw [semanticNormalizeProc.eq_4]
    exact sc_apply_two "PInput" ihName (StructuralCongruence.lambda_cong none _ _ ihBody)
  case drop =>
    intro n ih
    rw [semanticNormalizeProc.eq_5]
    exact sc_apply_one "PDrop" ih
  case quote =>
    intro p ih
    rw [semanticNormalizeProc.eq_6]
    exact sc_apply_one "NQuote" ih
  case lambda =>
    intro nm body ih
    rw [semanticNormalizeProc.eq_7]
    exact StructuralCongruence.lambda_cong nm _ _ ih
  case multiLambda =>
    intro n nms body ih
    rw [semanticNormalizeProc.eq_8]
    exact StructuralCongruence.multiLambda_cong n nms _ _ ih
  case subst =>
    intro body repl ihBody ihRepl
    rw [semanticNormalizeProc.eq_9]
    exact StructuralCongruence.subst_cong _ _ _ _ ihBody ihRepl
  case collection =>
    intro ct elems rest ih
    rw [semanticNormalizeProc.eq_10]
    exact StructuralCongruence.collection_general_cong ct _ _ rest ih.1 ih.2
  case other =>
    intro p notBvar notFvar notOutput notInput notDrop notQuote notLambda notMulti notSubst
      notCollection
    rw [semanticNormalizeProc.eq_11 p notBvar notFvar notOutput notInput notDrop notQuote
      notLambda notMulti notSubst notCollection]
    exact .refl _
  case nil =>
    rw [semanticNormalizeProcList.eq_1]
    exact ⟨rfl, fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)⟩
  case cons =>
    intro p ps ihHead ihTail
    rw [semanticNormalizeProcList.eq_2]
    refine ⟨congrArg Nat.succ ihTail.1, ?_⟩
    intro i h₁ h₂
    match i, h₁, h₂ with
    | 0, _, _ => exact ihHead
    | n + 1, h₁, h₂ =>
        exact ihTail.2 n (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

theorem normalizeName_sc (name : Pattern) : semanticNormalizeName name ≡ name :=
  normalize_sc.1 name

theorem normalizeProc_sc (process : Pattern) : semanticNormalizeProc process ≡ process :=
  normalize_sc.2.1 process

/-- The marked name substitution, in closed form. -/
theorem substNameMark_eq (k : Nat) (replacement name : Pattern) :
    semanticSubstNameMark k replacement name =
      if semanticNormalizeName name = .bvar k then (replacement, true)
      else (semanticNormalizeName name, false) := by
  unfold semanticSubstNameMark
  cases normalized : semanticNormalizeName name with
  | bvar m =>
      dsimp only
      rcases Nat.decEq m k with differs | same
      · rw [if_neg (fun hit => differs (beq_iff_eq.mp hit)),
          if_neg (fun equal => differs (Pattern.bvar.inj equal))]
      · subst same
        rw [if_pos (beq_iff_eq.mpr rfl), if_pos rfl]
  | fvar _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm
  | apply _ _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm
  | lambda _ _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm
  | multiLambda _ _ _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm
  | subst _ _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm
  | collection _ _ _ => exact (if_neg (fun equal => Pattern.noConfusion equal)).symm

/-- The name substitution, in closed form: the replacement if the normalised
name is the bound name, the normalised name otherwise. -/
theorem substName_eq (k : Nat) (replacement name : Pattern) :
    semanticSubstName k replacement name =
      if semanticNormalizeName name = .bvar k then replacement
      else semanticNormalizeName name := by
  unfold semanticSubstName
  rw [substNameMark_eq]
  split_ifs <;> rfl

/-- The substituted channel is congruent to the channel. -/
theorem substName_channel_sc {x : Pattern} (inert : ChannelInert x) (replacement : Pattern) :
    semanticSubstName 0 replacement x ≡ x := by
  rw [substName_eq, if_neg inert]
  exact normalizeName_sc x

/-- **One communication of the duplicator.**  Receiving the code `q` on `x`,
the duplicator's body resends `q` and runs it (after normalisation). -/
theorem commSubst_duplicatorBody (x q : Pattern) :
    semanticCommSubst (duplicatorBody x) q =
      par [.apply "POutput"
          [semanticSubstName 0 (.apply "NQuote" [semanticNormalizeProc q]) x,
            semanticNormalizeProc q], semanticNormalizeProc q] :=
  rfl

/-- The result of the communication is congruent to `x!(q) | q`. -/
theorem commSubst_duplicatorBody_sc {x : Pattern} (inert : ChannelInert x) (q : Pattern) :
    semanticCommSubst (duplicatorBody x) q ≡ par [.apply "POutput" [x, q], q] := by
  rw [commSubst_duplicatorBody]
  exact sc_par_two (sc_apply_two "POutput" (substName_channel_sc inert _)
    (normalizeProc_sc q)) (normalizeProc_sc q)

/-- The duplicator beside an output on its channel communicates: the source
is exactly the shape of the COMM rule. -/
def duplicator_comm (x q : Pattern) (rest : List Pattern) :
    par ([.apply "POutput" [x, q], duplicator x] ++ rest) ⇝
      par ([semanticCommSubst (duplicatorBody x) q] ++ rest) :=
  Reduces.comm (n := x) (q := q) (p := duplicatorBody x) (rest := rest)

/-! ## Unfolding -/

/-- **Replication unfolds**: `!P ⇝ !P | P`, for every process `P`. -/
theorem replicate_unfold {x : Pattern} (inert : ChannelInert x) (P : Pattern) :
    Nonempty (replicate x P ⇝ par [replicate x P, P]) := by
  have step := duplicator_comm x (par [duplicator x, P]) []
  simp only [List.append_nil] at step
  -- the result, flattened, is `x!(D | P) | D | P`
  have result : par [semanticCommSubst (duplicatorBody x) (par [duplicator x, P])] ≡
      par [replicate x P, P] := by
    have flatResult : par [semanticCommSubst (duplicatorBody x) (par [duplicator x, P])] ≡
        par [.apply "POutput" [x, par [duplicator x, P]], duplicator x, P] :=
      sc_trans (StructuralCongruence.par_singleton _)
        (sc_trans (commSubst_duplicatorBody_sc inert _)
          (StructuralCongruence.par_flatten [.apply "POutput" [x, par [duplicator x, P]]]
            [duplicator x, P]))
    have flatTarget : par [replicate x P, P] ≡
        par [.apply "POutput" [x, par [duplicator x, P]], duplicator x, P] :=
      sc_trans (StructuralCongruence.par_comm _ _)
        (sc_trans (StructuralCongruence.par_flatten [P]
            [.apply "POutput" [x, par [duplicator x, P]], duplicator x])
          (StructuralCongruence.par_perm _ _ List.perm_append_comm))
    exact sc_trans flatResult (sc_symm flatTarget)
  exact ⟨Reduces.equiv (StructuralCongruence.refl _) step result⟩

/-- The iterates `!P`, `!P | P`, `(!P | P) | P`, …. -/
def unfolding (x P : Pattern) : ℕ → Pattern
  | 0 => replicate x P
  | n + 1 => par [unfolding x P n, P]

/-- **The encoding runs away**: every iterate reduces to the next. -/
theorem unfolding_step {x : Pattern} (inert : ChannelInert x) (P : Pattern) :
    ∀ n, Nonempty (unfolding x P n ⇝ unfolding x P (n + 1))
  | 0 => replicate_unfold inert P
  | n + 1 => by
      obtain ⟨step⟩ := unfolding_step inert P n
      exact ⟨Reduces.par (rest := [P]) step⟩

/-- An infinite reduction sequence starting at `!P`. -/
theorem replicate_runs_forever {x : Pattern} (inert : ChannelInert x) (P : Pattern) :
    ∃ sequence : ℕ → Pattern, sequence 0 = replicate x P ∧
      ∀ n, Nonempty (sequence n ⇝ sequence (n + 1)) :=
  ⟨unfolding x P, rfl, unfolding_step inert P⟩

/-! ## The Lawvere reading -/

/-- Running a code on an argument code: send the argument as code on `x`,
and run the code beside it. -/
def run (x code argument : Pattern) : Pattern :=
  par [.apply "POutput" [x, argument], code]

/-- One-step reducibility, the relation up to which codes represent maps. -/
def ReducesTo (source target : Pattern) : Prop := Nonempty (source ⇝ target)

/-- The endomap whose fixed point is replication: put `P` beside. -/
def beside (P X : Pattern) : Pattern := par [X, P]

/-- The code of replication: the duplicator beside `P`. -/
def duplicatorCode (x P : Pattern) : Pattern := par [duplicator x, P]

/-- **Point-surjectivity.**  The code `D(x) | P` represents the diagonal
composite of `beside P`, up to one reduction step, on every argument code:
`x!(a) | (D(x) | P) ⇝ (x!(a) | a) | P`. -/
theorem duplicator_represents {x : Pattern} (inert : ChannelInert x) (P : Pattern) :
    RepresentsBy (run x) ReducesTo (duplicatorCode x P) (diagonalComposite (run x) (beside P)) := by
  intro argument
  have step := duplicator_comm x argument [P]
  -- rearrange the source into the COMM shape
  have source : run x (duplicatorCode x P) argument ≡
      par ([.apply "POutput" [x, argument], duplicator x] ++ [P]) :=
    StructuralCongruence.par_flatten [.apply "POutput" [x, argument]] [duplicator x, P]
  have target : par ([semanticCommSubst (duplicatorBody x) argument] ++ [P]) ≡
      diagonalComposite (run x) (beside P) argument := by
    change par [semanticCommSubst (duplicatorBody x) argument, P] ≡
      par [par [.apply "POutput" [x, argument], argument], P]
    exact sc_par_two (commSubst_duplicatorBody_sc inert argument) (StructuralCongruence.refl P)
  exact ⟨Reduces.equiv source step target⟩

/-- **The diagonal fixed point**: running the duplicator code on itself
reduces to itself beside `P`. -/
theorem replication_fixedPoint {x : Pattern} (inert : ChannelInert x) (P : Pattern) :
    ReducesTo (run x (duplicatorCode x P) (duplicatorCode x P))
      (beside P (run x (duplicatorCode x P) (duplicatorCode x P))) :=
  diagonal (run x) ReducesTo (beside P) (duplicator_represents inert P)

/-- The diagonal fixed point is replication beside one copy: `run c c` is
`!P | P` up to structural congruence. -/
theorem run_duplicatorCode_sc (x P : Pattern) :
    run x (duplicatorCode x P) (duplicatorCode x P) ≡ par [replicate x P, P] := by
  have left : run x (duplicatorCode x P) (duplicatorCode x P) ≡
      par [.apply "POutput" [x, par [duplicator x, P]], duplicator x, P] :=
    StructuralCongruence.par_flatten [.apply "POutput" [x, par [duplicator x, P]]]
      [duplicator x, P]
  have right : par [replicate x P, P] ≡
      par [.apply "POutput" [x, par [duplicator x, P]], duplicator x, P] :=
    sc_trans (StructuralCongruence.par_comm _ _)
      (sc_trans (StructuralCongruence.par_flatten [P]
          [.apply "POutput" [x, par [duplicator x, P]], duplicator x])
        (StructuralCongruence.par_perm _ _ List.perm_append_comm))
  exact sc_trans left (sc_symm right)

/-- The concrete instance on the closed name `@0`. -/
theorem replicate_atZero_unfold (P : Pattern) :
    Nonempty (replicate atZero P ⇝ par [replicate atZero P, P]) :=
  replicate_unfold atZero_channelInert P

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
