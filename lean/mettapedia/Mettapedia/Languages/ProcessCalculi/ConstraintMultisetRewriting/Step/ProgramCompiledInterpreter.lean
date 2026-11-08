import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledGround

/-!
# The interpreter: equations as data, one fixed family of schemas

An **interpreter** for pattern equations reads the program as data. Here it is itself a program of
pattern equations, `metaProg`, sixteen equations independent of the program it runs; compiled by
`ProgramEquations.compile`, it is a fixed family of sixteen schemas on the step.

* **Code.** An equation is stored as data (`eqCode`): its left-hand side as matching code
  (`mgen`: take a cell apart, check a symbol, bind a variable at its first occurrence, check it
  against the environment at a later one), and its right-hand side as building code (`bgen`, in
  postfix order). The environment is a list of the bound values, newest first, and a variable is
  found by its position.
* **Machine.** `ev P s` tries each stored equation (two equations, so the choice is the program's
  own nondeterminism); `try` starts matching; `mt` matches; `ck` walks the environment to check a
  repeated variable; `bj` builds; `rd` walks the environment to read a variable; `ans a` is the
  answer. Every step but the choice of the equation is administrative.
* **Exactness of the interpreter** (`interpreter_iff`): for a range-restricted program, the
  interpreter reaches `ans a` from `ev (code of the program) s` exactly when one equation of the
  program rewrites `s` to `a`. Matching that succeeds is followed to the answer
  (`match_success`, `build_success`); matching that fails reaches a stuck state that is not an
  answer (`match_failure`); and the machine is deterministic off the choice
  (`meta_deterministic`), so no other answer is reachable (`det_terminal`).
* **The join on the step** (`compiled_iff_interpreted`): on ground calls, one translated firing of
  the compiled program from the thread `s` represents the thread `a` exactly when a run of the
  compiled interpreter, a fixed family of schemas, from the thread `ev (code) s` represents the
  thread `ans a`. This is a simulation up to the interpreter's administrative steps.

On calls with variables the compiled account answers by two-way unification in one firing
(`ProgramEquations.answers_exact`); an interpreter must then allocate fresh variables in
administrative firings (`ProgramCompiledObstruction`), and its answers agree with the compiled ones
only up to the names of those variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-! ## Tuples -/

def seq : List Sx → Sx
  | [] => .sym 0
  | a :: l => .cell a (seq l)

/-- A tagged tuple. -/
def tup (k : ℕ) (l : List Sx) : Sx := .cell (.sym k) (seq l)

def pseq : List Pat → Pat
  | [] => .sym 0
  | p :: ps => .cell p (pseq ps)

def ptup (k : ℕ) (ps : List Pat) : Pat := .cell (.sym k) (pseq ps)

theorem pseq_inst (θ : ℕ → Sx) : ∀ ps : List Pat, (pseq ps).inst θ = seq (ps.map (Pat.inst θ))
  | [] => rfl
  | p :: ps => by
      show Sx.cell (p.inst θ) ((pseq ps).inst θ) = _
      rw [pseq_inst θ ps]
      rfl

theorem ptup_inst (θ : ℕ → Sx) (k : ℕ) (ps : List Pat) :
    (ptup k ps).inst θ = tup k (ps.map (Pat.inst θ)) := by
  show Sx.cell (.sym k) ((pseq ps).inst θ) = _
  rw [pseq_inst]
  rfl

theorem seq_inj : ∀ {l l' : List Sx}, seq l = seq l' ↔ l = l'
  | [], [] => by simp
  | [], _ :: _ => by simp [seq]
  | _ :: _, [] => by simp [seq]
  | a :: l, a' :: l' => by
      simp only [seq, Sx.cell.injEq, List.cons.injEq]
      rw [seq_inj]

theorem tup_inj {k k' : ℕ} {l l' : List Sx} : tup k l = tup k' l' ↔ k = k' ∧ l = l' := by
  simp only [tup, Sx.cell.injEq, Sx.sym.injEq, seq_inj]

/-! ## Data -/

def kons (a l : Sx) : Sx := tup 90 [a, l]
def knil : Sx := tup 91 []

def codeOf : List Sx → Sx
  | [] => knil
  | a :: l => kons a (codeOf l)

theorem codeOf_append (l₁ l₂ : List Sx) :
    codeOf (l₁ ++ l₂) = (l₁.foldr kons (codeOf l₂)) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp [codeOf, ih]

/-- Unary depths. -/
def nat : ℕ → Sx
  | 0 => tup 96 []
  | d + 1 => tup 97 [nat d]

def mcellI : Sx := tup 92 []
def msymI (k : ℕ) : Sx := tup 93 [.sym k]
def mbindI : Sx := tup 94 []
def mcheckI (d : ℕ) : Sx := tup 95 [nat d]
def bsymI (k : ℕ) : Sx := tup 98 [.sym k]
def bcellI : Sx := tup 99 []
def bvarI (d : ℕ) : Sx := tup 100 [nat d]

/-! ## States -/

def evS (P s : Sx) : Sx := tup 101 [P, s]
def tryS (E s : Sx) : Sx := tup 102 [E, s]
def eqcS (M B : Sx) : Sx := tup 103 [M, B]
def mtS (C S E B : Sx) : Sx := tup 104 [C, S, E, B]
def ckS (d E' v C S E B : Sx) : Sx := tup 105 [d, E', v, C, S, E, B]
def bjS (B S E : Sx) : Sx := tup 106 [B, S, E]
def rdS (d E' B S E : Sx) : Sx := tup 107 [d, E', B, S, E]
def ansS (a : Sx) : Sx := tup 108 [a]

theorem kons_inj {a l a' l' : Sx} : kons a l = kons a' l' ↔ a = a' ∧ l = l' := by
  simp [kons, tup_inj]

theorem mtS_inj {C S E B C' S' E' B' : Sx} :
    mtS C S E B = mtS C' S' E' B' ↔ C = C' ∧ S = S' ∧ E = E' ∧ B = B' := by
  simp [mtS, tup_inj]

theorem ckS_inj {d E₁ v C S E B d' E₁' v' C' S' E' B' : Sx} :
    ckS d E₁ v C S E B = ckS d' E₁' v' C' S' E' B' ↔
      d = d' ∧ E₁ = E₁' ∧ v = v' ∧ C = C' ∧ S = S' ∧ E = E' ∧ B = B' := by
  simp [ckS, tup_inj]

theorem evS_inj {P s P' s' : Sx} : evS P s = evS P' s' ↔ P = P' ∧ s = s' := by
  simp [evS, tup_inj]

theorem ansS_inj {a a' : Sx} : ansS a = ansS a' ↔ a = a' := by
  simp [ansS, tup_inj]

/-! ## The interpreter's equations -/

section Rules

private def v (i : ℕ) : Pat := .var i
private def pk (a l : Pat) : Pat := ptup 90 [a, l]
private def pn : Pat := ptup 91 []

def rEvTry : ProgramEquations.Equation := ⟨ptup 101 [pk (v 0) (v 1), v 2], ptup 102 [v 0, v 2]⟩
def rEvSkip : ProgramEquations.Equation := ⟨ptup 101 [pk (v 0) (v 1), v 2], ptup 101 [v 1, v 2]⟩
def rTry : ProgramEquations.Equation :=
  ⟨ptup 102 [ptup 103 [v 0, v 1], v 2], ptup 104 [v 0, pk (v 2) pn, pn, v 1]⟩
def rMcell : ProgramEquations.Equation :=
  ⟨ptup 104 [pk (ptup 92 []) (v 0), pk (.cell (v 1) (v 2)) (v 3), v 4, v 5],
    ptup 104 [v 0, pk (v 1) (pk (v 2) (v 3)), v 4, v 5]⟩
def rMsym : ProgramEquations.Equation :=
  ⟨ptup 104 [pk (ptup 93 [v 0]) (v 1), pk (v 0) (v 2), v 3, v 4], ptup 104 [v 1, v 2, v 3, v 4]⟩
def rMbind : ProgramEquations.Equation :=
  ⟨ptup 104 [pk (ptup 94 []) (v 0), pk (v 1) (v 2), v 3, v 4], ptup 104 [v 0, v 2, pk (v 1) (v 3), v 4]⟩
def rMcheck : ProgramEquations.Equation :=
  ⟨ptup 104 [pk (ptup 95 [v 0]) (v 1), pk (v 2) (v 3), v 4, v 5],
    ptup 105 [v 0, v 4, v 2, v 1, v 3, v 4, v 5]⟩
def rCkSucc : ProgramEquations.Equation :=
  ⟨ptup 105 [ptup 97 [v 0], pk (v 1) (v 2), v 3, v 4, v 5, v 6, v 7],
    ptup 105 [v 0, v 2, v 3, v 4, v 5, v 6, v 7]⟩
def rCkZero : ProgramEquations.Equation :=
  ⟨ptup 105 [ptup 96 [], pk (v 0) (v 1), v 0, v 2, v 3, v 4, v 5], ptup 104 [v 2, v 3, v 4, v 5]⟩
def rMdone : ProgramEquations.Equation := ⟨ptup 104 [pn, pn, v 0, v 1], ptup 106 [v 1, pn, v 0]⟩
def rBsym : ProgramEquations.Equation :=
  ⟨ptup 106 [pk (ptup 98 [v 0]) (v 1), v 2, v 3], ptup 106 [v 1, pk (v 0) (v 2), v 3]⟩
def rBcell : ProgramEquations.Equation :=
  ⟨ptup 106 [pk (ptup 99 []) (v 0), pk (v 1) (pk (v 2) (v 3)), v 4],
    ptup 106 [v 0, pk (.cell (v 2) (v 1)) (v 3), v 4]⟩
def rBvar : ProgramEquations.Equation :=
  ⟨ptup 106 [pk (ptup 100 [v 0]) (v 1), v 2, v 3], ptup 107 [v 0, v 3, v 1, v 2, v 3]⟩
def rRdSucc : ProgramEquations.Equation :=
  ⟨ptup 107 [ptup 97 [v 0], pk (v 1) (v 2), v 3, v 4, v 5], ptup 107 [v 0, v 2, v 3, v 4, v 5]⟩
def rRdZero : ProgramEquations.Equation :=
  ⟨ptup 107 [ptup 96 [], pk (v 0) (v 1), v 2, v 3, v 4], ptup 106 [v 2, pk (v 0) (v 3), v 4]⟩
def rDone : ProgramEquations.Equation := ⟨ptup 106 [pn, pk (v 0) pn, v 1], ptup 108 [v 0]⟩

end Rules

/-- **The interpreter**: sixteen equations, independent of the program it runs. -/
def metaProg : Program :=
  [rEvTry, rEvSkip, rTry, rMcell, rMsym, rMbind, rMcheck, rCkSucc, rCkZero, rMdone, rBsym, rBcell,
    rBvar, rRdSucc, rRdZero, rDone]

/-- An assignment from a list. -/
def sub (l : List Sx) (x : ℕ) : Sx := l.getD x (.sym 0)

abbrev Rt := Relation.ReflTransGen (GRewrite metaProg)

theorem fire {e : ProgramEquations.Equation} (member : e ∈ metaProg) (θ : ℕ → Sx) :
    GRewrite metaProg (e.lhs.inst θ) (e.rhs.inst θ) := ⟨e, member, θ, rfl, rfl⟩

/-! ## Code generation -/

/-- Matching code for a pattern, given the variables bound so far (newest first), and the bound
variables after it. -/
def mgen : Pat → List ℕ → List Sx × List ℕ
  | .var x, B => if x ∈ B then ([mcheckI (B.idxOf x)], B) else ([mbindI], x :: B)
  | .sym k, B => ([msymI k], B)
  | .cell a b, B =>
      (mcellI :: ((mgen a B).1 ++ (mgen b (mgen a B).2).1), (mgen b (mgen a B).2).2)

/-- Building code for a pattern, in postfix order, reading variables by position. -/
def bgen (B : List ℕ) : Pat → List Sx
  | .var x => [bvarI (B.idxOf x)]
  | .sym k => [bsymI k]
  | .cell a b => bgen B a ++ bgen B b ++ [bcellI]

/-- **An equation stored as data.** -/
def eqCode (e : ProgramEquations.Equation) : Sx :=
  eqcS (codeOf (mgen e.lhs []).1) (codeOf (bgen (mgen e.lhs []).2 e.rhs))

/-- A program stored as data. -/
def progCode (prog : Program) : Sx := codeOf (prog.map eqCode)

theorem mgen_bound_sub : ∀ (p : Pat) (B : List ℕ), ∀ x ∈ B, x ∈ (mgen p B).2
  | .var y, B, x, hx => by
      by_cases h : y ∈ B
      · simp [mgen, h, hx]
      · simp [mgen, h, hx]
  | .sym _, _, _, hx => hx
  | .cell a b, B, x, hx => mgen_bound_sub b _ x (mgen_bound_sub a B x hx)

theorem mgen_vars_sub : ∀ (p : Pat) (B : List ℕ), ∀ x ∈ p.vars, x ∈ (mgen p B).2
  | .var y, B, x, hx => by
      simp only [Pat.vars, List.mem_singleton] at hx
      subst hx
      by_cases h : x ∈ B
      · simp [mgen, h]
      · simp [mgen, h]
  | .sym _, _, _, hx => by simp [Pat.vars] at hx
  | .cell a b, B, x, hx => by
      simp only [Pat.vars, List.mem_append] at hx
      rcases hx with hx | hx
      · exact mgen_bound_sub b _ x (mgen_vars_sub a B x hx)
      · exact mgen_vars_sub b _ x hx

/-! ## Walking the environment -/

theorem getElem_map_idxOf {B : List ℕ} {x : ℕ} (member : x ∈ B) (θ : ℕ → Sx) :
    ∃ rest, (B.map θ).drop (B.idxOf x) = θ x :: rest := by
  have lt : B.idxOf x < (B.map θ).length := by
    rw [List.length_map]; exact List.idxOf_lt_length_iff.mpr member
  refine ⟨(B.map θ).drop (B.idxOf x + 1), ?_⟩
  rw [List.drop_eq_getElem_cons lt, List.getElem_map, List.getElem_idxOf]

theorem ck_walk (vv C S E B : Sx) : ∀ (d : ℕ) (L : List Sx), d < L.length →
    Rt (ckS (nat d) (codeOf L) vv C S E B) (ckS (nat 0) (codeOf (L.drop d)) vv C S E B)
  | 0, _, _ => .refl
  | d + 1, w :: L, lt => by
      have step : GRewrite metaProg (ckS (nat (d + 1)) (codeOf (w :: L)) vv C S E B)
          (ckS (nat d) (codeOf L) vv C S E B) :=
        fire (e := rCkSucc) (by simp [metaProg]) (sub [nat d, w, codeOf L, vv, C, S, E, B])
      exact Relation.ReflTransGen.head step (ck_walk vv C S E B d L (by simpa using lt))

theorem rd_walk (Bc S E : Sx) : ∀ (d : ℕ) (L : List Sx), d < L.length →
    Rt (rdS (nat d) (codeOf L) Bc S E) (rdS (nat 0) (codeOf (L.drop d)) Bc S E)
  | 0, _, _ => .refl
  | d + 1, w :: L, lt => by
      have step : GRewrite metaProg (rdS (nat (d + 1)) (codeOf (w :: L)) Bc S E)
          (rdS (nat d) (codeOf L) Bc S E) :=
        fire (e := rRdSucc) (by simp [metaProg]) (sub [nat d, w, codeOf L, Bc, S, E])
      exact Relation.ReflTransGen.head step (rd_walk Bc S E d L (by simpa using lt))

/-! ## Matching that succeeds -/

/-- **Matching that succeeds is followed to the end of the pattern's code.** -/
theorem match_success (p : Pat) : ∀ (B : List ℕ) (θ : ℕ → Sx) (C : List Sx) (S Bb : Sx),
    Rt (mtS (codeOf ((mgen p B).1 ++ C)) (kons (p.inst θ) S) (codeOf (B.map θ)) Bb)
      (mtS (codeOf C) S (codeOf ((mgen p B).2.map θ)) Bb) := by
  induction p with
  | var x =>
      intro B θ C S Bb
      by_cases bound : x ∈ B
      · simp only [mgen, if_pos bound, List.singleton_append]
        obtain ⟨rest, split⟩ := getElem_map_idxOf bound θ
        have first : GRewrite metaProg
            (mtS (codeOf (mcheckI (B.idxOf x) :: C)) (kons (θ x) S) (codeOf (B.map θ)) Bb)
            (ckS (nat (B.idxOf x)) (codeOf (B.map θ)) (θ x) (codeOf C) S (codeOf (B.map θ)) Bb) :=
          fire (e := rMcheck) (by simp [metaProg])
            (sub [nat (B.idxOf x), codeOf C, θ x, S, codeOf (B.map θ), Bb])
        have walk := ck_walk (θ x) (codeOf C) S (codeOf (B.map θ)) Bb (B.idxOf x) (B.map θ)
          (by rw [List.length_map]; exact List.idxOf_lt_length_iff.mpr bound)
        rw [split] at walk
        have last : GRewrite metaProg
            (ckS (nat 0) (codeOf (θ x :: rest)) (θ x) (codeOf C) S (codeOf (B.map θ)) Bb)
            (mtS (codeOf C) S (codeOf (B.map θ)) Bb) :=
          fire (e := rCkZero) (by simp [metaProg])
            (sub [θ x, codeOf rest, codeOf C, S, codeOf (B.map θ), Bb])
        exact (Relation.ReflTransGen.head first walk).tail last
      · simp only [mgen, if_neg bound, List.singleton_append]
        have step : GRewrite metaProg
            (mtS (codeOf (mbindI :: C)) (kons (θ x) S) (codeOf (B.map θ)) Bb)
            (mtS (codeOf C) S (codeOf ((x :: B).map θ)) Bb) :=
          fire (e := rMbind) (by simp [metaProg]) (sub [codeOf C, θ x, S, codeOf (B.map θ), Bb])
        exact Relation.ReflTransGen.single step
  | sym k =>
      intro B θ C S Bb
      have step : GRewrite metaProg
          (mtS (codeOf (msymI k :: C)) (kons (.sym k) S) (codeOf (B.map θ)) Bb)
          (mtS (codeOf C) S (codeOf (B.map θ)) Bb) :=
        fire (e := rMsym) (by simp [metaProg]) (sub [.sym k, codeOf C, S, codeOf (B.map θ), Bb])
      exact Relation.ReflTransGen.single step
  | cell a b iha ihb =>
      intro B θ C S Bb
      simp only [mgen, List.cons_append, List.append_assoc]
      have first : GRewrite metaProg
          (mtS (codeOf (mcellI :: ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C))))
            (kons (.cell (a.inst θ) (b.inst θ)) S) (codeOf (B.map θ)) Bb)
          (mtS (codeOf ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C)))
            (kons (a.inst θ) (kons (b.inst θ) S)) (codeOf (B.map θ)) Bb) :=
        fire (e := rMcell) (by simp [metaProg])
          (sub [codeOf ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C)), a.inst θ, b.inst θ, S,
            codeOf (B.map θ), Bb])
      exact Relation.ReflTransGen.head first
        ((iha B θ _ _ Bb).trans (ihb (mgen a B).2 θ C S Bb))

/-! ## Building -/

/-- **Building code pushes the instance of its pattern.** -/
theorem build_success (Bf : List ℕ) (θ : ℕ → Sx) (q : Pat) :
    (∀ x ∈ q.vars, x ∈ Bf) → ∀ (Bl : List Sx) (S : Sx),
      Rt (bjS (codeOf (bgen Bf q ++ Bl)) S (codeOf (Bf.map θ)))
        (bjS (codeOf Bl) (kons (q.inst θ) S) (codeOf (Bf.map θ))) := by
  induction q with
  | var x =>
      intro covered Bl S
      have bound : x ∈ Bf := covered x (by simp [Pat.vars])
      obtain ⟨rest, split⟩ := getElem_map_idxOf bound θ
      simp only [bgen, List.singleton_append]
      have first : GRewrite metaProg
          (bjS (codeOf (bvarI (Bf.idxOf x) :: Bl)) S (codeOf (Bf.map θ)))
          (rdS (nat (Bf.idxOf x)) (codeOf (Bf.map θ)) (codeOf Bl) S (codeOf (Bf.map θ))) :=
        fire (e := rBvar) (by simp [metaProg]) (sub [nat (Bf.idxOf x), codeOf Bl, S, codeOf (Bf.map θ)])
      have walk := rd_walk (codeOf Bl) S (codeOf (Bf.map θ)) (Bf.idxOf x) (Bf.map θ)
        (by rw [List.length_map]; exact List.idxOf_lt_length_iff.mpr bound)
      rw [split] at walk
      have last : GRewrite metaProg
          (rdS (nat 0) (codeOf (θ x :: rest)) (codeOf Bl) S (codeOf (Bf.map θ)))
          (bjS (codeOf Bl) (kons (θ x) S) (codeOf (Bf.map θ))) :=
        fire (e := rRdZero) (by simp [metaProg]) (sub [θ x, codeOf rest, codeOf Bl, S, codeOf (Bf.map θ)])
      exact (Relation.ReflTransGen.head first walk).tail last
  | sym k =>
      intro _ Bl S
      have step : GRewrite metaProg (bjS (codeOf (bsymI k :: Bl)) S (codeOf (Bf.map θ)))
          (bjS (codeOf Bl) (kons (.sym k) S) (codeOf (Bf.map θ))) :=
        fire (e := rBsym) (by simp [metaProg]) (sub [.sym k, codeOf Bl, S, codeOf (Bf.map θ)])
      exact Relation.ReflTransGen.single step
  | cell a b iha ihb =>
      intro covered Bl S
      have ca : ∀ x ∈ a.vars, x ∈ Bf := fun x hx => covered x (by simp [Pat.vars, hx])
      have cb : ∀ x ∈ b.vars, x ∈ Bf := fun x hx => covered x (by simp [Pat.vars, hx])
      simp only [bgen, List.append_assoc, List.singleton_append]
      have last : GRewrite metaProg
          (bjS (codeOf (bcellI :: Bl)) (kons (b.inst θ) (kons (a.inst θ) S)) (codeOf (Bf.map θ)))
          (bjS (codeOf Bl) (kons (.cell (a.inst θ) (b.inst θ)) S) (codeOf (Bf.map θ))) :=
        fire (e := rBcell) (by simp [metaProg])
          (sub [codeOf Bl, b.inst θ, a.inst θ, S, codeOf (Bf.map θ)])
      exact ((iha ca _ S).trans (ihb cb _ _)).tail last

/-- **An equation whose left-hand side matches is followed to its answer.** -/
theorem try_success (e : ProgramEquations.Equation) (restricted : RangeRestricted e) (θ : ℕ → Sx) :
    Rt (tryS (eqCode e) (e.lhs.inst θ)) (ansS (e.rhs.inst θ)) := by
  have start : GRewrite metaProg (tryS (eqCode e) (e.lhs.inst θ))
      (mtS (codeOf (mgen e.lhs []).1) (kons (e.lhs.inst θ) knil) knil
        (codeOf (bgen (mgen e.lhs []).2 e.rhs))) :=
    fire (e := rTry) (by simp [metaProg])
      (sub [codeOf (mgen e.lhs []).1, codeOf (bgen (mgen e.lhs []).2 e.rhs), e.lhs.inst θ])
  have matched := match_success e.lhs [] θ [] knil (codeOf (bgen (mgen e.lhs []).2 e.rhs))
  rw [List.append_nil] at matched
  have done : GRewrite metaProg
      (mtS knil knil (codeOf ((mgen e.lhs []).2.map θ)) (codeOf (bgen (mgen e.lhs []).2 e.rhs)))
      (bjS (codeOf (bgen (mgen e.lhs []).2 e.rhs)) knil (codeOf ((mgen e.lhs []).2.map θ))) :=
    fire (e := rMdone) (by simp [metaProg])
      (sub [codeOf ((mgen e.lhs []).2.map θ), codeOf (bgen (mgen e.lhs []).2 e.rhs)])
  have built := build_success (mgen e.lhs []).2 θ e.rhs
    (fun x hx => mgen_vars_sub e.lhs [] x (restricted x hx)) [] knil
  rw [List.append_nil] at built
  have answer : GRewrite metaProg (bjS knil (kons (e.rhs.inst θ) knil) (codeOf ((mgen e.lhs []).2.map θ)))
      (ansS (e.rhs.inst θ)) :=
    fire (e := rDone) (by simp [metaProg]) (sub [e.rhs.inst θ, codeOf ((mgen e.lhs []).2.map θ)])
  exact ((((Relation.ReflTransGen.single start).trans matched).tail done).trans built).tail answer

/-! ## Determinism off the choice -/

def htag : Sx → Option ℕ
  | .cell (.sym k) _ => some k
  | _ => none

def phtag : Pat → Option ℕ
  | .cell (.sym k) _ => some k
  | _ => none

theorem htag_inst : ∀ (p : Pat), phtag p ≠ none → ∀ θ : ℕ → Sx, htag (p.inst θ) = phtag p
  | .cell (.sym _) _, _, _ => rfl
  | .var _, h, _ => absurd rfl h
  | .sym _, h, _ => absurd rfl h
  | .cell (.var _) _, h, _ => absurd rfl h
  | .cell (.cell _ _) _, h, _ => absurd rfl h

/-- The two equations of the choice. -/
def evRules : List ProgramEquations.Equation := [rEvTry, rEvSkip]

theorem meta_restricted : ∀ e ∈ metaProg, ∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars := by decide

theorem meta_lhs_rigid : ∀ e ∈ metaProg, phtag e.lhs ≠ none := by decide

theorem meta_rhs_rigid : ∀ e ∈ metaProg, phtag e.rhs ≠ none := by decide

theorem meta_rhs_tag : ∀ e ∈ metaProg, e ∉ evRules → phtag e.rhs ≠ some 101 := by decide

theorem meta_lhs_101 : ∀ e ∈ metaProg, phtag e.lhs = some 101 → e ∈ evRules := by decide

theorem meta_lhs_104 : ∀ e ∈ metaProg, phtag e.lhs = some 104 →
    e ∈ [rMcell, rMsym, rMbind, rMcheck, rMdone] := by decide

theorem meta_lhs_105 : ∀ e ∈ metaProg, phtag e.lhs = some 105 → e ∈ [rCkSucc, rCkZero] := by decide

theorem meta_lhs_108 : ∀ e ∈ metaProg, phtag e.lhs ≠ some 108 := by decide

/-- **Distinct equations of the interpreter never overlap**, except the two of the choice. -/
theorem meta_overlap : ∀ e ∈ metaProg, ∀ e' ∈ metaProg,
    _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.compatible
      e.lhs e'.lhs = true → e = e' ∨ (e ∈ evRules ∧ e' ∈ evRules) := by decide

/-- A state that is not a choice. -/
def NonEv (X : Sx) : Prop := ∀ P s, X ≠ evS P s

/-- A state without successors. -/
def Stuck (X : Sx) : Prop := ∀ Y, ¬ GRewrite metaProg X Y

theorem ev_lhs {e : ProgramEquations.Equation} (he : e ∈ evRules) (θ : ℕ → Sx) :
    ∃ P s, e.lhs.inst θ = evS P s := by
  simp only [evRules, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- **The interpreter is deterministic off the choice.** -/
theorem meta_deterministic {X Y Y' : Sx} (hX : NonEv X) (one : GRewrite metaProg X Y)
    (two : GRewrite metaProg X Y') : Y = Y' := by
  obtain ⟨e, he, θ, hi, rfl⟩ := one
  obtain ⟨e', he', θ', hj, rfl⟩ := two
  rcases meta_overlap e he e' he'
      (_root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.compatible_of_inst
        _ _ (hi.trans hj.symm)) with rfl | ⟨ev, -⟩
  · refine Pat.inst_congr _ fun x hx => ?_
    exact Pat.inst_agree _ (hi.trans hj.symm) x (meta_restricted e he x hx)
  · obtain ⟨P, s, h⟩ := ev_lhs ev θ
    exact absurd (hi.symm.trans h) (hX P s)

theorem step_nonEv {X Y : Sx} (hX : NonEv X) (step : GRewrite metaProg X Y) : NonEv Y := by
  obtain ⟨e, he, θ, hi, rfl⟩ := step
  intro P s h
  by_cases ev : e ∈ evRules
  · obtain ⟨P', s', h'⟩ := ev_lhs ev θ
    exact hX P' s' (hi.symm.trans h')
  · have tag := congrArg htag h
    rw [htag_inst _ (meta_rhs_rigid e he)] at tag
    exact meta_rhs_tag e he ev tag

/-- **A deterministic run to a stuck state is followed by every run**: whatever another run
reaches, it can still reach the stuck state. -/
theorem det_terminal : ∀ {X W : Sx}, Rt X W → ∀ {Z : Sx}, NonEv X → Rt X Z → Stuck Z → Rt W Z := by
  intro X W toW
  induction toW using Relation.ReflTransGen.head_induction_on with
  | refl => intro Z _ toZ _; exact toZ
  | @head A B step _ ih =>
      intro Z hA toZ terminal
      rcases Relation.ReflTransGen.cases_head toZ with rfl | ⟨B', step', rest⟩
      · exact absurd step (terminal _)
      · have same := meta_deterministic hA step step'
        subst same
        exact ih (step_nonEv hA step) rest terminal

theorem stuck_ans (a : Sx) : Stuck (ansS a) := by
  rintro Y ⟨e, he, θ, h, -⟩
  have tag := congrArg htag h
  rw [htag_inst _ (meta_lhs_rigid e he)] at tag
  exact meta_lhs_108 e he tag

theorem ans_unique {X : Sx} (hX : NonEv X) {a b : Sx} (one : Rt X (ansS a)) (two : Rt X (ansS b)) :
    a = b := by
  have back := det_terminal two hX one (stuck_ans a)
  rcases Relation.ReflTransGen.cases_head back with h | ⟨c, step, -⟩
  · exact (ansS_inj.mp h).symm
  · exact absurd step (stuck_ans b c)

/-! ## Matching that fails -/

def NotAns (Z : Sx) : Prop := ∀ a, Z ≠ ansS a

theorem stuck_msym {k : ℕ} {C s S E B : Sx} (hs : s ≠ .sym k) :
    Stuck (mtS (kons (msymI k) C) (kons s S) E B) := by
  rintro Y ⟨e, he, θ, h, -⟩
  have tag := congrArg htag h
  rw [htag_inst _ (meta_lhs_rigid e he)] at tag
  have group := meta_lhs_104 e he tag
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at group
  rcases group with rfl | rfl | rfl | rfl | rfl
  · have h' : mtS (kons mcellI (θ 0)) (kons (.cell (θ 1) (θ 2)) (θ 3)) (θ 4) (θ 5) =
        mtS (kons (msymI k) C) (kons s S) E B := h
    simp [mtS_inj, kons_inj, mcellI, msymI, tup_inj] at h'
  · have h' : mtS (kons (tup 93 [θ 0]) (θ 1)) (kons (θ 0) (θ 2)) (θ 3) (θ 4) =
        mtS (kons (msymI k) C) (kons s S) E B := h
    rw [mtS_inj, kons_inj, kons_inj] at h'
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, -⟩ := h'
    rw [msymI, tup_inj] at h1
    exact hs (h2.symm.trans (List.cons.inj h1.2).1)
  · have h' : mtS (kons mbindI (θ 0)) (kons (θ 1) (θ 2)) (θ 3) (θ 4) =
        mtS (kons (msymI k) C) (kons s S) E B := h
    simp [mtS_inj, kons_inj, mbindI, msymI, tup_inj] at h'
  · have h' : mtS (kons (tup 95 [θ 0]) (θ 1)) (kons (θ 2) (θ 3)) (θ 4) (θ 5) =
        mtS (kons (msymI k) C) (kons s S) E B := h
    simp [mtS_inj, kons_inj, msymI, tup_inj] at h'
  · have h' : mtS knil knil (θ 0) (θ 1) = mtS (kons (msymI k) C) (kons s S) E B := h
    simp [mtS_inj, kons, knil, tup_inj] at h'

theorem stuck_mcell_sym {j : ℕ} {C S E B : Sx} : Stuck (mtS (kons mcellI C) (kons (.sym j) S) E B) := by
  rintro Y ⟨e, he, θ, h, -⟩
  have tag := congrArg htag h
  rw [htag_inst _ (meta_lhs_rigid e he)] at tag
  have group := meta_lhs_104 e he tag
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at group
  rcases group with rfl | rfl | rfl | rfl | rfl
  · have h' : mtS (kons mcellI (θ 0)) (kons (.cell (θ 1) (θ 2)) (θ 3)) (θ 4) (θ 5) =
        mtS (kons mcellI C) (kons (.sym j) S) E B := h
    simp [mtS_inj, kons_inj] at h'
  · have h' : mtS (kons (tup 93 [θ 0]) (θ 1)) (kons (θ 0) (θ 2)) (θ 3) (θ 4) =
        mtS (kons mcellI C) (kons (.sym j) S) E B := h
    simp [mtS_inj, kons_inj, mcellI, tup_inj] at h'
  · have h' : mtS (kons mbindI (θ 0)) (kons (θ 1) (θ 2)) (θ 3) (θ 4) =
        mtS (kons mcellI C) (kons (.sym j) S) E B := h
    simp [mtS_inj, kons_inj, mbindI, mcellI, tup_inj] at h'
  · have h' : mtS (kons (tup 95 [θ 0]) (θ 1)) (kons (θ 2) (θ 3)) (θ 4) (θ 5) =
        mtS (kons mcellI C) (kons (.sym j) S) E B := h
    simp [mtS_inj, kons_inj, mcellI, tup_inj] at h'
  · have h' : mtS knil knil (θ 0) (θ 1) = mtS (kons mcellI C) (kons (.sym j) S) E B := h
    simp [mtS_inj, kons, knil, tup_inj] at h'

theorem stuck_ck {w vv E' C S E B : Sx} (hw : w ≠ vv) : Stuck (ckS (nat 0) (kons w E') vv C S E B) := by
  rintro Y ⟨e, he, θ, h, -⟩
  have tag := congrArg htag h
  rw [htag_inst _ (meta_lhs_rigid e he)] at tag
  have group := meta_lhs_105 e he tag
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at group
  rcases group with rfl | rfl
  · have h' : ckS (tup 97 [θ 0]) (kons (θ 1) (θ 2)) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7) =
        ckS (nat 0) (kons w E') vv C S E B := h
    simp [ckS_inj, nat, tup_inj] at h'
  · have h' : ckS (tup 96 []) (kons (θ 0) (θ 1)) (θ 0) (θ 2) (θ 3) (θ 4) (θ 5) =
        ckS (nat 0) (kons w E') vv C S E B := h
    rw [ckS_inj, kons_inj] at h'
    obtain ⟨-, ⟨h1, -⟩, h2, -⟩ := h'
    exact hw (h1.symm.trans h2)

theorem notAns_mt {C S E B : Sx} : NotAns (mtS C S E B) := fun a h => by simp [mtS, ansS, tup_inj] at h

theorem notAns_ck {d E' vv C S E B : Sx} : NotAns (ckS d E' vv C S E B) := fun a h => by
  simp [ckS, ansS, tup_inj] at h

/-- **Matching that fails reaches a stuck state that is not an answer.** -/
theorem match_failure (p : Pat) : ∀ (B : List ℕ) (θ : ℕ → Sx) (s : Sx) (C : List Sx) (S Bb : Sx),
    (∀ θ' : ℕ → Sx, (∀ x ∈ B, θ' x = θ x) → p.inst θ' ≠ s) →
    ∃ Z, Rt (mtS (codeOf ((mgen p B).1 ++ C)) (kons s S) (codeOf (B.map θ)) Bb) Z ∧ Stuck Z ∧
      NotAns Z := by
  induction p with
  | var x =>
      intro B θ s C S Bb fails
      by_cases bound : x ∈ B
      · have differs : θ x ≠ s := fails θ (fun _ _ => rfl)
        simp only [mgen, if_pos bound, List.singleton_append]
        obtain ⟨rest, split⟩ := getElem_map_idxOf bound θ
        have first : GRewrite metaProg
            (mtS (codeOf (mcheckI (B.idxOf x) :: C)) (kons s S) (codeOf (B.map θ)) Bb)
            (ckS (nat (B.idxOf x)) (codeOf (B.map θ)) s (codeOf C) S (codeOf (B.map θ)) Bb) :=
          fire (e := rMcheck) (by simp [metaProg])
            (sub [nat (B.idxOf x), codeOf C, s, S, codeOf (B.map θ), Bb])
        have walk := ck_walk s (codeOf C) S (codeOf (B.map θ)) Bb (B.idxOf x) (B.map θ)
          (by rw [List.length_map]; exact List.idxOf_lt_length_iff.mpr bound)
        rw [split] at walk
        exact ⟨_, Relation.ReflTransGen.head first walk, stuck_ck differs, notAns_ck⟩
      · exfalso
        refine fails (fun y => if y = x then s else θ y) (fun y hy => ?_) (by simp [Pat.inst])
        have : y ≠ x := fun same => bound (same ▸ hy)
        simp [this]
  | sym k =>
      intro B θ s C S Bb fails
      have differs : s ≠ .sym k := fun same => fails θ (fun _ _ => rfl) (by simp [Pat.inst, same])
      exact ⟨_, .refl, stuck_msym differs, notAns_mt⟩
  | cell a b iha ihb =>
      intro B θ s C S Bb fails
      simp only [mgen, List.cons_append, List.append_assoc]
      cases s with
      | sym j => exact ⟨_, .refl, stuck_mcell_sym, notAns_mt⟩
      | cell s₁ s₂ =>
          have first : GRewrite metaProg
              (mtS (codeOf (mcellI :: ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C))))
                (kons (.cell s₁ s₂) S) (codeOf (B.map θ)) Bb)
              (mtS (codeOf ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C)))
                (kons s₁ (kons s₂ S)) (codeOf (B.map θ)) Bb) :=
            fire (e := rMcell) (by simp [metaProg])
              (sub [codeOf ((mgen a B).1 ++ ((mgen b (mgen a B).2).1 ++ C)), s₁, s₂, S,
                codeOf (B.map θ), Bb])
          by_cases left : ∃ θ₁ : ℕ → Sx, (∀ x ∈ B, θ₁ x = θ x) ∧ a.inst θ₁ = s₁
          · obtain ⟨θ₁, agree, matched⟩ := left
            have rightFails : ∀ θ' : ℕ → Sx, (∀ x ∈ (mgen a B).2, θ' x = θ₁ x) → b.inst θ' ≠ s₂ := by
              intro θ' agree' same
              refine fails θ' (fun x hx => (agree' x (mgen_bound_sub a B x hx)).trans (agree x hx)) ?_
              have leftSame : a.inst θ' = s₁ := by
                rw [← matched]
                exact Pat.inst_congr a fun x hx => agree' x (mgen_vars_sub a B x hx)
              simp [Pat.inst, leftSame, same]
            have env : B.map θ = B.map θ₁ := List.map_congr_left fun x hx => (agree x hx).symm
            have matchedRun := match_success a B θ₁ ((mgen b (mgen a B).2).1 ++ C) (kons s₂ S) Bb
            rw [matched, ← env] at matchedRun
            obtain ⟨Z, rest, stuck, notAns⟩ := ihb (mgen a B).2 θ₁ s₂ C S Bb rightFails
            exact ⟨Z, Relation.ReflTransGen.head first (matchedRun.trans rest), stuck, notAns⟩
          · obtain ⟨Z, rest, stuck, notAns⟩ := iha B θ s₁ ((mgen b (mgen a B).2).1 ++ C) (kons s₂ S) Bb
              (fun θ' agree same => left ⟨θ', agree, same⟩)
            exact ⟨Z, Relation.ReflTransGen.head first rest, stuck, notAns⟩

theorem try_nonEv (E s : Sx) : NonEv (tryS E s) := fun P s' h => by simp [tryS, evS, tup_inj] at h

/-- **An equation whose left-hand side does not match reaches a stuck state that is not an
answer.** -/
theorem try_failure (e : ProgramEquations.Equation) {s : Sx} (fails : ∀ θ : ℕ → Sx, e.lhs.inst θ ≠ s) :
    ∃ Z, Rt (tryS (eqCode e) s) Z ∧ Stuck Z ∧ NotAns Z := by
  have start : GRewrite metaProg (tryS (eqCode e) s)
      (mtS (codeOf (mgen e.lhs []).1) (kons s knil) knil (codeOf (bgen (mgen e.lhs []).2 e.rhs))) :=
    fire (e := rTry) (by simp [metaProg])
      (sub [codeOf (mgen e.lhs []).1, codeOf (bgen (mgen e.lhs []).2 e.rhs), s])
  obtain ⟨Z, rest, stuck, notAns⟩ := match_failure e.lhs [] (fun _ => .sym 0) s [] knil
    (codeOf (bgen (mgen e.lhs []).2 e.rhs)) (fun θ' _ => fails θ')
  rw [List.append_nil] at rest
  exact ⟨Z, Relation.ReflTransGen.head start rest, stuck, notAns⟩

/-! ## The choice of the equation -/

theorem ev_reaches_try (s : Sx) (e : ProgramEquations.Equation) :
    ∀ P : List ProgramEquations.Equation, e ∈ P → Rt (evS (codeOf (P.map eqCode)) s) (tryS (eqCode e) s)
  | [], h => absurd h List.not_mem_nil
  | e' :: P, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact .single (fire (e := rEvTry) (by simp [metaProg]) (sub [eqCode e, codeOf (P.map eqCode), s]))
      · exact Relation.ReflTransGen.head
          (fire (e := rEvSkip) (by simp [metaProg]) (sub [eqCode e', codeOf (P.map eqCode), s]))
          (ev_reaches_try s e P h)

theorem ev_answers (s a : Sx) : ∀ P : List ProgramEquations.Equation,
    Rt (evS (codeOf (P.map eqCode)) s) (ansS a) → ∃ e ∈ P, Rt (tryS (eqCode e) s) (ansS a) := by
  intro P
  induction P with
  | nil =>
      intro run
      rcases Relation.ReflTransGen.cases_head run with h | ⟨Y, ⟨e, he, θ, hi, -⟩, -⟩
      · exact absurd h (by simp [evS, ansS, tup_inj])
      · exfalso
        have tag := congrArg htag hi
        rw [htag_inst _ (meta_lhs_rigid e he)] at tag
        have ev := meta_lhs_101 e he tag
        simp only [evRules, List.mem_cons, List.mem_nil_iff, or_false] at ev
        rcases ev with rfl | rfl
        · have h' : evS (kons (θ 0) (θ 1)) (θ 2) = evS knil s := hi
          simp [evS_inj, kons, knil, tup_inj] at h'
        · have h' : evS (kons (θ 0) (θ 1)) (θ 2) = evS knil s := hi
          simp [evS_inj, kons, knil, tup_inj] at h'
  | cons e₀ P ih =>
      intro run
      rcases Relation.ReflTransGen.cases_head run with h | ⟨Y, ⟨e, he, θ, hi, rfl⟩, rest⟩
      · exact absurd h (by simp [evS, ansS, tup_inj])
      · have tag := congrArg htag hi
        rw [htag_inst _ (meta_lhs_rigid e he)] at tag
        have ev := meta_lhs_101 e he tag
        simp only [evRules, List.mem_cons, List.mem_nil_iff, or_false] at ev
        have h' : evS (kons (θ 0) (θ 1)) (θ 2) = evS (kons (eqCode e₀) (codeOf (P.map eqCode))) s := by
          rcases ev with rfl | rfl <;> exact hi
        rw [evS_inj, kons_inj] at h'
        obtain ⟨⟨h0, h1⟩, h2⟩ := h'
        rcases ev with rfl | rfl
        · have target : rEvTry.rhs.inst θ = tryS (eqCode e₀) s := by
            show tryS (θ 0) (θ 2) = _
            rw [h0, h2]
          rw [target] at rest
          exact ⟨e₀, List.mem_cons_self, rest⟩
        · have target : rEvSkip.rhs.inst θ = evS (codeOf (P.map eqCode)) s := by
            show evS (θ 1) (θ 2) = _
            rw [h1, h2]
          rw [target] at rest
          obtain ⟨e, he, run⟩ := ih rest
          exact ⟨e, List.mem_cons_of_mem _ he, run⟩

/-! ## Exactness of the interpreter -/

/-- **The interpreter is exact**: for a range-restricted program, it reaches the answer `a` from
`ev (code) s` exactly when one equation of the program rewrites `s` to `a`. -/
theorem interpreter_iff {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e) (s a : Sx) :
    Rt (evS (progCode prog) s) (ansS a) ↔ GRewrite prog s a := by
  constructor
  · intro run
    obtain ⟨e, he, tryRun⟩ := ev_answers s a prog run
    by_cases matched : ∃ θ : ℕ → Sx, e.lhs.inst θ = s
    · obtain ⟨θ, rfl⟩ := matched
      have same := ans_unique (try_nonEv _ _) tryRun (try_success e (restricted e he) θ)
      exact ⟨e, he, θ, rfl, same⟩
    · obtain ⟨Z, toZ, stuck, notAns⟩ := try_failure e (fun θ h => matched ⟨θ, h⟩)
      have back := det_terminal toZ (try_nonEv _ _) tryRun (stuck_ans a)
      rcases Relation.ReflTransGen.cases_head back with h | ⟨c, step, -⟩
      · exact absurd h (notAns a)
      · exact absurd step (stuck c)
  · rintro ⟨e, he, θ, rfl, rfl⟩
    exact (ev_reaches_try _ e prog he).trans (try_success e (restricted e he) θ)

/-! ## The join on the step -/

theorem gthread_tagged (s : Sx) : Tagged (gthread s) := tagged_tagged 40 _

theorem gthread_bounded (s : Sx) (n : ℕ) : Bounded n (gthread s) := fun v hv => by
  rw [gthread, thread, freeVars_tagged] at hv
  exact embed_bounded n s v hv

theorem apply_gthread (σ : Subst rows) (s : Sx) : σ.applyTerm (gthread s) = gthread s := by
  rw [gthread, thread, apply_tagged, apply_embed]

theorem ground_represents_unique {D : Config} {m : ℕ} {a b : Sx}
    (one : ORepresents D (gthread a ::ₘ 0) m) (two : ORepresents D (gthread b ::ₘ 0) m) : a = b := by
  obtain ⟨μ, solved, image⟩ := one
  have agree := represents_agree ⟨μ, solved, image⟩ two μ ((solved.solutions μ).mpr solved.idempotent)
  simp only [Multiset.map_cons, Multiset.map_zero, apply_gthread] at agree
  exact gthread_inj ((Multiset.cons_inj_left _).mp agree)

theorem single_bounded (s : Sx) : ∀ t ∈ [gthread s], Bounded 1 t := fun t h => by
  rw [List.mem_singleton] at h
  rw [h]
  exact gthread_bounded s 1

theorem single_tagged (s : Sx) : ∀ r ∈ [gthread s], Tagged r := fun r h => by
  rw [List.mem_singleton] at h
  rw [h]
  exact gthread_tagged s

/-- **The compiled program answers a ground call in one firing.** -/
theorem compiled_one_firing {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e) (s a : Sx) :
    (∃ D, Translated (compiled prog) (openInitial [gthread s], 1) (D, 2) ∧
      ORepresents D (gthread a ::ₘ 0) 2) ↔ GRewrite prog s a := by
  have rep := openInitial_represents [gthread s] (single_bounded s)
  have tag : ∀ r ∈ (([gthread s] : List Tm) : Multiset Tm), Tagged r := fun r h =>
    single_tagged s r (Multiset.mem_coe.mp h)
  constructor
  · rintro ⟨D, firing, repD⟩
    obtain ⟨W', step, repW'⟩ := eqFiring_complete rep tag firing
    have step' : EqStep prog (gthread s ::ₘ 0, 1) (W', 2) := step
    obtain ⟨b, rewrite, same⟩ := (eqStep_ground_iff restricted s 1 _).mp step'
    obtain ⟨rfl, -⟩ := Prod.mk.inj same
    have := ground_represents_unique repW' repD
    rw [← this]
    exact rewrite
  · intro rewrite
    have step := (eqStep_ground_iff restricted s 1 _).mpr ⟨a, rewrite, rfl⟩
    obtain ⟨D, firing, repD⟩ := eqStep_sound rep tag step
    exact ⟨D, firing, repD⟩

/-- **The compiled interpreter, a fixed family of schemas, reaches the same answers.** -/
theorem interpreted_runs {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e) (s a : Sx) :
    (∃ D m, Relation.ReflTransGen (Translated (compiled metaProg))
        (openInitial [gthread (evS (progCode prog) s)], 1) (D, m) ∧
      ORepresents D (gthread (ansS a) ::ₘ 0) m) ↔ GRewrite prog s a := by
  rw [← interpreter_iff restricted]
  have bounded := single_bounded (evS (progCode prog) s)
  have tag := single_tagged (evS (progCode prog) s)
  constructor
  · rintro ⟨D, m, run, repD⟩
    obtain ⟨W', path, repW'⟩ :=
      (equations_execution metaProg _ tag bounded (gthread (ansS a) ::ₘ 0) m).2 D run
    obtain ⟨b, k, same, groundRun⟩ := (eqRuns_ground meta_restricted (evS (progCode prog) s) 1).1 _ path
    obtain ⟨rfl, -⟩ := Prod.mk.inj same
    have := ground_represents_unique repW' repD
    rw [← this]
    exact groundRun
  · intro groundRun
    obtain ⟨k, path⟩ := (eqRuns_ground meta_restricted (evS (progCode prog) s) 1).2 _ groundRun
    obtain ⟨D, run, repD⟩ :=
      (equations_execution metaProg _ tag bounded (gthread (ansS a) ::ₘ 0) (1 + k)).1 path
    exact ⟨D, 1 + k, run, repD⟩

/-- **The compiled account and the interpreter agree on ground calls**: one translated firing of the
compiled program from the thread `s` represents the thread `a` exactly when a run of the compiled
interpreter from the thread `ev (code) s` represents the thread `ans a`. -/
theorem compiled_iff_interpreted {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e)
    (s a : Sx) :
    (∃ D, Translated (compiled prog) (openInitial [gthread s], 1) (D, 2) ∧
      ORepresents D (gthread a ::ₘ 0) 2) ↔
    (∃ D m, Relation.ReflTransGen (Translated (compiled metaProg))
        (openInitial [gthread (evS (progCode prog) s)], 1) (D, m) ∧
      ORepresents D (gthread (ansS a) ::ₘ 0) m) :=
  (compiled_one_firing restricted s a).trans (interpreted_runs restricted s a).symm

#print axioms match_success
#print axioms build_success
#print axioms try_success
#print axioms meta_overlap
#print axioms meta_deterministic
#print axioms det_terminal
#print axioms match_failure
#print axioms try_failure
#print axioms ev_answers
#print axioms interpreter_iff
#print axioms compiled_one_firing
#print axioms interpreted_runs
#print axioms compiled_iff_interpreted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled
