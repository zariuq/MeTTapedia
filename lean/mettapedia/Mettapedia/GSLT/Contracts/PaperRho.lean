import Mathlib.Data.Multiset.AddSub

/-!
# Locally nameless rho syntax and the literal-slot profile

This reference uses locally nameless binders, the process parallel-monoid
equations, and the two whole-name equations of Meredith and Radestock.
It does not import Pattern equations or a canonical-name decision routine.
Process congruence descends through process continuations and payloads,
not through a name position. This deliberately finer observer is not
the one used to justify the paper's output sugar. For that observer
see `PaperRhoStructuralCongruence`, which reuses this syntax and compares
names by name equivalence inside processes.

The operational entry is the closed-payload communication profile.
Literal code is sealed, while a whole name may be a spelling of a bound
index. Relational substitution does not descend into a missed name.
A drop activates the received process only on a whole-name hit. This
file does not assert named-source alpha adequacy or correspondence for
arbitrary open-payload communication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho

mutual
  inductive Name where
    | bound (index : Nat)
    | quote (body : Process)
  inductive Process where
    | zero
    | par (left right : Process)
    | send (subject : Name) (payload : Process)
    | receive (subject : Name) (body : Process)
    | drop (name : Name)
end

/-- Alpha is represented by the binder slots of the locally nameless
syntax. The only non-congruence process axioms are the parallel laws. -/
inductive ProcEq : Process → Process → Prop
  | refl (p : Process) : ProcEq p p
  | symm {p q : Process} : ProcEq p q → ProcEq q p
  | trans {p q r : Process} : ProcEq p q → ProcEq q r → ProcEq p r
  | unit (p : Process) : ProcEq (.par p .zero) p
  | swap (p q : Process) : ProcEq (.par p q) (.par q p)
  | assoc (p q r : Process) : ProcEq (.par (.par p q) r) (.par p (.par q r))
  | par {p p' q q' : Process} : ProcEq p p' → ProcEq q q' → ProcEq (.par p q) (.par p' q')
  | send (name : Name) {p q : Process} : ProcEq p q → ProcEq (.send name p) (.send name q)
  | receive (name : Name) {p q : Process} : ProcEq p q → ProcEq (.receive name p) (.receive name q)

/-- Whole-name equality, separate from process congruence. In particular
there is no rule lifting a `NameEq` proof into a process's subject slot. -/
inductive NameEq : Name → Name → Prop
  | refl (x : Name) : NameEq x x
  | symm {x y : Name} : NameEq x y → NameEq y x
  | trans {x y z : Name} : NameEq x y → NameEq y z → NameEq x z
  | quote_drop (x : Name) : NameEq (.quote (.drop x)) x
  | quote {p q : Process} : ProcEq p q → NameEq (.quote p) (.quote q)

def processEquations : Setoid Process :=
  ⟨ProcEq, ⟨ProcEq.refl, ProcEq.symm, ProcEq.trans⟩⟩

def nameEquations : Setoid Name :=
  ⟨NameEq, ⟨NameEq.refl, NameEq.symm, NameEq.trans⟩⟩

theorem quote_drop_with_unit (x : Name) :
    NameEq (.quote (.par (.drop x) .zero)) x :=
  .trans (.quote (.unit (.drop x))) (.quote_drop x)

/-! Literal quotation holds closed code. A syntactic quote that really
denotes an ambient bound name can instead be admitted by its whole-name
proof; this includes the wrapped-drop example above. -/
mutual
  inductive ScopedName : Nat → Name → Prop
    | bound {depth index : Nat} : index < depth → ScopedName depth (.bound index)
    | literal {depth : Nat} {code : Process} :
        ScopedProcess 0 code → ScopedName depth (.quote code)
    | binderAlias {depth index : Nat} {code : Process} :
        index < depth → NameEq (.quote code) (.bound index) → ScopedName depth (.quote code)
  inductive ScopedProcess : Nat → Process → Prop
    | zero {depth : Nat} : ScopedProcess depth .zero
    | par {depth : Nat} {p q : Process} :
        ScopedProcess depth p → ScopedProcess depth q → ScopedProcess depth (.par p q)
    | send {depth : Nat} {name : Name} {body : Process} :
        ScopedName depth name → ScopedProcess depth body → ScopedProcess depth (.send name body)
    | receive {depth : Nat} {name : Name} {body : Process} :
        ScopedName depth name → ScopedProcess (depth + 1) body →
          ScopedProcess depth (.receive name body)
    | drop {depth : Nat} {name : Name} : ScopedName depth name → ScopedProcess depth (.drop name)
end

theorem ScopedName.weaken {depth larger : Nat} {name : Name}
    (old : ScopedName depth name) (more : depth ≤ larger) : ScopedName larger name := by
  cases old with
  | bound inside => exact .bound (Nat.lt_of_lt_of_le inside more)
  | literal held => exact .literal held
  | binderAlias inside agrees => exact .binderAlias (Nat.lt_of_lt_of_le inside more) agrees

theorem ScopedProcess.weaken {depth larger : Nat} {p : Process}
    (old : ScopedProcess depth p) (more : depth ≤ larger) : ScopedProcess larger p :=
  match old with
  | .zero => .zero
  | .par left right => .par (left.weaken more) (right.weaken more)
  | .send subject body => .send (subject.weaken more) (body.weaken more)
  | .receive subject body => .receive (subject.weaken more) (body.weaken (Nat.succ_le_succ more))
  | .drop name => .drop (name.weaken more)
termination_by structural old

private theorem scope_par {depth : Nat} {p q : Process} :
    ScopedProcess depth (.par p q) ↔ ScopedProcess depth p ∧ ScopedProcess depth q :=
  ⟨fun hay => by cases hay with | par left right => exact ⟨left, right⟩,
    fun both => .par both.1 both.2⟩

private theorem scope_send {depth : Nat} {subject : Name} {p : Process} :
    ScopedProcess depth (.send subject p) ↔ ScopedName depth subject ∧ ScopedProcess depth p :=
  ⟨fun hay => by cases hay with | send head tail => exact ⟨head, tail⟩,
    fun both => .send both.1 both.2⟩

private theorem scope_receive {depth : Nat} {subject : Name} {p : Process} :
    ScopedProcess depth (.receive subject p) ↔
      ScopedName depth subject ∧ ScopedProcess (depth + 1) p :=
  ⟨fun hay => by cases hay with | receive head tail => exact ⟨head, tail⟩,
    fun both => .receive both.1 both.2⟩

theorem ProcEq.scoped_iff {p q : Process} (eq : ProcEq p q) :
    ∀ depth, ScopedProcess depth p ↔ ScopedProcess depth q := by
  induction eq with
  | refl _ => intro depth; rfl
  | symm _ ih => exact fun depth => (ih depth).symm
  | trans _ _ first second => exact fun depth => (first depth).trans (second depth)
  | unit p =>
      intro depth
      simp [scope_par, show ScopedProcess depth .zero from .zero]
  | swap p q => intro depth; simp [scope_par, and_comm]
  | assoc p q r => intro depth; simp [scope_par, and_assoc]
  | par _ _ first second => intro depth; simp only [scope_par, first depth, second depth]
  | send name _ ih => intro depth; simp only [scope_send, ih depth]
  | receive name _ ih => intro depth; simp only [scope_receive, ih (depth + 1)]

/-- The source name comparison is over the entire name, not a recursive
substitution into the contents of a literal quote. -/
inductive NameSubst (depth : Nat) (payload : Process) : Name → Name → Prop
  | hit {name : Name} : NameEq name (.bound depth) → NameSubst depth payload name (.quote payload)
  | miss {name : Name} : ¬ NameEq name (.bound depth) → NameSubst depth payload name name

/-- Semantic substitution with closed received code. Entering a receiver
changes the selected index but does not alter closed payload code. -/
inductive Subst (payload : Process) : Nat → Process → Process → Prop
  | zero {depth : Nat} : Subst payload depth .zero .zero
  | par {depth : Nat} {first first' second second' : Process} :
      Subst payload depth first first' → Subst payload depth second second' →
      Subst payload depth (.par first second) (.par first' second')
  | send {depth : Nat} {name name' : Name} {body body' : Process} :
      NameSubst depth payload name name' → Subst payload depth body body' →
      Subst payload depth (.send name body) (.send name' body')
  | receive {depth : Nat} {name name' : Name} {body body' : Process} :
      NameSubst depth payload name name' → Subst payload (depth + 1) body body' →
      Subst payload depth (.receive name body) (.receive name' body')
  | drop_hit {depth : Nat} {name : Name} : NameEq name (.bound depth) →
      Subst payload depth (.drop name) payload
  | drop_miss {depth : Nat} {name : Name} : ¬ NameEq name (.bound depth) →
      Subst payload depth (.drop name) (.drop name)

theorem NameSubst.lowers_scope {depth : Nat} {payload : Process} {name result : Name}
    (substitution : NameSubst depth payload name result)
    (admitted : ScopedName (depth + 1) name) (closed : ScopedProcess 0 payload) :
    ScopedName depth result := by
  cases substitution with
  | hit _ => exact .literal closed
  | miss different =>
      cases admitted with
      | bound below =>
          rename_i index
          have notEqual : index ≠ depth := by
            intro same
            subst index
            exact different (.refl _)
          exact .bound (by omega)
      | literal held => exact .literal held
      | binderAlias below sameName =>
          rename_i index code
          have notEqual : index ≠ depth := by
            intro same
            subst index
            exact different sameName
          exact .binderAlias (by omega) sameName

theorem Subst.lowers_scope {depth : Nat} {payload first second : Process}
    (substitution : Subst payload depth first second)
    (admitted : ScopedProcess (depth + 1) first) (closed : ScopedProcess 0 payload) :
    ScopedProcess depth second := by
  induction substitution with
  | zero => exact .zero
  | par _ _ ihLeft ihRight =>
      obtain ⟨left, right⟩ := scope_par.mp admitted
      exact .par (ihLeft left) (ihRight right)
  | send changes _ ih =>
      obtain ⟨head, tail⟩ := scope_send.mp admitted
      exact .send (changes.lowers_scope head closed) (ih tail)
  | receive changes _ ih =>
      obtain ⟨head, tail⟩ := scope_receive.mp admitted
      exact .receive (changes.lowers_scope head closed) (ih tail)
  | drop_hit _ =>
      -- Closed code remains valid in a surrounding context.
      exact closed.weaken (Nat.zero_le _)
  | drop_miss different =>
      cases admitted with
      | drop nameAdmitted => exact .drop ((NameSubst.miss different).lowers_scope nameAdmitted closed)

/-- COMM tests name equality directly; process congruence alone cannot
manufacture equal channel spellings. PAR does not reduce under a quote,
a drop, or a suspended input. -/
inductive Reduces : Process → Process → Prop
  | comm {offered waiting : Name} {payload body target : Process} :
      ScopedName 0 offered → ScopedName 0 waiting →
      ScopedProcess 0 payload → ScopedProcess 1 body →
      NameEq offered waiting → Subst payload 0 body target →
      Reduces (.par (.send offered payload) (.receive waiting body)) target
  | par {p q : Process} (frame : Process) : Reduces p q → Reduces (.par p frame) (.par q frame)
  | equiv {p p' q q' : Process} :
      ProcEq p p' → Reduces p' q' → ProcEq q' q → Reduces p q

theorem Reduces.preserves_closed_scope {source target : Process} (step : Reduces source target)
    (closed : ScopedProcess 0 source) : ScopedProcess 0 target := by
  induction step with
  | comm offered waiting payload body matched substitution =>
      exact substitution.lowers_scope body payload
  | par frame next ih =>
      obtain ⟨left, right⟩ := scope_par.mp closed
      exact .par (ih left) right
  | equiv before next after ih =>
      exact (after.scoped_iff 0).mp (ih ((before.scoped_iff 0).mp closed))

/-! ## A separating observation, not a general equality test -/

namespace Separation

/-- A syntactic tag on a subject; this is not a name equivalence test. -/
def wrapper : Name → Bool
  | .quote (.drop _) => true
  | _ => false

inductive Mark where
  | output (wrapped : Bool)
  | input
  | drop (bit : Bool)
  deriving DecidableEq

private def readCode (marks : Multiset Mark) : Bool :=
  if marks = {Mark.drop true} then true else decide (Mark.output true ∈ marks)

mutual
  def readName : Name → Bool
    | .bound _ => false
    | .quote p => readCode (readProcess p)
  def readProcess : Process → Multiset Mark
    | .zero => 0
    | .par p q => readProcess p + readProcess q
    | .send n _ => {Mark.output (wrapper n)}
    | .receive _ _ => {Mark.input}
    | .drop n => {Mark.drop (readName n)}
end

theorem procEq_preserves_read {p q : Process} (equiv : ProcEq p q) :
    readProcess p = readProcess q := by
  induction equiv with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | unit p => simp [readProcess]
  | swap p q => exact Multiset.add_comm _ _
  | assoc p q r => exact Multiset.add_assoc _ _ _
  | par _ _ first second => simp [readProcess, first, second]
  | send name _ => rfl
  | receive name _ => rfl

theorem nameEq_preserves_read {x y : Name} (equiv : NameEq x y) :
    readName x = readName y := by
  induction equiv with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | quote_drop name =>
      change readCode {Mark.drop (readName name)} = readName name
      cases readName name <;> simp [readCode]
  | quote eq => exact congrArg readCode (procEq_preserves_read eq)

def base : Name := .quote .zero
def wrapped : Name := .quote (.drop base)

/-- The same two names match as subjects but cannot be substituted for one
another by process congruence. Quoting those outputs keeps them distinct. -/
theorem alias_separation :
    NameEq wrapped base ∧ ¬ ProcEq (.send wrapped .zero) (.send base .zero) ∧
      ¬ NameEq (.quote (.send wrapped .zero)) (.quote (.send base .zero)) := by
  refine ⟨.quote_drop _, ?_, ?_⟩
  · intro eq
    have observed := procEq_preserves_read eq
    exact (by decide : ({Mark.output true} : Multiset Mark) ≠ {Mark.output false}) observed
  · intro eq
    have observed := nameEq_preserves_read eq
    change true = false at observed
    exact Bool.noConfusion observed

end Separation

namespace Controls

open Separation (base wrapped)

theorem alias_communicates :
    Reduces (.par (.send wrapped .zero) (.receive base (.drop (.bound 0)))) .zero :=
  .comm (.literal (.drop (.literal .zero))) (.literal .zero) .zero
    (.drop (.bound (by decide))) (.quote_drop _) (.drop_hit (.refl _))

private def underParallelUnit : Name := .quote (.par (.drop (.bound 0)) .zero)

theorem whole_name_under_unit_receives_payload :
    Reduces (.par (.send base (.send base .zero)) (.receive base (.drop underParallelUnit)))
      (.send base .zero) :=
  .comm (.literal .zero) (.literal .zero) (.send (.literal .zero) .zero)
    (.drop (.binderAlias (by decide : 0 < 1) (quote_drop_with_unit (.bound 0))))
    (.refl _) (.drop_hit (quote_drop_with_unit (.bound 0)))

private def inertCode : Name := .quote (.send wrapped .zero)

private theorem inertCode_misses : ¬ NameEq inertCode (.bound 0) := by
  intro same
  have observed := Separation.nameEq_preserves_read same
  change true = false at observed
  exact Bool.noConfusion observed

theorem unmatched_drop_remains_inert :
    Subst .zero 0 (.drop inertCode) (.drop inertCode) ∧
      ¬ Subst .zero 0 (.drop inertCode) .zero := by
  refine ⟨.drop_miss inertCode_misses, ?_⟩
  intro substituted
  cases substituted with
  | drop_hit matched => exact inertCode_misses matched

end Controls

#print axioms quote_drop_with_unit
#print axioms Subst.lowers_scope
#print axioms Reduces.preserves_closed_scope
#print axioms Separation.alias_separation
#print axioms Controls.alias_communicates
#print axioms Controls.whole_name_under_unit_receives_payload
#print axioms Controls.unmatched_drop_remains_inert

end Mettapedia.GSLT.Contracts.PaperRho
