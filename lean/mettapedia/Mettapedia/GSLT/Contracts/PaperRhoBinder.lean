import Mettapedia.GSLT.Contracts.PaperRho

/-!
# Executable whole-name binder comparison in the literal-slot profile

To ask whether a name denotes a selected binder slot, a quoted process
can have any spelling of a single drop with parallel units. Other
constructors cannot become a drop by the process equations. This gives
a decidable, complete *binder comparison*, without requiring a general
decision procedure for equality of arbitrary pairs of quoted names.
The coarser structural comparison for paper rho separately proves that
this binder test is unchanged.

The executable semantic substitution checks the whole name with this
test. Nonmatching names keep their literal spelling. A matching drop
runs the received code, whereas a matching subject holds its quote.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho

inductive BinderView where
  | empty
  | singleDrop (binder : Option Nat)
  | other

def BinderView.combine : BinderView → BinderView → BinderView
  | .empty, view | view, .empty => view
  | _, _ => .other

private theorem combine_comm (a b : BinderView) : a.combine b = b.combine a := by
  cases a <;> cases b <;> rfl

private theorem combine_assoc (a b c : BinderView) :
    (a.combine b).combine c = a.combine (b.combine c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem combine_empty_iff (a b : BinderView) :
    a.combine b = .empty ↔ a = .empty ∧ b = .empty := by
  cases a <;> cases b <;> simp [BinderView.combine]

private theorem combine_single_iff (a b : BinderView) (index : Nat) :
    a.combine b = .singleDrop (some index) ↔
      (a = .empty ∧ b = .singleDrop (some index)) ∨
        (a = .singleDrop (some index) ∧ b = .empty) := by
  cases a <;> cases b <;> simp [BinderView.combine]

mutual
  def binderIndex : Name → Option Nat
    | .bound index => some index
    | .quote body =>
        match binderView body with
        | .singleDrop index => index
        | _ => none

  def binderView : Process → BinderView
    | .zero => .empty
    | .par a b => (binderView a).combine (binderView b)
    | .drop n => .singleDrop (binderIndex n)
    | .send .. | .receive .. => .other
end

theorem ProcEq.binderView_eq {a b : Process} (eq : ProcEq a b) :
    binderView a = binderView b := by
  induction eq with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | unit a => cases view : binderView a <;> simp [binderView, view, BinderView.combine]
  | swap _ _ => exact combine_comm _ _
  | assoc _ _ _ => exact combine_assoc _ _ _
  | par _ _ first second => simp only [binderView, first, second]
  | send _ _ _ | receive _ _ _ => rfl

theorem NameEq.binderIndex_eq {a b : Name} (eq : NameEq a b) :
    binderIndex a = binderIndex b := by
  induction eq with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | quote_drop _ => rfl
  | quote eq => simp only [binderIndex, eq.binderView_eq]

private theorem processEq_zero_of_empty (p : Process)
    (empty : binderView p = .empty) : ProcEq p .zero := by
  cases p with
  | zero => exact .refl _
  | par a b =>
      obtain ⟨left, right⟩ := (combine_empty_iff _ _).mp empty
      exact .trans (.par (processEq_zero_of_empty a left) (processEq_zero_of_empty b right)) (.unit _)
  | send _ _ | receive _ _ | drop _ => simp [binderView] at empty
termination_by structural p

mutual
  private theorem nameEq_bound_of_index (n : Name) (index : Nat)
      (hit : binderIndex n = some index) : NameEq n (.bound index) := by
    cases n with
    | bound slot =>
        have eq : slot = index := Option.some.inj hit
        subst slot
        exact .refl _
    | quote p =>
        rw [binderIndex] at hit
        cases view : binderView p with
        | empty => rw [view] at hit; cases hit
        | other => rw [view] at hit; cases hit
        | singleDrop slot =>
            rw [view] at hit
            change slot = some index at hit
            subst slot
            obtain ⟨actual, processEq, nameEq⟩ := single_drop_of_view p index view
            exact .trans (.quote processEq) (.trans (.quote_drop actual) nameEq)
  termination_by structural n

  private theorem single_drop_of_view (p : Process) (index : Nat)
      (view : binderView p = .singleDrop (some index)) :
      ∃ n, ProcEq p (.drop n) ∧ NameEq n (.bound index) := by
    cases p with
    | zero | send _ _ | receive _ _ => simp [binderView] at view
    | drop n => exact ⟨n, .refl _, nameEq_bound_of_index n index (BinderView.singleDrop.inj view)⟩
    | par a b =>
        rcases (combine_single_iff _ _ _).mp view with ⟨empty, hit⟩ | ⟨hit, empty⟩
        · obtain ⟨n, processEq, nameEq⟩ := single_drop_of_view b index hit
          exact ⟨n, .trans (.swap _ _)
            (.trans (.par processEq (processEq_zero_of_empty a empty)) (.unit _)), nameEq⟩
        · obtain ⟨n, processEq, nameEq⟩ := single_drop_of_view a index hit
          exact ⟨n, .trans (.par processEq (processEq_zero_of_empty b empty)) (.unit _), nameEq⟩
  termination_by structural p
end

theorem nameEq_bound_iff (n : Name) (index : Nat) :
    NameEq n (.bound index) ↔ binderIndex n = some index :=
  ⟨NameEq.binderIndex_eq, nameEq_bound_of_index n index⟩

def bindName (payload : Process) (depth : Nat) (name : Name) : Name :=
  if binderIndex name = some depth then .quote payload else name

theorem bindName_fits (payload : Process) (depth : Nat) (name : Name) :
    NameSubst depth payload name (bindName payload depth name) := by
  unfold bindName
  split
  · rename_i yes
    exact .hit ((nameEq_bound_iff _ _).mpr yes)
  · rename_i no
    exact .miss (fun agrees => no ((nameEq_bound_iff _ _).mp agrees))

theorem NameSubst.bindName_eq {payload : Process} {depth : Nat} {name result : Name}
    (subst : NameSubst depth payload name result) : bindName payload depth name = result := by
  cases subst with
  | hit same => simp only [bindName, if_pos ((nameEq_bound_iff _ _).mp same)]
  | miss different => simp only [bindName, if_neg (fun hit => different ((nameEq_bound_iff _ _).mpr hit))]

def substitute (payload : Process) (depth : Nat) (body : Process) : Process :=
  match body with
  | .zero => .zero
  | .par a b => .par (substitute payload depth a) (substitute payload depth b)
  | .send n body => .send (bindName payload depth n) (substitute payload depth body)
  | .receive n body => .receive (bindName payload depth n) (substitute payload (depth + 1) body)
  | .drop n => if binderIndex n = some depth then payload else .drop n
termination_by structural body

theorem substitute_fits (payload : Process) (depth : Nat) (body : Process) :
    Subst payload depth body (substitute payload depth body) := by
  cases body with
  | zero => exact .zero
  | par a b => exact .par (substitute_fits payload depth a) (substitute_fits payload depth b)
  | send n tail => exact .send (bindName_fits ..) (substitute_fits payload depth tail)
  | receive n tail => exact .receive (bindName_fits ..) (substitute_fits payload (depth + 1) tail)
  | drop n =>
      unfold substitute
      split
      · rename_i yes
        exact .drop_hit ((nameEq_bound_iff _ _).mpr yes)
      · rename_i no
        exact .drop_miss (fun agrees => no ((nameEq_bound_iff _ _).mp agrees))
termination_by structural body

theorem Subst.substitute_eq {payload : Process} {depth : Nat} {body result : Process}
    (step : Subst payload depth body result) : substitute payload depth body = result := by
  induction step with
  | zero => rfl
  | par _ _ first second => simp only [substitute, first, second]
  | send names _ ih | receive names _ ih => simp only [substitute, names.bindName_eq, ih]
  | drop_hit proof => simp only [substitute, if_pos ((nameEq_bound_iff _ _).mp proof)]
  | drop_miss proof =>
      simp only [substitute, if_neg (fun agrees => proof ((nameEq_bound_iff _ _).mpr agrees))]

theorem subst_iff_substitute (payload : Process) (depth : Nat) (body result : Process) :
    Subst payload depth body result ↔ substitute payload depth body = result :=
  ⟨Subst.substitute_eq, fun same => same ▸ substitute_fits payload depth body⟩

namespace BinderControls

theorem units_and_nesting_do_not_hide_a_whole_name :
    binderIndex (.quote (.par .zero (.drop (.quote (.drop (.bound 2)))))) = some 2 := rfl

theorem another_parallel_component_prevents_hit :
    ¬ NameEq (.quote (.par (.drop (.bound 0)) (.drop (.bound 0)))) (.bound 0) := by
  rw [nameEq_bound_iff]
  decide

end BinderControls

#print axioms nameEq_bound_iff
#print axioms subst_iff_substitute
#print axioms BinderControls.units_and_nesting_do_not_hide_a_whole_name
#print axioms BinderControls.another_parallel_component_prevents_hit

end Mettapedia.GSLT.Contracts.PaperRho
