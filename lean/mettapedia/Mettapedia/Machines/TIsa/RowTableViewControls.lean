import Mettapedia.Machines.TIsa.RowTableView

/-! Complete rows, private preparation, and premature/stale publication controls. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.RowTableView.Controls

def layout : Layout := ⟨128,64,2⟩
def high : Word := 0x80000001000000ff
def allocated : ByteMemory := fun address =>
  if (64 ≤ address ∧ address < 72) ∨ (128 ≤ address ∧ address < 160) then some 0 else none
def initial : ByteMemory :=
  writeBytes (writeBytes (writeBytes allocated 64 (unpackBytes 8 1)) 128 (unpackBytes 8 7)) 136 (unpackBytes 8 11)
def partialRow : ByteMemory := writeBytes initial 144 (unpackBytes 8 high)
def prepared : ByteMemory := writeBytes partialRow 152 (unpackBytes 8 29)
def published : ByteMemory := writeBytes prepared 64 (unpackBytes 8 2)

theorem initial_rows : observe layout initial = some [[7,11]] := by decide

theorem preparation_hidden : observe layout partialRow = observe layout initial ∧
    observe layout prepared = observe layout initial := by
  have first : observe layout partialRow = observe layout initial :=
    prepare_hidden layout initial 1 144 high (by decide) (by decide) (Or.inr (by decide))
  have second : observe layout prepared = observe layout partialRow :=
    prepare_hidden layout partialRow 1 152 29 (by decide) (by decide) (Or.inr (by decide))
  exact ⟨first,second.trans first⟩

theorem commit_exposes_prepared_row : observe layout published = some [[7,11],[high,29]] := by
  exact commit_appends layout prepared 1 [[7,11]] [high,29] (by decide)
    (preparation_hidden.2.trans initial_rows) (by decide) (by decide) (Or.inl (by decide))

theorem premature_count_exposes_partial_row :
    observe layout (writeBytes partialRow 64 (unpackBytes 8 2)) = some [[7,11],[high,0]] ∧
      observe layout (writeBytes partialRow 64 (unpackBytes 8 2)) ≠ observe layout published := by decide

theorem published_row_is_not_private :
    observe layout (writeBytes initial 128 (unpackBytes 8 99)) ≠ observe layout initial := by decide

theorem missing_row_is_not_zero :
    let missing : ByteMemory := writeBytes (fun _ => none) 64 (unpackBytes 8 1)
    observe layout missing = none ∧ observe layout allocated = some [] := by decide

theorem stale_count_rejected : word published layout.count ≠ some (1#64) := by decide

theorem wrap_cannot_publish_an_append :
    ¬ ((-1#64).toNat + 1 < 2 ^ 64) ∧
      observe layout (writeBytes prepared 64 (unpackBytes 8 (BitVec.ofNat 64 ((-1#64).toNat + 1)))) = some [] := by decide

def aliasLayout : Layout := ⟨64,64,1⟩
def aliasPrepared : ByteMemory := writeBytes (writeBytes (fun _ => none) 64 (unpackBytes 8 1)) 72 (unpackBytes 8 37)

theorem count_alias_corrupts_old_row :
    ¬ aliasLayout.countApart 2 ∧ observe aliasLayout aliasPrepared = some [[1]] ∧
      observe aliasLayout (writeBytes aliasPrepared 64 (unpackBytes 8 2)) = some [[2],[37]] := by decide

#print axioms preparation_hidden
#print axioms commit_exposes_prepared_row
#print axioms premature_count_exposes_partial_row
#print axioms stale_count_rejected
#print axioms count_alias_corrupts_old_row
end Mettapedia.Machines.TIsa.RowTableView.Controls
