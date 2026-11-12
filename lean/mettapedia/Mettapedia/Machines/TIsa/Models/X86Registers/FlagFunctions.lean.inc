import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def undef_read_logic (_ : Unit) : SailM Nat := do
  (undefined_nat ())

/- Type quantifiers: k_ex567873_ : Bool -/

def _get_rflagsbits_af (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_rflagsbits_cf (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_rflagsbits_of (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_rflagsbits_pf (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_rflagsbits_sf (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_rflagsbits_zf (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def undef_read (_ : Unit) : SailM Nat := do
  (undef_read_logic ())


def undef_flg_logic (_ : Unit) : SailM Nat := do
  (undef_read ())


def undef_flg (_ : Unit) : SailM (BitVec 1) := do
  let sailval ← (( do (undef_flg_logic ()) ) : SailM Nat )
  (pure (bits_of_int sailval 1))


def log_rflags_write (_ : Unit) : SailM Unit := do
  (pure (print_bits "rflags = " (← readReg rflags)))


def write_user_rflags (user_flags_vector : (BitVec 32)) (undefined_mask : (BitVec 32)) : SailM Unit := do
  let input_rflags ← (( do readReg rflags ) : SailM rflagsbits )
  if (((_get_rflagsbits_cf undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_cf rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_cf rflags_var (_get_rflagsbits_cf user_flags_vector))
      writeReg rflags new_rflags)
  if (((_get_rflagsbits_pf undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_pf rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_pf rflags_var (_get_rflagsbits_pf user_flags_vector))
      writeReg rflags new_rflags)
  if (((_get_rflagsbits_af undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_af rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_af rflags_var (_get_rflagsbits_af user_flags_vector))
      writeReg rflags new_rflags)
  if (((_get_rflagsbits_zf undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_zf rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_zf rflags_var (_get_rflagsbits_zf user_flags_vector))
      writeReg rflags new_rflags)
  if (((_get_rflagsbits_sf undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_sf rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_sf rflags_var (_get_rflagsbits_sf user_flags_vector))
      writeReg rflags new_rflags)
  if (((_get_rflagsbits_of undefined_mask) == 1#1) : Bool)
  then
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let sailval ← (( do (undef_flg ()) ) : SailM (BitVec 1) )
      let new_rflags : rflagsbits := (_update_rflagsbits_of rflags_var sailval)
      writeReg rflags new_rflags)
  else
    (do
      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
      let new_rflags : rflagsbits :=
        (_update_rflagsbits_of rflags_var (_get_rflagsbits_of user_flags_vector))
      writeReg rflags new_rflags)
  if ((← readReg log_register_writes) : Bool)
  then (log_rflags_write ())
  else (pure ())

/- Type quantifiers: phy_addr : Int -/


end X86Registers.Functions
