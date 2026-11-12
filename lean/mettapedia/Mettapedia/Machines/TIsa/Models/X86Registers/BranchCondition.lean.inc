import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def jcc_cmovcc_setcc_spec (opcode : (BitVec 8)) : SailM Bool := do
  let low_nibble : (BitVec 4) := (Sail.BitVec.truncate (opcode &&& 0x0F#8) 4)
  let v_58 := low_nibble
  if ((eq_bits_nat v_58 0) : Bool)
  then
    (pure (1#1 == (← do
          let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
          (pure (_get_rflagsbits_of rflags_var)))))
  else
    (do
      if ((eq_bits_nat v_58 1) : Bool)
      then
        (pure (0#1 == (← do
              let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
              (pure (_get_rflagsbits_of rflags_var)))))
      else
        (do
          if ((eq_bits_nat v_58 2) : Bool)
          then
            (pure (1#1 == (← do
                  let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                  (pure (_get_rflagsbits_cf rflags_var)))))
          else
            (do
              if ((eq_bits_nat v_58 3) : Bool)
              then
                (pure (0#1 == (← do
                      let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                      (pure (_get_rflagsbits_cf rflags_var)))))
              else
                (do
                  if ((eq_bits_nat v_58 4) : Bool)
                  then
                    (pure (1#1 == (← do
                          let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                          (pure (_get_rflagsbits_zf rflags_var)))))
                  else
                    (do
                      if ((eq_bits_nat v_58 5) : Bool)
                      then
                        (pure (0#1 == (← do
                              let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                              (pure (_get_rflagsbits_zf rflags_var)))))
                      else
                        (do
                          if ((eq_bits_nat v_58 6) : Bool)
                          then
                            (pure ((1#1 == (← do
                                    let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                                    (pure (_get_rflagsbits_cf rflags_var)))) || (1#1 == (← do
                                    let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
                                    (pure (_get_rflagsbits_zf rflags_var))))))
                          else
                            (do
                              if ((eq_bits_nat v_58 7) : Bool)
                              then
                                (pure ((0#1 == (← do
                                        let rflags_var ← (( do readReg rflags ) : SailM rflagsbits
                                          )
                                        (pure (_get_rflagsbits_cf rflags_var)))) && (0#1 == (← do
                                        let rflags_var ← (( do readReg rflags ) : SailM rflagsbits
                                          )
                                        (pure (_get_rflagsbits_zf rflags_var))))))
                              else
                                (do
                                  if ((eq_bits_nat v_58 8) : Bool)
                                  then
                                    (pure (1#1 == (← do
                                          let rflags_var ← (( do readReg rflags ) : SailM
                                            rflagsbits )
                                          (pure (_get_rflagsbits_sf rflags_var)))))
                                  else
                                    (do
                                      if ((eq_bits_nat v_58 9) : Bool)
                                      then
                                        (pure (0#1 == (← do
                                              let rflags_var ← (( do readReg rflags ) : SailM
                                                rflagsbits )
                                              (pure (_get_rflagsbits_sf rflags_var)))))
                                      else
                                        (do
                                          if ((eq_bits_nat v_58 10) : Bool)
                                          then
                                            (pure (1#1 == (← do
                                                  let rflags_var ← (( do readReg rflags ) : SailM
                                                    rflagsbits )
                                                  (pure (_get_rflagsbits_pf rflags_var)))))
                                          else
                                            (do
                                              if ((eq_bits_nat v_58 11) : Bool)
                                              then
                                                (pure (0#1 == (← do
                                                      let rflags_var ← (( do readReg rflags ) :
                                                        SailM rflagsbits )
                                                      (pure (_get_rflagsbits_pf rflags_var)))))
                                              else
                                                (do
                                                  if ((eq_bits_nat v_58 12) : Bool)
                                                  then
                                                    (pure (! ((← do
                                                            let rflags_var ← (( do readReg rflags
                                                              ) : SailM rflagsbits )
                                                            (pure (_get_rflagsbits_sf rflags_var))) == (← do
                                                            let rflags_var ← (( do readReg rflags
                                                              ) : SailM rflagsbits )
                                                            (pure (_get_rflagsbits_of rflags_var))))))
                                                  else
                                                    (do
                                                      if ((eq_bits_nat v_58 13) : Bool)
                                                      then
                                                        (pure ((← do
                                                              let rflags_var ← (( do
                                                                readReg rflags ) : SailM rflagsbits
                                                                )
                                                              (pure (_get_rflagsbits_sf rflags_var))) == (← do
                                                              let rflags_var ← (( do
                                                                readReg rflags ) : SailM rflagsbits
                                                                )
                                                              (pure (_get_rflagsbits_of rflags_var)))))
                                                      else
                                                        (do
                                                          if ((eq_bits_nat v_58 14) : Bool)
                                                          then
                                                            (pure ((1#1 == (← do
                                                                    let rflags_var ← (( do
                                                                      readReg rflags ) : SailM
                                                                      rflagsbits )
                                                                    (pure (_get_rflagsbits_zf
                                                                        rflags_var)))) || (! ((← do
                                                                      let rflags_var ← (( do
                                                                        readReg rflags ) : SailM
                                                                        rflagsbits )
                                                                      (pure (_get_rflagsbits_sf
                                                                          rflags_var))) == (← do
                                                                      let rflags_var ← (( do
                                                                        readReg rflags ) : SailM
                                                                        rflagsbits )
                                                                      (pure (_get_rflagsbits_of
                                                                          rflags_var)))))))
                                                          else
                                                            (do
                                                              if ((eq_bits_nat v_58 15) : Bool)
                                                              then
                                                                (pure ((0#1 == (← do
                                                                        let rflags_var ← (( do
                                                                          readReg rflags ) : SailM
                                                                          rflagsbits )
                                                                        (pure (_get_rflagsbits_zf
                                                                            rflags_var)))) && ((← do
                                                                        let rflags_var ← (( do
                                                                          readReg rflags ) : SailM
                                                                          rflagsbits )
                                                                        (pure (_get_rflagsbits_sf
                                                                            rflags_var))) == (← do
                                                                        let rflags_var ← (( do
                                                                          readReg rflags ) : SailM
                                                                          rflagsbits )
                                                                        (pure (_get_rflagsbits_of
                                                                            rflags_var))))))
                                                              else (pure false))))))))))))))))

end X86Registers.Functions
