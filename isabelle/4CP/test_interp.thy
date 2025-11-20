theory test_interp
imports "theories/Disk/Disk_KCSD"
begin

(* Test interpretation *)
interpretation test_xor: comp_fun_commute "\<lambda>x acc. xor_chain x acc"
  apply standard
  apply (rule ext)
  apply (simp add: xor_chain_left_commute)
  done

end
