(* Export the finite ProofTrace closure of a selected HOL Light theorem.

   This file runs only with the checked-in ProofTrace kernel patch applied.
   The emitted JSON-lines files are an untrusted source artifact: MIK must
   independently validate their rule applications and theorem results. *)

#use "ProofTrace/proofs.ml";;

let proof_children proof =
  let Proof(_,_,content) = proof in
  match content with
    Prefl _ | Pbeta _ | Passume _ | Paxiom _ | Pdef _ -> []
  | Ptrans(left,right)
  | Pmkcomb(left,right)
  | Peqmp(left,right)
  | Pdeduct(left,right) -> [left;right]
  | Pabs(parent,_)
  | Pinst(parent,_)
  | Pinstt(parent,_)
  | Pdeft(parent,_,_,_) -> [parent];;

let proof_closure root =
  let seen = Hashtbl.create 257 in
  let rec visit proof =
    let index = proof_index proof in
    if not (Hashtbl.mem seen index) then begin
      Hashtbl.add seen index proof;
      List.iter visit (proof_children proof)
    end in
  visit root;
  Hashtbl.fold (fun _ proof acc -> proof :: acc) seen []
  |> List.sort (fun left right -> proof_index left - proof_index right);;

let write_lines filename render values =
  let channel = open_out filename in
  List.iter
    (fun value -> Printf.fprintf channel "%s\n" (render value))
    values;
  flush channel;
  close_out channel;;

let dump_proof_closure prefix theorem_name theorem =
  let root = proof_of theorem in
  let closure = proof_closure root in
  write_lines (prefix ^ ".proofs") proof_string closure;
  write_lines (prefix ^ ".theorems") theorem_string closure;
  let names = open_out (prefix ^ ".names") in
  Printf.fprintf names
    "{\"id\": %d, \"nm\": \"%s\"}\n"
    (proof_index root) (String.escaped theorem_name);
  flush names;
  close_out names;
  Printf.printf
    "HOL_LIGHT_PROOF_CLOSURE_OK theorem=%s root=%d nodes=%d\n"
    theorem_name (proof_index root) (List.length closure);;

let output_prefix =
  try Sys.getenv "MIK_HOL_LIGHT_TRACE_PREFIX"
  with Not_found -> "ProofTrace/mik_self_imp";;

let p = `p:bool`;;
let self_imp = DISCH p (ASSUME p);;

if not (aconv (concl self_imp) (mk_imp(p,p))) then
  failwith "HOLLightProofClosure: SELF_IMP conclusion";;

if hyp self_imp <> [] then
  failwith "HOLLightProofClosure: SELF_IMP hypotheses";;

dump_proof_closure output_prefix "SELF_IMP" self_imp;;

#quit;;
