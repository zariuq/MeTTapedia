use "sml/metta_m1.sml";

fun read_all_file fname =
  let
    val ins = TextIO.openIn fname
    val text = TextIO.inputAll ins
    val _ = TextIO.closeIn ins
  in
    text
  end;

fun run_file fname =
  case run_program_text 80 (read_all_file fname) of
    ProgramOutput text => print text
  | ProgramRunError msg =>
      (TextIO.output (TextIO.stdErr, "ParseError: " ^ msg ^ "\n");
       OS.Process.exit OS.Process.failure);

val _ =
  case CommandLine.arguments () of
    [fname] => run_file fname
  | _ =>
      (case OS.Process.getEnv "METTA_FILE" of
         SOME fname => run_file fname
       | NONE =>
           (TextIO.output (TextIO.stdErr, "usage: METTA_FILE=FILE run_metta_file.sml\n");
            OS.Process.exit OS.Process.failure));
