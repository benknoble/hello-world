structure MyProg = struct
  val add : int list -> int = List.foldr op+ 0

  val add_s : string list -> string =
    Int.toString
    o add
    o (List.mapPartial Int.fromString)

  fun main (arg0 : string, argv : string list) : OS.Process.status =
    (
    app (fn s => print (s ^ "\n")) argv;
    print ((add_s argv) ^ "\n");
    OS.Process.sleep (Time.fromSeconds 1);
    print ((valOf (OS.Process.getEnv "SHELL")) ^ "\n");
    OS.Process.system "echo 'hoogabooga'";
    OS.Process.success
    )
end
