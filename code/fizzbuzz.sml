(* https://themonadreader.files.wordpress.com/2014/04/fizzbuzz.pdf *)
structure Prelude = struct
  infixr $
  fun f $ x = f x
  fun id x = x
  fun const x = fn _ => x
  fun curry f = fn a => fn b => f (a, b)

  val join = String.concatWith
  fun range start stop =
    map (fn i => i + start) $ List.tabulate ((stop - start + 1), id)

  fun println s = print $ s ^ "\n"
end

signature FIZZBUZZ = sig
  val apply : int -> string
end

structure Original : FIZZBUZZ = struct
  local
    open Prelude
    infixr $
  in
    fun apply n =
      let
        fun test d s b =
          if n mod d = 0
          then (fn _ => s ^ (b ""))
          else b
        val fizz = test 3 "fizz"
        val buzz = test 5 "buzz"
      in
        fizz (buzz id) $ Int.toString n
      end
  end
end

structure Builder : sig
  type builder = string -> string
  val id : builder
  val base : builder
  val const : string -> builder
  val appE : builder -> string
  val comp : builder -> builder -> builder
  val concat : builder -> builder -> builder
  val flatten : builder list -> builder
  val switch : builder -> builder -> bool -> builder
end = struct
  type builder = string -> string

  fun id s = s
  val base = fn _ => ""
  fun appE b = b ""
  fun const s = fn _ => s
  fun comp l r = l o r
  fun concat l r = fn s => (l s) ^ (r s)
  val flatten = List.foldr (fn (a,b) => concat a b) (fn s => s)
  fun switch t f b = if b then t else f
end

structure WithBuilder : FIZZBUZZ = struct
  local
    open Prelude
    infixr $
  in
    fun apply n =
      let
        fun test d s b =
          Builder.switch
          (Builder.concat (Builder.const s) (Builder.const $ Builder.appE b))
          b
          (n mod d = 0)
        val fizz = test 3 "fizz"
        val buzz = test 5 "buzz"
      in
        fizz (buzz Builder.id) $
        Int.toString n
      end
  end
end

signature SKIPHALTPRINT = sig
  type program
  val interp : program -> string
end

signature PAPER = sig
  include SKIPHALTPRINT
  include FIZZBUZZ
end

structure Raw : PAPER = struct
  open Prelude
  infixr $

  datatype cmd = Skip | Halt | Print of string
  type program = cmd list

  fun interp p = case p
                   of Skip :: p' => interp p'
                    | Halt :: _ => ""
                    | Print s :: p' => s ^ interp p'
                    | [] => ""

  type context = program -> program
  fun fizz (n : int) : context =
    if n mod 3 = 0
    then fn x => Print "fizz" :: x @ [Halt]
    else id
  fun buzz (n : int) : context =
    if n mod 5 = 0
    then fn x => Print "buzz" :: x @ [Halt]
    else id
  fun base (n : int) : context = fn x => x @ [Print $ Int.toString n]
  fun fb (n : int) : program = (base n o fizz n o buzz n) [Skip]

  val apply = interp o fb
end

structure AsFold : PAPER = struct
  open Prelude
  infixr $

  datatype cmd = Skip | Halt | Print of string
  type program = cmd list

  fun step (c : cmd, acc : string) : string =
    case c
      of Skip => acc
       | Halt => ""
       | Print s => s ^ acc

  val interp = List.foldr step ""

  type context = program -> program
  fun fizz (n : int) : context =
    if n mod 3 = 0
    then fn x => Print "fizz" :: x @ [Halt]
    else id
  fun buzz (n : int) : context =
    if n mod 5 = 0
    then fn x => Print "buzz" :: x @ [Halt]
    else id
  fun base (n : int) : context = fn x => x @ [Print $ Int.toString n]
  fun fb (n : int) : program = (base n o fizz n o buzz n) [Skip]

  val apply = interp o fb
end

(* We rely on
 * List.foldr step "" p = List.foldr (op o) Prelude.id (List.map step * p) ""
 *
 * With this we push step into the list of program instructions and simplify:
 * fun step (c, acc) =
 *  case c
 *    of Skip => id acc
 *     | Halt => const ""
 *     | Print s => (fn t => s ^ t) acc
 *
 * And now we see that each command is really a function : string -> string (id,
 * const, and fn t => s ^ t).
 *
 * Furthermore, we interpret by folding (op o), as in the equality; but this is
 * just application of o. So the type of the command becomes the type of a
 * program, and we write them directly. Interpreting is then a matter of
 * applying to the base value!
 *
 * I was so near to rediscovering this backwards with builders! I only had the
 * wrong primitives, I think, and so was doomed to re-produce the final
 * example (the structure Original).
 *
 * The remaining transformations eliminate skip/halt/print altogether via
 * inlining.
 *)
structure Inlining : PAPER = struct
  open Prelude
  infixr $

  type program = string -> string

  val skip : program = id
  val halt : program = const ""
  (* op ^ won't work because it tuple-izes it's argument. Ugh. *)
  val print : string -> program = curry op ^

  fun interp p = p ""

  type context = program -> program
  fun fizz (n : int) : context =
    if n mod 3 = 0
    then fn x => print "fizz" o x o halt
    else id
  fun buzz (n : int) : context =
    if n mod 5 = 0
    then fn x => print "buzz" o x o halt
    else id
  fun base (n : int) : context = fn x => x o (print $ Int.toString n)
  fun fb (n : int) : program = (base n o fizz n o buzz n) skip

  val apply = interp o fb
end

structure T = struct
  local
    open Prelude
    infixr $
  in
    fun try apply start stop =
      let val printFizzBuzz = println o join "\n" o map apply
      in printFizzBuzz $ range start stop
      end
    fun test apply = (map apply $ range 1 20) = [
      "1", "2", "fizz", "4", "buzz",
      "fizz", "7", "8", "fizz", "buzz",
      "11", "fizz", "13", "14", "fizzbuzz",
      "16", "17", "fizz", "19", "buzz"
    ]
  end
end
