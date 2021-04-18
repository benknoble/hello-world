structure MS = struct

  fun split xs =
    case xs
      of [] => ([], [])
       | [x] => ([x], [])
       | x::y::t => let val (s1, s2) = split t
                    in (x::s1, y::s2)
                    end

  fun merge f xys =
    case xys
      of ([], ys) => ys
       | (xs, []) => xs
       | (x::xs, y::ys) => if f (x, y)
                           then x::(merge f (xs, y::ys))
                           else y::(merge f (x::xs, ys))

  fun sort f xs =
    case xs
      of [] => []
       | [x] => [x]
       | _ => let val (p, q) = split xs
              in merge f (sort f p, sort f q)
              end


  (* examples *)
  val scrambled = [4,2,5,1,8]
  val asc = sort Int.< scrambled (* [1,2,4,5,8] *)
  val desc = sort Int.> scrambled (* [8,5,4,2,1] *)

  (* Int.< has type int * int -> bool; it's the same value as op< unless you've
   * redefined the infix < operator.
   *
   * We could also have written sort (fn (x, y) => x < y) …, so if you want to
   * avoid a confusing example *and* show anonymous function/lambda syntax,
   * there you go. *)
  val asc_anon = sort (fn (x, y) => x < y) scrambled (* [1,2,4,5,8] *)

end
