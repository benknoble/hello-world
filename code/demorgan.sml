structure Lists = struct
  fun cartesian a b = List.concat (map (fn a => map (fn b => (a,b)) b) a)
end

structure Print = struct
  fun println s = print (s ^ "\n")
end

structure Binary = struct
  fun and' x y = x andalso y
  fun or' x y = x orelse y
  fun nand x y = not (and' x y)
  fun nor x y = not (or' x y)
  fun ornot x y = or' (not x) (not y)
  fun andnot x y = and' (not x) (not y)

  fun tt f = map (fn (a, b) => [a, b, f a b]) (Lists.cartesian [false, true] [false, true])
  val pretty_tt =
    Print.println
    o String.concatWith "\n"
    o (map (String.concatWith "\t" o (map Bool.toString)))
    o tt
end
