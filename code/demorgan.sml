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

  fun tt f = ListXProd.map (fn (a, b) => [a, b, f a b]) ([false, true], [false, true])
  val pretty_tt =
    Print.println
    o String.concatWith "\n"
    o (map (String.concatWith "\t" o (map Bool.toString)))
    o tt

  val nand_is_ornot = (tt nand = tt ornot)
  val nor_is_andnot = (tt nor = tt andnot)
  val demorgan_is_right = and' nand_is_ornot nor_is_andnot
end
