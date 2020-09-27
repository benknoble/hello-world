(*
 * Once upon a time...
 *)

structure Vampire = struct
  type params = {location: string,
                 birthDate: int,
                 deathDate: int,
                 weaknesses: string list}
  type vampire = params
  fun new (v : params) : vampire = v
  fun age (v : vampire) : int = (#deathDate v) - (#birthDate v)
end

(* Alternate *)
structure Vampire1 = struct
  type params = {location: string,
                 birthDate: int,
                 deathDate: int,
                 weaknesses: string list}

  type vampire = params * int

  fun new (p : params) : vampire =
    let val age = (#deathDate p) - (#birthDate p)
    in (p, age)
    end

  fun age ((_, age) : vampire) : int = age
end

(* ...there was a guy named Vlad *)

structure Romainia = struct
  val dracula = Vampire.new {location="Transylvania",
                             birthDate=1428,
                             deathDate=1476,
                             weaknesses=["Sunlight", "Garlic"]}
end
