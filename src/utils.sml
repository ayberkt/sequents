structure Utils = struct

  fun printLn s = print (s ^ "\n")

  fun catOpts [] = []
    | catOpts (SOME x::os) = x::(catOpts os)
    | catOpts (NONE::os) = catOpts os

  val mapi =
    fn f => fn (xs : 'a list) =>
      let
        fun mapi' f [] _ = []
          | mapi' f (x::xs) n = (f (n, x))::(mapi' f xs (n+1))
      in mapi' f xs 0 end

  fun range' 0 = [0]
    | range' x = x::(range' (x-1))

  fun range x =
    if x >= 0
    then range' x
    else raise Fail "negative number in range"

  fun getSome  _ [] = NONE
    | getSome (f : 'a -> 'b option) ((x::xs) : 'a list) =
        (case f x of
          NONE => getSome f xs
        | x => x)

  fun intersperse y [] = []
    | intersperse y [x] = [x]
    | intersperse y (x::xs)=x::y::(intersperse y xs)

  fun nub [] = []
    | nub (x::xs) = x::nub (List.filter (fn y => y <> x) xs)

  val replicateStr : int -> string -> string =
    let
      fun replicateStr' 0 s = ""
        | replicateStr' n s = s ^ replicateStr' (n-1) s
    in
      fn n => fn s =>
        if n >= 0
        then replicateStr' n s
        else raise Fail "replicateStr given negative number"
    end

end
