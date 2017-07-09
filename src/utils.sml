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

  fun getSome'  _ [] = NONE
    | getSome' (f : 'a -> 'b option) ((x::xs) : 'a list) =
        (case f x of
          NONE => getSome f xs
        | x => x)
  and getSome f xs = (printLn "  -- `getSome`"; getSome' f xs)



end
