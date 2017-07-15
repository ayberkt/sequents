structure PropLrVals =
  PropLrValsFun(structure Token = LrParser.Token)

structure PropLex =
  PropLexFun(structure Tokens = PropLrVals.Tokens)

structure PropParser =
  JoinWithArg
    (structure LrParser = LrParser
     structure ParserData = PropLrVals.ParserData
     structure Lex = PropLex)

structure Parser = struct
  fun stringreader s =
    let
      val pos = ref 0
    	val remainder = ref (String.size s)
  	  fun min(a, b) = if a < b then a else b
  	in
      fn n =>
  	    let
          val m = min(n, !remainder)
  	      val s = String.substring(s, !pos, m)
  	      val () = pos := !pos + m
  	      val () = remainder := !remainder - m
  	    in
  	      s
  	    end
  	end

  exception ParseError of Pos.t * string

  fun error fname (s, pos, pos') : unit =
    raise ParseError (Pos.pos (pos fname) (pos' fname), s)

  fun parse text =
    let
        val lexer =  PropParser.makeLexer (stringreader text) "stdin"
                    (* parse is complete -- skip the next token, either ; or eof *)
        val (res, _) = PropParser.parse (1, lexer, error "stdin", "stdin")
    in
        res
    end
end
