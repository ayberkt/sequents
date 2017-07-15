type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fname : string) => Tokens.EOF (!pos, !pos)

val between = fn yt => Coord.addchar (size yt) o (!pos)

exception LexerError of pos

%%
%arg (fname : string);
%header (functor PropLexFun (structure Tokens : Prop_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any   = [@a-zA-Z0-9];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (pos := between yytext; continue ());

"~"                => (Tokens.NEG     (!pos, Coord.nextchar o (!pos)));
"=>"               => (Tokens.IMPL    (!pos, Coord.nextchar o (!pos)));
"/\\"              => (Tokens.CONJ    (!pos, Coord.nextchar o (!pos)));
"\\/"              => (Tokens.DISJ    (!pos, Coord.nextchar o (!pos)));
"T"                => (Tokens.TOP     (!pos, Coord.nextchar o (!pos)));
"F"                => (Tokens.BOT     (!pos, Coord.nextchar o (!pos)));

"("                => (Tokens.LPAREN  (!pos, Coord.nextchar o (!pos)));
")"                => (Tokens.RPAREN  (!pos, Coord.nextchar o (!pos)));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, between yytext));
