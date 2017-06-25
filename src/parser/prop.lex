type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref 0
val eof = fn () => Tokens.EOF(!pos, !pos)

exception LexerError of pos

%%
%header (functor PropLexFun (structure Tokens : Prop_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any   = [@a-zA-Z0-9];
whitespace = [\ \t];
%%

\n                 => (pos := !pos + 1; lex ());
{whitespace}+      => (lex ());

"=>"               => (Tokens.IMPLIES (!pos, pos := !pos + 2));
"/\\"              => (Tokens.CONJ    (!pos, pos := !pos + 2));
"\\/"              => (Tokens.DISJ    (!pos, pos := !pos + 2));
"T"                => (Tokens.TOP     (!pos, pos := !pos + 1));
"F"                => (Tokens.BOT     (!pos, pos := !pos + 1));

"("                => (Tokens.LPAREN (!pos, !pos));
")"                => (Tokens.RPAREN (!pos, !pos));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, !pos));
