module Duanwu.Lexer

import public Text.Lexer

%default total

public export
data Token = Ident String
           | BoolLit Bool
           | IntLit Integer
           | StrLit String
           | Symbol String
           | Comment String
           | EndInput

export
Show Token where
  show (Ident x)   = "identifier " ++ x
  show (BoolLit x) = "boolean " ++ show x
  show (IntLit x)  = "number " ++ show x
  show (StrLit x)  = "string " ++ show x
  show (Symbol x)  = "symbol" ++ x
  show (Comment x) = "comment"
  show EndInput    = "end of input"

export
Show (TokenData Token) where
  show t = show (line t, col t, tok t)

comment : Lexer
comment = is ';' <+> many (isNot '\n')

ident : Lexer
ident = initial <+> many subseq <|> peculiar
  where
    specialIni : Lexer
    specialIni = oneOf "!$%&*/:<=>?^_~"

    initial : Lexer
    initial = alpha <|> specialIni

    specialSubSeq : Lexer
    specialSubSeq = oneOf "+-.@"

    subseq : Lexer
    subseq = initial <|> digit <|> specialSubSeq

    peculiar : Lexer
    peculiar = is '+' <|> is '-' <|> exact "..."

boolean : Lexer
boolean = exact "#t" <|> exact "#f"

symbols : List String
symbols = ["(", ")", "#(", "'", "`", ",", ",@", "."]

rawTokens : TokenMap Token
rawTokens =
  [(comment, Comment),
   (space, Comment),
   (ident, Ident),
   (intLit, IntLit . cast),
   (stringLit, StrLit . stripQuotes),
   (boolean, BoolLit . (== "#t"))] ++
  map (\x => (exact x, Symbol)) symbols
  where
    stripQuotes : String -> String
    stripQuotes = assert_total (strTail . reverse . strTail . reverse)

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex str
  = case Lexer.Core.lex rawTokens str of
         (tok, (l, c, "")) => Right $ filter notComment tok ++ [MkToken l c EndInput]
         (_, fail) => Left fail
  where
    notComment : TokenData Token -> Bool
    notComment t = case tok t of
                        Comment _ => False
                        _ => True

testLex : String -> String
testLex = show . lex
