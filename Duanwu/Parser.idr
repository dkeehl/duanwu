module Duanwu.Parser

import LispVal
import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators

symbol : Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

parseNumber : Parser LispVal
parseNumber = map LispNum integer

parseNegNum : Parser LispVal
parseNegNum = do char '-'
                 num <- integer
                 pure $ LispNum (- num)

parseString : Parser LispVal
parseString = do char '"'
                 chars <- many (noneOf "\"")
                 char '"'
                 pure $ LispStr (pack chars)

parseAtom : Parser LispVal
parseAtom = do first <- letter <|> symbol
               rest <- many (alphaNum <|> symbol)
               let atom = pack (first :: rest) 
               pure $ case atom of
                           "#t" => LispBool True
                           "#f" => LispBool False
                           _    => LispAtom atom

parseNil : Parser LispVal
parseNil = do string "Nil"
              pure LispNil

mutual
  export
  parseExpr : Parser LispVal
  parseExpr = parseNumber
           <|> parseNegNum
           <|> parseNil
           <|> parseString
           <|> parseAtom
           <|> parseQuoted
           <|> parseList
           <|> parseDotted

  parseList : Parser LispVal
  parseList = do char '('
                 spaces
                 e <- sepBy parseExpr spaces
                 spaces
                 char ')'
                 pure $ LispList e

  parseDotted : Parser LispVal
  parseDotted = do char '('
                   head <- sepBy parseExpr spaces
                   spaces
                   char '.'
                   spaces
                   tail <- parseExpr
                   char ')'
                   pure $ LispDotted head tail

  parseQuoted : Parser LispVal
  parseQuoted = do char '\''
                   e <- parseExpr
                   pure $ LispList [LispAtom "quote", e]

export
readExpr : String -> Either LispError LispVal
readExpr input = case parse parseExpr input of
                      Left err => Left $ Parser err
                      Right val => Right val

