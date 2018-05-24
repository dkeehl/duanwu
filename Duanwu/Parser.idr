module Duanwu.Parser

import Duanwu.LispVal
import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators

symbol : Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

parseNumber : Parser LispVal
parseNumber = map Num integer

parseNegNum : Parser LispVal
parseNegNum = do char '-'
                 num <- integer
                 pure $ Num (- num)

parseString : Parser LispVal
parseString = do char '"'
                 chars <- many (noneOf "\"")
                 char '"'
                 pure $ Str (pack chars)

parseAtom : Parser LispVal
parseAtom = do first <- letter <|> symbol
               rest <- many (alphaNum <|> symbol)
               let atom = pack (first :: rest) 
               pure $ case atom of
                           "#t" => Bool True
                           "#f" => Bool False
                           _    => Atom atom

parseNil : Parser LispVal
parseNil = do string "nil"
              pure Nil

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
                 pure $ List e

  parseDotted : Parser LispVal
  parseDotted = do char '('
                   head <- sepBy parseExpr spaces
                   spaces
                   char '.'
                   spaces
                   tail <- parseExpr
                   char ')'
                   pure $ Dotted head tail

  parseQuoted : Parser LispVal
  parseQuoted = do char '\''
                   e <- parseExpr
                   pure $ List [Atom "quote", e]

readAndParse : Parser a -> String -> Either LispError a
readAndParse parser input = case parse parser input of
                                 Left err => Left $ Parser err
                                 Right val => Right val

export
readExpr : String -> Either LispError LispVal
readExpr = readAndParse parseExpr

export
readExprList : String -> Either LispError (List LispVal)
readExprList = readAndParse (sepBy parseExpr spaces)

