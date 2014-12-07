module Language.JavaScript.JSON
       where

import Control.Applicative ((<$>), (<*))

import Text.Parsec ((<|>),
                    char, choice, notFollowedBy, optionMaybe, satisfy)
import Text.ParserCombinators.Parsec.Prim (GenParser)

import Language.JavaScript.Lexer

type JSONParser a = GenParser Char () a

jsonWhiteSpace :: JSONParser Char
jsonWhiteSpace =
  choice $ char <$>
  [ '\t', '\r', '\n', ' ' ]

jsonString =
  do { char '"'; ms <- optionMaybe jsonStringCharacters; char '"' }

jsonStringCharacters =
  do { c <- jsonStringCharacter; ms <- optionMaybe jsonStringCharacters; return () }

jsonStringCharacter =
  do { notFollowedBy $ satisfy $ \c -> c == '"' || c == '\\' || c <= '\x001F'; sourceCharacter } <|>
  do { char '\\'; jsonEscapeSequence }

jsonEscapeSequence =
  jsonEscapeCharacter <|>
  unicodeEscapeSequence

jsonEscapeCharacter =
  choice $ char <$> [ '"', '/', '\\', 'b', 'f', 'n', 'r', 't' ]

jsonNumber =
  do { optionMaybe $ char '-'; decimalIntegerLiteral; mfv <- jsonFraction; mev <- optionMaybe exponentPart; return () }

jsonFraction =
  do { char '.'; decimalDigits }

jsonNullLiteral =
  do { nullLiteral }

jsonBooleanLiteral =
  do { booleanLiteral }

jsonText =
  do { jsonValue }

jsonValue =
  jsonNullLiteral <|>
  jsonBooleanLiteral <|>
  jsonObject <|>
  jsonArray <|>
  jsonString <|>
  jsonNumber

jsonObject =
  do { char '{'; mml <- optionMaybe jsonMemberList; char '}' }

jsonMember =
  do { jsonString; char ':'; jsonValue }

jsonMemberList =
  do { m <- jsonMember; applyRest jsonMemberListRest  }

jsonMemberListRest =
  do { char ','; m <- jsonMember; applyRest jsonMemberListRest }

jsonArray =
  do { char '['; mel <- optionMaybe jsonElementList; char ']' }

jsonElementList =
  do { v <- jsonValue; applyRest jsonElementListRest }

jsonElementListRest =
  do { char ','; v <- jsonValue; applyRest jsonElementListRest }
