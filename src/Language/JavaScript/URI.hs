module Language.JavaScript.URI
       where

import Text.Parsec ((<|>),
                    SourcePos,
                    anyChar, choice, getPosition, many,
                    notFollowedBy, optionMaybe, runParser,
                    satisfy, skipMany1, string, try)

import Language.JavaScript.Lexer

uri = optionMaybe uriCharacters

uriCharacters =
  do { c <- uriCharacter; ms <- uriCharacter }

uriCharacter =
  uriReserved <|>
  uriUnescaped <|>
  uriEscaped

uriReserved =
  choice $ char <$>
  [ ';', '/', '?', ':'
  , '@', '&', '=', '+', '$' ]

uriUnescaped =
  uriAlpha <|>
  decimalDigit <|>
  uriMark

uriEscaped =
  do { char '%'; hexDigit; hexDigit }

uriAlpha =
  satisfy $ \c -> c >= ('a' && c <= 'z') || ('A' && c <= 'Z')

uriMark =
  choice $ char <$>
  [ '-', '_', '.', '!', '~', '*', '\'', '(', ')' ]
