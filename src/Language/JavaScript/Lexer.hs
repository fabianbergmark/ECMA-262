{-# LANGUAGE FlexibleContexts,
             RankNTypes #-}

module Language.JavaScript.Lexer
       where

import Control.Applicative ((<$>), (<*))
import Control.Monad (void)

import Data.Char
import Data.Maybe (mapMaybe)

import Text.Parsec ((<|>),
                    SourcePos,
                    anyChar, choice, getPosition, many,
                    notFollowedBy, optionMaybe, runParser,
                    satisfy, skipMany1, string, try)
import Text.Parsec.Char (char, oneOf)
import Text.Parsec.Prim (ParsecT, Stream,
                         getState, modifyState)
import Text.Parsec.Token (GenLanguageDef(..), LanguageDef)
import Text.ParserCombinators.Parsec.Prim (GenParser)

import Language.JavaScript.AST

javaScript :: LanguageDef TokenState
javaScript = LanguageDef {
  commentStart = "/*",
  commentEnd = "*/",
  commentLine = "//",
  nestedComments = False,
  identStart = identifierStart,
  identLetter = identifierPart,
  opStart = oneOf "!%&( )*,-.:;<=>?[ ]^{|}~",
  opLetter = oneOf "=+-<>&|",
  reservedNames =
    [ "break", "case", "catch", "continue", "debugger", "default"
    , "delete", "do", "else", "finally", "for", "function", "if"
    , "in" , "instanceof", "new", "return", "this", "throw", "try"
    , "typeof", "var", "void", "while", "with"
    , "class", "const", "enum", "export", "extends", "import", "super"
    , "implements", "interface", "let", "package", "private", "protected"
    , "public", "static", "yield"
    , "null", "true", "false" ],
  reservedOpNames =
    [ "{", "}", "(", ")", "[", "]", ".", ";", ",", "<", ">", "<="
    , ">=", "==", "!=", "===", "!==", "+", "-", "*", "%", "++", "--"
    , "<<", ">>", ">>>", "&", "|", "^", "!", "~", "&&", "||", "?", ":"
    , "=", "+=", "-=", "*=", "%=", "<<=", ">>=", ">>>=", "&=", "|=", "^=" ],
  caseSensitive = True }

data InputElement
  = InputElementIdentName IdentName
  | InputElementLiteral Literal
  | InputElementPunctuator Punctuator
  | InputElementLineTerminator
  deriving (Eq, Show)

data InputElementDiv
  = InputElementDivWhiteSpace
  | InputElementDivLineTerminator
  | InputElementDivComment Comment
  | InputElementDivToken Token
  | InputElementDivDivPunctuator DivPunctuator
  deriving (Eq, Show)

data InputElementRegExp
  = InputElementRegExpWhiteSpace
  | InputElementRegExpLineTerminator
  | InputElementRegExpComment Comment
  | InputElementRegExpToken Token
  | InputElementRegExpRegExpLit RegExpLit
  deriving (Eq, Show)

data Comment
  = CommentMultiLine String
  | CommentSingleLine String
  deriving (Eq, Show)

data Token
  = TokenIdentName IdentName
  | TokenPunctuator Punctuator
  | TokenNumLit NumLit
  | TokenStringLit StringLit
  deriving (Eq, Show)

data Punctuator
  = Punctuator String
  deriving (Eq, Show)

data DivPunctuator
  = DivPunctuator String
  deriving (Eq, Show)

applyRest :: Stream s m t =>
             ParsecT s u m (b -> ParsecT s u m b) -> b -> ParsecT s u m b
applyRest pr a = do
  mr <- optionMaybe $ try pr
  case mr of
   Just r -> r a
   Nothing -> return a

data TokenState
  = TokenState
    { tokenStateLeadingDivAllowed :: Bool }

type TokenParser st a = GenParser Char st a
type TokenSTParser a = GenParser Char TokenState a

newTokenState :: TokenState
newTokenState = TokenState {
  tokenStateLeadingDivAllowed = False }

isLeadingDivAllowed :: TokenSTParser Bool
isLeadingDivAllowed = do
  s <- getState
  return $ tokenStateLeadingDivAllowed s

setLeadingDivAllowed :: TokenSTParser ()
setLeadingDivAllowed =
  modifyState $ \s -> s { tokenStateLeadingDivAllowed = True }

setLeadingDivDisallowed :: TokenSTParser ()
setLeadingDivDisallowed =
  modifyState $ \s -> s { tokenStateLeadingDivAllowed = False }

sourceCharacter :: TokenParser st Char
sourceCharacter = anyChar

inputElementDiv :: TokenSTParser InputElementDiv
inputElementDiv =
  do { void whiteSpace; return InputElementDivWhiteSpace } <|>
  do { void lineTerminator; return InputElementDivLineTerminator } <|>
  do { c <- comment; return $ InputElementDivComment c } <|>
  do { t <- token; return $ InputElementDivToken t } <|>
  do { p <- divPunctuator; return $ InputElementDivDivPunctuator p }

inputElementRegExp :: TokenSTParser InputElementRegExp
inputElementRegExp =
  do { void whiteSpace; return InputElementRegExpWhiteSpace } <|>
  do { void lineTerminator; return InputElementRegExpLineTerminator } <|>
  do { c <- comment; return $ InputElementRegExpComment c } <|>
  do { t <- token; return $ InputElementRegExpToken t } <|>
  do { re <- regularExpressionLiteral; return $ InputElementRegExpRegExpLit re }

whiteSpace :: Stream String m Char => ParsecT [Char] u m Char
whiteSpace =
  do { choice $ char <$>
       [ '\x0009', '\x000B'
       , '\x000C', '\x0020'
       , '\x00A0', '\xFEFF' ] } <|>
  satisfy (\c -> generalCategory c == Space)

lineTerminator :: TokenParser st Char
lineTerminator =
  choice $ char <$>
  [ '\x000A', '\x000D'
  , '\x2028', '\x2029' ]

lineTerminatorSequence :: TokenParser st ()
lineTerminatorSequence =
  skipMany1 $ choice
  [ void $ char '\x000A'
  , void $ try $ do { void $ char '\x000D'; (notFollowedBy $ char '\x000A') }
  , void $ char '\x2028', void $ char '\x2029'
  , void $ string "\x000D\x000A" ]

comment :: TokenParser st Comment
comment =
  multiLineComment <|>
  singleLineComment

multiLineComment :: TokenParser st Comment
multiLineComment =
  do { void . try $ string "/*"; ms <- optionMaybe multiLineCommentChars; void $ string "*/";
       case ms of
       Nothing -> return $ CommentMultiLine ""
       Just s -> return $ CommentMultiLine s }

multiLineCommentChars :: TokenParser st String
multiLineCommentChars =
  do { c <- multiLineNotAsteriskChar; ms <- optionMaybe multiLineCommentChars;
       case ms of
        Nothing -> return [c]
        Just s -> return $ c:s } <|>
  do { c <- try $ do { char '*' <* notFollowedBy (char '/') }; ms <- optionMaybe postAsteriskCommentChars;
       case ms of
        Nothing -> return [c]
        Just s -> return $ c:s }

postAsteriskCommentChars :: TokenParser st String
postAsteriskCommentChars =
  do { c <- multiLineNotForwardSlashOrAsteriskChar; ms <- optionMaybe multiLineCommentChars;
       case ms of
        Nothing -> return [c]
        Just s -> return $ c:s } <|>
  do { c <- char '*'; ms <- optionMaybe postAsteriskCommentChars;
       case ms of
        Nothing -> return [c]
        Just s -> return $ c:s }

multiLineNotAsteriskChar :: TokenParser st Char
multiLineNotAsteriskChar =
  do { notFollowedBy $ char '*'; sourceCharacter }

multiLineNotForwardSlashOrAsteriskChar :: TokenParser st Char
multiLineNotForwardSlashOrAsteriskChar =
  do { notFollowedBy $ char '/' <|> char '*'; sourceCharacter }

singleLineComment :: TokenParser st Comment
singleLineComment =
  do { void . try $ string "//"; ms <- optionMaybe singleLineCommentChars;
       case ms of
        Nothing -> return $ CommentSingleLine ""
        Just s -> return $ CommentSingleLine s }

singleLineCommentChars :: TokenParser st String
singleLineCommentChars =
  do { c <- singleLineCommentChar; ms <- optionMaybe singleLineCommentChars;
       case ms of
        Nothing -> return [c]
        Just s -> return $ c:s }

singleLineCommentChar :: TokenParser st Char
singleLineCommentChar =
  do { notFollowedBy lineTerminator; sourceCharacter }

token :: TokenSTParser Token
token =
  do { i <- identifierName; return $ TokenIdentName i } <|>
  do { p <- punctuator; return $ TokenPunctuator p } <|>
  do { n <- numericLiteral; setLeadingDivAllowed; return $ TokenNumLit n } <|>
  do { s <- stringLiteral; setLeadingDivAllowed; return $ TokenStringLit s }

identifier :: TokenSTParser Ident
identifier =
  do { notFollowedBy reservedWord; i <- identifierName; setLeadingDivAllowed; return $ Ident i; }

identifierName :: TokenSTParser IdentName
identifierName =
  do { c <- identifierStart; applyRest identifierNameRest $ IdentName [c];  }

identifierNameRest :: TokenSTParser (IdentName -> TokenSTParser IdentName)
identifierNameRest =
  do { c <- identifierPart; return $ \(IdentName s) -> applyRest identifierNameRest (IdentName $ s ++ [c]) }

identifierStart :: TokenSTParser Char
identifierStart =
  unicodeLetter <|>
  char '$' <|>
  char '_' <|>
  do { void $ char '\\'; unicodeEscapeSequence }

identifierPart :: TokenSTParser Char
identifierPart =
  identifierStart <|>
  unicodeCombiningMark <|>
  unicodeDigit <|>
  unicodeConnectorPunctuation <|>
  char '\x200C' <|>
  char '\x200D'

unicodeLetter :: TokenParser st Char
unicodeLetter =
  satisfy $ \c -> let cat = generalCategory c in
                   cat == UppercaseLetter ||
                   cat == LowercaseLetter ||
                   cat == TitlecaseLetter ||
                   cat == ModifierLetter ||
                   cat == OtherLetter ||
                   cat == LetterNumber

unicodeCombiningMark :: TokenParser st Char
unicodeCombiningMark =
  satisfy $ \c -> let cat = generalCategory c in
                   cat == NonSpacingMark ||
                   cat == SpacingCombiningMark

unicodeDigit :: TokenParser st Char
unicodeDigit =
  satisfy $ \c -> let cat = generalCategory c in
                   cat == DecimalNumber

unicodeConnectorPunctuation :: TokenParser st Char
unicodeConnectorPunctuation =
  satisfy $ \c -> let cat = generalCategory c
                  in cat == ConnectorPunctuation

reservedWord :: TokenParser st ()
reservedWord =
  void keyword <|>
  void futureReservedWord <|>
  void nullLiteral <|>
  void booleanLiteral

keyword :: TokenParser st String
keyword =
  choice $ try . string <$>
  [ "break", "case", "catch", "continue", "debugger", "default", "delete"
  , "do", "else", "finally", "for", "function", "if", "in"
  , "instanceof", "new", "return", "this", "throw", "try"
  , "typeof", "var", "void", "while", "with" ]

futureReservedWord :: TokenParser st String
futureReservedWord =
  choice $ try . string <$>
  [ "class", "const", "enum", "export", "extends", "import", "super"
  , "implements", "interface", "let", "package", "private", "protected"
  , "public", "static", "yield" ]

punctuator :: TokenSTParser Punctuator
punctuator = do
  p <- choice $ try . string <$>
       [ "~", "}", "||", "|=", "|", "{"
       , "^=", "^", "]", "[", "?", ">>>="
       , ">>>", ">>=", ">>", ">=", ">", "==="
       , "==", "=", "<=", "<<=", "<<", "<"
       , ";", ":", ".", "-=", "--", "-", ","
       , "+=", "++", "+", "*=", "*", ")", "("
       , "&=", "&&", "&", "%=", "%", "!==", "!=", "!" ]
  if p `elem` ["]", "--", "++", ")"]
    then setLeadingDivAllowed
    else setLeadingDivDisallowed
  return $ Punctuator p

divPunctuator :: TokenSTParser DivPunctuator
divPunctuator = do
  dp <- try (string "/=") <|> string "/"
  setLeadingDivDisallowed
  return $ DivPunctuator dp

literal :: TokenSTParser Literal
literal =
  do { n <- nullLiteral; setLeadingDivAllowed; return $ LiteralNull n } <|>
  do { b <- booleanLiteral; setLeadingDivAllowed; return $ LiteralBool b } <|>
  do { n <- numericLiteral; setLeadingDivAllowed; setLeadingDivAllowed; return $ LiteralNum n } <|>
  do { s <- stringLiteral; setLeadingDivAllowed; return $ LiteralString s } <|>
  do { r <- regularExpressionLiteral; return $ LiteralRegExp r }

nullLiteral :: TokenParser st NullLit
nullLiteral =
  do { void $ string "null"; return NullLit }

booleanLiteral :: TokenParser st BoolLit
booleanLiteral =
  do { void $ string "true"; return $ BoolLit True } <|>
  do { void $ string "false"; return $ BoolLit False }

numericLiteral :: TokenParser st NumLit
numericLiteral =
  do { mv <- hexIntegerLiteral; return $ NumLit $ fromIntegral mv } <|>
  do { mv <- decimalLiteral; return $ NumLit mv }

decimalLiteral :: TokenParser st Double
decimalLiteral =
  do { mv <- try $ do { decimalIntegerLiteral <* char '.' };
       mdv <- optionMaybe decimalDigits; mev <- optionMaybe exponentPart;
       case mdv of
        Nothing -> do
          case mev of
           Nothing -> return $ fromIntegral mv
           Just ev -> return $ (fromIntegral mv) * 10 ^^ ev
        Just (dv, n) -> do
          case mev of
           Nothing ->
             return $ (fromIntegral mv) + (fromIntegral dv) * 10 ^^ (-n)
           Just ev ->
             return $ ((fromIntegral mv) + (fromIntegral dv) * 10 ^^ (-n)) * 10 ^^ ev } <|>
  do { void $ char '.'; (mv, n) <- decimalDigits; mev <- optionMaybe exponentPart;
       case mev of
        Nothing ->
          return $ (fromIntegral mv) * 10 ^^ (-n)
        Just ev -> do
          return $ (fromIntegral mv) * 10 ^^ (ev - n) } <|>
  do { mv <- decimalIntegerLiteral; mev <- optionMaybe exponentPart;
       case mev of
        Nothing -> return $ fromIntegral mv
        Just ev -> return $ (fromIntegral mv) * 10 ^^ ev }

decimalIntegerLiteral :: TokenParser st Int
decimalIntegerLiteral =
  do { void $ char '0'; return 0 } <|>
  do { mv <- nonZeroDigit; mdv <- optionMaybe decimalDigits;
       case mdv of
        Nothing -> return mv
        Just (dv, n) -> do
          return $ mv * 10 ^ n + dv }

decimalDigits :: TokenParser st (Int, Int)
decimalDigits =
  do { dv <- decimalDigit; applyRest decimalDigitsRest (dv, 1) }

decimalDigitsRest :: TokenParser st ((Int, Int) -> TokenParser st (Int, Int))
decimalDigitsRest =
  do { dv <- decimalDigit; return $ \(mv, n) -> applyRest decimalDigitsRest (mv * 10 + dv, n + 1) }

decimalDigit :: TokenParser st Int
decimalDigit =
  do { void $ char '0'; return 0 } <|>
  do { void $ char '1'; return 1 } <|>
  do { void $ char '2'; return 2 } <|>
  do { void $ char '3'; return 3 } <|>
  do { void $ char '4'; return 4 } <|>
  do { void $ char '5'; return 5 } <|>
  do { void $ char '6'; return 6 } <|>
  do { void $ char '7'; return 7 } <|>
  do { void $ char '8'; return 8 } <|>
  do { void $ char '9'; return 9 }

nonZeroDigit :: TokenParser st Int
nonZeroDigit =
  do { void $ char '1'; return 1 } <|>
  do { void $ char '2'; return 2 } <|>
  do { void $ char '3'; return 3 } <|>
  do { void $ char '4'; return 4 } <|>
  do { void $ char '5'; return 5 } <|>
  do { void $ char '6'; return 6 } <|>
  do { void $ char '7'; return 7 } <|>
  do { void $ char '8'; return 8 } <|>
  do { void $ char '9'; return 9 }

exponentPart :: TokenParser st Int
exponentPart =
  do { void $ exponentIndicator; mv <- signedInteger; return mv }

exponentIndicator :: TokenParser st Char
exponentIndicator =
  char 'e' <|> char 'E'

signedInteger :: TokenParser st Int
signedInteger =
  do { (mv, _) <- decimalDigits; return mv } <|>
  do { void $ char '+'; (mv, _) <- decimalDigits; return mv } <|>
  do { void $ char '-'; (mv, _) <- decimalDigits; return (-mv) }

hexIntegerLiteral :: TokenParser st Int
hexIntegerLiteral =
  do { try (void $ string "0x") <|> try (void $ string "0X"); applyRest hexIntegerLiteralRest 0 }

hexIntegerLiteralRest :: TokenParser st (Int -> TokenParser st Int)
hexIntegerLiteralRest =
  do { dv <- hexDigit; return $ \mv -> applyRest hexIntegerLiteralRest (mv * 16 + dv) }

hexDigit :: TokenParser st Int
hexDigit =
  do { void $ char '0'; return 0 } <|>
  do { void $ char '1'; return 1 } <|>
  do { void $ char '2'; return 2 } <|>
  do { void $ char '3'; return 3 } <|>
  do { void $ char '4'; return 4 } <|>
  do { void $ char '5'; return 5 } <|>
  do { void $ char '6'; return 6 } <|>
  do { void $ char '7'; return 7 } <|>
  do { void $ char '8'; return 8 } <|>
  do { void $ char '9'; return 9 } <|>
  do { void $ char 'a' <|> char 'A'; return 10 } <|>
  do { void $ char 'b' <|> char 'B'; return 11 } <|>
  do { void $ char 'c' <|> char 'C'; return 12 } <|>
  do { void $ char 'd' <|> char 'D'; return 13 } <|>
  do { void $ char 'e' <|> char 'E'; return 14 } <|>
  do { void $ char 'f' <|> char 'F'; return 15 }

stringLiteral :: TokenParser st StringLit
stringLiteral =
  do { void $ char '"'; msv <- optionMaybe doubleStringCharacters; void $ char '"';
       case msv of
        Nothing -> return $ StringLit ""
        Just sv -> return $ StringLit sv } <|>
  do { void $ char '\''; msv <- optionMaybe singleStringCharacters; void $ char '\'';
       case msv of
        Nothing -> return $ StringLit ""
        Just sv -> return $ StringLit sv }

doubleStringCharacters :: TokenParser st String
doubleStringCharacters =
  do { cv <- doubleStringCharacter; msv <- optionMaybe doubleStringCharacters;
       case msv of
        Nothing -> return cv
        Just sv -> return $ cv ++ sv }

singleStringCharacters :: TokenParser st String
singleStringCharacters =
  do { cv <- singleStringCharacter; msv <- optionMaybe singleStringCharacters;
       case msv of
        Nothing -> return cv
        Just sv -> return $ cv ++ sv}

doubleStringCharacter :: TokenParser st String
doubleStringCharacter =
  do { notFollowedBy $ char '"' <|> char '\\' <|> lineTerminator; c <- sourceCharacter; return [c] } <|>
  do { void $ char '\\'; c <- escapeSequence; return [c] } <|>
  do { void $ lineContinuation; return "" }

singleStringCharacter :: TokenParser st String
singleStringCharacter =
  do { notFollowedBy $ char '\'' <|> char '\\' <|> lineTerminator; c <- sourceCharacter; return [c] } <|>
  do { void $ char '\\'; c <- escapeSequence; return [c] } <|>
  do { void $ lineContinuation; return "" }

lineContinuation :: TokenParser st String
lineContinuation =
  do { void $ char '\\'; lineTerminatorSequence; return "" }

escapeSequence :: TokenParser st Char
escapeSequence =
  characterEscapeSequence <|>
  do { void $ char '0'; notFollowedBy decimalDigit; return '\0' } <|>
  hexEscapeSequence <|>
  unicodeEscapeSequence

characterEscapeSequence :: TokenParser st Char
characterEscapeSequence =
  do { ec <- singleEscapeCharacter;
       case ec of
        'b'  -> return '\x0008'
        't'  -> return '\x0009'
        'n'  -> return '\x000A'
        'v'  -> return '\x000B'
        'f'  -> return '\x000C'
        'r'  -> return '\x000D'
        '"'  -> return '\x0022'
        '\'' -> return '\x0027'
        '\\' -> return '\x005C'
        _ -> error "panic" {- This Should never happen! -} } <|>
  nonEscapeCharacter

singleEscapeCharacter :: TokenParser st Char
singleEscapeCharacter =
  choice $ char <$>
  [ '\'', '"', '\\', 'b', 'f', 'n', 'r', 't', 'v' ]

nonEscapeCharacter :: TokenParser st Char
nonEscapeCharacter =
  do { notFollowedBy $ escapeCharacter <|> void lineTerminator; sourceCharacter }

escapeCharacter :: TokenParser st ()
escapeCharacter =
  void singleEscapeCharacter <|>
  void decimalDigit <|>
  void (char 'x') <|>
  void (char 'u')

hexEscapeSequence :: TokenParser st Char
hexEscapeSequence =
  do { void $ char 'x'; mv1 <- hexDigit; mv2 <- hexDigit;
       return $ chr $ 16 * mv1 + mv2 }

unicodeEscapeSequence :: TokenParser st Char
unicodeEscapeSequence =
  do { void $ char 'u'; mv1 <- hexDigit; mv2 <- hexDigit; mv3 <- hexDigit; mv4 <- hexDigit;
       return $ chr $ 4096 * mv1 + 256 * mv2 + 16 * mv3 + mv4 }

regularExpressionLiteral :: TokenSTParser RegExpLit
regularExpressionLiteral =
  do { void $ char '/'; pattern <- regularExpressionBody; void $ char '/'; flags <- regularExpressionFlags;
       return $ RegExpLit (pattern, flags) }

regularExpressionBody :: TokenParser st String
regularExpressionBody =
  do { c <- regularExpressionFirstChar; s <- regularExpressionChars; return $ c ++ s }

regularExpressionChars :: TokenParser st String
regularExpressionChars =
  do { c <- regularExpressionChar; s <- regularExpressionChars; return $ c ++ s } <|>
  return ""

regularExpressionFirstChar :: TokenParser st String
regularExpressionFirstChar =
  do { notFollowedBy $ char '*' <|> char '\\' <|> char '/' <|> char '['; c <- regularExpressionNonTerminator;
       return [c] } <|>
  do { c <- regularExpressionBackslashSequence; return [c] } <|>
  regularExpressionClass

regularExpressionChar :: TokenParser st String
regularExpressionChar =
  do { notFollowedBy $ char '\\' <|> char '/' <|> char '['; c <- regularExpressionNonTerminator;
       return [c] } <|>
  do { c <- regularExpressionBackslashSequence; return [c] } <|>
  regularExpressionClass

regularExpressionBackslashSequence :: TokenParser st Char
regularExpressionBackslashSequence =
  do { void $ char '\\'; regularExpressionNonTerminator }

regularExpressionNonTerminator :: TokenParser st Char
regularExpressionNonTerminator =
  do { notFollowedBy lineTerminator; sourceCharacter }

regularExpressionClass :: TokenParser st String
regularExpressionClass =
  do { void $ char '['; s <- regularExpressionClassChars; void $ char ']'; return s }

regularExpressionClassChars :: TokenParser st String
regularExpressionClassChars =
  do { c <- regularExpressionClassChar; s <- regularExpressionClassChars; return $ c:s } <|>
  return ""

regularExpressionClassChar :: TokenParser st Char
regularExpressionClassChar =
  do { notFollowedBy $ char ']' <|> char '\\';  regularExpressionNonTerminator } <|>
  regularExpressionBackslashSequence

regularExpressionFlags :: TokenSTParser String
regularExpressionFlags =
  do { c <- identifierPart; s <- regularExpressionFlags; return $ c:s } <|>
  return ""

lexer :: TokenSTParser [(SourcePos, InputElement)]
lexer = (mapMaybe toInputElement) <$>
        (many $ do
            p <- getPosition;
            da <- isLeadingDivAllowed
            edr <- if da
                   then Left <$> inputElementDiv
                   else Right <$> inputElementRegExp
            return (p, edr))
  where
    isLineTerminator c = c `elem` [ '\x000A', '\x000D', '\x2028', '\x2029' ]
    toInputElement (p, edr) = do
      case edr of
       Left ied -> toInputElementDiv (p, ied)
       Right ier -> toInputElementRegExp (p, ier)
    toInputElementDiv (p, ied) =
      case ied of
       InputElementDivWhiteSpace -> Nothing
       InputElementDivLineTerminator ->
         Just (p, InputElementLineTerminator)
       InputElementDivComment (CommentSingleLine _) ->
         Nothing
       InputElementDivComment (CommentMultiLine s)
         | any isLineTerminator s -> Just (p, InputElementLineTerminator)
         | otherwise -> Nothing
       InputElementDivToken (TokenIdentName i) ->
         Just (p, InputElementIdentName i)
       InputElementDivToken (TokenPunctuator pu) ->
         Just (p, InputElementPunctuator pu)
       InputElementDivToken (TokenNumLit n) ->
         Just (p, InputElementLiteral $ LiteralNum n)
       InputElementDivToken (TokenStringLit s) ->
         Just (p, InputElementLiteral $ LiteralString s)
       InputElementDivDivPunctuator (DivPunctuator s) ->
         Just (p, InputElementPunctuator $  Punctuator s)
    toInputElementRegExp (p, ier) =
      case ier of
       InputElementRegExpWhiteSpace -> Nothing
       InputElementRegExpLineTerminator ->
         Just (p, InputElementLineTerminator)
       InputElementRegExpComment (CommentSingleLine _) -> Nothing
       InputElementRegExpComment (CommentMultiLine s)
         | any isLineTerminator s -> Just (p, InputElementLineTerminator)
         | otherwise -> Nothing
       InputElementRegExpToken (TokenIdentName i) ->
         Just (p, InputElementIdentName i)
       InputElementRegExpToken (TokenPunctuator pu) ->
         Just (p, InputElementPunctuator pu)
       InputElementRegExpToken (TokenNumLit n) ->
         Just (p, InputElementLiteral $ LiteralNum n)
       InputElementRegExpToken (TokenStringLit s) ->
         Just (p, InputElementLiteral $ LiteralString s)
       InputElementRegExpRegExpLit re ->
         Just (p, InputElementLiteral $ LiteralRegExp re)

runLexer :: String -> [(SourcePos, InputElement)]
runLexer s =
  case runParser lexer newTokenState "" s of
   Right l -> l
   Left _  -> []

lexJavaScript :: String -> [(SourcePos, InputElement)]
lexJavaScript input = runLexer input
