module Language.JavaScript.Prim where

import Control.Monad (guard, void)

import Text.Parsec ((<|>),
                    SourcePos,
                    eof, many)
import Text.Parsec.Prim (getState, lookAhead, modifyState)
import Text.Parsec.Token (GenLanguageDef(..))
import Text.ParserCombinators.Parsec.Prim (GenParser)
import qualified Text.ParserCombinators.Parsec.Prim as Parsec (token)

import Language.JavaScript.AST
import Language.JavaScript.Lexer hiding (token, lineTerminator, punctuator)

data JSPState
  = JSPState
    { jspStateNLFlag :: Bool }

getNLFlag :: JSParser Bool
getNLFlag = do { s <- getState; return $ jspStateNLFlag s }
setNLFlag :: JSParser ()
setNLFlag = modifyState $ \s -> s { jspStateNLFlag = True }
unsetNLFlag :: JSParser ()
unsetNLFlag = modifyState $ \s -> s { jspStateNLFlag = False }

newJSPState :: JSPState
newJSPState = JSPState {
  jspStateNLFlag = False }

type JSParser a = GenParser (SourcePos, InputElement) JSPState a

lexeme :: JSParser a -> JSParser a
lexeme p =
  do { x <- p; unsetNLFlag; void $ many lineTerminator; return x }

mytoken :: (InputElement -> Maybe a) -> JSParser a
mytoken test =
  Parsec.token showTok posFromTok testTok
  where
    showTok (pos, t)    = show t
    posFromTok (pos, t) = pos
    testTok (pos, t)    = test t

equal :: InputElement -> JSParser ()
equal test = mytoken (\tok -> if tok == test then Just () else Nothing)

lineTerminator :: JSParser ()
lineTerminator =
  do { equal InputElementLineTerminator; setNLFlag }

noLineTerminatorHere :: JSParser ()
noLineTerminatorHere =
  do { nl <- getNLFlag; guard (not nl) }

priorNL :: JSParser ()
priorNL =
  do { nl <- getNLFlag; guard nl }

autoSemi :: JSParser ()
autoSemi =
  punctuator ";" <|>
  priorNL <|>
  void (lookAhead $ punctuator "}") <|>
  eof

identName :: String -> JSParser ()
identName s = lexeme $ equal $ InputElementIdentName $ IdentName s

getIdentName :: JSParser IdentName
getIdentName = lexeme $ mytoken get
  where
    get (InputElementIdentName i) = Just i
    get _ = Nothing

getIdent :: JSParser Ident
getIdent = lexeme $ mytoken get
  where
    get (InputElementIdentName i@(IdentName n)) =
      if n `elem` reservedNames javaScript
      then Nothing
      else Just $ Ident i
    get _ = Nothing

punctuator :: String -> JSParser ()
punctuator p = lexeme $ equal $ InputElementPunctuator $ Punctuator p

getLiteral :: JSParser Literal
getLiteral = lexeme $ mytoken get
  where
    get (InputElementLiteral l) = Just l
    get (InputElementIdentName (IdentName "null")) = Just $ LiteralNull NullLit
    get (InputElementIdentName (IdentName "true")) = Just $ LiteralBool $ BoolLit True
    get (InputElementIdentName (IdentName "false")) = Just $ LiteralBool $ BoolLit False
    get _ = Nothing

getNumLit :: JSParser NumLit
getNumLit = lexeme $ mytoken get
  where
    get (InputElementLiteral (LiteralNum n)) = Just n
    get _ = Nothing

getStringLit :: JSParser StringLit
getStringLit = lexeme $ mytoken get
  where
    get (InputElementLiteral (LiteralString s)) = Just s
    get _ = Nothing
