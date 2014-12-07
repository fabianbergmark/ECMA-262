module Language.JavaScript.Parser
       ( parseJavaScript ) where

import Control.Applicative ((<*), (*>))

import Text.Parsec

import Language.JavaScript.AST
import Language.JavaScript.Lexer (lexJavaScript)
import Language.JavaScript.Prim
import Language.JavaScript.Util

chainl1' :: (Stream s m t) =>
            ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (a -> b -> a) -> ParsecT s u m a
chainl1' pa pb op = do
  a <- pa
  rest a
  where
    rest a = do { f <- op; b <- pb; rest (f a b) } <|> return a

primExpr :: JSParser PrimExpr
primExpr =
  do { identName "this" ; return PrimExprThis } <|>
  do { name <- getIdent; return $ PrimExprIdent name} <|>
  do { l <- getLiteral; return $ PrimExprLiteral l } <|>
  do { a <- arrayLit; return $ PrimExprArray a } <|>
  do { o <- objectLit; return $ PrimExprObject o } <|>
  do { punctuator "("; e <- expr; punctuator ")"; return $ PrimExprParens e }

arrayLit :: JSParser ArrayLit
arrayLit =
  try (do { punctuator "["; me <- optionMaybe elision; punctuator "]"; return $ ArrayLitH me }) <|>
  try (do { punctuator "["; el <- elementList; punctuator "]"; return $ ArrayLit el }) <|>
  do { punctuator "[";
       el <- elementList;
       punctuator ",";
       me <- optionMaybe elision;
       punctuator "]";
       return $ ArrayLitT el me }

elementList :: JSParser ElementList
elementList =
  do { me <- optionMaybe elision; ae <- assignExpr; applyRest elementListRest (ElementList me ae) }

elementListRest :: JSParser (ElementList -> JSParser ElementList)
elementListRest =
  do { punctuator ","; me <- optionMaybe elision; ae <- assignExpr; return $ \el -> applyRest elementListRest (ElementListCons el me ae) }

elision :: JSParser Elision
elision =
  do { punctuator ","; applyRest elisionRest ElisionComma }

elisionRest :: JSParser (Elision -> JSParser Elision)
elisionRest =
  do { punctuator ","; return $ \e -> applyRest elisionRest (ElisionCons e) }

objectLit :: JSParser ObjectLit
objectLit =
  try (do { punctuator "{"; punctuator "}"; return ObjectLitEmpty }) <|>
  do { punctuator "{"; pl <- propList; optional $ punctuator ","; punctuator "}"; return $ ObjectLit pl }

propList :: JSParser PropList
propList =
  do { pa <- propAssign; applyRest propListRest (PropListAssign pa) }

propListRest :: JSParser (PropList -> JSParser PropList)
propListRest =
  do { punctuator ","; pa <- propAssign; return $ \pl -> applyRest propListRest (PropListCons pl pa) }

propAssign :: JSParser PropAssign
propAssign =
  do { pn <- propName; punctuator ":"; ae <- assignExpr; return $ PropAssignField pn ae } <|>
  do { identName "get"; pn <- propName; punctuator "("; punctuator ")"; punctuator "{"; fb <- funcBody; punctuator "}"; return $ PropAssignGet pn fb } <|>
  do { identName "set"; pn <- propName; punctuator "("; pl <- propSetParamList;  punctuator ")"; punctuator "{"; fb <- funcBody; punctuator "}"; return $ PropAssignSet pn pl fb }

propName :: JSParser PropName
propName =
  do { name <- getIdentName; return $ PropNameId name } <|>
  do { sl <- getStringLit; return $ PropNameStr sl } <|>
  do { nl <- getNumLit; return $ PropNameNum nl }

propSetParamList :: JSParser PropSetParamList
propSetParamList =
  do { i <- getIdent; return $ PropSetParamList i }

memberExpr :: JSParser MemberExpr
memberExpr =
  do { identName "new"; me <- memberExpr; args <- arguments; applyRest memberExprRest (MemberExprNew me args) } <|>
  do { pe <- primExpr; applyRest memberExprRest (MemberExprPrim pe) } <|>
  do { fe <- funcExpr; applyRest memberExprRest (MemberExprFunc fe) }

memberExprRest :: JSParser (MemberExpr -> JSParser MemberExpr)
memberExprRest =
  do { punctuator "["; e <- expr; punctuator "]"; return $ \me -> applyRest memberExprRest (MemberExprArray me e) } <|>
  do { punctuator "."; name <- getIdentName; return $ \me -> applyRest memberExprRest (MemberExprDot me name) }

newExpr :: JSParser NewExpr
newExpr =
  try (do { me <- memberExpr; return $ NewExprMember me }) <|>
  do { identName "new"; ne <- newExpr; return $ NewExprNew ne }

callExpr :: JSParser CallExpr
callExpr =
  do { me <- memberExpr; args <- arguments; applyRest callExprRest (CallExprMember me args) }

callExprRest :: JSParser (CallExpr -> JSParser CallExpr)
callExprRest =
  do { args <- arguments; return $ \ce -> applyRest callExprRest (CallExprCall ce args) } <|>
  do { punctuator "["; e <- expr; punctuator "]"; return $ \ce -> applyRest callExprRest (CallExprArray ce e) } <|>
  do { punctuator "."; name <- getIdentName; return $ \ce -> applyRest callExprRest (CallExprDot ce name) }

arguments :: JSParser Arguments
arguments =
  try (do { punctuator "("; punctuator ")"; return ArgumentsEmpty }) <|>
  do { punctuator "("; al <- argumentList; punctuator ")"; return $ Arguments al }

argumentList :: JSParser ArgumentList
argumentList =
  chainl1'
  (do { ae <- assignExpr; return $ ArgumentList ae })
  assignExpr
  (do { punctuator ","; return ArgumentListCons })

leftExpr :: JSParser LeftExpr
leftExpr =
  try (do { ce <- callExpr; return $ LeftExprCallExpr ce }) <|>
  do { ne <- newExpr; return $ LeftExprNewExpr ne }

postFixExpr :: JSParser PostFixExpr
postFixExpr = do
  le <- leftExpr
  do { punctuator "++"; return $ PostFixExprPostInc le } <|>
    do { punctuator "--"; return $ PostFixExprPostDec le } <|>
    do { return $ PostFixExprLeftExpr le }

uExpr :: JSParser UExpr
uExpr =
  do { identName "delete"; u <- uExpr; return $ UExprDelete u } <|>
  do { identName "void"; u <- uExpr; return $ UExprVoid u } <|>
  do { identName "typeof"; u <- uExpr; return $ UExprTypeOf u } <|>
  do { punctuator "++"; u <- uExpr; return $ UExprDoublePlus u } <|>
  do { punctuator "--"; u <- uExpr; return $ UExprDoubleMinus u } <|>
  do { punctuator "+"; u <- uExpr; return $ UExprUnaryPlus u } <|>
  do { punctuator "-"; u <- uExpr; return $ UExprUnaryMinus u } <|>
  do { punctuator "~"; u <- uExpr; return $ UExprBitNot u } <|>
  do { punctuator "!"; u <- uExpr; return $ UExprNot u } <|>
  do { pe <- postFixExpr; return $ UExprPostFix pe }

multExpr :: JSParser MultExpr
multExpr =
  chainl1'
  (do { u <- uExpr; return $ MultExpr u })
  uExpr
  (do { punctuator "*"; return MultExprMult } <|>
   do { punctuator "/"; return MultExprDiv } <|>
   do { punctuator "%"; return MultExprMod })

addExpr :: JSParser AddExpr
addExpr =
  chainl1'
  (do { m <- multExpr; return $ AddExpr m })
  multExpr
  (do { punctuator "+"; return AddExprAdd } <|>
   do { punctuator "-"; return AddExprSub })

shiftExpr :: JSParser ShiftExpr
shiftExpr =
  chainl1'
  (do { a <- addExpr; return $ ShiftExpr a })
  addExpr
  (do { punctuator "<<"; return ShiftExprLeft } <|>
   do { punctuator ">>"; return ShiftExprRight } <|>
   do { punctuator ">>>"; return ShiftExprRightZero })

relExpr :: JSParser RelExpr
relExpr =
  chainl1'
  (do { s <- shiftExpr; return $ RelExpr s })
  shiftExpr
  (do { punctuator "<"; return RelExprLess } <|>
   do { punctuator ">"; return RelExprGreater } <|>
   do { punctuator "<="; return RelExprLessEq } <|>
   do { punctuator ">="; return RelExprGreaterEq } <|>
   do { identName "instanceof"; return RelExprInstanceOf } <|>
   do { identName "in"; return RelExprIn })

relExprNoIn :: JSParser RelExprNoIn
relExprNoIn =
  chainl1'
  (do { s <- shiftExpr; return $ RelExprNoIn s })
  shiftExpr
  (do { punctuator "<"; return RelExprNoInLess } <|>
   do { punctuator ">"; return RelExprNoInGreater } <|>
   do { punctuator "<="; return RelExprNoInLessEq } <|>
   do { punctuator ">="; return RelExprNoInGreaterEq } <|>
   do { identName "instanceof"; return RelExprNoInInstanceOf })

eqExpr :: JSParser EqExpr
eqExpr =
  chainl1'
  (do { r <- relExpr; return $ EqExpr r })
  relExpr
  (do { punctuator "=="; return EqExprEq } <|>
   do { punctuator "!="; return EqExprNotEq } <|>
   do { punctuator "==="; return EqExprStrictEq } <|>
   do { punctuator "!=="; return EqExprStrictNotEq })

eqExprNoIn :: JSParser EqExprNoIn
eqExprNoIn =
  chainl1'
  (do { r <- relExprNoIn; return $ EqExprNoIn r })
  relExprNoIn
  (do { punctuator "=="; return EqExprNoInEq } <|>
   do { punctuator "!="; return EqExprNoInNotEq } <|>
   do { punctuator "==="; return EqExprNoInStrictEq } <|>
   do { punctuator "!=="; return EqExprNoInStrictNotEq })

bitAndExpr :: JSParser BitAndExpr
bitAndExpr =
  chainl1'
  (do { e <- eqExpr; return $ BitAndExpr e })
  eqExpr
  (do { punctuator "&"; return $ BitAndExprAnd })

bitAndExprNoIn :: JSParser BitAndExprNoIn
bitAndExprNoIn =
  chainl1'
  (do { e <- eqExprNoIn; return $ BitAndExprNoIn e })
  eqExprNoIn
  (do { punctuator "&"; return $ BitAndExprNoInAnd })

bitXorExpr :: JSParser BitXorExpr
bitXorExpr =
  chainl1'
  (do { bae <- bitAndExpr; return $ BitXorExpr bae })
  bitAndExpr
  (do { punctuator "^"; return $ BitXorExprXor })

bitXorExprNoIn :: JSParser BitXorExprNoIn
bitXorExprNoIn =
  chainl1'
  (do { bae <- bitAndExprNoIn; return $ BitXorExprNoIn bae })
  bitAndExprNoIn
  (do { punctuator "^"; return $ BitXorExprNoInXor })

bitOrExpr :: JSParser BitOrExpr
bitOrExpr =
  chainl1'
  (do { bxe <- bitXorExpr; return $ BitOrExpr bxe })
  bitXorExpr
  (do { punctuator "|"; return $ BitOrExprOr })

bitOrExprNoIn :: JSParser BitOrExprNoIn
bitOrExprNoIn =
  chainl1'
  (do { bxe <- bitXorExprNoIn; return $ BitOrExprNoIn bxe })
  bitXorExprNoIn
  (do { punctuator "|"; return $ BitOrExprNoInOr })

logicalAndExpr :: JSParser LogicalAndExpr
logicalAndExpr =
  chainl1'
  (do { boe <- bitOrExpr; return $ LogicalAndExpr boe })
  bitOrExpr
  (do { punctuator "&&"; return $ LogicalAndExprAnd })

logicalAndExprNoIn :: JSParser LogicalAndExprNoIn
logicalAndExprNoIn =
  chainl1'
  (do { boe <- bitOrExprNoIn; return $ LogicalAndExprNoIn boe })
  bitOrExprNoIn
  (do { punctuator "&&"; return $ LogicalAndExprNoInAnd })

logicalOrExpr :: JSParser LogicalOrExpr
logicalOrExpr =
  chainl1'
  (do { lae <- logicalAndExpr; return $ LogicalOrExpr lae })
  logicalAndExpr
  (do { punctuator "||"; return $ LogicalOrExprOr })

logicalOrExprNoIn :: JSParser LogicalOrExprNoIn
logicalOrExprNoIn =
  chainl1'
  (do { lae <- logicalAndExprNoIn; return $ LogicalOrExprNoIn lae })
  logicalAndExprNoIn
  (do { punctuator "||"; return $ LogicalOrExprNoInOr })

condExpr :: JSParser CondExpr
condExpr = do
  loe <- logicalOrExpr
  do { try $ do { punctuator "?"; }; ae1 <- assignExpr; punctuator ":"; ae2 <- assignExpr; return $ CondExprIf loe ae1 ae2 } <|>
    do { return $ CondExpr loe }

condExprNoIn :: JSParser CondExprNoIn
condExprNoIn = do
  loe <- logicalOrExprNoIn;
  do { try $ do { punctuator "?"; }; ae1 <- assignExpr; punctuator ":"; ae2 <- assignExpr; return $ CondExprNoInIf loe ae1 ae2 } <|>
    do { return $ CondExprNoIn loe }

assignExpr :: JSParser AssignExpr
assignExpr =
  try (do { le <- leftExpr; ao <- assignOp; ae <- assignExpr; return $ AssignExprAssign le ao ae }) <|>
  do { ce <- condExpr; return $ AssignExprCondExpr ce }

assignExprNoIn :: JSParser AssignExprNoIn
assignExprNoIn =
  try (do { le <- leftExpr; ao <- assignOp; ae <- assignExprNoIn; return $ AssignExprNoInAssign le ao ae }) <|>
  do { ce <- condExprNoIn; return $ AssignExprNoInCondExpr ce }

assignOp :: JSParser AssignOp
assignOp =
  do { punctuator "="; return AssignOpNormal } <|>
  do { punctuator "*="; return AssignOpMult } <|>
  do { punctuator "/="; return AssignOpDiv } <|>
  do { punctuator "%="; return AssignOpMod } <|>
  do { punctuator "+="; return AssignOpPlus } <|>
  do { punctuator "-="; return AssignOpMinus } <|>
  do { punctuator "<<="; return AssignOpShiftLeft } <|>
  do { punctuator ">>="; return AssignOpShiftRight } <|>
  do { punctuator ">>>="; return AssignOpShiftRightZero } <|>
  do { punctuator "&="; return AssignOpBitAnd } <|>
  do { punctuator "^="; return AssignOpBitXor } <|>
  do { punctuator "|="; return AssignOpBitOr }

expr :: JSParser Expr
expr =
  chainl1'
  (do { ae <- assignExpr; return $ Expr ae })
  assignExpr
  (do { punctuator ","; return ExprCons })

exprNoIn :: JSParser ExprNoIn
exprNoIn =
  chainl1'
  (do { ae <- assignExprNoIn; return $ ExprNoIn ae })
  assignExprNoIn
  (do { punctuator ","; return ExprNoInCons })

stmt :: JSParser Stmt
stmt =
  do { b <- block; return $ StmtBlock b } <|>
  do { vs <- varStmt; return $ StmtVar vs } <|>
  do { es <- emptyStmt; return $ StmtEmpty es } <|>
  try (do { es <- exprStmt; return $ StmtExpr es }) <|>
  do { ic <- contStmt; return $ StmtCont ic } <|>
  do { is <- ifStmt; return $ StmtIf is } <|>
  do { is <- itStmt; return $ StmtIt is } <|>
  do { bs <- breakStmt; return $ StmtBreak bs } <|>
  do { rs <- returnStmt; return $ StmtReturn rs } <|>
  do { ws <- withStmt; return $ StmtWith ws } <|>
  do { ss <- switchStmt; return $ StmtSwitch ss } <|>
  do { ts <- throwStmt; return $ StmtThrow ts } <|>
  do { ts <- tryStmt; return $ StmtTry ts } <|>
  do { ds <- dbgStmt; return $ StmtDbg ds } <|>
  do { ls <- labelledStmt; return $ StmtLabelled ls }

block :: JSParser Block
block =
  do { punctuator "{"; msl <- optionMaybe stmtList; punctuator "}"; return $ Block msl }

stmtList :: JSParser StmtList
stmtList =
  chainl1'
  (do { s <- stmt; return $ StmtList s })
  stmt
  (do { return StmtListCons })

varStmt :: JSParser VarStmt
varStmt =
  do { identName "var"; vdl <- varDeclList; return $ VarStmt vdl }

varDeclList :: JSParser VarDeclList
varDeclList =
  chainl1'
  (do { vd <- varDecl; return $ VarDeclList vd})
  varDecl
  (do { punctuator ","; return $ VarDeclListCons })

varDeclListNoIn :: JSParser VarDeclListNoIn
varDeclListNoIn =
  chainl1'
  (do { vd <- varDeclNoIn; return $ VarDeclListNoIn vd})
  varDeclNoIn
  (do { punctuator ","; return $ VarDeclListNoInCons})

varDecl :: JSParser VarDecl
varDecl =
  do { i <- getIdent; mInit <- optionMaybe initialiser; return $ VarDecl i mInit }

varDeclNoIn :: JSParser VarDeclNoIn
varDeclNoIn =
  do { i <- getIdent; mInit <- optionMaybe initialiserNoIn; return $ VarDeclNoIn i mInit }

initialiser :: JSParser Initialiser
initialiser =
  do { punctuator "="; ae <- assignExpr; return $ Initialiser ae }

initialiserNoIn :: JSParser InitialiserNoIn
initialiserNoIn =
  do { punctuator "="; ae <- assignExprNoIn; return $ InitialiserNoIn ae }

emptyStmt :: JSParser EmptyStmt
emptyStmt =
  do { punctuator ";"; return EmptyStmt }

exprStmt :: JSParser ExprStmt
exprStmt =
  do { notFollowedBy (try $ punctuator "{" <|> identName "function"); e <- expr; autoSemi; return $ ExprStmt e }

ifStmt :: JSParser IfStmt
ifStmt =
  try (do { identName "if"; punctuator "("; e <- expr; punctuator ")"; s1 <- stmt; identName "else"; s2 <- stmt; return $ IfStmtIfElse e s1 s2 }) <|>
  do { identName "if"; punctuator "("; e <- expr; punctuator ")"; s <- stmt; return $ IfStmtIf e s }

itStmt :: JSParser ItStmt
itStmt =
  try (do { identName "do"; s <- stmt; identName "while"; punctuator "("; e <- expr; punctuator ")"; return $ ItStmtDoWhile s e }) <|>
  try (do { identName "while"; punctuator "("; e <- expr; punctuator ")"; s <- stmt; return $ ItStmtWhile e s }) <|>
  try (do { identName "for"; punctuator "("; me1 <- optionMaybe exprNoIn; punctuator ";"; me2 <- optionMaybe expr; punctuator ";"; me3 <- optionMaybe expr; punctuator ")"; s <- stmt; return $ ItStmtFor me1 me2 me3 s }) <|>
  try (do { identName "for"; punctuator "("; identName "var"; vdl <- varDeclListNoIn; punctuator ";"; me1 <- optionMaybe expr; punctuator ";"; me2 <- optionMaybe expr; punctuator ")"; s <- stmt; return $ ItStmtForVar vdl me1 me2 s }) <|>
  do { identName "for"; punctuator "("; le <- leftExpr; identName "in"; e <- expr; punctuator ")"; s <- stmt; return $ ItStmtForIn le e s } <|>
  do { identName "for"; punctuator "("; identName "var"; vd <- varDeclNoIn; identName "in"; e <- expr; punctuator ")"; s <- stmt; return $ ItStmtForVarIn vd e s }

contStmt :: JSParser ContStmt
contStmt =
  try (do { identName "continue"; autoSemi; return ContStmt }) <|>
  do { identName "continue"; noLineTerminatorHere; i <- getIdent; autoSemi; return $ ContStmtLabelled i }

breakStmt :: JSParser BreakStmt
breakStmt =
  try (do { identName "break"; autoSemi; return BreakStmt }) <|>
  do { identName "break"; noLineTerminatorHere; i <- getIdent; autoSemi; return $ BreakStmtLabelled i }

returnStmt :: JSParser ReturnStmt
returnStmt =
  try (do { identName "return"; autoSemi; return ReturnStmt }) <|>
  do { identName "return"; noLineTerminatorHere; e <- expr; autoSemi; return $ ReturnStmtExpr e }

withStmt :: JSParser WithStmt
withStmt =
  do { identName "with"; punctuator "("; e <- expr; punctuator ")"; s <- stmt; return $ WithStmt e s }

switchStmt :: JSParser SwitchStmt
switchStmt =
  do { identName "switch"; punctuator "("; e <- expr; punctuator ")"; cb <- caseBlock; return $ SwitchStmt e cb }

caseBlock :: JSParser CaseBlock
caseBlock =
  try (do { punctuator "{"; mcc <- optionMaybe caseClauses; punctuator "}"; return $ CaseBlock mcc }) <|>
  do { punctuator "{"; mcc1 <- optionMaybe caseClauses; dc <- defaultClause; mcc2 <- optionMaybe caseClauses; punctuator "}"; return $ CaseBlockDefault mcc1 dc mcc2 }

caseClauses :: JSParser CaseClauses
caseClauses =
  chainl1'
  (do { cc <- caseClause; return $ CaseClauses cc })
  caseClause
  (do { return $ CaseClausesCons })

caseClause :: JSParser CaseClause
caseClause =
  do { identName "case"; e <- expr; punctuator ":"; msl <- optionMaybe stmtList; return $ CaseClause e msl }

defaultClause :: JSParser DefaultClause
defaultClause =
  do { identName "default"; punctuator ":"; msl <- optionMaybe stmtList; return $ DefaultClause msl }

labelledStmt :: JSParser LabelledStmt
labelledStmt =
  do { i <- getIdent; punctuator ":"; s <- stmt; return $ LabelledStmt i s }

throwStmt :: JSParser ThrowStmt
throwStmt =
  do { identName "throw"; noLineTerminatorHere; e <- expr; autoSemi; return $ ThrowStmt e }

tryStmt :: JSParser TryStmt
tryStmt = do
  identName "try"
  b <- block
  do { f <- finally; return $ TryStmtBF b f } <|>
    do { c <- catch;
         do { f <- finally; return $ TryStmtBCF b c f } <|>
         do { return $ TryStmtBC b c }
       }

catch :: JSParser Catch
catch =
  do { identName "catch"; punctuator "("; i <- getIdent; punctuator ")"; b <- block; return $ Catch i b }

finally :: JSParser Finally
finally =
  do { identName "finally"; b <- block; return $ Finally b }

dbgStmt :: JSParser DbgStmt
dbgStmt =
  do { identName "debugger"; autoSemi; return DbgStmt }

funcDecl :: JSParser FuncDecl
funcDecl =
  do { identName "function"; i <- getIdent; punctuator "("; mfpl <- optionMaybe formalParamList; punctuator ")"; punctuator "{"; fb <- funcBody; punctuator "}"; return $ FuncDecl i mfpl fb }

funcExpr :: JSParser FuncExpr
funcExpr =
  do { identName "function"; mi <- optionMaybe getIdent; punctuator "("; mfpl <- optionMaybe formalParamList; punctuator ")"; punctuator "{"; fb <- funcBody; punctuator "}"; return $ FuncExpr mi mfpl fb }

formalParamList :: JSParser FormalParamList
formalParamList =
  chainl1'
  (do { i <- getIdent; return $ FormalParamList i })
  getIdent
  (do { punctuator ","; return $ FormalParamListCons })

funcBody :: JSParser FuncBody
funcBody =
  do { mse <- optionMaybe sourceElements; return $ FuncBody mse }

program :: JSParser Program
program =
  do { mse <- optionMaybe sourceElements; return $ Program mse }

sourceElements :: JSParser SourceElements
sourceElements =
  chainl1'
  (do { se <- sourceElement; return $ SourceElements se })
  sourceElement
  (do { return SourceElementsCons })

sourceElement :: JSParser SourceElement
sourceElement =
  do { s <- stmt; return $ SourceElementStmt s } <|>
  do { fd <- funcDecl; return $ SourceElementFuncDecl fd }

parseJavaScript :: String -> Either ParseError Program
parseJavaScript input =
  let p = many lineTerminator *> program <* many lineTerminator <* eof
  in runParser p newJSPState "" $ lexJavaScript input
