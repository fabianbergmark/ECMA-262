{-# LANGUAGE AllowAmbiguousTypes,
             FlexibleContexts,
             FlexibleInstances,
             FunctionalDependencies,
             GeneralizedNewtypeDeriving,
             MultiParamTypeClasses,
             OverlappingInstances,
             PatternSynonyms,
             RankNTypes,
             RecordWildCards,
             ScopedTypeVariables,
             TypeOperators,
             TypeSynonymInstances #-}

module Language.JavaScript.Interpret
       where

import Control.Applicative ((<$>), (<|>), (<*>))
import Control.Lens (Lens', (.=), (?=), (%=))
import qualified Control.Lens as Lens (at, lens, use)
import Control.Monad (void)
import Control.Monad (forM, liftM2, when)
import qualified Control.Monad.Trans.Except as Except
  (ExceptT, catchE, runExceptT, throwE)
import qualified Control.Monad.Trans.State.Lazy as State
  (StateT(..), evalStateT)

import Data.Default
import Data.Int
import Data.Fixed (mod')
import Data.Map (Map)
import qualified Data.Map as Map
  (empty, fromList, insert, lookup, member, toList)
import Data.Maybe (fromJust, isJust)
import Data.Word
import Data.Bits
  ((.|.), (.&.), complement, shiftL, shiftR, xor)
import Data.Foldable (foldlM)

import Prelude (Bool(..), Double, Either(..), Integer,
                Maybe(..), String,
                Eq((/=), (==)), Floating(..), Fractional(..),
                Functor(..), Monad(..), Num((+), (-), (*), abs),
                Ord((>), (<), (>=), (<=)), Real, RealFloat, RealFrac, Show(..),
                ($), (.), (^), (++),
                (&&), (||), (!!),
                const, elem, error, flip, floor, foldl,
                fromInteger, fromIntegral, id, isInfinite, isNaN, isNegativeZero,
                length, maybe, mod, not, null, show, signum, snd, succ,
                undefined)
import qualified Prelude

import Safe (tailSafe)

import Language.JavaScript.AST
import Language.JavaScript.String
import Language.JavaScript.SubType

class Interpret f m t | f -> t where
  interpret :: f -> m t

class Interpret1 f m p t | f -> p, f -> t where
  interpret1 :: f -> p -> m t

instance (Functor m, Monad m) => Interpret Literal m Value where
  interpret (LiteralNull n) = do
    n' <- interpret n
    return $ inj n'
  interpret (LiteralBool b) =  do
    b' <- interpret b
    return $ inj b'
  interpret (LiteralNum n) =  do
    n' <- interpret n
    return $ inj n'
  interpret (LiteralString s) =  do
    s' <- interpret s
    return $ inj s'
  interpret (LiteralRegExp r) = do
    r' <- interpret r
    return $ inj r'

instance (Functor m, Monad m) => Interpret NullLit m Null where
  interpret NullLit = return Null

instance (Functor m, Monad m) => Interpret BoolLit m Bool where
  interpret (BoolLit b) = return b

instance (Functor m, Monad m) => Interpret StringLit m String where
  interpret (StringLit s) = return s

instance (Functor m, Monad m) => Interpret NumLit m Number where
  interpret (NumLit n) = return $ Number n

instance (Functor m, Monad m) => Interpret RegExpLit m Undefined where
  interpret (RegExpLit _) = return $ Undefined

instance (Functor m, Monad m) =>
         Interpret PrimExpr (JavaScriptT m) CallValue where
  interpret PrimExprThis = do
    v <- Lens.use $ contextStack . currentContext . thisBinding
    return $ inj v

  interpret (PrimExprIdent (Ident (IdentName s))) = do
    env <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    let strict = False
    inj <$> getIdentifierReference (Just env) s strict

  interpret (PrimExprLiteral l) = do
    v <- interpret l
    return $ inj v
  interpret (PrimExprArray a) = do
    o <- interpret a
    return $ inj o
  interpret (PrimExprObject o) = do
    v <- interpret o
    return $ inj v
  interpret (PrimExprParens e) = do
    v <- interpret e
    return $ inj v

instance (Functor m, Monad m) =>
         Interpret ArrayLit (JavaScriptT m) Object where
  interpret (ArrayLitH me) = do
    a <- newArrayObject []
    pad <- case me of
            Just e -> interpret e
            _ -> return $ Number 0
    put a "length" (inj pad) False
    return a

  interpret (ArrayLit e) = interpret e
  interpret (ArrayLitT e mel) = do
    array <- interpret e
    pad <- case mel of
            Just el -> interpret el
            _ -> return $ Number 0
    len <- get array "length" >>= toNumber
    newLen <- toUint32 (pad + len)
    put array "length" (inj $ Number $ fromIntegral newLen) False
    return array

instance (Functor m, Monad m) =>
         Interpret ObjectLit (JavaScriptT m) Object where
  interpret ObjectLitEmpty = do
    o <- newObjectObject Nothing
    return o

  interpret (ObjectLit pl) = interpret pl

instance (Functor m, Monad m) =>
         Interpret PropList (JavaScriptT m) Object where
  interpret (PropListAssign pa) = do
    obj <- newObjectObject Nothing
    PropertyIdentifier name desc <- interpret pa
    defineOwnProperty obj name desc False
    return obj

  interpret (PropListCons pl pa) = do
    obj <- interpret pl
    PropertyIdentifier name desc <- interpret pa
    mPrevious <- getOwnProperty obj name
    case mPrevious of
     JSJust previous -> return ()
     JSNothing -> return ()
    defineOwnProperty obj name desc False
    return obj

instance (Functor m, Monad m) =>
         Interpret PropAssign (JavaScriptT m) PropertyIdentifier where
  interpret (PropAssignField pn ae) = do
    propName <- interpret pn
    exprValue <- interpret ae
    propValue <- getValue exprValue
    let desc = def {
          propertyDescriptorValue        = Just propValue,
          propertyDescriptorWritable     = Just True,
          propertyDescriptorEnumerable   = Just True,
          propertyDescriptorConfigurable = Just True }
    return $ PropertyIdentifier propName desc

  interpret (PropAssignGet pn fb) = do
    propName <- interpret pn
    lex <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    let strict = False
    closure <- newFunctionObject Nothing fb lex strict
    let desc = def {
          propertyDescriptorGet          = Just closure,
          propertyDescriptorEnumerable   = Just True,
          propertyDescriptorConfigurable = Just True }
    return $ PropertyIdentifier propName desc

  interpret (PropAssignSet pn (PropSetParamList i) fb) = do
    propName <- interpret pn
    lex <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    let strict = False
    closure <- newFunctionObject (Just (FormalParamList i)) fb lex strict
    let desc = def {
          propertyDescriptorSet          = Just closure,
          propertyDescriptorEnumerable   = Just True,
          propertyDescriptorConfigurable = Just True }
    return $ PropertyIdentifier propName desc

instance (Functor m, Monad m) =>
         Interpret PropName (JavaScriptT m) String where
  interpret (PropNameId (IdentName s)) = return s
  interpret (PropNameStr (StringLit s)) = return s
  interpret (PropNameNum (NumLit n)) = do
    let nbr = Number n
    toString nbr

instance (Functor m, Monad m) =>
         Interpret Elision m Number where
  interpret (ElisionComma) = return $ Number 1
  interpret (ElisionCons e ) = do
    Number n <- interpret e
    return $ Number (n+1)

instance (Functor m, Monad m) =>
         Interpret ElementList (JavaScriptT m) Object where
  interpret (ElementList me ae) = do
    array <- newArrayObject []
    firstIndex <-
      case me of
       Just e -> interpret e
       _ -> return $ Number 0
    initResult <- interpret ae
    initValue <- getValue initResult
    s <- toString firstIndex
    defineOwnProperty
      array
      s
      (def {
          propertyDescriptorValue        = Just initValue,
          propertyDescriptorWritable     = Just True,
          propertyDescriptorEnumerable   = Just True,
          propertyDescriptorConfigurable = Just True })
      False
    return array

  interpret (ElementListCons el me ae) = do
    array <- interpret el
    pad <- case me of
            Just e -> interpret e
            _ -> return $ Number 0
    initResult <- interpret ae
    initValue <- getValue initResult
    len <- get array "length"
    newLen <- pad `operatorPlus` len >>=
              toUint32 >>=
              toString . Number . fromIntegral
    let desc = def {
          propertyDescriptorValue        = Just initValue,
          propertyDescriptorWritable     = Just True,
          propertyDescriptorEnumerable   = Just True,
          propertyDescriptorConfigurable = Just True }
    defineOwnProperty array newLen desc False
    return array


instance (Functor m, Monad m) =>
         Interpret Stmt (JavaScriptT m) Completion where
  interpret (StmtBlock b) = interpret b
  interpret (StmtVar v) = interpret v
  interpret (StmtEmpty e) = interpret e
  interpret (StmtExpr e) = interpret e
  interpret (StmtIf i) = interpret i
  interpret (StmtIt i) = interpret i
  interpret (StmtCont c) = interpret c
  interpret (StmtBreak b) = interpret b
  interpret (StmtReturn r) = interpret r
  interpret (StmtWith w) = interpret w
  interpret (StmtLabelled l) = interpret l
  interpret (StmtSwitch s) = interpret s
  interpret (StmtThrow t) = interpret t
  interpret (StmtTry t) = interpret t
  interpret (StmtDbg d) = interpret d

instance (Functor m, Monad m) =>
         Interpret Block (JavaScriptT m) Completion where
  interpret (Block Nothing) =
    return $ Completion CompletionTypeNormal Nothing Nothing
  interpret (Block (Just sl)) = interpret sl

instance (Functor m, Monad m) =>
         Interpret StmtList (JavaScriptT m) Completion where
  interpret (StmtList stmt) =
    Except.catchE
    (interpret stmt)
    (\v -> return $ Completion CompletionTypeThrow (Just v) Nothing)
  interpret (StmtListCons sl stmt) = do
    slc <- interpret sl
    case slc of
     Completion CompletionTypeNormal slv _ ->
       Except.catchE
       (do
           s@(Completion sty sva sta) <- (interpret stmt :: JavaScriptT m Completion)
           if isJust sva
             then return $ Completion sty sva sta
             else return $ Completion sty slv sta)
       (\v -> return $ Completion CompletionTypeThrow (Just v) Nothing)
     _ -> return slc

instance (Functor m, Monad m) =>
         Interpret VarStmt (JavaScriptT m) Completion where
  interpret (VarStmt vdl) = do
    interpret vdl
    return $ Completion CompletionTypeNormal Nothing Nothing

instance (Functor m, Monad m) =>
         Interpret VarDeclList (JavaScriptT m) String where
  interpret (VarDeclList vd) = interpret vd
  interpret (VarDeclListCons vdl vd) = do
    interpret vdl
    interpret vd

instance (Functor m, Monad m) =>
         Interpret VarDeclListNoIn (JavaScriptT m) String where
  interpret (VarDeclListNoIn vd) = interpret vd
  interpret (VarDeclListNoInCons vdl vd) = do
    interpret vdl
    interpret vd

instance (Functor m, Monad m) =>
         Interpret VarDecl (JavaScriptT m) String where
  interpret (VarDecl (Ident (IdentName s)) Nothing) =
    return s
  interpret (VarDecl ident@(Ident (IdentName s)) (Just init)) = do
    lhs <- interpret ident
    rhs <- interpret init
    value <- getValue rhs
    putValue lhs value
    return s

instance (Functor m, Monad m) =>
         Interpret VarDeclNoIn (JavaScriptT m) String where
  interpret (VarDeclNoIn (Ident (IdentName s)) Nothing) =
    return s
  interpret (VarDeclNoIn ident@(Ident (IdentName s)) (Just init)) = do
    lhs <- interpret ident
    rhs <- interpret init
    value <- getValue rhs
    putValue lhs value
    return s

instance (Functor m, Monad m) =>
         Interpret Initialiser (JavaScriptT m) CallValue where
  interpret (Initialiser ae) = interpret ae

instance (Functor m, Monad m) =>
         Interpret InitialiserNoIn (JavaScriptT m) CallValue where
  interpret (InitialiserNoIn ae) = interpret ae

instance (Functor m, Monad m) =>
         Interpret EmptyStmt m Completion where
  interpret EmptyStmt =
    return $
    Completion CompletionTypeNormal Nothing Nothing

instance (Functor m, Monad m) =>
         Interpret ExprStmt (JavaScriptT m) Completion where
  interpret (ExprStmt e) = do
    exprRef <- interpret e
    v <- getValue exprRef
    return $ Completion CompletionTypeNormal (Just v) Nothing

instance (Functor m, Monad m) =>
         Interpret IfStmt (JavaScriptT m) Completion where
  interpret (IfStmtIfElse e s1 s2) = do
    exprRef <- interpret e
    b <- getValue exprRef >>= return . toBoolean
    if b
      then interpret s1
      else interpret s2

  interpret (IfStmtIf e s) = do
    exprRef <- interpret e
    b <- getValue exprRef >>= return . toBoolean
    if b
      then interpret s
      else return $ Completion CompletionTypeNormal Nothing Nothing

instance (Functor m, Monad m) =>
         Interpret ItStmt (JavaScriptT m) Completion where
  interpret (ItStmtDoWhile stmt expr) = doWhile Nothing
    where
      doWhile :: Maybe Value -> JavaScriptT m Completion
      doWhile v = do
        s@(Completion sty sv sta) <- interpret stmt
        let v' = sv <|> v
        ils <- inCurrentLabelSet sta
        if sty /= CompletionTypeContinue ||
           not ils
          then do
          if sty == CompletionTypeBreak &&
             ils
            then return $ Completion CompletionTypeNormal v Nothing
            else
            if sty /= CompletionTypeNormal
            then return s
            else do
              exprRef <- interpret expr
              b <- getValue exprRef >>= return . toBoolean
              if b
                then doWhile v'
                else return $ Completion CompletionTypeNormal v' Nothing
          else do
          exprRef <- interpret expr
          b <- getValue exprRef >>= return . toBoolean
          if b
            then doWhile v'
            else return $ Completion CompletionTypeNormal v' Nothing

  interpret (ItStmtWhile expr stmt) = while Nothing
    where
      while :: Maybe Value -> JavaScriptM Completion
      while v = do
        exprRef <- interpret expr
        b <- getValue exprRef >>= return . toBoolean
        if not b
          then return $ Completion CompletionTypeNormal v Nothing
          else do
          s@(Completion sty sv sta) <- interpret stmt
          let v' = sv <|> v
          ils <- inCurrentLabelSet sta
          if sty /= CompletionTypeContinue ||
             not ils
            then
            if sty == CompletionTypeBreak &&
               ils
            then return $ Completion CompletionTypeNormal v' Nothing
            else
              if sty /= CompletionTypeNormal
              then return s
              else while v'
            else while v'

  interpret (ItStmtFor me1 me2 me3 s) = do
    case me1 of
     Just e1 -> do
       exprRef <- interpret e1
       getValue exprRef
       return ()
     _ -> return ()
    for Nothing
    where
      for :: Maybe Value -> JavaScriptM Completion
      for v = do
        case me2 of
         Just e2 -> do
           testExprRef <- interpret e2
           b <- getValue testExprRef >>= return . toBoolean
           if not b
             then return $ Completion CompletionTypeNormal v Nothing
             else runLoop v
         _ -> runLoop v
      runLoop v = do
        stmt@(Completion sty sv sta) <- interpret s
        let v' = sv <|> v
        ils <- inCurrentLabelSet sta
        if sty == CompletionTypeBreak &&
           ils
          then return $ Completion CompletionTypeNormal v' Nothing
          else
          if (sty /= CompletionTypeContinue ||
              not ils) &&
             sty /= CompletionTypeNormal
          then return stmt
          else do
            case me3 of
             Just e3 -> do
               incExprRef <- interpret e3
               getValue incExprRef
               return ()
             Nothing -> return ()
            for v'

  interpret (ItStmtForVar vdl me2 me3 s) = do
    interpret vdl
    for Nothing
    where
      for :: Maybe Value -> JavaScriptM Completion
      for v = do
        case me2 of
         Just e2 -> do
           testExprRef <- interpret e2
           b <- getValue testExprRef >>= return . toBoolean
           if not b
             then return $ Completion CompletionTypeNormal v Nothing
             else runLoop v
         _ -> runLoop v
      runLoop v = do
        stmt@(Completion sty sv sta) <- interpret s
        let v' = sv <|> v
        ils <- inCurrentLabelSet sta
        if sty == CompletionTypeBreak &&
           ils
          then return $ Completion CompletionTypeNormal v' Nothing
          else
          if (sty /= CompletionTypeContinue ||
              not ils) &&
             sty /= CompletionTypeNormal
          then return stmt
          else do
            case me3 of
             Just e3 -> do
               incExprRef <- interpret e3
               getValue incExprRef
               return ()
             Nothing -> return ()
            for v'

  interpret (ItStmtForIn le e s) = do
    exprRef <- interpret e
    exprValue <- getValue exprRef
    case exprValue of
     ValueNull _ ->
       return $ Completion CompletionTypeNormal Nothing Nothing
     ValueUndefined _ ->
       return $ Completion CompletionTypeNormal Nothing Nothing
     _ -> do
       obj <- toObject exprValue
       ps <- Lens.use $ properties obj
       forIn (Map.toList ps) Nothing
     where
       forIn :: [(String, Property)] -> Maybe Value -> JavaScriptM Completion
       forIn [] v = return $ Completion CompletionTypeNormal v Nothing
       forIn ((p, pr):ps) v =  do
         let enum = case pr of
                  PropertyData (DataDescriptor {..}) ->
                    dataDescriptorEnumerable
                  PropertyAccessor (AccessorDescriptor {..}) ->
                    accessorDescriptorEnumerable
         if enum
           then do
           lhsRef <- interpret le
           putValue lhsRef p
           stmt@(Completion sty sv sta) <- interpret s
           let v' = sv <|> v
           ils <- inCurrentLabelSet sta
           if sty == CompletionTypeBreak &&
              ils
             then return $ Completion CompletionTypeNormal v Nothing
             else
             if (sty /= CompletionTypeContinue ||
                 not ils) &&
                sty /= CompletionTypeNormal
             then return stmt
             else forIn ps v'
           else forIn ps v

  interpret (ItStmtForVarIn vd e s) = do
    varName <- interpret vd
    exprRef <- interpret e
    exprValue <- getValue exprRef
    case exprValue of
     ValueNull _ ->
       return $ Completion CompletionTypeNormal Nothing Nothing
     ValueUndefined _ ->
       return $ Completion CompletionTypeNormal Nothing Nothing
     _ -> do
       obj <- toObject exprValue
       ps <- Lens.use $ properties obj
       forIn (Map.toList ps) varName Nothing
     where
       forIn :: [(String, Property)] -> String -> Maybe Value ->
                JavaScriptM Completion
       forIn [] _ v = return $ Completion CompletionTypeNormal v Nothing
       forIn ((p, pr):ps) varName v =  do
         let enum = case pr of
                  PropertyData (DataDescriptor {..}) ->
                    dataDescriptorEnumerable
                  PropertyAccessor (AccessorDescriptor {..}) ->
                    accessorDescriptorEnumerable
         if enum
           then do
           varRef <- interpret (Ident (IdentName varName))
           putValue varRef p
           stmt@(Completion sty sv sta) <- interpret s
           let v' = sv <|> v
           ils <- inCurrentLabelSet sta
           if sty == CompletionTypeBreak &&
              ils
             then return $ Completion CompletionTypeNormal v Nothing
             else
             if (sty /= CompletionTypeContinue ||
                 not ils) &&
                sty /= CompletionTypeNormal
             then return stmt
             else forIn ps varName v'
           else forIn ps varName v

instance (Functor m, Monad m) =>
         Interpret ContStmt m Completion where
  interpret (ContStmt) =
    return $
    Completion CompletionTypeContinue Nothing Nothing

  interpret (ContStmtLabelled i) =
    return $
    Completion CompletionTypeContinue Nothing (Just i)

instance (Functor m, Monad m) =>
         Interpret BreakStmt m Completion where
  interpret (BreakStmt) =
    return $
    Completion CompletionTypeBreak Nothing Nothing

  interpret (BreakStmtLabelled i) =
    return $
    Completion CompletionTypeBreak Nothing (Just i)

instance (Functor m, Monad m) =>
         Interpret ReturnStmt (JavaScriptT m) Completion where
  interpret (ReturnStmt) = do
    return $ Completion CompletionTypeReturn (inj Undefined) Nothing
  interpret (ReturnStmtExpr e) = do
    exprRef <- interpret e
    v <- getValue exprRef
    return $ Completion CompletionTypeReturn (Just v) Nothing

instance (Functor m, Monad m) =>
         Interpret WithStmt (JavaScriptT m) Completion where
  interpret (WithStmt expr stmt) = do
    val <- interpret expr
    obj <- getValue val >>= toObject
    oldEnv <- Lens.use (contextStack . currentContext . lexicalEnvironment)
    newEnv <- newObjectObjectEnvironment obj (Just oldEnv)
    contextStack . currentContext . lexicalEnvironment .= newEnv
    c <- Except.catchE
         (interpret stmt :: JavaScriptT m Completion)
         (\v -> return $ Completion CompletionTypeThrow (Just v) Nothing)
    contextStack . currentContext . lexicalEnvironment .= oldEnv
    return c

instance (Functor m, Monad m) =>
         Interpret SwitchStmt (JavaScriptT m) Completion where
  interpret (SwitchStmt expr cb) = do
    exprRef <- interpret expr
    v <- getValue exprRef
    r@(Completion rty rv rta) <- interpret1 cb v
    case rty of
     CompletionTypeBreak ->
       if False
       then return $ Completion CompletionTypeNormal rv Nothing
       else return r
     _ -> return r

instance (Functor m, Monad m) =>
         Interpret1 CaseBlock (JavaScriptT m) Value Completion where
  interpret1 (CaseBlock mccs) = \input -> do
    let v = Nothing
    case mccs of
     Nothing -> return $ Completion CompletionTypeNormal v Nothing
     Just ccs -> do
       ecv <- search input ccs v
       case ecv of
        Left c -> return c
        Right (v', mrccs) -> do
          case mrccs of
           Nothing -> return $ Completion CompletionTypeNormal v' Nothing
           Just rccs -> falltrough rccs v'
    where
      search input (CaseClauses c@(CaseClause e msl)) v = do
        clauseSelector <- interpret c
        if input == clauseSelector
          then do
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             if cty /= CompletionTypeNormal
               then return $ Left r
               else return $ Right (cv, Nothing)
           Nothing -> return $ Right (v, Nothing)
          else return $ Left $ Completion CompletionTypeNormal v Nothing
      search input (CaseClausesCons ccs c@(CaseClause e msl)) v = do
        clauseSelector <- interpret c
        if input == clauseSelector
          then do
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             if cty /= CompletionTypeNormal
               then return $ Left r
               else return $ Right (cv, Just ccs)
           Nothing -> return $ Right (v, Just ccs)
          else search input ccs v
      falltrough (CaseClauses c@(CaseClause e msl)) v = do
        case msl of
         Just sl -> do
           r@(Completion cty cv cta) <- interpret sl
           let v' = cv <|> v
           if cty /= CompletionTypeNormal
             then return $ Completion cty v' cta
             else return $ Completion CompletionTypeNormal v' Nothing
         Nothing -> return $ Completion CompletionTypeNormal v Nothing
      falltrough (CaseClausesCons ccs c@(CaseClause e msl)) v = do
        case msl of
         Just sl -> do
           r@(Completion cty cv cta) <- interpret sl
           let v' = cv <|> v
           if cty /= CompletionTypeNormal
             then return $ Completion cty v' cta
             else falltrough ccs v'
         Nothing -> return $ Completion CompletionTypeNormal v Nothing

  interpret1 (CaseBlockDefault mfccs df@(DefaultClause msl) mrccs) = \input -> do
    let v = Nothing
        found = False
    ecvf <- case mfccs of
            Nothing -> return $ Right (v, found)
            Just fccs -> searchFirst input found fccs v
    case ecvf of
     Left c -> return c
     Right (v', found') -> do
       let foundInB = False
       ecvf' <- case (found, mrccs) of
                 (False, _) -> return $ Right (v, foundInB, mrccs)
                 (_, Nothing) -> return $ Right (v, foundInB, mrccs)
                 (_, Just rccs) -> searchSecond input foundInB rccs v'
       case ecvf' of
        Left c -> return c
        Right (v'', foundInB', mrrccs) -> do
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             let v''' = cv <|> v''
             if cty /= CompletionTypeNormal
               then return $ Completion cty v''' cta
               else do
               case mrrccs of
                Just rrccs -> falltrough rrccs v'''
                Nothing -> return $ Completion CompletionTypeNormal v''' Nothing
    where
      searchFirst input found cs@(CaseClauses c@(CaseClause e msl)) v = do
        if not found
          then do
          clauseSelector <- interpret c
          if input == clauseSelector
            then searchFirst input True cs v
            else return $ Right (v, found)
          else do
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             let v' = cv <|> v
             if cty /= CompletionTypeNormal
               then return $ Left $ Completion cty v' cta
               else return $ Right (v', found)
           Nothing -> return $ Right (v, found)
      searchFirst input found cccs@(CaseClausesCons ccs c) v = do
        if not found
          then do
          clauseSelector <- interpret c
          if input == clauseSelector
            then searchFirst input True cccs v
            else return $ Right (v, found)
          else do
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             let v' = cv <|> v
             if cty /= CompletionTypeNormal
               then return $ Left $ Completion cty v' cta
               else searchFirst input found ccs v'
           Nothing -> searchFirst input found ccs v
      searchSecond input foundInB cs@(CaseClauses c@(CaseClause e msl)) v = do
        clauseSelector <- interpret c
        if input == clauseSelector
          then do
          let foundInB' = True
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             let v' = cv <|> v
             if cty /= CompletionTypeNormal
               then return $ Left $ Completion cty v' cta
               else return $ Right (v', foundInB', Nothing)
           Nothing -> return $ Right (v, foundInB', Nothing)
          else return $ Right (v, foundInB, Nothing)
      searchSecond input foundInB (CaseClausesCons ccs c@(CaseClause e msl)) v = do
        clauseSelector <- interpret c
        if input == clauseSelector
          then do
          let foundInB' = True
          case msl of
           Just sl -> do
             r@(Completion cty cv cta) <- interpret sl
             let v' = cv <|> v
             if cty /= CompletionTypeNormal
               then return $ Left $ Completion cty v' cta
               else return $ Right (v', foundInB', Just ccs)
           Nothing -> return $ Right (v, foundInB', Just ccs)
          else searchSecond input foundInB ccs v
      falltrough cs@(CaseClauses c@(CaseClause e msl)) v = do
        case msl of
         Just sl -> do
           r@(Completion cty cv cta) <- interpret sl
           let v' = cv <|> v
           if cty /= CompletionTypeNormal
             then return $ Completion cty v' cta
             else return $ Completion CompletionTypeNormal v' Nothing
         Nothing -> return $ Completion CompletionTypeNormal v Nothing
      falltrough (CaseClausesCons ccs c@(CaseClause e msl)) v = do
        case msl of
         Just sl -> do
           r@(Completion cty cv cta) <- interpret sl
           let v' = cv <|> v
           if cty /= CompletionTypeNormal
             then return $ Completion cty v' cta
             else falltrough ccs v'
         Nothing -> falltrough ccs v

instance (Functor m, Monad m) =>
         Interpret CaseClause (JavaScriptT m) Value where
  interpret (CaseClause expr _) = do
    exprRef <- interpret expr
    getValue exprRef

instance (Functor m, Monad m) =>
         Interpret LabelledStmt (JavaScriptT m) Completion where
  interpret (LabelledStmt ident stmt) = do
    contextStack . currentContext . labels %= (ident:)
    c@(Completion cty cv cta) <- interpret stmt
    contextStack . currentContext . labels %= tailSafe
    if cty == CompletionTypeBreak &&
       cta == Just ident
      then return $ Completion CompletionTypeNormal cv Nothing
      else return c

instance (Functor m, Monad m) =>
         Interpret ThrowStmt (JavaScriptT m) Completion where
  interpret (ThrowStmt expr) = do
    exprRef <- interpret expr
    v <- getValue exprRef
    return $ Completion CompletionTypeThrow (Just v) Nothing

instance (Functor m, Monad m) =>
         Interpret TryStmt (JavaScriptT m) Completion where
  interpret (TryStmtBC block catch) = do
    b@(Completion cty (Just cv) cta) <- interpret block
    if cty /= CompletionTypeThrow
      then return b
      else interpret1 catch cv
  interpret (TryStmtBF block finally) = do
    b@(Completion bcty bcv bcta) <- interpret block
    f@(Completion fcty fcv fcta) <- interpret finally
    if fcty == CompletionTypeNormal
      then return b
      else return f
  interpret (TryStmtBCF block catch finally) = do
    b@(Completion bcty (Just bcv) bcta) <- interpret block
    c <- if bcty == CompletionTypeThrow
      then interpret1 catch bcv
      else return b
    f@(Completion fcty fcv fcta) <- interpret finally
    if fcty == CompletionTypeNormal
      then return c
      else return f

instance (Functor m, Monad m) =>
         Interpret1 Catch (JavaScriptT m) Value Completion where
  interpret1 (Catch (Ident (IdentName ident)) block) = \c -> do
    oldEnv <- Lens.use (contextStack . currentContext . lexicalEnvironment)
    catchEnv <- newDeclarativeEnvironment (Just oldEnv)
    envRec <- Lens.use $ lexicalEnvironmentInternal catchEnv . environmentRecord
    createMutableBinding envRec ident Nothing
    setMutableBinding envRec ident c False
    contextStack . currentContext . lexicalEnvironment .= catchEnv
    b <- interpret block
    contextStack . currentContext . lexicalEnvironment .= oldEnv
    return b

instance (Functor m, Monad m) =>
         Interpret Finally (JavaScriptT m) Completion where
  interpret (Finally block) = interpret block

instance (Functor m, Monad m) =>
         Interpret DbgStmt (JavaScriptT m) Completion where
  interpret (DbgStmt) = return $ Completion CompletionTypeNormal Nothing Nothing

instance (Functor m, Monad m) =>
         Interpret FuncDecl (JavaScriptT m) Object where
  interpret (FuncDecl i mfpl fb) = do
    var <- Lens.use $ contextStack . currentContext . variableEnvironment
    let strict = False
    newFunctionObject mfpl fb var strict

instance (Functor m, Monad m) =>
         Interpret Program (JavaScriptT m) Completion where
  interpret program@(Program mses) = do
    case mses of
     Nothing -> return $ Completion CompletionTypeNormal Nothing Nothing
     Just ses -> do
       enterGlobalContext program
       result <- interpret ses
       popContext
       return result

instance (Functor m, Monad m) =>
         Interpret FuncExpr (JavaScriptT m) Object where
  interpret (FuncExpr Nothing mfpl fb) = do
    lex <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    let strict = False
    newFunctionObject mfpl fb lex strict
  interpret (FuncExpr (Just (Ident (IdentName s))) mfpl fb) = do
    lex <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    funcEnv <- newDeclarativeEnvironment (Just lex)
    envRec <- Lens.use $ lexicalEnvironmentInternal funcEnv . environmentRecord
    decEnvRec <- Lens.use $ environmentRecordInternal envRec .
                 declarativeEnvironmentRecord
    createImmutableBindingDeclarative decEnvRec s
    let strict = False
    closure <- newFunctionObject mfpl fb funcEnv strict
    initializeImmutableBindingDeclarative decEnvRec s (inj closure)
    return closure

instance (Functor m, Monad m) =>
         Interpret FuncBody (JavaScriptT m) Completion where
  interpret (FuncBody Nothing) = return $
    Completion CompletionTypeNormal (Just (inj Undefined)) Nothing
  interpret (FuncBody (Just ses)) = interpret ses

instance (Functor m, Monad m) =>
         Interpret SourceElements (JavaScriptT m) Completion where
  interpret (SourceElementsCons ses se) = do
    headResult@(Completion hcty hcv hcta) <- interpret ses
    if hcty /= CompletionTypeNormal
      then return headResult
      else do
      tailResult@(Completion tcty tcv tcta) <- interpret se
      let v = tcv <|> hcv
      return $ Completion tcty v tcta
  interpret (SourceElements se) = interpret se

instance (Functor m, Monad m) =>
         Interpret SourceElement (JavaScriptT m) Completion where
  interpret (SourceElementStmt s) = interpret s
  interpret (SourceElementFuncDecl fd) =
    return $ Completion CompletionTypeNormal Nothing Nothing

instance (Functor m, Monad m) =>
         Interpret UExpr (JavaScriptT m) CallValue where
  interpret (UExprPostFix pfe) = interpret pfe

  interpret (UExprDelete ue) = do
    (rv :: CallValue) <- interpret ue
    case rv of
     Left ref -> do
       case getBase ref of
        BaseUndefined _ -> do
          if isStrictReference ref
            then newSyntaxErrorObject Nothing >>= jsThrow . inj
            else return $ inj True
        BaseProperty propertyBase -> do
          obj <- toObject $ inj propertyBase
          inj <$> delete obj (getReferencedName ref) (isStrictReference ref)
        BaseEnvironmentRecord environmentRecordBase -> do
           if isStrictReference ref
             then newSyntaxErrorObject Nothing >>= jsThrow . inj
             else do
             inj <$> deleteBinding environmentRecordBase (getReferencedName ref)

  interpret (UExprVoid ue) = do
    expr <- interpret ue
    getValue expr
    return $ inj Undefined

  interpret (UExprTypeOf ue) = do
    vr <- interpret ue
    case vr of
     Left ref -> do
       if isUnresolvableReference ref
         then return $ inj "undefined"
         else do
         val <- getValue ref
         return . inj . show $ typeOf val
     Right val -> do
       return . inj . show $ typeOf val

  interpret (UExprDoublePlus ue) = do
    (expr :: CallValue) <- interpret ue
    case prj expr of
     Just ref -> do
       if isStrictReference ref
         then do
         case prj (getBase ref) of
          Just (er :: EnvironmentRecord) -> do
            let name = getReferencedName ref
            if name == "eval" ||
               name == "arguments"
              then newSyntaxErrorObject Nothing >>= jsThrow . inj
              else return ()
          Nothing -> return ()
         else return ()
     Nothing -> return ()
    v <- getValue expr
    oldValue <- toNumber v
    let newValue = oldValue + (Number 1)
    putValue expr newValue
    return $ inj newValue

  interpret (UExprDoubleMinus ue) = do
    expr <- interpret ue
    case prj expr of
     Just ref -> do
       if isStrictReference ref
         then do
         case prj (getBase ref) of
          Just (er :: EnvironmentRecord) -> do
            let name = getReferencedName ref
            if name == "eval" ||
               name == "arguments"
              then newSyntaxErrorObject Nothing >>= jsThrow . inj
              else return ()
          Nothing -> return ()
         else return ()
     Nothing -> return ()
    v <- getValue expr
    oldValue <- toNumber v
    let newValue = oldValue - (Number 1)
    putValue expr newValue
    return $ inj newValue

  interpret (UExprUnaryPlus ue) = do
    expr <- interpret ue
    v <- getValue expr
    inj <$> toNumber v

  interpret (UExprUnaryMinus ue) = do
    expr <- interpret ue
    v <- getValue expr
    oldValue <- toNumber v
    return $ inj (-oldValue)

  interpret (UExprBitNot ue) = do
    expr <- interpret ue
    v <- getValue expr
    oldValue <- toInt32 v
    return $ inj $ Number (fromIntegral $ complement oldValue)

  interpret (UExprNot ue) = do
    expr <- interpret ue
    v <- getValue expr
    let oldValue = toBoolean v
    return $ inj $ not oldValue

instance (Functor m, Monad m) =>
         Interpret MemberExpr (JavaScriptT m) CallValue where
  interpret (MemberExprPrim pe) = do
    v <- interpret pe
    return $ inj v

  interpret (MemberExprFunc fe) = do
    (o :: Object) <- interpret fe
    return $ inj o

  interpret (MemberExprArray me expr) = do
    baseReference <- interpret me
    baseValue <- getValue baseReference
    propertyNameReference <- interpret expr
    propertyNameValue <- getValue propertyNameReference
    baseValueCoercible <- toObjectCoercible baseValue
    propertyNameString <- toString propertyNameValue
    let strict = False
    return $ inj $ Reference (inj baseValueCoercible) propertyNameString strict

  interpret (MemberExprDot me (IdentName s)) = do
    baseReference <- interpret me
    baseValue <- getValue baseReference
    baseValueCoercible <- toObjectCoercible baseValue
    let strict = False
    return $ inj $ Reference (inj baseValueCoercible) s strict

  interpret (MemberExprNew me args) = do
    ref <- interpret me
    constructor <- getValue ref
    argList <- interpret args
    case constructor of
     ValueObject o -> do
       inj <$> construct o argList
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj

instance (Functor m, Monad m) =>
         Interpret NewExpr (JavaScriptT m) CallValue where
  interpret (NewExprMember me) = interpret me
  interpret (NewExprNew ne) = do
    ref <- interpret ne
    constructor <- getValue ref
    case constructor of
     ValueObject o -> do
       inj <$> construct o (List [])
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj


instance (Functor m, Monad m) =>
         Interpret CallExpr (JavaScriptT m) CallValue where
  interpret (CallExprMember me args) = do
    rv <- interpret me
    func <- getValue rv
    argList <- interpret args
    case func of
     ValueObject o -> do
       thisValue <-
         case rv of
          Left ref -> do
            case toPropertyReference ref of
              Right propertyBase -> return $ inj propertyBase
              Left (Left er) -> do
                implicitThisValue er
          _ -> return $ inj Undefined
       call o thisValue argList
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj

  interpret (CallExprCall ce args) = do
    rv <- interpret ce
    func <- getValue rv
    argList <- interpret args
    case func of
     ValueObject o -> do
       thisValue <-
         case rv of
          Left ref -> do
            case toPropertyReference ref of
              Right propertyBase -> return $ inj propertyBase
              Left (Left er) -> do
                implicitThisValue er
          _ -> return $ inj Undefined
       call o thisValue argList
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj

  interpret (CallExprArray ce expr) = do
    baseReference <- interpret ce
    baseValue <- getValue baseReference
    propertyNameReference <- interpret expr
    propertyNameValue <- getValue propertyNameReference
    baseValueCoercible <- toObjectCoercible baseValue
    propertyNameString <- toString propertyNameValue
    let strict = False
    return $ inj $ Reference (inj baseValueCoercible) propertyNameString strict

  interpret (CallExprDot ce (IdentName s)) = do
    baseReference <- interpret ce
    baseValue <- getValue baseReference
    baseValueCoercible <- toObjectCoercible baseValue
    let strict = False
    return $ inj $ Reference (inj baseValueCoercible) s strict

instance (Functor m, Monad m) =>
         Interpret Arguments (JavaScriptT m) (List Value) where
  interpret (ArgumentsEmpty) = return (List [])
  interpret (Arguments al) = interpret al

instance (Functor m, Monad m) =>
         Interpret ArgumentList (JavaScriptT m) (List Value) where
  interpret (ArgumentList ae) = do
    ref <- interpret ae
    arg <- getValue ref
    return $ List [arg]

  interpret (ArgumentListCons al ae) = do
    List precedingArgs <- interpret al
    ref <- interpret ae
    arg <- getValue ref
    return $ List (precedingArgs ++ [arg])

instance (Functor m, Monad m) =>
         Interpret LeftExpr (JavaScriptT m) CallValue where
  interpret (LeftExprNewExpr ne) = do
    v <- interpret ne
    return $ inj v
  interpret (LeftExprCallExpr ce) = interpret ce

instance (Functor m, Monad m) =>
         Interpret PostFixExpr (JavaScriptT m) CallValue where
  interpret (PostFixExprLeftExpr le) = interpret le

  interpret (PostFixExprPostInc le) = do
    lhs <- interpret le
    case lhs of
     CallValueReference ref ->
       when (isStrictReference ref) $ do
         case getBase ref of
          BaseEnvironmentRecord _ -> do
            let name = getReferencedName ref
            when (name == "eval" || name == "arguments") $
              newSyntaxErrorObject Nothing >>= jsThrow . inj
          _ -> return ()
     _ -> return ()
    oldValue <- getValue lhs >>= toNumber
    let newValue = oldValue + (Number 1)
    putValue lhs newValue
    return (inj oldValue)

  interpret (PostFixExprPostDec le) = do
    lhs <- interpret le
    case lhs of
     CallValueReference ref ->
       when (isStrictReference ref) $ do
         case getBase ref of
          BaseEnvironmentRecord _ -> do
            let name = getReferencedName ref
            when (name == "eval" || name == "arguments") $
              newSyntaxErrorObject Nothing >>= jsThrow . inj
          _ -> return ()
     _ -> return ()
    oldValue <- getValue lhs >>= toNumber
    let newValue = oldValue - (Number 1)
    putValue lhs newValue
    return (inj oldValue)

instance (Functor m, Monad m) =>
         Interpret MultExpr (JavaScriptT m) CallValue where
  interpret (MultExpr ue) = interpret ue

  interpret (MultExprMult me ue) = do
    left <- interpret me
    right <- interpret ue
    inj <$> left `operatorMult` right

  interpret (MultExprDiv me ue) = do
    left <- interpret me
    right <- interpret ue
    inj <$> left `operatorDiv` right

  interpret (MultExprMod me ue) = do
    left <- interpret me
    right <- interpret ue
    inj <$> left `operatorMod` right

instance (Functor m, Monad m) =>
         Interpret AddExpr (JavaScriptT m) CallValue where
  interpret (AddExpr me) = interpret me

  interpret (AddExprAdd ae me) = do
    lref <- interpret ae
    rref <- interpret me
    inj <$> lref `operatorPlus` rref

  interpret (AddExprSub ae me) = do
    lref <- interpret ae
    rref <- interpret me
    inj <$> lref `operatorMinus` rref

instance (Functor m, Monad m) =>
         Interpret ShiftExpr (JavaScriptT m) CallValue where
  interpret (ShiftExpr ae) = interpret ae
  interpret (ShiftExprLeft se ae) = do
    lref <- interpret se
    rref <- interpret ae
    inj <$> lref `operatorLeftShift` rref

  interpret (ShiftExprRight se ae) = do
    lref <- interpret se
    rref <- interpret ae
    inj <$> lref `operatorSignedRightShift` rref

  interpret (ShiftExprRightZero se ae) = do
    lref <- interpret se
    rref <- interpret ae
    inj <$> lref `operatorUnsignedRightShift` rref

instance (Functor m, Monad m) =>
         Interpret RelExpr (JavaScriptT m) CallValue where
  interpret (RelExpr se) = interpret se

  interpret (RelExprLess re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess lval rval True
    case mr of
     JSNothing -> return $ inj False
     JSJust r -> return $ inj r

  interpret (RelExprGreater re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess rval lval False
    case mr of
     JSNothing -> return $ inj False
     JSJust r -> return $ inj r

  interpret (RelExprLessEq re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess rval lval False
    case mr of
     JSNothing -> return $ inj False
     JSJust _ -> return $ inj True

  interpret (RelExprGreaterEq re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess lval rval True
    case mr of
     JSNothing -> return $ inj False
     JSJust True -> return $ inj False
     JSJust False -> return $ inj True

  interpret (RelExprInstanceOf re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    case rval of
     ValueObject o -> do
       inj <$> hasInstance o lval
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj

  interpret (RelExprIn re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    case prj rval of
     Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj
     Just obj -> do
       s <- toString lval
       inj <$> hasProperty obj s

instance (Functor m, Monad m) =>
         Interpret RelExprNoIn (JavaScriptT m) CallValue where
  interpret (RelExprNoIn se) = interpret se
  interpret (RelExprNoInLess re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess lval rval True
    case mr of
     JSNothing -> return $ inj False
     JSJust r -> return $ inj r

  interpret (RelExprNoInGreater re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess rval lval False
    case mr of
     JSNothing -> return $ inj False
     JSJust r -> return $ inj r

  interpret (RelExprNoInLessEq re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess rval lval False
    case mr of
     JSNothing -> return $ inj False
     JSJust _ -> return $ inj True

  interpret (RelExprNoInGreaterEq re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    mr <- compareLess lval rval True
    case mr of
     JSNothing -> return $ inj False
     JSJust True -> return $ inj False
     JSJust False -> return $ inj True

  interpret (RelExprNoInInstanceOf re se) = do
    lref <- interpret re
    lval <- getValue lref
    rref <- interpret se
    rval <- getValue rref
    case rval of
     ValueObject obj ->
       inj <$> hasInstance obj lval
     _ -> newTypeErrorObject Nothing >>= jsThrow . inj

instance (Functor m, Monad m) =>
         Interpret EqExpr (JavaScriptT m) CallValue where
  interpret (EqExpr re) = interpret re

  interpret (EqExprEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    inj <$> compare rval lval

  interpret (EqExprNotEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    r <- compare rval lval
    return $ inj $ not r

  interpret (EqExprStrictEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    return $ inj $ compareStrict rval lval

  interpret (EqExprStrictNotEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    return $ inj $ not $ compareStrict rval lval

instance (Functor m, Monad m) =>
         Interpret EqExprNoIn (JavaScriptT m) CallValue where
  interpret (EqExprNoIn re) = interpret re

  interpret (EqExprNoInEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    inj <$> compare rval lval

  interpret (EqExprNoInNotEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    r <- compare rval lval
    return $ inj $ not r

  interpret (EqExprNoInStrictEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    return $ inj $ compareStrict rval lval

  interpret (EqExprNoInStrictNotEq eq re) = do
    lref <- interpret eq
    lval <- getValue lref
    rref <- interpret re
    rval <- getValue rref
    return $ inj $ not $ compareStrict rval lval

instance (Functor m, Monad m) =>
         Interpret BitAndExpr (JavaScriptT m) CallValue where
  interpret (BitAndExpr eq) = interpret eq

  interpret (BitAndExprAnd bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseAnd` rref

instance (Functor m, Monad m) =>
         Interpret BitAndExprNoIn (JavaScriptT m) CallValue where
  interpret (BitAndExprNoIn eq) = interpret eq

  interpret (BitAndExprNoInAnd bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseAnd` rref

instance (Functor m, Monad m) =>
         Interpret BitXorExpr (JavaScriptT m) CallValue where
  interpret (BitXorExpr eq) = interpret eq

  interpret (BitXorExprXor bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseXor` rref

instance (Functor m, Monad m) =>
         Interpret BitXorExprNoIn (JavaScriptT m) CallValue where
  interpret (BitXorExprNoIn eq) = interpret eq

  interpret (BitXorExprNoInXor bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseXor` rref

instance (Functor m, Monad m) =>
         Interpret BitOrExpr (JavaScriptT m) CallValue where
  interpret (BitOrExpr eq) = interpret eq

  interpret (BitOrExprOr bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseOr` rref

instance (Functor m, Monad m) =>
         Interpret BitOrExprNoIn (JavaScriptT m) CallValue where
  interpret (BitOrExprNoIn eq) = interpret eq

  interpret (BitOrExprNoInOr bae eq) = do
    lref <- interpret bae
    rref <- interpret eq
    inj <$> lref `operatorBitwiseOr` rref

instance (Functor m, Monad m) =>
         Interpret LogicalAndExpr (JavaScriptT m) CallValue where
  interpret (LogicalAndExpr boe) = interpret boe

  interpret (LogicalAndExprAnd lae boe) = do
    lref <- interpret lae
    lval <- getValue lref
    if not $ toBoolean lval
      then return $ inj lval
      else do
      rref <- interpret boe
      inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret LogicalAndExprNoIn (JavaScriptT m) CallValue where
  interpret (LogicalAndExprNoIn boe) = do
    n <- interpret boe
    return $ inj n

  interpret (LogicalAndExprNoInAnd lae boe) = do
    lref <- interpret lae
    lval <- getValue lref
    if not $ toBoolean lval
      then return $ inj lval
      else do
      rref <- interpret boe
      inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret LogicalOrExpr (JavaScriptT m) CallValue where
  interpret (LogicalOrExpr boe) = interpret boe

  interpret (LogicalOrExprOr lae boe) = do
    lref <- interpret lae
    lval <- getValue lref
    if not $ toBoolean lval
      then return $ inj lval
      else do
      rref <- interpret boe
      inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret LogicalOrExprNoIn (JavaScriptT m) CallValue where
  interpret (LogicalOrExprNoIn boe) = interpret boe

  interpret (LogicalOrExprNoInOr lae boe) = do
    lref <- interpret lae
    lval <- getValue lref
    if toBoolean lval
      then return $ inj lval
      else do
      rref <- interpret boe
      inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret CondExpr (JavaScriptT m) CallValue where
  interpret (CondExpr loe) = interpret loe

  interpret (CondExprIf loe ae1 ae2) = do
    lref <- interpret loe
    lval <- getValue lref
    if toBoolean lval
      then do
      trueRef <- interpret ae1
      inj <$> getValue trueRef
      else do
      falseRef <- interpret ae2
      inj <$> getValue falseRef

instance (Functor m, Monad m) =>
         Interpret CondExprNoIn (JavaScriptT m) CallValue where
  interpret (CondExprNoIn loe) = interpret loe

  interpret (CondExprNoInIf loe ae1 ae2) = do
    lref <- interpret loe
    lval <- getValue lref
    if toBoolean lval
      then do
      trueRef <- interpret ae1
      inj <$> getValue trueRef
      else do
      falseRef <- interpret ae2
      inj <$> getValue falseRef

instance (Functor m, Monad m) =>
         Interpret AssignExpr (JavaScriptT m) CallValue where
  interpret (AssignExprCondExpr ce) = interpret ce

  interpret (AssignExprAssign le AssignOpNormal ae) = do
    lref <- interpret le
    rref <- interpret ae
    rval <- getValue rref
    case lref of
     CallValueReference ref -> do
       when (isStrictReference ref &&
             typeOf (getBase ref) == TypeEnvironmentRecord &&
             (getReferencedName ref == "eval" ||
              getReferencedName ref == "arguments")) $ do
         newSyntaxErrorObject Nothing >>= jsThrow . inj
     _ -> return ()
    putValue lref rval
    return $ inj rval

  interpret (AssignExprAssign le aop ae) = do
    lref <- interpret le
    lval <- getValue lref
    rref <- interpret ae
    rval <- getValue rref
    r <- case aop of
          AssignOpMult -> inj <$> lval `operatorMult` rval
          AssignOpDiv -> inj <$> lval `operatorDiv` rval
          AssignOpMod -> inj <$> lval `operatorMod` rval
          AssignOpPlus -> lval `operatorPlus` rval
          AssignOpMinus -> inj <$> lval `operatorMinus` rval
          AssignOpShiftLeft -> inj <$> lval `operatorLeftShift` rval
          AssignOpShiftRight -> inj <$> lval `operatorSignedRightShift` rval
          AssignOpShiftRightZero -> inj <$> lval `operatorUnsignedRightShift` rval
          AssignOpBitAnd -> inj <$> lval `operatorBitwiseAnd` rval
          AssignOpBitXor -> inj <$> lval `operatorBitwiseXor` rval
          AssignOpBitOr -> inj <$> lval `operatorBitwiseOr` rval
    case lref of
     CallValueReference ref -> do
       when (isStrictReference ref &&
             typeOf (getBase ref) == TypeEnvironmentRecord &&
             (getReferencedName ref == "eval" ||
              getReferencedName ref == "arguments")) $ do
         newSyntaxErrorObject Nothing >>= jsThrow . inj
     _ -> return ()
    putValue lref r
    return $ inj r

instance (Functor m, Monad m) =>
         Interpret AssignExprNoIn (JavaScriptT m) CallValue where
  interpret (AssignExprNoInCondExpr ce) = interpret ce

  interpret (AssignExprNoInAssign le AssignOpNormal ae) = do
    lref <- interpret le
    rref <- interpret ae
    rval <- getValue rref
    case prj lref of
     Just ref -> do
       when (isStrictReference ref &&
             typeOf (getBase ref) == TypeEnvironmentRecord &&
             (getReferencedName ref == "eval" ||
              getReferencedName ref == "arguments")) $ do
         newSyntaxErrorObject Nothing >>= jsThrow . inj
     Nothing -> return ()
    putValue lref rval
    return $ inj rval

  interpret (AssignExprNoInAssign le aop ae) = do
    lref <- interpret le
    lval <- getValue lref
    rref <- interpret ae
    rval <- getValue rref
    r <- case aop of
          AssignOpMult -> inj <$> lval `operatorMult` rval
          AssignOpDiv -> inj <$> lval `operatorDiv` rval
          AssignOpMod -> inj <$> lval `operatorMod` rval
          AssignOpPlus -> lval `operatorPlus` rval
          AssignOpMinus -> inj <$> lval `operatorMinus` rval
          AssignOpShiftLeft -> inj <$> lval `operatorLeftShift` rval
          AssignOpShiftRight -> inj <$> lval `operatorSignedRightShift` rval
          AssignOpShiftRightZero -> inj <$> lval `operatorUnsignedRightShift` rval
          AssignOpBitAnd -> inj <$> lval `operatorBitwiseAnd` rval
          AssignOpBitXor -> inj <$> lval `operatorBitwiseXor` rval
          AssignOpBitOr -> inj <$> lval `operatorBitwiseOr` rval
    case prj lref of
     Just ref -> do
       when (isStrictReference ref &&
             typeOf (getBase ref) == TypeEnvironmentRecord &&
             (getReferencedName ref == "eval" ||
              getReferencedName ref == "arguments")) $ do
         newSyntaxErrorObject Nothing >>= jsThrow . inj
     Nothing -> return ()
    putValue lref r
    return $ inj r

instance (Functor m, Monad m) =>
         Interpret Expr (JavaScriptT m) CallValue where
  interpret (Expr ae) = interpret ae

  interpret (ExprCons e ae) = do
    lref <- interpret e
    getValue lref
    rref <- interpret ae
    inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret ExprNoIn (JavaScriptT m) CallValue where
  interpret (ExprNoIn ae) = interpret ae

  interpret (ExprNoInCons e ae) = do
    lref <- interpret e
    getValue lref
    rref <- interpret ae
    inj <$> getValue rref

instance (Functor m, Monad m) =>
         Interpret Ident (JavaScriptT m) Reference where
  interpret (Ident (IdentName s)) = do
    env <- Lens.use $ contextStack . currentContext . lexicalEnvironment
    let strict = False
    getIdentifierReference (Just env) s strict

declarationBindingInstantiation :: (Functor m, Monad m) =>
                                   Code -> JavaScriptT m ()
declarationBindingInstantiation c = do
  let strict = False
      configurableBindings =
        case c of
         CodeEval {} -> True
         _ -> False

  case c of
   CodeFunction func args -> do
     (FuncBody mses) <- code func
     (lex, env) <- step1
     dec <- Lens.use $ environmentRecordInternal env . declarativeEnvironmentRecord
     names <- step2 strict dec func args
     case mses of
      Just ses -> do
        step3 strict configurableBindings env ses
        argumentsAlreadyDeclared <- step4 env
        when (not argumentsAlreadyDeclared) $ do
          step5 strict lex dec func names args
        step6 strict configurableBindings env ses
        return ()
      Nothing -> do
        argumentsAlreadyDeclared <- step4 env
        when (not argumentsAlreadyDeclared) $ do
          step5 strict lex dec func names args
        return ()
   CodeGlobal (Program mses) -> do
     (lex, env) <- step1
     case mses of
      Just ses -> do
        step3 strict configurableBindings env ses
        step4 env
        step6 strict configurableBindings env ses
        return ()
      Nothing -> do
        step4 env
        return ()
  where
    step1 :: (Functor m, Monad m) =>
             JavaScriptT m (LexicalEnvironment, EnvironmentRecord)
    step1 = do
      var <- Lens.use $ contextStack . currentContext . variableEnvironment
      env <- Lens.use $ lexicalEnvironmentInternal var . environmentRecord
      return (var, env)

    step2 :: (Functor m, Monad m) =>
             Bool -> DeclarativeEnvironmentRecord -> Object -> List Value ->
             JavaScriptT m (List String)
    step2 strict env func args@(List as) = do
      names@(List ns) <- formalParameters func
      let argCount = length as
          n = 0
      (flip . flip foldlM) n ns $ \n argName -> do
        let n' = n+1
            v = if n' > argCount
                then inj Undefined
                else as !! (n' - 1)
        argAlreadyDeclared <- hasBindingDeclarative env argName
        when (not argAlreadyDeclared) $ do
          createMutableBindingDeclarative env argName Nothing
        setMutableBindingDeclarative env argName v strict
        return n'
      return names

    step3 :: (Functor m, Monad m) =>
             Bool -> Bool -> EnvironmentRecord -> SourceElements ->
             JavaScriptT m ()
    step3 strict configurableBindings env ses = do
      forM (extractFuncDecls ses) $
        \f@(FuncDecl (Ident (IdentName fn)) mfpl fb) -> do
          fo <- interpret f
          funcAlreadyDeclared <- hasBinding env fn
          if (not funcAlreadyDeclared)
            then createMutableBinding env fn (Just configurableBindings)
            else do
            if False
              then return ()
              else return ()
          setMutableBinding env fn (inj fo) strict
      return ()

    step4 :: (Functor m, Monad m) =>
             EnvironmentRecord -> JavaScriptT m Bool
    step4 env = do
      argumentsAlreadyDeclared <- hasBinding env "arguments"
      return argumentsAlreadyDeclared

    step5 :: (Functor m, Monad m) =>
             Bool -> LexicalEnvironment -> DeclarativeEnvironmentRecord ->
             Object -> List String -> List Value -> JavaScriptT m ()
    step5 strict lex env func names args@(List as) = do
      argsObj <- createArgumentsObject
                 func names args lex strict
      if strict
        then do
        createImmutableBindingDeclarative env "arguments"
        initializeImmutableBindingDeclarative env "arguments" (inj argsObj)
        return ()
        else do
        createMutableBindingDeclarative env "arguments" Nothing
        setMutableBindingDeclarative env "arguments" (inj argsObj) False

    step6 :: (Functor m, Monad m) =>
             Bool -> Bool -> EnvironmentRecord -> SourceElements ->
             JavaScriptT m ()
    step6 strict configurableBindings env ses = do
      forM (extractVarDeclIdents ses) $ \(Ident (IdentName dn)) -> do
        varAlreadyDeclared <- hasBinding env dn
        when (not varAlreadyDeclared) $ do
          createMutableBinding env dn (Just configurableBindings)
          setMutableBinding env dn (inj Undefined) strict
      return ()

    extractFuncDecls :: SourceElements -> [FuncDecl]
    extractFuncDecls (SourceElements (SourceElementFuncDecl fd)) = [fd]
    extractFuncDecls (SourceElements _) = []
    extractFuncDecls (SourceElementsCons ses (SourceElementFuncDecl fd)) =
      fd:(extractFuncDecls ses)
    extractFuncDecls (SourceElementsCons ses _) =
      extractFuncDecls ses

    extractVarDeclIdents :: SourceElements -> [Ident]
    extractVarDeclIdents (SourceElementsCons ses se) =
      extractVarDeclIdentsSE se ++ extractVarDeclIdents ses
    extractVarDeclIdents (SourceElements se) =
      extractVarDeclIdentsSE se
    extractVarDeclIdentsSE (SourceElementStmt s) =
      extractVarDeclIdentsS s
    extractVarDeclIdentsSE _ = []
    extractVarDeclIdentsS (StmtVar vs) =
      extractVarDeclIdentsVS vs
    extractVarDeclIdentsS _ = []
    extractVarDeclIdentsVS (VarStmt vdl) =
      extractVarDeclIdentsVDL vdl
    extractVarDeclIdentsVDL (VarDeclList vd) =
      extractVarDeclIdentsVD vd
    extractVarDeclIdentsVDL (VarDeclListCons vdl vd) =
      extractVarDeclIdentsVD vd ++ extractVarDeclIdentsVDL vdl
    extractVarDeclIdentsVD (VarDecl i _) = [i]


type UInt16 = Word16
type UInt32 = Word32

data Context
  = Context
    { contextLexicalEnvironment  :: LexicalEnvironment
    , contextVariableEnvironment :: LexicalEnvironment
    , contextThisBinding         :: Value
    , contextLabels              :: [Ident] }
  deriving (Show)

lexicalEnvironment :: Lens' Context LexicalEnvironment
lexicalEnvironment =
  Lens.lens
  contextLexicalEnvironment
  (\c le -> c { contextLexicalEnvironment = le })

variableEnvironment :: Lens' Context LexicalEnvironment
variableEnvironment =
  Lens.lens
  contextVariableEnvironment
  (\c ve -> c { contextVariableEnvironment = ve })

thisBinding :: Lens' Context Value
thisBinding =
  Lens.lens
  contextThisBinding
  (\c t -> c { contextThisBinding = t })

labels :: Lens' Context [Ident]
labels = Lens.lens contextLabels (\c ls -> c { contextLabels = ls })

inCurrentLabelSet :: Maybe Ident -> JavaScriptM Bool
inCurrentLabelSet mi = do
  case mi of
   Just i -> do
     ls <- Lens.use $ contextStack . currentContext . labels
     return (i `elem` ls)
   _ -> return True

data ContextStack
  = ContextStack
    { contextStackCurrent :: Context
    , contextStackStack   :: [Context] }
  deriving (Show)

currentContext :: Lens' ContextStack Context
currentContext =
  Lens.lens
  contextStackCurrent
  (\cs c -> cs { contextStackCurrent = c })

type EnvironmentRecordHeap
  = Map EnvironmentRecord EnvironmentRecordInternal

type DeclarativeEnvironmentRecordHeap
  = Map DeclarativeEnvironmentRecord DeclarativeEnvironmentRecordInternal

type LexicalEnvironmentHeap
  = Map LexicalEnvironment LexicalEnvironmentInternal

type ObjectHeap m = Map Object (ObjectInternal m)

data JavaScriptState m
  = JavaScriptState
    { javaScriptStateContextStack                     :: ContextStack
    , javaScriptStateNextInternalId                   :: InternalId
    , javaScriptStateEnvironmentRecordHeap            :: EnvironmentRecordHeap
    , javaScriptStateDeclarativeEnvironmentRecordHeap :: DeclarativeEnvironmentRecordHeap
    , javaScriptStateLexicalEnvironmentHeap           :: LexicalEnvironmentHeap
    , javaScriptStateObjectHeap                       :: ObjectHeap m
    , javaScriptStateGlobalLexicalEnvironment         :: LexicalEnvironment
    , javaScriptStateGlobalObject                     :: Object
    , javaScriptStateArrayPrototypeObject             :: Object
    , javaScriptStateBooleanPrototypeObject           :: Object
    , javaScriptStateDatePrototypeObject              :: Object
    , javaScriptStateErrorPrototypeObject             :: Object
    , javaScriptStateEvalErrorPrototypeObject         :: Object
    , javaScriptStateRangeErrorPrototypeObject        :: Object
    , javaScriptStateReferenceErrorPrototypeObject    :: Object
    , javaScriptStateSyntaxErrorPrototypeObject       :: Object
    , javaScriptStateTypeErrorPrototypeObject         :: Object
    , javaScriptStateURIErrorPrototypeObject          :: Object
    , javaScriptStateFunctionPrototypeObject          :: Object
    , javaScriptStateNumberPrototypeObject            :: Object
    , javaScriptStateObjectPrototypeObject            :: Object
    , javaScriptStateRegExpPrototypeObject            :: Object
    , javaScriptStateStringPrototypeObject            :: Object
    , javaScriptStateThrowTypeErrorObject             :: Object }

initialState :: (Functor m, Monad m) => JavaScriptState m
initialState =
  let ctx = Context {
        contextLexicalEnvironment  = error "Unitialised lexical environment",
        contextVariableEnvironment = error "Unitialised variable environment",
        contextThisBinding         = error "Unitialised this binding",
        contextLabels              = [] }

      ctxs = ContextStack {
        contextStackCurrent = ctx,
        contextStackStack   = [] }

      environmentRecordHeap =
        Map.fromList
        [ (globalEnvironmentRecord, globalEnvironmentRecordInternal) ]

      declarativeEnvironmentRecordHeap =
        Map.empty

      lexicalEnvironmentHeap =
        Map.fromList
        [ (globalLexicalEnvironment, globalLexicalEnvironmentInternal) ]

      objectHeap =
        Map.fromList
        [ (globalObject, globalObjectInternal)
        , (arrayPrototypeObject, arrayPrototypeObjectInternal)
        , (booleanPrototypeObject, booleanPrototypeObjectInternal)
        , (datePrototypeObject, datePrototypeObjectInternal)
        , (errorPrototypeObject, errorPrototypeObjectInternal)
        , (errorPrototypeToString, errorPrototypeToStringInternal)
        , (evalErrorPrototypeObject, evalErrorPrototypeObjectInternal)
        , (rangeErrorPrototypeObject, rangeErrorPrototypeObjectInternal)
        , (referenceErrorPrototypeObject, referenceErrorPrototypeObjectInternal)
        , (syntaxErrorPrototypeObject, syntaxErrorPrototypeObjectInternal)
        , (typeErrorPrototypeObject, typeErrorPrototypeObjectInternal)
        , (uriErrorPrototypeObject, uriErrorPrototypeObjectInternal)
        , (functionPrototypeObject, functionPrototypeObjectInternal)
        , (numberPrototypeObject, numberPrototypeObjectInternal)
        , (objectPrototypeObject, objectPrototypeObjectInternal)
        , (regExpPrototypeObject, regExpPrototypeObjectInternal)
        , (stringPrototypeObject, stringPrototypeObjectInternal)
        , (throwTypeErrorObject, throwTypeErrorObjectInternal)
        , (objectConstructor, objectConstructorInternal)
        , (functionConstructor, functionConstructorInternal)
        , (arrayConstructor, arrayConstructorInternal)
        , (stringConstructor, stringConstructorInternal)
        , (booleanConstructor, booleanConstructorInternal)
        , (numberConstructor, numberConstructorInternal)
        , (dateConstructor, dateConstructorInternal)
        , (regExpConstructor, regExpConstructorInternal)
        , (errorConstructor, errorConstructorInternal)
        , (evalErrorConstructor, evalErrorConstructorInternal)
        , (rangeErrorConstructor, rangeErrorConstructorInternal)
        , (referenceErrorConstructor, referenceErrorConstructorInternal)
        , (syntaxErrorConstructor, syntaxErrorConstructorInternal)
        , (typeErrorConstructor, typeErrorConstructorInternal)
        , (uriErrorConstructor, uriErrorConstructorInternal)
        , (mathObject, mathObjectInternal)
        , (jsonObject, jsonObjectInternal) ]

      globalLexicalEnvironmentInternal =
        LexicalEnvironmentInternal globalEnvironmentRecord Nothing
      globalLexicalEnvironment = LexicalEnvironment 0

      globalEnvironmentRecordInternal =
        EnvironmentRecordInternalObject
        (ObjectEnvironmentRecord globalObject True)
      globalEnvironmentRecord = EnvironmentRecord 1

      globalObject = Object 2
      globalObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      globalObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("NaN", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj nan,
                 dataDescriptorWritable       = False,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = False })
           , ("Infinity", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj posInf,
                 dataDescriptorWritable       = False,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = False })
           , ("undefined", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj Undefined,
                 dataDescriptorWritable       = False,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = False })
           , ("eval", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalEval,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("parseInt", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalParseInt,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("parseFloat", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalParseFloat,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("isNaN", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalIsNaN,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("isFinite", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalIsFinite,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("decodeURI", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalDecodeURI,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("decodeURIComponent", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalDecodeURIComponent,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("encodeURI", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalEncodeURI,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("encodeURIComponent", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj globalEncodeURIComponent,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Object", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj objectConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Function", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj functionConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Array", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj arrayConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("String", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj stringConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Boolean", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj booleanConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Number", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj numberConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Date", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj dateConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("RegExp", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj regExpConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Error", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj errorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("EvalError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj evalErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("RangeError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj rangeErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("ReferenceError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj referenceErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("SyntaxError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj syntaxErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("TypeError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj typeErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("URIError", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj uriErrorConstructor,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("Math", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj mathObject,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True })
           , ("JSON", PropertyData $ DataDescriptor {
                 dataDescriptorValue          = inj jsonObject,
                 dataDescriptorWritable       = True,
                 dataDescriptorEnumerable     = False,
                 dataDescriptorConfigurable   = True }) ],
        objectInternalPrototype         = const $ return JSNull,
        objectInternalClass             = const $ return "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      globalEval = error "globalEval" :: Object
      globalParseInt = error "globalParseInt" :: Object
      globalParseFloat = error "globalParseFloat" :: Object
      globalIsNaN = error "globalIsNaN" :: Object
      globalIsFinite = error "globalIsFinite" :: Object
      globalDecodeURI = error "globalDecodeURI" :: Object
      globalDecodeURIComponent = error "globalDecodeURIComponent" :: Object
      globalEncodeURI = error "globalEncodeURI" :: Object
      globalEncodeURIComponent = error "globalEncodeURIComponent" :: Object

      arrayPrototypeObject = Object 3
      arrayPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ def {
                 dataDescriptorValue = inj $ Number 0 })
           , ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLocaleString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeToLocaleString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("concat", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeConcat,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("join", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeJoin,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("pop", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypePop,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("push", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypePush,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("reverse", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeReverse,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("shift", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeShift,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("slice", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeSlice,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("sort", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeSort,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("splice", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeSplice,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("unshift", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeUnshift,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("indexOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeIndexOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("lastIndexOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeLastIndexOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("every", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeEvery,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("some", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeSome,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("forEach", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeForEach,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("map", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeMap,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("filter", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeFilter,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("reduce", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeReduce,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("reduceRight", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj arrayPrototypeReduceRight,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Array",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = arrayDefineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      arrayPrototypeToString = error "arrayPrototypeToString" :: Object
      arrayPrototypeToLocaleString = error "arrayPrototypeToLocaleString" :: Object
      arrayPrototypeConcat = error "arrayPrototypeConcat" :: Object
      arrayPrototypeJoin = error "arrayPrototypeJoin" :: Object
      arrayPrototypePop = error "arrayPrototypePop" :: Object
      arrayPrototypePush = error "arrayPrototypePush" :: Object
      arrayPrototypeReverse = error "arrayPrototypeReverse" :: Object
      arrayPrototypeShift = error "arrayPrototypeShift" :: Object
      arrayPrototypeSlice = error "arrayPrototypeSlice" :: Object
      arrayPrototypeSort = error "arrayPrototypeSort" :: Object
      arrayPrototypeSplice = error "arrayPrototypeSplice" :: Object
      arrayPrototypeUnshift = error "arrayPrototypeUnshift" :: Object
      arrayPrototypeIndexOf = error "arrayPrototypeUndexOf" :: Object
      arrayPrototypeLastIndexOf = error "arrayPrototypeLastIndexOf" :: Object
      arrayPrototypeEvery = error "arrayPrototypeEvery" :: Object
      arrayPrototypeSome = error "arrayPrototypeSome" :: Object
      arrayPrototypeForEach = error "arrayPrototypeForEach" :: Object
      arrayPrototypeMap = error "arrayPrototypeMap" :: Object
      arrayPrototypeFilter = error "arrayPrototypeFilter" :: Object
      arrayPrototypeReduce = error "arrayPrototypeReduce" :: Object
      arrayPrototypeReduceRight = error "arrayPrototypeReduceRight" :: Object

      booleanPrototypeObject = Object 4
      booleanPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj booleanConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj booleanPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("valueOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj booleanPrototypeValueOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Boolean",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just (const $ return (inj False)),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      booleanPrototypeToString = error "booleanPrototypeToString" :: Object

      booleanPrototypeValueOf = error "booleanPrototypeValueOf" :: Object

      datePrototypeObject = Object 5
      datePrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Date",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just (const $ return (inj nan)),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      errorPrototypeObject = Object 6
      errorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj errorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "Error",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj errorPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      errorPrototypeToString = Object 7
      errorPrototypeToStringInternal :: (Functor m, Monad m) => ObjectInternal m
      errorPrototypeToStringInternal =
        propertyFunctionObject errorPrototypeToStringCallImpl 0

      evalErrorPrototypeObject = Object 8
      evalErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      evalErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj evalErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "EvalError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      rangeErrorPrototypeObject = Object 9
      rangeErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      rangeErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj rangeErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "RangeError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      referenceErrorPrototypeObject = Object 10
      referenceErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      referenceErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj referenceErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "ReferenceError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      syntaxErrorPrototypeObject = Object 11
      syntaxErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      syntaxErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj syntaxErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "SyntaxError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      typeErrorPrototypeObject = Object 12
      typeErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      typeErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj typeErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "TypeError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      uriErrorPrototypeObject = Object 13
      uriErrorPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      uriErrorPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj uriErrorConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("name", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "URIError",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("message", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj "",
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist errorPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      functionPrototypeObject = Object 14
      functionPrototypeObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      functionPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ def {
                 dataDescriptorValue = inj $ Number 0 })
           , ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj functionConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj functionPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("apply", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj functionPrototypeApply,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("call", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj functionPrototypeCall,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("bind", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj functionPrototypeBind,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Just functionPrototypeCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      functionPrototypeToString = error "functionPrototypeToString" :: Object
      functionPrototypeApply = error "functionPrototypeApply" :: Object
      functionPrototypeCall = error "functionPrototypeCall" :: Object
      functionPrototypeBind = error "functionPrototypeBind" :: Object

      numberPrototypeObject = Object 15
      numberPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLocaleString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeToLocaleString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("valueOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeValueOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toFixed", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeToFixed,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toExponential", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeToExponential,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toPrecision", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj numberPrototypeToPrecision,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Number",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just (const $ return (inj (Number 0))),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      numberPrototypeToString = error "numberPrototypeToString" :: Object
      numberPrototypeToLocaleString = error "numberPrototypeToLocaleString" :: Object
      numberPrototypeValueOf = error "numberPrototypeValueOf" :: Object
      numberPrototypeToFixed = error "numberPrototypeToFixed" :: Object
      numberPrototypeToExponential = error "numberPrototypeToExponential" :: Object
      numberPrototypeToPrecision = error "numberPrototypeToPrecision" :: Object

      objectPrototypeObject = Object 16
      objectPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLocaleString", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeToLocaleString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("valueOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeValueOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("hasOwnProperty", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeHasOwnProperty,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("isPrototypeOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeIsPrototypeOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("propertyIsEnumerable", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectPrototypeIsEnumerable,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return JSNull,
        objectInternalClass             = const $ return "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just (const $ return (inj (Number 0))),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      objectPrototypeToString = error "objectPrototypeToString" :: Object
      objectPrototypeToLocaleString = error "objectPrototypeToLocaleString" :: Object
      objectPrototypeValueOf = error "objectPrototypeValueOf" :: Object
      objectPrototypeHasOwnProperty = error "objectPrototypeHasOwnProperty" :: Object
      objectPrototypeIsPrototypeOf = error "objectPrototypeIsPrototypeOf" :: Object
      objectPrototypeIsEnumerable = error "objectPrototypeIsEnumerable" :: Object

      regExpPrototypeObject = Object 17
      regExpPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "RegExp",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = stringGetOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Just regExpMatchImpl,
        objectInternalParameterMap      = Nothing }

      stringPrototypeObject = Object 18
      stringPrototypeObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("constructor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj stringConstructor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toString", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeToString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("valueOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeValueOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("charAt", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeCharAt,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("charCodeAt", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeCharCodeAt,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("concat", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeConcat,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("indexOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeIndexOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("lastIndexOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeLastIndexOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("localeCompare", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeLocaleCompare,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("match", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeMatch,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("replace", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeReplace,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("search", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeSearch,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("slice", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeSlice,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("split", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeSplit,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("substring", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeSubString,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLowerCase", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeToLowerCase,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLocaleLowerCase", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeToLocaleLowerCase,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toUpperCase", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeToUpperCase,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("toLocaleUpperCase", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeToLocaleUpperCase,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("trim", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeTrim,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "String",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = stringGetOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just $ stringPrimitiveValueImpl (inj ""),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      stringPrototypeToString = error "stringPrototypeToString" :: Object
      stringPrototypeValueOf = error "stringPrototypeValueOf" :: Object
      stringPrototypeCharAt = error "stringPrototypeCharAt" :: Object
      stringPrototypeCharCodeAt = error "stringPrototypeCharCodeAt" :: Object
      stringPrototypeConcat = error "stringPrototypeConcat" :: Object
      stringPrototypeIndexOf = error "stringPrototypeIndexOf" :: Object
      stringPrototypeLastIndexOf = error "stringPrototypeLastIndexOf" :: Object
      stringPrototypeLocaleCompare = error "stringPrototypeLocaleCompare" :: Object
      stringPrototypeMatch = error "stringPrototypeMatch" :: Object
      stringPrototypeReplace = error "stringPrototypeReplace" :: Object
      stringPrototypeSearch = error "stringPrototypeSearch" :: Object
      stringPrototypeSlice = error "stringPrototypeSlice" :: Object
      stringPrototypeSplit = error "stringPrototypeSplit" :: Object
      stringPrototypeSubString = error "stringPrototypeSubString" :: Object
      stringPrototypeToLowerCase = error "stringPrototypeToLowerCase" :: Object
      stringPrototypeToLocaleLowerCase = error "stringPrototypeToLocaleLowerCase" :: Object
      stringPrototypeToUpperCase = error "stringPrototypeToUpperCase" :: Object
      stringPrototypeToLocaleUpperCase = error "stringPrototypeToLocaleUpperCase" :: Object
      stringPrototypeTrim = error "stringPrototypeTrim" :: Object

      throwTypeErrorObject = Object 19
      throwTypeErrorObjectInternal = error "throwTypeErrorObject"

      objectConstructor = Object 20
      objectConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ def {
                 dataDescriptorValue = inj (Number 1) })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj objectPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("getPrototypeOf", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorGetPrototypeOf,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("getOwnPropertyDescriptor", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorGetOwnPropertyDescriptor,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("getOwnPropertyNames", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorGetOwnPropertyNames,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("create", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorCreate,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("defineProperty", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorDefineProperty,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("defineProperties", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorDefineProperties,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("seal", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorSeal,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("freeze", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorFreeze,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("preventExtensions", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorPreventExtensions,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("isSealed", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorIsSealed,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("isFrozen", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorIsFrozen,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("isExtensible", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorIsExtensible,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("keys", PropertyData $ DataDescriptor {
                 dataDescriptorValue =
                    inj objectConstructorKeys,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $
                                          return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just (const $ return (inj (Number 0))),
        objectInternalConstruct         = Just objectConstructorConstructImpl,
        objectInternalCall              = Just objectConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      objectConstructorGetPrototypeOf = error "objectConstructorGetPrototypeOf" :: Object
      objectConstructorGetOwnPropertyDescriptor = error "objectConstructorGetOwnPropertyDescriptor" :: Object
      objectConstructorGetOwnPropertyNames = error "objectConstructorGetOwnPropertyNames" :: Object
      objectConstructorCreate = error "objectConstructorCreate" :: Object
      objectConstructorDefineProperty = error "objectConstructorDefineProperty" :: Object
      objectConstructorDefineProperties = error "objectConstructorDefineProperties" :: Object
      objectConstructorSeal = error "objectConstructorSeal" :: Object
      objectConstructorFreeze = error "objectConstructorFreeze" :: Object
      objectConstructorPreventExtensions = error "objectConstructorPreventExtensions" :: Object
      objectConstructorIsSealed = error "objectConstructorIsSealed" :: Object
      objectConstructorIsFrozen = error "objectConstructorIsFrozen" :: Object
      objectConstructorIsExtensible = error "objectConstructorIsExtensible" :: Object
      objectConstructorKeys = error "objectConstructorKeys" :: Object

      functionConstructor = Object 21
      functionConstructorInternal :: (Functor m, Monad m) => ObjectInternal m
      functionConstructorInternal = ObjectInternal {
        objectInternalProperties =
           Map.fromList
           [ ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ functionPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }),
             ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })],
        objectInternalPrototype         = const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just functionConstructorConstructImpl,
        objectInternalCall              = Just functionConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      arrayConstructor = Object 22
      arrayConstructorInternal :: (Functor m, Monad m) => ObjectInternal m
      arrayConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ arrayPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("isArray", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ arrayConstructorIsArray,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just arrayConstructorConstructImpl,
        objectInternalCall              = Just arrayConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      arrayConstructorIsArray = error "arrayConstructorIsArray" :: Object

      stringConstructor = Object 23
      stringConstructorInternal :: (Functor m, Monad m) => ObjectInternal m
      stringConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("fromCharCode", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ stringConstructorFromCharCode,
                 dataDescriptorWritable = True,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "String",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just stringConstructorConstructImpl,
        objectInternalCall              = Just stringConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      stringConstructorFromCharCode = error "stringConstructorFromCharCode" :: Object

      booleanConstructor = Object 24
      booleanConstructorInternal :: (Functor m, Monad m) => ObjectInternal m
      booleanConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ booleanPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Boolean",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just booleanConstructorConstructImpl,
        objectInternalCall              = Just booleanConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      numberConstructor = Object 25
      numberConstructorInternal :: (Functor m, Monad m) => ObjectInternal m
      numberConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ numberPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("MAX_VALUE", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("MIN_VALUE", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("NaN", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("NEGATIVE_INFINITY", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("POSITIVE_INFINITY", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Number",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just numberConstructorConstructImpl,
        objectInternalCall              = Just numberConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      dateConstructor = Object 26
      dateConstructorInternal = error "dateConstructorInternal"

      regExpConstructor = Object 27
      regExpConstructorInternal = error "regExpConstructorInternal"

      errorConstructor = Object 28
      errorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj errorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      evalErrorConstructor = Object 29
      evalErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj evalErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "EvalError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      rangeErrorConstructor = Object 30
      rangeErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj rangeErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "RangeError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      referenceErrorConstructor = Object 31
      referenceErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj referenceErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "ReferenceError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      syntaxErrorConstructor = Object 32
      syntaxErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj syntaxErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "SyntaxError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      typeErrorConstructor = Object 33
      typeErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj typeErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "TypeError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      uriErrorConstructor = Object 34
      uriErrorConstructorInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj $ Number 1,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("prototype", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj uriErrorPrototypeObject,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "URIError",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just errorConstructorConstructImpl,
        objectInternalCall              = Just errorConstructorCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      mathObject = Object 35
      mathObjectInternal :: (Functor m, Monad m) => ObjectInternal m
      mathObjectInternal = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("E", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("LN10", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("LN2", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("LOG2E", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("LOG10E", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("PI", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("SQRT1_2", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("SQRT2", PropertyData $ DataDescriptor {
                 dataDescriptorValue = undefined,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("abs", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathAbs,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("acos", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathAcos,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("asin", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathAsin,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("atan", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathAtan,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("atan2", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathAtan2,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("ceil", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathCeil,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("cos", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathCos,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("exp", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathExp,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("floor", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathFloor,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("log", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathLog,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("max", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathMax,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("min", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathMin,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("pow", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathPow,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("random", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathRandom,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("round", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathRound,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("sin", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathSin,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("sqrt", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathSqrt,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False })
           , ("tan", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj mathTan,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         = const $ return (JSExist objectPrototypeObject),
        objectInternalClass             = const $ return "Math",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

      mathAbs = error "mathAbs" :: Object
      mathAcos = error "mathAcos" :: Object
      mathAsin = error "mathAsin" :: Object
      mathAtan = error "mathAtan" :: Object
      mathAtan2 = error "mathAtan2" :: Object
      mathCeil = error "mathCeil" :: Object
      mathCos = error "mathCos" :: Object
      mathExp = error "mathExp" :: Object
      mathFloor = error "mathFloor" :: Object
      mathLog = error "mathLog" :: Object
      mathMax = error "mathMax" :: Object
      mathMin = error "mathMin" :: Object
      mathPow = error "mathPow" :: Object
      mathRandom = error "mathRandom" :: Object
      mathRound = error "mathRound" :: Object
      mathSin = error "mathSin" :: Object
      mathSqrt = error "mathSqrt" :: Object
      mathTan = error "mathTan" :: Object

      jsonObject = Object 36
      jsonObjectInternal = error "jsonObjectInternal"

      nextInternalId = 37

      propertyFunctionObject :: (Functor m, Monad m) =>
                                InternalCallType m -> Number -> ObjectInternal m
      propertyFunctionObject c l = ObjectInternal {
        objectInternalProperties        =
           Map.fromList
           [ ("length", PropertyData $ DataDescriptor {
                 dataDescriptorValue = inj l,
                 dataDescriptorWritable = False,
                 dataDescriptorEnumerable = False,
                 dataDescriptorConfigurable = False }) ],
        objectInternalPrototype         =
          const $ return (JSExist functionPrototypeObject),
        objectInternalClass             = const $ return "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = functionGetImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Just c,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  in
   JavaScriptState {
     javaScriptStateContextStack                     =
        ctxs,
     javaScriptStateNextInternalId                   =
       nextInternalId,
     javaScriptStateEnvironmentRecordHeap            =
       environmentRecordHeap,
     javaScriptStateDeclarativeEnvironmentRecordHeap =
       declarativeEnvironmentRecordHeap,
     javaScriptStateLexicalEnvironmentHeap           =
       lexicalEnvironmentHeap,
     javaScriptStateObjectHeap                       =
       objectHeap,
     javaScriptStateGlobalLexicalEnvironment         =
       globalLexicalEnvironment,
     javaScriptStateGlobalObject                     =
       globalObject,
     javaScriptStateArrayPrototypeObject             =
       arrayPrototypeObject,
     javaScriptStateBooleanPrototypeObject           =
       booleanPrototypeObject,
     javaScriptStateDatePrototypeObject              =
       datePrototypeObject,
     javaScriptStateErrorPrototypeObject             =
       errorPrototypeObject,
     javaScriptStateEvalErrorPrototypeObject         =
       evalErrorPrototypeObject,
     javaScriptStateRangeErrorPrototypeObject        =
       rangeErrorPrototypeObject,
     javaScriptStateReferenceErrorPrototypeObject    =
       referenceErrorPrototypeObject,
     javaScriptStateSyntaxErrorPrototypeObject       =
       syntaxErrorPrototypeObject,
     javaScriptStateTypeErrorPrototypeObject         =
       typeErrorPrototypeObject,
     javaScriptStateURIErrorPrototypeObject          =
       uriErrorPrototypeObject,
     javaScriptStateFunctionPrototypeObject          =
       functionPrototypeObject,
     javaScriptStateNumberPrototypeObject            =
       numberPrototypeObject,
     javaScriptStateObjectPrototypeObject            =
       objectPrototypeObject,
     javaScriptStateRegExpPrototypeObject            =
       regExpPrototypeObject,
     javaScriptStateStringPrototypeObject            =
       stringPrototypeObject,
     javaScriptStateThrowTypeErrorObject             =
       throwTypeErrorObject }

pushContext :: Context -> JavaScriptM ()
pushContext ctx = do
  contextStack %= push
  where
    push :: ContextStack -> ContextStack
    push (ContextStack c cs) = ContextStack ctx (c:cs)

popContext :: JavaScriptM ()
popContext = do
  contextStack %= pop
  where
    pop :: ContextStack -> ContextStack
    pop (ContextStack _ []) = error "Internal error: no context to pop"
    pop (ContextStack _ (c:cs)) = ContextStack c cs

contextStack :: Lens' (JavaScriptState m) ContextStack
contextStack = Lens.lens
               javaScriptStateContextStack
               (\jss cs -> jss { javaScriptStateContextStack = cs })

nextInternalId :: Lens' (JavaScriptState m) InternalId
nextInternalId = Lens.lens
             javaScriptStateNextInternalId
             (\jss noi -> jss { javaScriptStateNextInternalId = noi })

environmentRecordHeap :: Lens' (JavaScriptState m) EnvironmentRecordHeap
environmentRecordHeap =
  Lens.lens
  javaScriptStateEnvironmentRecordHeap
  (\jss erh -> jss { javaScriptStateEnvironmentRecordHeap = erh })

declarativeEnvironmentRecordHeap :: Lens' (JavaScriptState m) DeclarativeEnvironmentRecordHeap
declarativeEnvironmentRecordHeap =
  Lens.lens
  javaScriptStateDeclarativeEnvironmentRecordHeap
  (\jss derh -> jss { javaScriptStateDeclarativeEnvironmentRecordHeap = derh })

lexicalEnvironmentHeap :: Lens' (JavaScriptState m) LexicalEnvironmentHeap
lexicalEnvironmentHeap =
  Lens.lens
  javaScriptStateLexicalEnvironmentHeap
  (\jss lh -> jss { javaScriptStateLexicalEnvironmentHeap = lh })

lexicalEnvironmentInternal :: LexicalEnvironment -> Lens' (JavaScriptState m) LexicalEnvironmentInternal
lexicalEnvironmentInternal i =
  Lens.lens
  (\JavaScriptState {..} ->
    case Map.lookup i javaScriptStateLexicalEnvironmentHeap of
     Nothing -> error "Internal error: can't find lexicalEnvironment environment"
     Just o -> o)
  (\jss@(JavaScriptState {..}) oi ->
    jss { javaScriptStateLexicalEnvironmentHeap = Map.insert i oi javaScriptStateLexicalEnvironmentHeap })

mLexicalEnvironmentInternal :: LexicalEnvironment -> Lens' (JavaScriptState m) (Maybe LexicalEnvironmentInternal)
mLexicalEnvironmentInternal i = lexicalEnvironmentHeap . Lens.at i

objectHeap :: Lens' (JavaScriptState m) (ObjectHeap m)
objectHeap = Lens.lens
             javaScriptStateObjectHeap
             (\jss oh -> jss { javaScriptStateObjectHeap = oh })

internalObject :: Object -> Lens' (JavaScriptState m) (ObjectInternal m)
internalObject i =
  Lens.lens
  (\JavaScriptState {..} ->
    case Map.lookup i javaScriptStateObjectHeap of
     Nothing -> error "Internal error: can't find object"
     Just o -> o)
  (\jss@(JavaScriptState {..}) oi ->
    jss { javaScriptStateObjectHeap = Map.insert i oi javaScriptStateObjectHeap })

mInternalObject :: Object -> Lens' (JavaScriptState m) (Maybe (ObjectInternal m))
mInternalObject i = objectHeap . Lens.at i

globalLexicalEnvironment :: Lens' (JavaScriptState m) LexicalEnvironment
globalLexicalEnvironment =
  Lens.lens
  javaScriptStateGlobalLexicalEnvironment
  (\jss lid -> jss { javaScriptStateGlobalLexicalEnvironment = lid })

globalObject :: Lens' (JavaScriptState m) Object
globalObject =
  Lens.lens
  javaScriptStateGlobalObject
  (\jss oid -> jss { javaScriptStateGlobalObject = oid })

arrayPrototypeObject :: Lens' (JavaScriptState m) Object
arrayPrototypeObject =
  Lens.lens
  javaScriptStateArrayPrototypeObject
  (\jss oid -> jss { javaScriptStateArrayPrototypeObject = oid })

booleanPrototypeObject :: Lens' (JavaScriptState m) Object
booleanPrototypeObject =
  Lens.lens
  javaScriptStateBooleanPrototypeObject
  (\jss oid -> jss { javaScriptStateBooleanPrototypeObject = oid })

datePrototypeObject :: Lens' (JavaScriptState m) Object
datePrototypeObject =
  Lens.lens
  javaScriptStateDatePrototypeObject
  (\jss oid -> jss { javaScriptStateDatePrototypeObject = oid })

errorPrototypeObject :: Lens' (JavaScriptState m) Object
errorPrototypeObject =
  Lens.lens
  javaScriptStateErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateErrorPrototypeObject = oid })

evalErrorPrototypeObject :: Lens' (JavaScriptState m) Object
evalErrorPrototypeObject =
  Lens.lens
  javaScriptStateEvalErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateEvalErrorPrototypeObject = oid })

rangeErrorPrototypeObject :: Lens' (JavaScriptState m) Object
rangeErrorPrototypeObject =
  Lens.lens
  javaScriptStateRangeErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateRangeErrorPrototypeObject = oid })

referenceErrorPrototypeObject :: Lens' (JavaScriptState m) Object
referenceErrorPrototypeObject =
  Lens.lens
  javaScriptStateReferenceErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateReferenceErrorPrototypeObject = oid })

syntaxErrorPrototypeObject :: Lens' (JavaScriptState m) Object
syntaxErrorPrototypeObject =
  Lens.lens
  javaScriptStateSyntaxErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateSyntaxErrorPrototypeObject = oid })

typeErrorPrototypeObject :: Lens' (JavaScriptState m) Object
typeErrorPrototypeObject =
  Lens.lens
  javaScriptStateTypeErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateTypeErrorPrototypeObject = oid })

uriErrorPrototypeObject :: Lens' (JavaScriptState m) Object
uriErrorPrototypeObject =
  Lens.lens
  javaScriptStateURIErrorPrototypeObject
  (\jss oid -> jss { javaScriptStateURIErrorPrototypeObject = oid })

functionPrototypeObject :: Lens' (JavaScriptState m) Object
functionPrototypeObject =
  Lens.lens
  javaScriptStateFunctionPrototypeObject
  (\jss oid -> jss { javaScriptStateFunctionPrototypeObject = oid })

numberPrototypeObject :: Lens' (JavaScriptState m) Object
numberPrototypeObject =
  Lens.lens
  javaScriptStateNumberPrototypeObject
  (\jss oid -> jss { javaScriptStateNumberPrototypeObject = oid })

objectPrototypeObject :: Lens' (JavaScriptState m) Object
objectPrototypeObject =
  Lens.lens
  javaScriptStateObjectPrototypeObject
  (\jss oid -> jss { javaScriptStateObjectPrototypeObject = oid })

regexpPrototypeObject :: Lens' (JavaScriptState m) Object
regexpPrototypeObject =
  Lens.lens
  javaScriptStateRegExpPrototypeObject
  (\jss oid -> jss { javaScriptStateRegExpPrototypeObject = oid })

stringPrototypeObject :: Lens' (JavaScriptState m) Object
stringPrototypeObject =
  Lens.lens
  javaScriptStateStringPrototypeObject
  (\jss oid -> jss { javaScriptStateStringPrototypeObject = oid })

throwTypeErrorObject :: Lens' (JavaScriptState m) Object
throwTypeErrorObject =
  Lens.lens
  javaScriptStateThrowTypeErrorObject
  (\jss oid -> jss { javaScriptStateThrowTypeErrorObject = oid })

type JavaScriptT m = Except.ExceptT Value (State.StateT (JavaScriptState m) m)
type JavaScriptM a = forall m. (Functor m, Monad m) => JavaScriptT m a

runJavaScriptT :: (Functor m, Monad m) =>
                  JavaScriptState m ->
                  JavaScriptT m a ->
                  m (Either Value a)
runJavaScriptT s a = flip State.evalStateT s $ Except.runExceptT a

jsThrow :: Value -> JavaScriptM a
jsThrow v = Except.throwE v

type JSNullable a = a + Null

pattern JSNull = Right Null

pattern JSExist a = Left a

type JSMaybe a = a + Undefined

pattern JSNothing = Right Undefined

pattern JSJust a = Left a

jsMaybe :: b -> (a -> b) -> JSMaybe a -> b
jsMaybe b f ma =
  case ma of
   JSJust a  -> f a
   JSNothing -> b
   _ -> b

type Primitive = Null + Undefined + Number + String + Bool

pattern PrimitiveNull a      = Left a                          :: Primitive
pattern PrimitiveUndefined a = Right (Left a)                  :: Primitive
pattern PrimitiveNumber a    = Right (Right (Left a))          :: Primitive
pattern PrimitiveString a    = Right (Right (Right (Left a)))  :: Primitive
pattern PrimitiveBool a      = Right (Right (Right (Right a))) :: Primitive

type Value = Object + Primitive

pattern ValueObject a    = Left a                       :: Value
pattern ValuePrimitive a = Right a                      :: Value
pattern ValueNull a      = Right (PrimitiveNull a)      :: Value
pattern ValueUndefined a = Right (PrimitiveUndefined a) :: Value
pattern ValueNumber a    = Right (PrimitiveNumber a)    :: Value
pattern ValueString a    = Right (PrimitiveString a)    :: Value
pattern ValueBool a      = Right (PrimitiveBool a)      :: Value

type CallValue = Reference + Value

pattern CallValueReference a = Left a                   :: CallValue
pattern CallValueValue a     = Right a                  :: CallValue
pattern CallValueObject a    = Right (ValueObject a)    :: CallValue
pattern CallValuePrimitive a = Right (ValuePrimitive a) :: CallValue
pattern CallValueNull a      = Right (ValueNull a)      :: CallValue
pattern CallValueUndefined a = Right (ValueUndefined a) :: CallValue
pattern CallValueNumber a    = Right (ValueNumber a)    :: CallValue
pattern CallValueString a    = Right (ValueString a)    :: CallValue
pattern CallValueBool a      = Right (ValueBool a)      :: CallValue

type Spec a = EnvironmentRecord +
              LexicalEnvironment +
              PropertyIdentifier +
              PropertyDescriptor +
              Completion +
              List a +
              Reference

pattern SpecEnvironmentRecord a  = Left a
pattern SpecLexicalEnvironment a = Right (Left a)
pattern SpecPropertyIdentifier a = Right (Right (Left a))
pattern SpecPropertyDescriptor a = Right (Right (Right (Left a)))
pattern SpecCompletion a         = Right (Right (Right (Right (Left a))))
pattern SpecList a               = Right (Right (Right (Right (Right (Left a)))))
pattern SpecReference a          = Right (Right (Right (Right (Right (Right a)))))

type ECMA a = EnvironmentRecord +
              LexicalEnvironment +
              PropertyIdentifier +
              PropertyDescriptor +
              Completion +
              List a +
              Reference +
              Value

pattern ECMAEnvironmentRecord a  = Left a
pattern ECMALexicalEnvironment a = Right (Left a)
pattern ECMAPropertyIdentifier a = Right (Right (Left a))
pattern ECMAPropertyDescriptor a = Right (Right (Right (Left a)))
pattern ECMACompletion a         = Right (Right (Right (Right (Left a))))
pattern ECMAList a               = Right (Right (Right (Right (Right (Left a)))))
pattern ECMAReference a          = Right (Right (Right (Right (Right (Right (Left a))))))
pattern ECMAValue a              = Right (Right (Right (Right (Right (Right (Right a))))))

data Undefined =
  Undefined
  deriving (Eq, Ord, Show)

data Null
  = Null
  deriving (Eq, Ord, Show)

data Signum
  = SignumPos
  | SignumNeg
  deriving (Eq, Show)

newtype Number
  = Number Double
  deriving (Eq, Floating, Fractional, Num, Ord, Real, RealFloat, RealFrac, Show)

nan :: Number
nan = Number (0 / 0)

posInf :: Number
posInf = Number (1 / 0)

negInf :: Number
negInf = Number ((-1) / 0)

type Base = EnvironmentRecord + Object + Undefined + Number + String + Bool

pattern BaseEnvironmentRecord a = Left a :: Base
pattern BaseObject a = Right (Left a) :: Base
pattern BaseUndefined a = Right (Right (Left a)) :: Base
pattern BaseProperty a = Right (Right (Right a)) :: Base
pattern BaseNumber a = Right (Right (Right (Left a))) :: Base
pattern BaseString a = Right (Right (Right (Right (Left a)))) :: Base
pattern BaseBool a = Right (Right (Right (Right (Right a)))) :: Base

data Reference
  = Reference Base String Bool
  deriving (Eq, Show)

getBase :: Reference -> Base
getBase (Reference base _ _) = base

getReferencedName :: Reference -> String
getReferencedName (Reference _ name _) = name

isStrictReference :: Reference -> Bool
isStrictReference (Reference _ _ strict) = strict

toPrimitiveBase :: Reference ->
                   (EnvironmentRecord + Object + Undefined)
                   +
                   (Number + String + Bool)
toPrimitiveBase (Reference (BaseEnvironmentRecord er) _ _) = Left (inj er)
toPrimitiveBase (Reference (BaseObject o) _ _) = Left (inj o)
toPrimitiveBase (Reference (BaseUndefined u) _ _) = Left (inj u)
toPrimitiveBase (Reference (BaseNumber n) _ _) = Right (inj n)
toPrimitiveBase (Reference (BaseString s) _ _) = Right (inj s)
toPrimitiveBase (Reference (BaseBool b) _ _) = Right (inj b)

isPropertyReference :: Reference -> Bool
isPropertyReference ref =
  case toPropertyReference ref of
   Left _ -> False
   _ -> True

toPropertyReference :: Reference ->
                       (EnvironmentRecord + Undefined)
                       +
                       (Object + Number + String + Bool)
toPropertyReference (Reference (BaseEnvironmentRecord er) _ _) = Left (inj er)
toPropertyReference (Reference (BaseUndefined u) _ _) = Left (inj u)
toPropertyReference (Reference (BaseObject o) _ _) = Right (inj o)
toPropertyReference (Reference (BaseNumber n) _ _) = Right (inj n)
toPropertyReference (Reference (BaseString s) _ _) = Right (inj s)
toPropertyReference (Reference (BaseBool b) _ _) = Right (inj b)

isUnresolvableReference :: Reference -> Bool
isUnresolvableReference ref =
  case toUnresolvableReference ref of
   Left _ -> True
   _ -> False

toUnresolvableReference :: Reference ->
                           Undefined
                           +
                           (EnvironmentRecord + Object + Number + String + Bool)
toUnresolvableReference (Reference (BaseUndefined u) _ _) = Left u
toUnresolvableReference (Reference (BaseEnvironmentRecord er) _ _) = Right (inj er)
toUnresolvableReference (Reference (BaseObject o) _ _) = Right (inj o)
toUnresolvableReference (Reference (BaseProperty p) _ _) = Right (inj p)
toUnresolvableReference (Reference (BaseNumber n) _ _) = Right (inj n)
toUnresolvableReference (Reference (BaseString s) _ _) = Right (inj s)
toUnresolvableReference (Reference (BaseBool b) _ _) = Right (inj b)

newtype List a
  = List [a]
  deriving (Eq, Show)

data CompletionType
  = CompletionTypeNormal
  | CompletionTypeBreak
  | CompletionTypeContinue
  | CompletionTypeReturn
  | CompletionTypeThrow
  deriving (Eq, Show)

data Completion
  = Completion CompletionType (Maybe Value) (Maybe Ident)
  deriving (Eq, Show)

data Type
  = TypeNumber
  | TypeString
  | TypeBoolean
  | TypeUndefined
  | TypeNull
  | TypeObject
  | TypeReference
  | TypeList
  | TypeCompletion
  | TypePropertyDescriptor
  | TypePropertyIdentifier
  | TypeLexicalEnvironment
  | TypeEnvironmentRecord
  deriving (Eq, Show)

typeOf :: forall v a. (SubType v (ECMA a)) => v -> Type
typeOf v =
  case (inj v :: ECMA a) of
   ECMAEnvironmentRecord _ -> TypeEnvironmentRecord
   ECMALexicalEnvironment _ -> TypeLexicalEnvironment
   ECMAPropertyIdentifier _ -> TypePropertyIdentifier
   ECMAPropertyDescriptor _ -> TypePropertyDescriptor
   ECMACompletion _ -> TypeCompletion
   ECMAList _ -> TypeList
   ECMAReference _ -> TypeReference
   ECMAValue (ValueObject _) -> TypeObject
   ECMAValue (ValueNull _) -> TypeNull
   ECMAValue (ValueUndefined _) -> TypeUndefined
   ECMAValue (ValueBool _) -> TypeBoolean
   ECMAValue (ValueString _) -> TypeString
   ECMAValue (ValueNumber _) -> TypeNumber

getValue :: (Functor m, Monad m, SubType v CallValue) =>
            v -> JavaScriptT m Value
getValue sub = do
  case (inj sub :: CallValue) of
   CallValueValue v -> return v
   CallValueReference ref -> do
     let base = getBase ref
     case toUnresolvableReference ref of
       Left _ -> newReferenceErrorObject Nothing >>= jsThrow . inj
       Right resolvableBase -> do
         case resolvableBase of
          Right propertyBase -> do
            case propertyBase of
             Left objectBase -> do
               get objectBase (getReferencedName ref)
             Right primitiveBase -> do
               let p = getReferencedName ref
               o <- toObject (inj primitiveBase)
               mDesc <- getProperty o p
               case mDesc of
                JSNothing -> return $ inj Undefined
                JSJust (PropertyDescriptor {..}) -> do
                  case toDataDescriptor mDesc of
                   JSJust (DataDescriptor {..}) -> do
                     return dataDescriptorValue
                   JSNothing ->
                    case propertyDescriptorGet of
                     Nothing -> return $ inj Undefined
                     Just getter -> do
                       callNative getter (inj primitiveBase) (List [])
          Left environmentRecordBase -> do
            getBindingValue
              environmentRecordBase
              (getReferencedName ref)
              (isStrictReference ref)

putValue :: (SubType v1 CallValue, SubType v2 Value) =>
            v1 -> v2 -> JavaScriptM ()
putValue rv w = do
  case (inj rv :: CallValue) of
   Right _ -> newReferenceErrorObject Nothing >>= jsThrow . inj
   Left ref -> do
     let base = getBase ref
     case toUnresolvableReference ref of
      Left _ -> do
        if isStrictReference ref
          then newReferenceErrorObject Nothing >>= jsThrow . inj
          else do
          global <- Lens.use globalObject
          put global (getReferencedName ref) (inj w) False
      Right resolvableBase -> do
        case resolvableBase of
         Right propertyBase -> do
           case propertyBase of
            Left objectBase -> do
              put objectBase (getReferencedName ref) (inj w) (isStrictReference ref)
            Right primitiveBase -> do
              let p = getReferencedName ref
                  throw = isStrictReference ref
              o <- toObject (inj primitiveBase)
              c <- canPut o p
              if not c
                then do
                if throw
                  then newTypeErrorObject Nothing >>= jsThrow . inj
                  else return ()
                else do
                ownDesc <- getOwnProperty o p
                if isDataDescriptor ownDesc
                  then
                  if throw
                  then newTypeErrorObject Nothing >>= jsThrow . inj
                  else return ()
                  else do
                  desc <- getProperty o p
                  case toAccessorDescriptor desc of
                   JSJust (AccessorDescriptor {..}) -> do
                     let JSJust setter = accessorDescriptorSet
                     call setter (inj primitiveBase) (List [(inj w)])
                     return ()
                   JSNothing -> do
                     if throw
                       then newTypeErrorObject Nothing >>= jsThrow . inj
                       else return ()
         Left environmentRecordBase -> do
           setMutableBinding
             environmentRecordBase
             (getReferencedName ref)
             (inj w)
             (isStrictReference ref)

data Property
  = PropertyData DataDescriptor
  | PropertyAccessor AccessorDescriptor
  deriving (Eq, Show)

data DataDescriptor
  = DataDescriptor
    { dataDescriptorValue        :: Value
    , dataDescriptorWritable     :: Bool
    , dataDescriptorEnumerable   :: Bool
    , dataDescriptorConfigurable :: Bool }
  deriving (Eq, Show)

instance Default DataDescriptor where
  def = DataDescriptor {
    dataDescriptorValue        = inj Undefined,
    dataDescriptorWritable     = False,
    dataDescriptorEnumerable   = False,
    dataDescriptorConfigurable = False }

data AccessorDescriptor
  = AccessorDescriptor
    { accessorDescriptorGet          :: JSMaybe Object
    , accessorDescriptorSet          :: JSMaybe Object
    , accessorDescriptorEnumerable   :: Bool
    , accessorDescriptorConfigurable :: Bool }
  deriving (Eq, Show)

instance Default AccessorDescriptor where
  def = AccessorDescriptor {
    accessorDescriptorGet          = JSNothing,
    accessorDescriptorSet          = JSNothing,
    accessorDescriptorEnumerable   = False,
    accessorDescriptorConfigurable = False }

data PropertyIdentifier
  = PropertyIdentifier String PropertyDescriptor

data PropertyDescriptor
  = PropertyDescriptor
    { propertyDescriptorValue        :: Maybe Value
    , propertyDescriptorGet          :: Maybe Object
    , propertyDescriptorSet          :: Maybe Object
    , propertyDescriptorWritable     :: Maybe Bool
    , propertyDescriptorEnumerable   :: Maybe Bool
    , propertyDescriptorConfigurable :: Maybe Bool }
  deriving (Eq, Show)

instance Default PropertyDescriptor where
  def = PropertyDescriptor {
    propertyDescriptorValue        = Nothing,
    propertyDescriptorGet          = Nothing,
    propertyDescriptorSet          = Nothing,
    propertyDescriptorWritable     = Nothing,
    propertyDescriptorEnumerable   = Nothing,
    propertyDescriptorConfigurable = Nothing }

isAccessorDescriptor :: JSMaybe PropertyDescriptor -> Bool
isAccessorDescriptor mp =
  case mp of
   JSJust PropertyDescriptor {..} ->
     isJust propertyDescriptorGet || isJust propertyDescriptorSet
   _ -> False

toAccessorDescriptor :: JSMaybe PropertyDescriptor -> JSMaybe AccessorDescriptor
toAccessorDescriptor mp =
  case mp of
   JSNothing -> JSNothing
   JSJust p@(PropertyDescriptor {..}) ->
     if isAccessorDescriptor mp
     then JSJust $ AccessorDescriptor {
       accessorDescriptorGet          = maybe JSNothing JSJust propertyDescriptorGet,
       accessorDescriptorSet          = maybe JSNothing JSJust propertyDescriptorSet,
       accessorDescriptorEnumerable   = maybe False id propertyDescriptorEnumerable,
       accessorDescriptorConfigurable = maybe False id propertyDescriptorConfigurable }
     else JSNothing

fromAccessorDescriptor :: AccessorDescriptor -> PropertyDescriptor
fromAccessorDescriptor AccessorDescriptor {..} =
  PropertyDescriptor {
    propertyDescriptorValue        = Nothing,
    propertyDescriptorGet          = jsMaybe Nothing Just accessorDescriptorGet,
    propertyDescriptorSet          = jsMaybe Nothing Just accessorDescriptorSet,
    propertyDescriptorWritable     = Nothing,
    propertyDescriptorEnumerable   = Just accessorDescriptorEnumerable,
    propertyDescriptorConfigurable = Just accessorDescriptorConfigurable }

isDataDescriptor :: JSMaybe PropertyDescriptor -> Bool
isDataDescriptor mp =
  case mp of
   JSJust (PropertyDescriptor {..}) ->
     isJust propertyDescriptorValue || isJust propertyDescriptorWritable
   JSNothing -> False

toDataDescriptor :: JSMaybe PropertyDescriptor -> JSMaybe DataDescriptor
toDataDescriptor mp =
  case mp of
   JSNothing -> JSNothing
   JSJust p@(PropertyDescriptor {..}) ->
     if isDataDescriptor mp
     then JSJust $ DataDescriptor {
       dataDescriptorValue        = maybe (inj Undefined) id propertyDescriptorValue,
       dataDescriptorWritable     = maybe False id propertyDescriptorWritable,
       dataDescriptorEnumerable   = maybe False id propertyDescriptorEnumerable,
       dataDescriptorConfigurable = maybe False id propertyDescriptorConfigurable }
     else JSNothing

fromDataDescriptor :: DataDescriptor -> PropertyDescriptor
fromDataDescriptor DataDescriptor {..} =
  PropertyDescriptor {
    propertyDescriptorValue        = Just dataDescriptorValue,
    propertyDescriptorGet          = Nothing,
    propertyDescriptorSet          = Nothing,
    propertyDescriptorWritable     = Just dataDescriptorWritable,
    propertyDescriptorEnumerable   = Just dataDescriptorEnumerable,
    propertyDescriptorConfigurable = Just dataDescriptorConfigurable }

isGenericDescriptor :: JSMaybe PropertyDescriptor -> Bool
isGenericDescriptor desc =
  not $ isAccessorDescriptor desc || isDataDescriptor desc

fromPropertyDescriptor :: JSMaybe PropertyDescriptor -> JavaScriptM (JSMaybe Object)
fromPropertyDescriptor mdesc = do
  o <- newObjectObject Nothing
  case mdesc of
   JSNothing -> return JSNothing
   JSJust desc@(PropertyDescriptor {..}) -> do
     if isDataDescriptor mdesc
       then do
       defineOwnProperty
         o
         "value"
         def {
           propertyDescriptorValue = propertyDescriptorValue,
           propertyDescriptorWritable = Just True,
           propertyDescriptorEnumerable = Just True,
           propertyDescriptorConfigurable = Just True }
         False
       defineOwnProperty
         o
         "writable"
         def {
           propertyDescriptorValue = inj <$> propertyDescriptorWritable,
           propertyDescriptorWritable = Just True,
           propertyDescriptorEnumerable = Just True,
           propertyDescriptorConfigurable = Just True }
         False
       else do
       defineOwnProperty
         o
         "get"
         def {
           propertyDescriptorValue = inj <$> propertyDescriptorGet,
           propertyDescriptorWritable = Just True,
           propertyDescriptorEnumerable = Just True,
           propertyDescriptorConfigurable = Just True }
         False
       defineOwnProperty
         o
         "set"
         def {
           propertyDescriptorValue = inj <$> propertyDescriptorSet,
           propertyDescriptorWritable = Just True,
           propertyDescriptorEnumerable = Just True,
           propertyDescriptorConfigurable = Just True }
         False
     return $ JSJust o

data LexicalEnvironment
  = LexicalEnvironment InternalId
  deriving (Eq, Ord, Show)

data LexicalEnvironmentInternal
  = LexicalEnvironmentInternal EnvironmentRecord (Maybe LexicalEnvironment)
  deriving (Eq, Show)

environmentRecord :: Lens' LexicalEnvironmentInternal EnvironmentRecord
environmentRecord =
  Lens.lens
  (\(LexicalEnvironmentInternal er _) -> er)
  (\(LexicalEnvironmentInternal _ mc) er -> LexicalEnvironmentInternal er mc)

getIdentifierReference :: Maybe LexicalEnvironment -> String -> Bool ->
                          JavaScriptM Reference
getIdentifierReference mLex name strict = do
  case mLex of
   Nothing ->
     return $ Reference (inj Undefined) name strict
   Just lex -> do
     LexicalEnvironmentInternal envRec outer <- Lens.use $ lexicalEnvironmentInternal lex
     exists <- hasBinding envRec name
     if exists
       then return $ Reference (inj envRec) name strict
       else getIdentifierReference outer name strict

newDeclarativeEnvironment :: Maybe LexicalEnvironment ->
                             JavaScriptM LexicalEnvironment
newDeclarativeEnvironment e = do
  ier <- createNextInternalId
  ider <- createNextInternalId
  ile <- createNextInternalId
  let decEnvRecInternal
        = DeclarativeEnvironmentRecordInternal {
          declarativeEnvironmentRecordInternalBindings = Map.empty }
      decEnvRec = DeclarativeEnvironmentRecord ider
      envrecInternal
        = EnvironmentRecordInternalDeclarative decEnvRec
      envrec = EnvironmentRecord ier
      envInternal = LexicalEnvironmentInternal envrec e
      env = LexicalEnvironment ile
  mEnvironmentRecordInternal envrec ?= envrecInternal
  mDeclarativeEnvironmentRecordInternal decEnvRec ?= decEnvRecInternal
  mLexicalEnvironmentInternal env ?= envInternal
  return env

newObjectObjectEnvironment :: Object -> Maybe LexicalEnvironment -> JavaScriptM LexicalEnvironment
newObjectObjectEnvironment o e = do
  ier <- createNextInternalId
  ile <- createNextInternalId
  let envrecInternal = EnvironmentRecordInternalObject (ObjectEnvironmentRecord o False)
      envrec = EnvironmentRecord ier
      envInternal = LexicalEnvironmentInternal envrec e
      env = LexicalEnvironment ile
  mEnvironmentRecordInternal envrec ?= envrecInternal
  mLexicalEnvironmentInternal env ?= envInternal
  return env

enterGlobalContext :: Program -> JavaScriptM ()
enterGlobalContext program = do
  global <- Lens.use globalObject
  globalEnvironment <- Lens.use globalLexicalEnvironment
  contextStack . currentContext . variableEnvironment .= globalEnvironment
  contextStack . currentContext . lexicalEnvironment .= globalEnvironment
  contextStack . currentContext . thisBinding .= (inj global)
  declarationBindingInstantiation (CodeGlobal program)

enterEvalContext :: JavaScriptM ()
enterEvalContext = error "enterEvalContext"

enterFunctionContext :: Object -> Value -> List Value -> JavaScriptM ()
enterFunctionContext f thisArg args = do
  let strict = False
  thisBinding <-
    if strict
      then return thisArg
    else
      case thisArg of
       ValueNull _ -> do
         global <- Lens.use globalObject
         return (inj global)
       ValueUndefined _ -> do
         global <- Lens.use globalObject
         return (inj global)
       _ -> do
         obj <- toObject thisArg
         return (inj obj)
  lex <- scope f
  localEnv <- newDeclarativeEnvironment (Just lex)
  let ctx = Context {
        contextLexicalEnvironment  = localEnv,
        contextVariableEnvironment = localEnv,
        contextThisBinding         = thisBinding,
        contextLabels              = [] }
  pushContext ctx
  declarationBindingInstantiation (CodeFunction f args)

data EnvironmentRecord
  = EnvironmentRecord InternalId
  deriving (Eq, Ord, Show)

data EnvironmentRecordInternal
  = EnvironmentRecordInternalDeclarative DeclarativeEnvironmentRecord
  | EnvironmentRecordInternalObject ObjectEnvironmentRecord
  deriving (Eq, Show)

environmentRecordInternal :: EnvironmentRecord ->
                             Lens' (JavaScriptState m) EnvironmentRecordInternal
environmentRecordInternal i =
  Lens.lens
  (\JavaScriptState {..} ->
    case Map.lookup i javaScriptStateEnvironmentRecordHeap of
     Nothing -> error "Internal error: can't find environmentRecord"
     Just o -> o)
  (\jss@(JavaScriptState {..}) oi ->
    jss { javaScriptStateEnvironmentRecordHeap = Map.insert i oi javaScriptStateEnvironmentRecordHeap })

mEnvironmentRecordInternal :: EnvironmentRecord -> Lens' (JavaScriptState m) (Maybe EnvironmentRecordInternal)
mEnvironmentRecordInternal i = environmentRecordHeap . Lens.at i

declarativeEnvironmentRecord :: Lens'
                                EnvironmentRecordInternal
                                DeclarativeEnvironmentRecord
declarativeEnvironmentRecord =
  Lens.lens
  (\eri -> case eri of
            EnvironmentRecordInternalDeclarative der -> der
            _ -> error "Not a declarative environment record")
  (\eri der -> case eri of
            EnvironmentRecordInternalDeclarative _ ->
              EnvironmentRecordInternalDeclarative der
            _ -> error "Not a declarative environment record")

objectEnvironmentRecord :: Lens'
                           EnvironmentRecordInternal
                           ObjectEnvironmentRecord
objectEnvironmentRecord =
  Lens.lens
  (\eri -> case eri of
            EnvironmentRecordInternalObject der -> der
            _ -> error "Not a object environment record")
  (\eri der -> case eri of
            EnvironmentRecordInternalObject _ ->
              EnvironmentRecordInternalObject der
            _ -> error "Not a object environment record")

data DeclarativeEnvironmentRecord
  = DeclarativeEnvironmentRecord InternalId
  deriving (Eq, Ord, Show)

data DeclarativeBinding
  = DeclarativeBindingMutable
    { declarativeBindingMutableValue  :: Value
    , declarativeBindingMutableDelete :: Bool }
  | DeclarativeBindingImmutable
    { declarativeBindingImmutableValue       :: Value
    , declarativeBindingImmutableInitialised :: Bool }
  deriving (Eq, Show)

data DeclarativeEnvironmentRecordInternal
  = DeclarativeEnvironmentRecordInternal
    { declarativeEnvironmentRecordInternalBindings
      :: Map String DeclarativeBinding }

internalDeclarativeEnvironmentRecordBindings
  :: Lens'
     DeclarativeEnvironmentRecordInternal
     (Map String DeclarativeBinding)
internalDeclarativeEnvironmentRecordBindings =
  Lens.lens
  declarativeEnvironmentRecordInternalBindings
  (\deri bs ->
    deri { declarativeEnvironmentRecordInternalBindings = bs })

internalDeclarativeEnvironmentRecordBinding
  :: String ->
     Lens'
     DeclarativeEnvironmentRecordInternal
     (Maybe DeclarativeBinding)
internalDeclarativeEnvironmentRecordBinding n =
  internalDeclarativeEnvironmentRecordBindings . Lens.at n

declarativeEnvironmentRecordInternal
  :: DeclarativeEnvironmentRecord ->
     Lens' (JavaScriptState m) DeclarativeEnvironmentRecordInternal
declarativeEnvironmentRecordInternal i =
  Lens.lens
  (\JavaScriptState {..} ->
    case Map.lookup i javaScriptStateDeclarativeEnvironmentRecordHeap of
     Nothing -> error "Internal error: can't find declarativeEnvironmentRecord"
     Just o -> o)
  (\jss@(JavaScriptState {..}) oi ->
    jss { javaScriptStateDeclarativeEnvironmentRecordHeap =
             Map.insert i oi javaScriptStateDeclarativeEnvironmentRecordHeap })

mDeclarativeEnvironmentRecordInternal :: DeclarativeEnvironmentRecord -> Lens' (JavaScriptState m) (Maybe DeclarativeEnvironmentRecordInternal)
mDeclarativeEnvironmentRecordInternal i =
  declarativeEnvironmentRecordHeap . Lens.at i

data ObjectEnvironmentRecord
  = ObjectEnvironmentRecord
    { objectEnvironmentRecordBindingObject :: Object
    , objectEnvironmentRecordProvideThis   :: Bool }
  deriving (Eq, Show)

hasBinding :: EnvironmentRecord -> String -> JavaScriptM Bool
hasBinding er n = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     hasBindingDeclarative der n
   EnvironmentRecordInternalObject oer ->
     hasBindingObject oer n

hasBindingDeclarative :: DeclarativeEnvironmentRecord ->
                         String -> JavaScriptM Bool
hasBindingDeclarative envRec n = do
  deri <- Lens.use $ declarativeEnvironmentRecordInternal envRec
  let bindings = declarativeEnvironmentRecordInternalBindings deri
  return $ Map.member n bindings

hasBindingObject :: ObjectEnvironmentRecord ->
                    String -> JavaScriptM Bool
hasBindingObject envRec n = do
  let bindings = objectEnvironmentRecordBindingObject envRec
  hasProperty bindings n

createMutableBinding :: EnvironmentRecord -> String -> Maybe Bool -> JavaScriptM ()
createMutableBinding er n d = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     createMutableBindingDeclarative der n d
   EnvironmentRecordInternalObject oer ->
     createMutableBindingObject oer n d

createMutableBindingDeclarative :: DeclarativeEnvironmentRecord ->
                                   String -> Maybe Bool -> JavaScriptM ()
createMutableBindingDeclarative envRec n d = do
  let markDel = maybe False id d
      binding = DeclarativeBindingMutable (inj Undefined) markDel
  declarativeEnvironmentRecordInternal envRec .
    internalDeclarativeEnvironmentRecordBinding n ?= binding

createMutableBindingObject :: ObjectEnvironmentRecord ->
                              String -> Maybe Bool -> JavaScriptM ()
createMutableBindingObject envRec n d = do
  let bindings = objectEnvironmentRecordBindingObject envRec
      configValue = if d == Just True then True else False
      desc = def {
        propertyDescriptorValue        = Just (inj Undefined),
        propertyDescriptorWritable     = Just True,
        propertyDescriptorEnumerable   = Just True,
        propertyDescriptorConfigurable = Just configValue }
  defineOwnProperty bindings n desc True
  return ()

setMutableBinding :: EnvironmentRecord -> String -> Value -> Bool -> JavaScriptM ()
setMutableBinding er n v s = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     setMutableBindingDeclarative der n v s
   EnvironmentRecordInternalObject oer ->
     setMutableBindingObject oer n v s

setMutableBindingDeclarative :: DeclarativeEnvironmentRecord ->
                                String -> Value -> Bool -> JavaScriptM ()
setMutableBindingDeclarative envRec n v s = do
  binding <- Lens.use $ declarativeEnvironmentRecordInternal envRec .
             internalDeclarativeEnvironmentRecordBinding n
  case binding of
   Nothing -> error "Internal error: setMutableBindingDeclarative assert failed"
   Just (DeclarativeBindingMutable _ d) -> do
     let binding = DeclarativeBindingMutable v d
     declarativeEnvironmentRecordInternal envRec .
       internalDeclarativeEnvironmentRecordBinding n ?= binding
   Just (DeclarativeBindingImmutable {}) ->
     if s
     then newTypeErrorObject Nothing >>= jsThrow . inj
     else return ()

setMutableBindingObject :: ObjectEnvironmentRecord ->
                           String -> Value -> Bool -> JavaScriptM ()
setMutableBindingObject envRec n v s = do
  let bindings = objectEnvironmentRecordBindingObject envRec
  put bindings n v s

getBindingValue :: EnvironmentRecord -> String -> Bool -> JavaScriptM Value
getBindingValue er n s = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     getBindingValueDeclarative der n s
   EnvironmentRecordInternalObject oer ->
     getBindingValueObject oer n s

getBindingValueDeclarative :: DeclarativeEnvironmentRecord ->
                              String -> Bool -> JavaScriptM Value
getBindingValueDeclarative envRec n s = do
  binding <- Lens.use $ declarativeEnvironmentRecordInternal envRec .
             internalDeclarativeEnvironmentRecordBinding n
  case binding of
   Nothing -> error "Internal error: getBindingValueDeclarative assert failed"
   Just (DeclarativeBindingImmutable v False) ->
     if not s
     then return (inj Undefined)
     else newReferenceErrorObject Nothing >>= jsThrow . inj
   Just (DeclarativeBindingImmutable v _) -> return v
   Just (DeclarativeBindingMutable v _) -> return v

getBindingValueObject :: ObjectEnvironmentRecord ->
                         String -> Bool -> JavaScriptM Value
getBindingValueObject envRec n s = do
  let bindings = objectEnvironmentRecordBindingObject envRec
  value <- hasProperty bindings n
  if not value
    then do
    if not s
      then return (inj Undefined)
      else newReferenceErrorObject Nothing >>= jsThrow . inj
    else get bindings n

deleteBinding :: EnvironmentRecord -> String -> JavaScriptM Bool
deleteBinding er n = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     deleteBindingDeclarative der n
   EnvironmentRecordInternalObject oer ->
     deleteBindingObject oer n

deleteBindingDeclarative :: DeclarativeEnvironmentRecord ->
                            String -> JavaScriptM Bool
deleteBindingDeclarative envRec n = do
  binding <- Lens.use $ declarativeEnvironmentRecordInternal envRec .
             internalDeclarativeEnvironmentRecordBinding n
  case binding of
   Nothing -> return True
   Just (DeclarativeBindingMutable _ True) -> do
     declarativeEnvironmentRecordInternal envRec .
       internalDeclarativeEnvironmentRecordBinding n .= Nothing
     return True
   _ -> return False

deleteBindingObject :: ObjectEnvironmentRecord ->
                       String -> JavaScriptM Bool
deleteBindingObject envRec n = do
  let bindings = objectEnvironmentRecordBindingObject envRec
  delete bindings n False

implicitThisValue :: EnvironmentRecord -> JavaScriptM Value
implicitThisValue er = do
  eri <- Lens.use $ environmentRecordInternal er
  case eri of
   EnvironmentRecordInternalDeclarative der ->
     implicitThisValueDeclarative der
   EnvironmentRecordInternalObject oer ->
     implicitThisValueObject oer

implicitThisValueDeclarative :: DeclarativeEnvironmentRecord ->
                                JavaScriptM Value
implicitThisValueDeclarative _ = return (inj Undefined)

implicitThisValueObject :: ObjectEnvironmentRecord ->
                           JavaScriptM Value
implicitThisValueObject envRec = do
  if objectEnvironmentRecordProvideThis envRec
    then return $ inj $ objectEnvironmentRecordBindingObject envRec
    else return $ inj Undefined

createImmutableBindingDeclarative :: DeclarativeEnvironmentRecord ->
                                     String ->
                                     JavaScriptM ()
createImmutableBindingDeclarative  envRec n = do
  let binding = DeclarativeBindingImmutable (inj Undefined) False
  declarativeEnvironmentRecordInternal envRec .
    internalDeclarativeEnvironmentRecordBinding n ?= binding

initializeImmutableBindingDeclarative :: DeclarativeEnvironmentRecord ->
                                         String ->
                                         Value ->
                                         JavaScriptM ()
initializeImmutableBindingDeclarative envRec n v = do
  let binding = DeclarativeBindingImmutable v True
  declarativeEnvironmentRecordInternal envRec .
    internalDeclarativeEnvironmentRecordBinding n ?= binding

data MatchResult
  = MatchResult

type InternalId = Int

data Object
  = Object InternalId
  deriving (Eq, Ord, Show)

type InternalPrototypeType m         = Object -> JavaScriptT m (JSNullable Object)
type InternalClassType m             = Object -> JavaScriptT m String
type InternalExtensibleType m        = Object -> JavaScriptT m Bool
type InternalGetType m               = Object -> String -> JavaScriptT m Value
type InternalGetOwnPropertyType m    = Object -> String -> JavaScriptT m (JSMaybe PropertyDescriptor)
type InternalGetPropertyType m       = Object -> String -> JavaScriptT m (JSMaybe PropertyDescriptor)
type InternalPutType m               = Object -> String -> Value -> Bool -> JavaScriptT m ()
type InternalCanPutType m            = Object -> String -> JavaScriptT m Bool
type InternalHasPropertyType m       = Object -> String -> JavaScriptT m Bool
type InternalDeleteType m            = Object -> String -> Bool -> JavaScriptT m Bool
type InternalDefaultValueType m      = Object -> Maybe Hint -> JavaScriptT m Primitive
type InternalDefineOwnPropertyType m = Object -> String -> PropertyDescriptor -> Bool -> JavaScriptT m Bool
type InternalPrimitiveValueType m    = Object -> JavaScriptT m Primitive
type InternalConstructType m         = Object -> List Value -> JavaScriptT m Object
type InternalCallType m              = Object -> Value -> List Value -> JavaScriptT m CallValue
type InternalCallNativeType m        = Object -> Value -> List Value -> JavaScriptT m Value
type InternalHasInstanceType m       = Object -> Value -> JavaScriptT m Bool
type InternalScopeType m             = Object -> JavaScriptT m LexicalEnvironment
type InternalFormalParametersType m  = Object -> JavaScriptT m (List String)
type InternalCodeType m              = Object -> JavaScriptT m FuncBody
type InternalTargetFunctionType m    = Object -> JavaScriptT m Object
type InternalBoundThisType m         = Object -> JavaScriptT m Value
type InternalBoundArgumentsType m    = Object -> JavaScriptT m (List Value)
type InternalMatchType m             = Object -> String -> Int -> JavaScriptT m MatchResult
type InternalParameterMapType m      = Object -> JavaScriptT m Object

data ObjectInternal m =
  ObjectInternal
  { objectInternalProperties        :: Map String Property
  , objectInternalPrototype         :: InternalPrototypeType m
  , objectInternalClass             :: InternalClassType m
  , objectInternalExtensible        :: InternalExtensibleType m
  , objectInternalGet               :: InternalGetType m
  , objectInternalGetOwnProperty    :: InternalGetOwnPropertyType m
  , objectInternalGetProperty       :: InternalGetPropertyType m
  , objectInternalPut               :: InternalPutType m
  , objectInternalCanPut            :: InternalCanPutType m
  , objectInternalHasProperty       :: InternalHasPropertyType m
  , objectInternalDelete            :: InternalDeleteType m
  , objectInternalDefaultValue      :: InternalDefaultValueType m
  , objectInternalDefineOwnProperty :: InternalDefineOwnPropertyType m
  , objectInternalPrimitiveValue    :: Maybe (InternalPrimitiveValueType m)
  , objectInternalConstruct         :: Maybe (InternalConstructType m)
  , objectInternalCall              :: Maybe (InternalCallType m)
  , objectInternalHasInstance       :: Maybe (InternalHasInstanceType m)
  , objectInternalScope             :: Maybe (InternalScopeType m)
  , objectInternalFormalParameters  :: Maybe (InternalFormalParametersType m)
  , objectInternalCode              :: Maybe (InternalCodeType m)
  , objectInternalTargetFunction    :: Maybe (InternalTargetFunctionType m)
  , objectInternalBoundThis         :: Maybe (InternalBoundThisType m)
  , objectInternalBoundArguments    :: Maybe (InternalBoundArgumentsType m)
  , objectInternalMatch             :: Maybe (InternalMatchType m)
  , objectInternalParameterMap      :: Maybe (InternalParameterMapType m) }

internalProperties :: Lens' (ObjectInternal m) (Map String Property)
internalProperties =
  Lens.lens
  objectInternalProperties
  (\oi ps -> oi { objectInternalProperties = ps })

internalProperty :: String -> Lens' (ObjectInternal m) (Maybe Property)
internalProperty p = internalProperties . Lens.at p

properties :: Object -> Lens' (JavaScriptState m) (Map String Property)
properties o = internalObject o . internalProperties

property :: Object -> String -> Lens' (JavaScriptState m) (Maybe Property)
property o p = internalObject o . internalProperty p

internalPrototype :: Lens' (ObjectInternal m) (InternalPrototypeType m)
internalPrototype =
  Lens.lens
  objectInternalPrototype
  (\oi p -> oi { objectInternalPrototype = p })

prototype :: (Functor m, Monad m) => InternalPrototypeType m
prototype o = callInternalProperty o objectInternalPrototype

internalClass :: Lens' (ObjectInternal m) (InternalClassType m)
internalClass =
  Lens.lens
  objectInternalClass
  (\oi c -> oi { objectInternalClass = c })

class' :: (Functor m, Monad m) => InternalClassType m
class' o = callInternalProperty o objectInternalClass

internalExtensible :: Lens' (ObjectInternal m) (InternalExtensibleType m)
internalExtensible =
  Lens.lens
  objectInternalExtensible
  (\oi e -> oi { objectInternalExtensible = e })

extensible :: (Functor m, Monad m) => InternalExtensibleType m
extensible o = callInternalProperty o objectInternalExtensible

internalGet :: Lens' (ObjectInternal m) (InternalGetType m)
internalGet =
  Lens.lens
  objectInternalGet
  (\oi g -> oi { objectInternalGet = g })

get :: (Functor m, Monad m) => InternalGetType m
get o = callInternalProperty1 o objectInternalGet

internalGetOwnProperty :: Lens' (ObjectInternal m) (InternalGetOwnPropertyType m)
internalGetOwnProperty =
  Lens.lens
  objectInternalGetOwnProperty
  (\oi gop -> oi { objectInternalGetOwnProperty = gop })

getOwnProperty :: (Functor m, Monad m) => InternalGetOwnPropertyType m
getOwnProperty o = callInternalProperty1 o objectInternalGetOwnProperty

internalGetProperty :: Lens' (ObjectInternal m) (InternalGetPropertyType m)
internalGetProperty =
  Lens.lens
  objectInternalGetProperty
  (\oi gp -> oi { objectInternalGetProperty = gp })

getProperty :: (Functor m, Monad m) => InternalGetPropertyType m
getProperty o = callInternalProperty1 o objectInternalGetProperty

internalPut :: Lens' (ObjectInternal m) (InternalPutType m)
internalPut =
  Lens.lens
  objectInternalPut
  (\oi p -> oi { objectInternalPut = p })

put :: (Functor m, Monad m) => InternalPutType m
put o = callInternalProperty3 o objectInternalPut

internalCanPut :: Lens' (ObjectInternal m) (InternalCanPutType m)
internalCanPut =
  Lens.lens
  objectInternalCanPut
  (\oi cp -> oi { objectInternalCanPut = cp })

canPut :: (Functor m, Monad m) => InternalCanPutType m
canPut o = callInternalProperty1 o objectInternalCanPut

internalHasProperty :: Lens' (ObjectInternal m) (InternalHasPropertyType m)
internalHasProperty =
  Lens.lens
  objectInternalHasProperty
  (\oi hp -> oi { objectInternalHasProperty = hp })

hasProperty :: (Functor m, Monad m) => InternalHasPropertyType m
hasProperty o = callInternalProperty1 o objectInternalHasProperty

internalDelete :: Lens' (ObjectInternal m) (InternalDeleteType m)
internalDelete =
  Lens.lens
  objectInternalDelete
  (\oi d -> oi { objectInternalDelete = d })

delete :: (Functor m, Monad m) => InternalDeleteType m
delete o = callInternalProperty2 o objectInternalDelete

internalDefaultValue :: Lens' (ObjectInternal m) (InternalDefaultValueType m)
internalDefaultValue =
  Lens.lens
  objectInternalDefaultValue
  (\oi dv -> oi { objectInternalDefaultValue = dv })

defaultValue :: (Functor m, Monad m) => InternalDefaultValueType m
defaultValue o = callInternalProperty1 o objectInternalDefaultValue

internalDefineOwnProperty :: Lens' (ObjectInternal m) (InternalDefineOwnPropertyType m)
internalDefineOwnProperty =
  Lens.lens
  objectInternalDefineOwnProperty
  (\oi dop -> oi { objectInternalDefineOwnProperty = dop })

defineOwnProperty :: (Functor m, Monad m) => InternalDefineOwnPropertyType m
defineOwnProperty o = callInternalProperty3 o objectInternalDefineOwnProperty

internalPrimitiveValue :: Lens' (ObjectInternal m) (Maybe (InternalPrimitiveValueType m))
internalPrimitiveValue =
  Lens.lens
  objectInternalPrimitiveValue
  (\oi mpv -> oi { objectInternalPrimitiveValue = mpv })

primitiveValue :: (Functor m, Monad m) => InternalPrimitiveValueType m
primitiveValue o = callInternalOptionalProperty o objectInternalPrimitiveValue

internalConstruct :: Lens' (ObjectInternal m) (Maybe (InternalConstructType m))
internalConstruct =
  Lens.lens
  objectInternalConstruct
  (\oi c -> oi { objectInternalConstruct = c })

construct :: (Functor m, Monad m) => InternalConstructType m
construct o = callInternalOptionalProperty1 o objectInternalConstruct

internalCall :: Lens' (ObjectInternal m) (Maybe (InternalCallType m))
internalCall =
  Lens.lens
  objectInternalCall
  (\oi c -> oi { objectInternalCall = c })

call :: (Functor m, Monad m) => InternalCallType m
call o = callInternalOptionalProperty2 o objectInternalCall

callNative :: (Functor m, Monad m) => InternalCallNativeType m
callNative o t l = do
  rv <- callInternalOptionalProperty2 o objectInternalCall t l
  case prj rv of
   Nothing -> error "Native function can't return references"
   Just v -> return v

hasInstance :: (Functor m, Monad m) => InternalHasInstanceType m
hasInstance o = callInternalOptionalProperty1 o objectInternalHasInstance

internalHasInstance :: Lens' (ObjectInternal m) (Maybe (InternalHasInstanceType m))
internalHasInstance =
  Lens.lens
  objectInternalHasInstance
  (\oi hi -> oi { objectInternalHasInstance = hi })

scope :: (Functor m, Monad m) => InternalScopeType m
scope o = callInternalOptionalProperty o objectInternalScope

internalScope :: Lens' (ObjectInternal m) (Maybe (InternalScopeType m))
internalScope =
  Lens.lens
  objectInternalScope
  (\oi s -> oi { objectInternalScope = s })

formalParameters :: (Functor m, Monad m) => InternalFormalParametersType m
formalParameters o = callInternalOptionalProperty o objectInternalFormalParameters

internalFormalParameters :: Lens' (ObjectInternal m) (Maybe (InternalFormalParametersType m))
internalFormalParameters =
  Lens.lens
  objectInternalFormalParameters
  (\oi fp -> oi { objectInternalFormalParameters = fp })

code :: (Functor m, Monad m) => InternalCodeType m
code o = callInternalOptionalProperty o objectInternalCode

internalCode :: Lens' (ObjectInternal m) (Maybe (InternalCodeType m))
internalCode =
  Lens.lens
  objectInternalCode
  (\oi c -> oi { objectInternalCode = c })

internalTargetFunction :: Lens' (ObjectInternal m) (Maybe (InternalTargetFunctionType m))
internalTargetFunction =
  Lens.lens
  objectInternalTargetFunction
  (\oi tf -> oi { objectInternalTargetFunction = tf })

internalBoundThis :: Lens' (ObjectInternal m) (Maybe (InternalBoundThisType m))
internalBoundThis =
  Lens.lens
  objectInternalBoundThis
  (\oi bt -> oi { objectInternalBoundThis = bt })

internalBoundArguments :: Lens' (ObjectInternal m) (Maybe (InternalBoundArgumentsType m))
internalBoundArguments =
  Lens.lens
  objectInternalBoundArguments
  (\oi bas -> oi { objectInternalBoundArguments = bas })

internalMatch :: Lens' (ObjectInternal m) (Maybe (InternalMatchType m))
internalMatch =
  Lens.lens
  objectInternalMatch
  (\oi m -> oi { objectInternalMatch = m })

internalParameterMap :: Lens' (ObjectInternal m) (Maybe (InternalParameterMapType m))
internalParameterMap =
  Lens.lens
  objectInternalParameterMap
  (\oi pm -> oi { objectInternalParameterMap = pm })

callInternalProperty :: (Functor m, Monad m) => Object -> (ObjectInternal m -> Object -> JavaScriptT m a) -> JavaScriptT m a
callInternalProperty o p = do
  oi <- Lens.use $ internalObject o
  p oi o

callInternalProperty1 :: (Functor m, Monad m) => Object -> (ObjectInternal m -> Object -> a -> JavaScriptT m b) -> a -> JavaScriptT m b
callInternalProperty1 o p a = do
  oi <- Lens.use $ internalObject o
  p oi o a

callInternalProperty2 :: (Functor m, Monad m) => Object -> (ObjectInternal m -> Object -> a -> b -> JavaScriptT m c) -> a -> b -> JavaScriptT m c
callInternalProperty2 o p a b = do
  oi <- Lens.use $ internalObject o
  p oi o a b

callInternalProperty3 :: (Functor m, Monad m) => Object -> (ObjectInternal m -> Object -> a -> b -> c -> JavaScriptT m d) -> a -> b -> c -> JavaScriptT m d
callInternalProperty3 o p a b c = do
  oi <- Lens.use $ internalObject o
  p oi o a b c

callInternalOptionalProperty :: (Functor m, Monad m) => Object -> (ObjectInternal m -> Maybe (Object -> JavaScriptT m a)) -> JavaScriptT m a
callInternalOptionalProperty o p = do
  oi <- Lens.use $ internalObject o
  case p oi of
   Just op -> op o
   Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

callInternalOptionalProperty1 :: (Functor m, Monad m) =>
                                 Object ->
                                 (ObjectInternal m ->
                                  Maybe (Object -> a -> JavaScriptT m b)) ->
                                 a ->
                                 JavaScriptT m b
callInternalOptionalProperty1 o p a = do
  oi <- Lens.use $ internalObject o
  case p oi of
   Just op -> op o a
   Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

callInternalOptionalProperty2 :: (Functor m, Monad m) =>
                                 Object ->
                                 (ObjectInternal m ->
                                  Maybe (Object -> a -> b -> JavaScriptT m c)) ->
                                 a -> b ->
                                 JavaScriptT m c
callInternalOptionalProperty2 o p a b = do
  oi <- Lens.use $ internalObject o
  case p oi of
   Just op -> op o a b
   Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

callInternalOptionalProperty3 :: (Functor m, Monad m) =>
                                 Object ->
                                 (ObjectInternal m ->
                                  Maybe (Object -> a -> b -> c -> JavaScriptT m d)) ->
                                 a -> b -> c ->
                                 JavaScriptT m d
callInternalOptionalProperty3 o p a b c = do
  oi <- Lens.use $ internalObject o
  case p oi of
   Just op -> op o a b c
   Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

getOwnPropertyImpl :: Object -> String -> JavaScriptM (JSMaybe PropertyDescriptor)
getOwnPropertyImpl o p = do
  oi@(ObjectInternal {..}) <- Lens.use $ internalObject o
  case Map.lookup p objectInternalProperties of
   Just x -> do
     case x of
      PropertyData (DataDescriptor {..}) -> do
        return $ JSJust
          def { propertyDescriptorValue = Just dataDescriptorValue
              , propertyDescriptorWritable = Just dataDescriptorWritable
              , propertyDescriptorEnumerable = Just dataDescriptorEnumerable
              , propertyDescriptorConfigurable = Just dataDescriptorConfigurable }
      PropertyAccessor (AccessorDescriptor {..}) -> do
        return $ JSJust
          def { propertyDescriptorGet = jsMaybe Nothing Just accessorDescriptorGet
              , propertyDescriptorSet = jsMaybe Nothing Just accessorDescriptorSet
              , propertyDescriptorEnumerable = Just accessorDescriptorEnumerable
              , propertyDescriptorConfigurable = Just accessorDescriptorConfigurable }

   Nothing -> return JSNothing

getPropertyImpl :: Object -> String -> JavaScriptM (JSMaybe PropertyDescriptor)
getPropertyImpl o p = do
  prop <- getOwnProperty o p
  case prop of
   JSJust _ -> return prop
   JSNothing -> do
     proto <- prototype o
     case proto of
      JSNull -> return JSNothing
      JSExist po -> do
        getProperty po p

getImpl :: Object -> String -> JavaScriptM Value
getImpl o p = do
  mDesc <- getProperty o p
  case mDesc of
   JSNothing -> return $ inj Undefined
   JSJust desc@(PropertyDescriptor {..}) -> do
     case toDataDescriptor mDesc of
      JSJust DataDescriptor {..} -> return dataDescriptorValue
      JSNothing -> do
        case propertyDescriptorGet of
         Nothing -> return $ inj Undefined
         Just getter -> callNative getter (inj o) (List [])

canPutImpl :: Object -> String -> JavaScriptM Bool
canPutImpl o p = do
  mDesc <- getOwnProperty o p
  case mDesc of
   JSJust desc@(PropertyDescriptor {..}) -> do
     case toAccessorDescriptor mDesc of
      JSJust AccessorDescriptor {..} -> do
       case accessorDescriptorSet of
        JSNothing -> return False
        _ -> return True
      _ -> return $ fromJust propertyDescriptorWritable
   JSNothing -> do
     nProto <- prototype o
     case nProto of
      JSNull -> extensible o
      JSExist proto -> do
        mInherited <- getProperty proto p
        case mInherited of
         JSNothing -> extensible o
         JSJust inherited@(PropertyDescriptor {..}) -> do
           if isAccessorDescriptor mInherited
             then do
             case propertyDescriptorSet of
              Nothing -> return False
              _ -> return True
             else do
             e <- extensible o
             if not e
               then return False
               else return $ fromJust propertyDescriptorWritable

putImpl :: Object -> String -> Value -> Bool -> JavaScriptM ()
putImpl o p v throw = do
  c <- canPut o p
  if not c
    then do
    if throw
      then newTypeErrorObject Nothing >>= jsThrow . inj
      else return ()
    else do
    ownDesc <- getOwnProperty o p
    if isDataDescriptor ownDesc
      then do
      let valueDesc = def { propertyDescriptorValue = Just v }
      defineOwnProperty o p valueDesc throw
      return ()
      else do
      desc <- getProperty o p
      if isAccessorDescriptor desc
        then do
        let JSJust (PropertyDescriptor {..}) = desc
        let setter = fromJust propertyDescriptorSet
        callNative setter (inj o) (List [v])
        return ()
        else do
        let newDesc = def {
              propertyDescriptorValue = Just v,
              propertyDescriptorWritable = Just True,
              propertyDescriptorEnumerable = Just True,
              propertyDescriptorConfigurable = Just True }
        defineOwnProperty o p newDesc throw
        return ()
  return ()

hasPropertyImpl :: Object -> String -> JavaScriptM Bool
hasPropertyImpl o p = do
  desc <- getProperty o p
  case desc of
   JSNothing -> return False
   _ -> return True

deleteImpl :: Object -> String -> Bool -> JavaScriptM Bool
deleteImpl o p throw = do
  desc <- getOwnProperty o p
  case desc of
   JSNothing -> return True
   JSJust (PropertyDescriptor {..}) -> do
     if propertyDescriptorConfigurable == Just True
       then do
       return True
       else do
       if throw
         then newTypeErrorObject Nothing >>= jsThrow . inj
         else return False

data Hint
  = HintString
  | HintNumber
  deriving (Eq, Show)

defaultValueImpl :: Object -> Maybe Hint -> JavaScriptM Primitive
defaultValueImpl o (Just HintString) = do
  f <- get o "toString"
  mc <- toCallable f
  case mc of
   Just c -> do
     str <- call c (inj o) (List [])
     case prj str of
      Just p -> return p
      Nothing -> valueOfBranch
   Nothing -> valueOfBranch
  where
    valueOfBranch = do
      valueOf <- get o "valueOf"
      mc <- toCallable valueOf
      case mc of
       Just c -> do
         val <- call c (inj o) (List [])
         case val of
          CallValuePrimitive p -> return p
          _ -> newTypeErrorObject Nothing >>= jsThrow . inj
       Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

defaultValueImpl o (Just HintNumber) = do
  valueOf <- get o "valueOf"
  mc <- toCallable valueOf
  case mc of
   Just c -> do
     val <- call c (inj o) (List [])
     case prj val of
      Just p -> return p
      Nothing -> toStringBranch
   Nothing -> toStringBranch
  where
    toStringBranch = do
      f <- get o "toString"
      mc <- toCallable f
      case mc of
       Just c -> do
         str <- call c (inj o) (List [])
         case str of
          CallValuePrimitive p -> return p
          _ -> newTypeErrorObject Nothing >>= jsThrow . inj
       Nothing -> newTypeErrorObject Nothing >>= jsThrow . inj

defaultValueImpl o Nothing = defaultValueImpl o (Just HintNumber)

functionPrototypeCallImpl :: (Monad m) => InternalCallType m
functionPrototypeCallImpl _ _ _ = return (inj Undefined)

newFunctionObject :: Maybe FormalParamList ->
                     FuncBody ->
                     LexicalEnvironment ->
                     Bool ->
                     JavaScriptM Object
newFunctionObject mfpl fb scope strict = do
  i <- createNextInternalId
  function <- Lens.use functionPrototypeObject
  let f = Object i
      names = case mfpl of
               Just fpl ->
                 foldFormalParamList (\(Ident (IdentName s)) -> (s:)) [] fpl
               Nothing -> []
      len = length names
      oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist function),
        objectInternalClass             = const $ return "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = functionGetImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just functionConstructImpl,
        objectInternalCall              = Just functionCallImpl,
        objectInternalHasInstance       = Just functionHasInstanceImpl,
        objectInternalScope             = Just $ const $ return scope,
        objectInternalFormalParameters  = Just $ const $ return $ List names,
        objectInternalCode              = Just $ const $ return fb,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

  mInternalObject f ?= oi
  defineOwnProperty
    f
    "length"
    def {
      propertyDescriptorValue        = Just $ inj (Number $ fromIntegral len),
      propertyDescriptorWritable     = Just False,
      propertyDescriptorEnumerable   = Just False,
      propertyDescriptorConfigurable = Just False }
    False
  proto <- newObjectObject Nothing
  defineOwnProperty
    proto
    "constructor"
    def {
      propertyDescriptorValue        = Just $ inj f,
      propertyDescriptorWritable     = Just True,
      propertyDescriptorEnumerable   = Just False,
      propertyDescriptorConfigurable = Just True }
    False
  defineOwnProperty
    f
    "prototype"
    def {
      propertyDescriptorValue        = Just $ inj proto,
      propertyDescriptorWritable     = Just True,
      propertyDescriptorEnumerable   = Just False,
      propertyDescriptorConfigurable = Just False }
    False
  if strict
    then do
    thrower <- Lens.use throwTypeErrorObject
    defineOwnProperty
      f
      "caller"
      def {
        propertyDescriptorGet          = Just thrower,
        propertyDescriptorSet          = Just thrower,
        propertyDescriptorEnumerable   = Just False,
        propertyDescriptorConfigurable = Just False }
      False
    return f
    else return f
  where
    foldFormalParamList f a (FormalParamList i) = f i a
    foldFormalParamList f a (FormalParamListCons fpl i) =
      f i (foldFormalParamList f a fpl)

functionConstructorCallImpl :: (Functor m, Monad m) =>
                               InternalCallType m
functionConstructorCallImpl f _ args =
  inj <$>functionConstructorConstructImpl f args

functionConstructorConstructImpl :: (Functor m, Monad m) =>
                                    InternalConstructType m
functionConstructorConstructImpl f args = error "functionConstructorConstructImpl"

functionCallImpl :: (Functor m, Monad m) => InternalCallType m
functionCallImpl f this args = do
  fpl <- formalParameters f
  enterFunctionContext f this args
  mc <- Lens.use $ internalObject f . internalCode
  result <- case mc of
   Nothing ->
     return $ Completion CompletionTypeNormal (inj Undefined) Nothing
   Just c -> do
     fb <- c f
     interpret fb
  popContext
  case result of
   Completion CompletionTypeThrow (Just v) _ -> jsThrow v
   Completion CompletionTypeReturn (Just v) _ -> return (inj v)
   _ -> return (inj Undefined)

functionGetImpl :: (Functor m, Monad m) => InternalGetType m
functionGetImpl f p = do
  v <- getImpl f p
  return v

functionConstructImpl :: (Functor m, Monad m) => InternalConstructType m
functionConstructImpl f l = do
  i <- createNextInternalId
  proto <- get f "prototype"
  p <- case proto of
           ValueObject o -> return o
           _ -> Lens.use objectPrototypeObject
  let obj = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject f ?= oi
  result <- call f (inj obj) l
  case result of
   CallValueObject o -> return o
   _ -> return obj

functionHasInstanceImpl :: (Functor m, Monad m) => InternalHasInstanceType m
functionHasInstanceImpl = error "functionHasInstanceImpl"

newArrayObject :: [Value] -> JavaScriptM Object
newArrayObject as = do
  let properties =
        [ ("length", PropertyData $
                     def { dataDescriptorValue =
                              inj $ Number (fromIntegral $ length as),
                           dataDescriptorWritable = True,
                           dataDescriptorEnumerable = True,
                           dataDescriptorConfigurable = True }) ] ++
        (snd $
         foldl
         (\(n, ps) a -> (n+1, (show n, PropertyData $
                                       def { dataDescriptorValue = a,
                                             dataDescriptorWritable = True,
                                             dataDescriptorEnumerable = True,
                                             dataDescriptorConfigurable = True }):ps))
         (0 :: Int, []) as)
  i <- createNextInternalId
  let a = Object i
  p <- Lens.use arrayPrototypeObject
  let oi = ObjectInternal {
    objectInternalProperties        = Map.fromList properties,
    objectInternalPrototype         = const $ return (JSExist p),
    objectInternalClass             = const $ return "Array",
    objectInternalExtensible        = const $ return True,
    objectInternalGet               = getImpl,
    objectInternalGetOwnProperty    = getOwnPropertyImpl,
    objectInternalGetProperty       = getPropertyImpl,
    objectInternalPut               = putImpl,
    objectInternalCanPut            = canPutImpl,
    objectInternalHasProperty       = hasPropertyImpl,
    objectInternalDelete            = deleteImpl,
    objectInternalDefaultValue      = defaultValueImpl,
    objectInternalDefineOwnProperty = arrayDefineOwnPropertyImpl,
    objectInternalPrimitiveValue    = Nothing,
    objectInternalConstruct         = Nothing,
    objectInternalCall              = Nothing,
    objectInternalHasInstance       = Nothing,
    objectInternalScope             = Nothing,
    objectInternalFormalParameters  = Nothing,
    objectInternalCode              = Nothing,
    objectInternalTargetFunction    = Nothing,
    objectInternalBoundThis         = Nothing,
    objectInternalBoundArguments    = Nothing,
    objectInternalMatch             = Nothing,
    objectInternalParameterMap      = Nothing }
  mInternalObject a ?= oi
  return a

arrayConstructorCallImpl :: (Functor m, Monad m) => InternalCallType m
arrayConstructorCallImpl a _ args =
  inj <$> arrayConstructorConstructImpl a args

arrayConstructorConstructImpl :: InternalConstructType m
arrayConstructorConstructImpl a args = undefined

arrayDefineOwnPropertyImpl :: (Functor m, Monad m) =>
                              InternalDefineOwnPropertyType m
arrayDefineOwnPropertyImpl a p desc throw = do
  JSJust oldLenDesc <- getOwnProperty a "length" >>= return . toDataDescriptor
  oldLen <- toNumber $ dataDescriptorValue oldLenDesc
  if p == "length"
    then do
    case propertyDescriptorValue desc of
     Nothing -> defineOwnPropertyImpl a p desc throw
     Just v -> do
       newLen <- toUint32 v
       curLen <- toNumber v
       if fromIntegral newLen /= curLen
         then newRangeErrorObject Nothing >>= jsThrow . inj
         else do
         let newLenDesc = desc {
               propertyDescriptorValue = Just (inj $ Number $ fromIntegral newLen) }
         if fromIntegral newLen >= oldLen
           then do
           defineOwnPropertyImpl a "length" newLenDesc throw
           else do
           if not $ dataDescriptorWritable oldLenDesc
             then reject
             else do
             let (newWritable, newLenDesc') =
                   case propertyDescriptorWritable newLenDesc of
                   Just False -> (False, newLenDesc {
                                     propertyDescriptorWritable = Just True })
                   _ -> (True, newLenDesc)
             succeeded <- defineOwnPropertyImpl a "length" newLenDesc' throw
             if not succeeded
               then return False
               else do
               r <- deleteLoop newLen oldLen newLenDesc' newWritable
               if not r
                 then return r
                 else do
                 when (not newWritable) $ void $
                   defineOwnPropertyImpl a "lenght" (def { propertyDescriptorWritable = Just False }) False
                 return True
    else do
    iai <- isArrayIndex p
    if iai
      then do
      index <- toUint32 p
      if fromIntegral index >= oldLen && dataDescriptorWritable oldLenDesc == False
        then reject
        else do
        succeeded <- defineOwnPropertyImpl a p desc False
        if not succeeded
          then reject
          else do
          when (fromIntegral index >= oldLen) $ void $ do
            let oldLenDesc' = oldLenDesc {
                  dataDescriptorValue = inj $ Number $ fromIntegral (index + 1) }
            defineOwnPropertyImpl a "length" (fromDataDescriptor oldLenDesc') False
          return True
      else defineOwnPropertyImpl a p desc throw

  where
    deleteLoop :: UInt32 -> Number -> PropertyDescriptor -> Bool -> JavaScriptM Bool
    deleteLoop newLen oldLen newLenDesc newWritable = do
      if fromIntegral newLen < oldLen
        then do
        let oldLen' = oldLen - 1
        deleteSucceeded <- toString oldLen >>= \s -> delete a s False
        if (not deleteSucceeded)
          then do
          let writable =
                if not newWritable
                then Just False
                else propertyDescriptorWritable newLenDesc
              newLenDesc' = newLenDesc {
                propertyDescriptorValue = Just $ inj (oldLen' + 1),
                propertyDescriptorWritable = writable }
          defineOwnPropertyImpl a "length" newLenDesc' False
          reject
          else
          deleteLoop newLen oldLen' newLenDesc newWritable
        else return True

    isArrayIndex s = do
      ui <- toUint32 p
      c <- toString (Number $ fromIntegral ui)
      return $ c == p && ui /= 2 ^ (32 :: Int) - 1

    reject :: JavaScriptM Bool
    reject =
      if throw
      then newTypeErrorObject Nothing >>= jsThrow . inj
      else return False

newBooleanObject :: Value ->
                    JavaScriptM Object
newBooleanObject v = do
  i <- createNextInternalId
  boolean <- Lens.use booleanPrototypeObject
  let b = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist boolean),
        objectInternalClass             = const $ return "Boolean",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just $ const $ return $ inj (toBoolean v),
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject b ?= oi
  return b

booleanConstructorCallImpl :: (Functor m, Monad m) =>
                              InternalCallType m
booleanConstructorCallImpl _ _ (List vs) = do
  case vs of
   (v:_) -> return . inj $ toBoolean v
   _ -> return (inj False)

booleanConstructorConstructImpl :: (Functor m, Monad m) =>
                                   InternalConstructType m
booleanConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newBooleanObject v
   _ -> newBooleanObject (inj False)

newNumberObject :: Maybe Value ->
                   JavaScriptM Object
newNumberObject mv = do
  i <- createNextInternalId
  nv <- maybe (return (Number 0)) toNumber mv
  number <- Lens.use numberPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist number),
        objectInternalClass             = const $ return "Number",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just $ const $ return $ inj nv,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

numberConstructorCallImpl :: (Functor m, Monad m) =>
                             InternalCallType m
numberConstructorCallImpl _ _ (List vs) = do
  case vs of
   (v:_) -> inj <$> toNumber v
   _ -> return . inj $ Number 0

numberConstructorConstructImpl :: (Functor m, Monad m) =>
                                  InternalConstructType m
numberConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newNumberObject (Just v)
   _ -> newNumberObject Nothing

newErrorObject :: Maybe Value ->
                  JavaScriptM Object
newErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  error <- Lens.use errorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist error),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

errorConstructorCallImpl :: (Functor m, Monad m) =>
                            InternalCallType m
errorConstructorCallImpl e _ args = do
  inj <$> errorConstructorConstructImpl e args

errorConstructorConstructImpl :: (Functor m, Monad m) =>
                                 InternalConstructType m
errorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newErrorObject (Just v)
   _ -> newErrorObject Nothing

errorPrototypeToStringCallImpl :: (Functor m, Monad m) => InternalCallType m
errorPrototypeToStringCallImpl _ v _ = do
  case v of
   ValueObject o -> do
     name <- get o "name"
     name' <- case name of
               ValueUndefined _ -> return "Error"
               _ -> toString name
     msg <- get o "message"
     msg' <- case msg of
              ValueUndefined _ -> return ""
              _ -> toString msg
     if null name'
       then return (inj msg')
       else
       if null msg'
       then return (inj name')
       else return (inj $ name' ++ ": " ++ msg')
   _ -> newTypeErrorObject Nothing >>= jsThrow . inj

newEvalErrorObject :: Maybe Value -> JavaScriptM Object
newEvalErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use evalErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

evalErrorConstructorCallImpl :: (Functor m, Monad m) =>
                                InternalCallType m
evalErrorConstructorCallImpl e _ args = do
  inj <$> evalErrorConstructorConstructImpl e args

evalErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                     InternalConstructType m
evalErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newEvalErrorObject (Just v)
   _ -> newEvalErrorObject Nothing

newRangeErrorObject :: Maybe Value -> JavaScriptM Object
newRangeErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use rangeErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

rangeErrorConstructorCallImpl :: (Functor m, Monad m) =>
                                 InternalCallType m
rangeErrorConstructorCallImpl e _ args = do
  inj <$> rangeErrorConstructorConstructImpl e args

rangeErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                      InternalConstructType m
rangeErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newRangeErrorObject (Just v)
   _ -> newRangeErrorObject Nothing

newReferenceErrorObject :: Maybe Value -> JavaScriptM Object
newReferenceErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use referenceErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

referenceErrorConstructorCallImpl :: (Functor m, Monad m) =>
                                     InternalCallType m
referenceErrorConstructorCallImpl e _ args = do
  inj <$> referenceErrorConstructorConstructImpl e args

referenceErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                          InternalConstructType m
referenceErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newReferenceErrorObject (Just v)
   _ -> newReferenceErrorObject Nothing

newSyntaxErrorObject :: Maybe Value -> JavaScriptM Object
newSyntaxErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use syntaxErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

syntaxErrorConstructorCallImpl :: (Functor m, Monad m) =>
                                  InternalCallType m
syntaxErrorConstructorCallImpl e _ args = do
  inj <$> syntaxErrorConstructorConstructImpl e args

syntaxErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                       InternalConstructType m
syntaxErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newSyntaxErrorObject (Just v)
   _ -> newSyntaxErrorObject Nothing

newTypeErrorObject :: Maybe Value -> JavaScriptM Object
newTypeErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use typeErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

typeErrorConstructorCallImpl :: (Functor m, Monad m) =>
                                InternalCallType m
typeErrorConstructorCallImpl e _ args = do
  inj <$> typeErrorConstructorConstructImpl e args

typeErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                     InternalConstructType m
typeErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newTypeErrorObject (Just v)
   _ -> newTypeErrorObject Nothing

newUriErrorObject :: Maybe Value -> JavaScriptM Object
newUriErrorObject mv = do
  i <- createNextInternalId
  properties <- case mv of
                 Nothing -> return []
                 Just (ValueUndefined _) -> return []
                 Just v -> do
                   s <- toString v
                   return [ ("message", PropertyData $ DataDescriptor {
                                dataDescriptorValue          = inj s,
                                dataDescriptorWritable       = False,
                                dataDescriptorEnumerable     = False,
                                dataDescriptorConfigurable   = False }) ]
  p <- Lens.use uriErrorPrototypeObject
  let n = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.fromList properties,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Error",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject n ?= oi
  return n

uriErrorConstructorCallImpl :: (Functor m, Monad m) =>
                               InternalCallType m
uriErrorConstructorCallImpl e _ args = do
  inj <$> uriErrorConstructorConstructImpl e args

uriErrorConstructorConstructImpl :: (Functor m, Monad m) =>
                                    InternalConstructType m
uriErrorConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newUriErrorObject (Just v)
   _ -> newUriErrorObject Nothing

newStringObject :: Maybe Value ->
                   JavaScriptM Object
newStringObject mv = do
  i <- createNextInternalId
  sv <- maybe (return "") toString mv
  string <- Lens.use stringPrototypeObject
  let s = Object i
      oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist string),
        objectInternalClass             = const $ return "String",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = stringGetOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Just $ stringPrimitiveValueImpl mv,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
  mInternalObject s ?= oi
  return s

stringConstructorCallImpl :: (Functor m, Monad m) => InternalCallType m
stringConstructorCallImpl s _ (List ss) = do
  case ss of
   (s:_) -> inj <$> toString s
   _ -> return (inj "")

stringConstructorConstructImpl :: (Functor m, Monad m) =>
                                  InternalConstructType m
stringConstructorConstructImpl s (List vs) = do
  case vs of
   (v:_) -> newStringObject (Just v)
   _ -> newStringObject Nothing

stringGetOwnPropertyImpl :: (Functor m, Monad m) =>
                            InternalGetOwnPropertyType m
stringGetOwnPropertyImpl s p = do
  desc <- getOwnPropertyImpl s p
  case desc of
   JSJust d -> return $ JSJust d
   JSNothing -> do
     ns <- toInteger p >>= toString . Number . fromIntegral . abs
     if not (ns == p)
       then return (inj Undefined)
       else do
       PrimitiveString str <- primitiveValue s
       index <- toInteger p
       let len = length str
       if fromIntegral len <= index
         then return (inj Undefined)
         else do
         let resultStr = [str !! fromInteger index]
         return $ JSJust def {
           propertyDescriptorValue        = Just (inj resultStr),
           propertyDescriptorWritable     = Just False,
           propertyDescriptorEnumerable   = Just True,
           propertyDescriptorConfigurable = Just False }


stringPrimitiveValueImpl :: (Functor m, Monad m) =>
                            Maybe Value -> InternalPrimitiveValueType m
stringPrimitiveValueImpl mv _ = do
  case mv of
   Just v -> inj <$> toString v
   Nothing -> return (inj "")

regExpMatchImpl = undefined

createArgumentsObject :: Object ->
                         List String ->
                         List Value ->
                         LexicalEnvironment ->
                         Bool ->
                         JavaScriptM Object
createArgumentsObject func (List names) (List args) env strict = do
  let len = length args
  obj <- newObjectObject Nothing
  object <- Lens.use objectPrototypeObject
  internalObject obj %= \oi -> oi { objectInternalClass = const $ return "Arguments",
                                    objectInternalPrototype = const $ return (JSExist object) }
  defineOwnProperty
    obj
    "length"
    (def {
        propertyDescriptorValue = Just (inj (Number (fromIntegral len))),
        propertyDescriptorWritable = Just True,
        propertyDescriptorEnumerable = Just False,
        propertyDescriptorConfigurable = Just True })
     False
  return obj

data Code
  = CodeGlobal Program
  | CodeEval (Maybe SourceElements)
  | CodeFunction Object (List Value)

createNextInternalId :: JavaScriptM InternalId
createNextInternalId = do
  next <- Lens.use nextInternalId
  nextInternalId .= succ next
  return next

newObjectObject :: Maybe Value -> JavaScriptM Object
newObjectObject mv =
  case mv of
   Just v ->
     case v of
      ValueObject o -> do
        return o
      _ ->
        if typeOf v == TypeString ||
           typeOf v == TypeBoolean ||
           typeOf v == TypeNumber
        then toObject v
        else createObject
   _ -> createObject
  where
    createObject = do
      i <- createNextInternalId
      let o = Object i
      p <- Lens.use objectPrototypeObject
      let oi = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist p),
        objectInternalClass             = const $ return "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = functionGetImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Just functionConstructImpl,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }
      mInternalObject o ?= oi
      return o

objectConstructorCallImpl :: (Functor m, Monad m) =>
                             InternalCallType m
objectConstructorCallImpl o _ lvs@(List vs) =
  case vs of
   (ValueNull _:_) -> inj <$> objectConstructorConstructImpl o lvs
   (ValueUndefined _:_) -> inj <$> objectConstructorConstructImpl o lvs
   [] -> inj <$> objectConstructorConstructImpl o lvs
   (v:_) -> inj <$> toObject v

objectConstructorConstructImpl :: (Functor m, Monad m) =>
                                  InternalConstructType m
objectConstructorConstructImpl _ (List vs) = do
  case vs of
   (v:_) -> newObjectObject (Just v)
   _ -> newObjectObject Nothing


defineOwnPropertyImpl :: (Functor m, Monad m) =>
                         InternalDefineOwnPropertyType m
defineOwnPropertyImpl o p desc throw = do
  mCurrent <- getOwnProperty o p
  e <- extensible o
  case (mCurrent, e) of
   (JSNothing, False) -> reject
   (JSNothing, True) -> do
     if isGenericDescriptor (JSJust desc) || isDataDescriptor (JSJust desc)
       then do
       let dp = PropertyData
                DataDescriptor {
                  dataDescriptorValue        =
                     maybe (inj Undefined) id (propertyDescriptorValue desc),
                  dataDescriptorWritable     =
                    maybe False id (propertyDescriptorWritable desc),
                  dataDescriptorEnumerable   =
                    maybe False id (propertyDescriptorEnumerable desc),
                  dataDescriptorConfigurable =
                    maybe False id (propertyDescriptorConfigurable desc) }
       property o p ?= dp
       else do
       let ap = PropertyAccessor
                AccessorDescriptor {
                  accessorDescriptorGet          =
                     maybe JSNothing JSJust (propertyDescriptorGet desc),
                  accessorDescriptorSet          =
                    maybe JSNothing JSJust (propertyDescriptorSet desc),
                  accessorDescriptorEnumerable   =
                    maybe False id (propertyDescriptorEnumerable desc),
                  accessorDescriptorConfigurable =
                    maybe False id (propertyDescriptorConfigurable desc) }
       property o p ?= ap
     return True
   (JSJust current, _) -> do
     if (propertyDescriptorValue desc == Nothing ||
         (sameValue <$>
          propertyDescriptorValue desc <*>
          propertyDescriptorValue current) == Just True) &&
        (propertyDescriptorGet desc == Nothing ||
         (sameValue <$>
          propertyDescriptorGet desc <*>
          propertyDescriptorGet current) == Just True) &&
        (propertyDescriptorSet desc == Nothing ||
         (sameValue <$>
          propertyDescriptorSet desc <*>
          propertyDescriptorSet current) == Just True) &&
        (propertyDescriptorWritable desc == Nothing ||
         (sameValue <$>
          propertyDescriptorWritable desc <*>
          propertyDescriptorWritable current) == Just True) &&
        (propertyDescriptorEnumerable desc == Nothing ||
         (sameValue <$>
          propertyDescriptorEnumerable desc <*>
          propertyDescriptorEnumerable current) == Just True) &&
        (propertyDescriptorConfigurable desc == Nothing ||
         (sameValue <$>
          propertyDescriptorConfigurable desc <*>
          propertyDescriptorConfigurable current) == Just True)
       then return True
       else
       if (propertyDescriptorConfigurable current == Just False)
       then
         if (propertyDescriptorConfigurable desc == Just True)
         then reject
         else
           if ((==) <$>
               (propertyDescriptorEnumerable desc) <*>
               (propertyDescriptorEnumerable current)) ==
              Just False
           then reject
           else checkDescriptor current
       else checkDescriptor current
  where
    reject =
      if throw
      then newTypeErrorObject Nothing >>= jsThrow . inj
      else return False
    checkDescriptor current = do
      if isGenericDescriptor (JSJust desc)
        then setValue
        else do
        case (isDataDescriptor (JSJust current), isDataDescriptor (JSJust desc)) of
         (cb, db) | cb /= db -> do
                      if propertyDescriptorConfigurable current == Just False
                        then reject
                        else
                        if isDataDescriptor (JSJust current)
                        then do
                          error "Convert B"
                        else do
                          error "Convert C"
         (True, True) -> do
           if propertyDescriptorConfigurable current == Just False
             then
             if propertyDescriptorWritable current == Just False &&
                propertyDescriptorWritable desc == Just True
             then reject
             else
               if propertyDescriptorWritable current == Just False &&
                  propertyDescriptorWritable desc == Just True
               then reject
               else
                 case (propertyDescriptorWritable current,
                       propertyDescriptorValue desc,
                       propertyDescriptorValue current) of
                  (Just False, Just dv, Just cv) | not $ sameValue dv cv -> reject
                  _ -> setValue
             else setValue
         _ -> do
           if propertyDescriptorConfigurable current == Just False
             then do
             case (propertyDescriptorSet desc,
                   propertyDescriptorSet current) of
              (Just ds, Just cs) | not $ sameValue ds cs -> reject
              _ -> do
                case (propertyDescriptorSet desc,
                      propertyDescriptorGet current) of
                 (Just dg, Just cg) | not $ sameValue dg cg -> reject
                 _ -> setValue
             else setValue
    setValue = do
      property o p %=
        \(Just prop) ->
         Just $
         case prop of
          PropertyData prop ->
            PropertyData prop {
              dataDescriptorValue        =
                 maybe
                 (dataDescriptorValue prop)
                 id
                 (propertyDescriptorValue desc),
              dataDescriptorWritable     =
                maybe
                (dataDescriptorWritable prop)
                id
                (propertyDescriptorWritable desc),
              dataDescriptorEnumerable   =
                maybe
                (dataDescriptorEnumerable prop)
                id
                (propertyDescriptorEnumerable desc),
              dataDescriptorConfigurable =
                maybe
                (dataDescriptorConfigurable prop)
                id
                (propertyDescriptorConfigurable desc) }
          PropertyAccessor prop ->
            PropertyAccessor prop {
              accessorDescriptorGet          =
                 maybe
                 (accessorDescriptorGet prop)
                 JSJust
                 (propertyDescriptorGet desc),
              accessorDescriptorSet          =
                   maybe
                   (accessorDescriptorSet prop)
                   JSJust
                   (propertyDescriptorSet desc),
              accessorDescriptorEnumerable   =
                maybe
                (accessorDescriptorEnumerable prop)
                id
                (propertyDescriptorEnumerable desc),
              accessorDescriptorConfigurable =
                maybe
                (accessorDescriptorConfigurable prop)
                id
                (propertyDescriptorConfigurable desc) }
      return True

toPrimitive :: (SubType v Value) =>
               v -> Maybe Hint -> JavaScriptM Primitive
toPrimitive v mpt =
  case inj v of
   ValueObject o -> defaultValue o mpt
   ValuePrimitive p -> return p

toBoolean :: (SubType v Value) =>
             v -> Bool
toBoolean v =
  case (inj v :: Value) of
   (ValueUndefined _) -> False
   (ValueNull _) -> False
   (ValueBool b) -> b
   (ValueNumber n) ->
     if isNaN n || n == Number 0
     then False
     else True
   (ValueString s) -> not $ null s
   (ValueObject _) -> True

toNumber :: (SubType v Value) =>
            v -> JavaScriptM Number
toNumber v =
  case (inj v :: Value) of
   ValueUndefined _ -> return nan
   ValueNull _ -> return $ Number 0
   ValueBool b -> return $ if b then Number 1 else Number 0
   ValueNumber n -> return n
   ValueString s -> do
     case parseString s of
      Just d -> return $ Number d
      Nothing -> return nan
   ValueObject _ -> toPrimitive v (Just HintNumber) >>= toNumber

toInteger :: (SubType v Value) =>
             v -> JavaScriptM Integer
toInteger v = do
  number <- toNumber v
  if isNaN number
    then return 0
    else return $ floor (signum number) * floor (abs number)

toInt32 :: (SubType v Value) =>
           v -> JavaScriptM Int32
toInt32 v = do
  number <- toNumber v
  if isNaN number || isInfinite number || number == Number 0
    then return 0
    else do
    let posInt = floor (signum number) * floor (abs number)
        int32bit = posInt `mod` 2 ^ (32 :: Int)
    if int32bit >= 2 ^ (31 :: Int)
      then return $ fromInteger $ int32bit - 2 ^ (32 :: Int)
      else return $ fromInteger int32bit

toUint32 :: (SubType v Value) =>
            v -> JavaScriptM UInt32
toUint32 v = do
  number <- toNumber v
  if isNaN number || isInfinite number || number == Number 0
    then return 0
    else do
    let posInt = floor (signum number) * floor (abs number)
        int32bit = posInt `mod` 2 ^ (32 :: Int)
    return $ fromInteger int32bit

toUint16 :: (SubType v Value) =>
            v -> JavaScriptM UInt16
toUint16 v = do
  number <- toNumber v
  if isNaN number || isInfinite number || number == Number 0
    then return 0
    else do
    let posInt = floor (signum number) * floor (abs number)
        int16bit = posInt `mod` 2 ^ (16 :: Int)
    return $ fromInteger int16bit

primitiveToString :: (SubType v Primitive) =>
                     v -> String
primitiveToString p =
  case (inj p :: Primitive) of
   PrimitiveUndefined _ -> "undefined"
   PrimitiveNull _ -> "null"
   PrimitiveBool b ->  if b then "true" else "false"
   PrimitiveNumber (Number n) -> show n
   PrimitiveString s -> s

toString :: (SubType v Value) =>
            v -> JavaScriptM String
toString v =
  case (inj v :: Value) of
   ValuePrimitive p -> return $ primitiveToString p
   ValueObject _ -> toPrimitive v (Just HintString) >>= toString

toObject :: Value -> JavaScriptM Object
toObject v =
  case v of
   ValueUndefined _ -> newTypeErrorObject Nothing >>= jsThrow . inj
   ValueNull _ -> newTypeErrorObject Nothing >>= jsThrow . inj
   ValueBool b -> newBooleanObject (inj b)
   ValueNumber n -> newNumberObject (inj n)
   ValueString s -> newStringObject (inj s)
   ValueObject o -> return o

checkObjectCoercible :: Value -> JavaScriptM ()
checkObjectCoercible v = void $ toObjectCoercible v

toObjectCoercible :: Value -> JavaScriptM (Object + Number + String + Bool)
toObjectCoercible (ValueUndefined _) = newTypeErrorObject Nothing >>= jsThrow . inj
toObjectCoercible (ValueNull _) = newTypeErrorObject Nothing >>= jsThrow . inj
toObjectCoercible (ValueObject o) = return $ inj o
toObjectCoercible (ValueNumber n) = return $ inj n
toObjectCoercible (ValueString s) = return $ inj s
toObjectCoercible (ValueBool b) = return $ inj b

isCallable :: Value -> JavaScriptM Bool
isCallable v = isJust <$> toCallable v

toCallable :: Value -> JavaScriptM (Maybe Object)
toCallable (ValueObject o) = do
  ObjectInternal {..} <- Lens.use $ internalObject o
  if isJust objectInternalCall
    then return $ Just o
    else return Nothing
toCallable _ = return Nothing

sameValue :: (SubType v1 Value, SubType v2 Value) =>
             v1 -> v2 -> Bool
sameValue x y = do
  case (inj x :: Value, inj y :: Value) of
   (ValueUndefined _, ValueUndefined _) -> True
   (ValueNull _, ValueNull _) -> True
   (ValueNumber (Number nx), ValueNumber (Number ny)) ->
     if isNaN nx && isNaN ny
     then True
     else
       if nx == 0 && isNegativeZero ny ||
          isNegativeZero nx && ny == 0
       then False
       else
         if nx == ny
         then True
         else False
   (ValueString sx, ValueString sy) -> sx == sy
   (ValueBool bx, ValueBool by) -> bx == by
   (ValueObject ox, ValueObject oy) -> ox == oy
   _ -> False

compare :: (SubType v1 Value, SubType v2 Value) =>
           v1 -> v2 -> JavaScriptM Bool
compare x y = do
  case (inj x :: Value, inj y :: Value) of
   (ValueUndefined _, ValueUndefined _) -> return True
   (ValueNull _, ValueNull _) -> return True
   (ValueNumber nx, ValueNumber ny) -> return (nx == ny)
   (ValueString sx, ValueString sy) -> return (sx == sy)
   (ValueBool bx, ValueBool by) -> return (bx == by)
   (ValueObject ox, ValueObject oy) -> return (ox == oy)
   (ValueNull _, ValueUndefined _) -> return True
   (ValueUndefined _, ValueNull _) -> return True
   (ValueNumber nx, ValueString sy) -> do
     ny <- toNumber y
     compare nx ny
   (ValueString sx, ValueNumber ny) -> do
     nx <- toNumber x
     compare nx ny
   (ValueBool bx, _) -> do
     nx <- toNumber bx
     compare nx y
   (_, ValueBool by) -> do
     ny <- toNumber by
     compare x ny
   (ValueString sx, ValueObject oy) -> do
     py <- toPrimitive oy Nothing
     compare sx py
   (ValueNumber nx, ValueObject oy) -> do
     py <- toPrimitive oy Nothing
     compare nx py
   (ValueObject ox, ValueString sy) -> do
     px <- toPrimitive ox Nothing
     compare px sy
   (ValueObject ox, ValueNumber ny) -> do
     px <- toPrimitive ox Nothing
     compare px ny
   _ -> return False

compareStrict :: Value -> Value -> Bool
compareStrict x y = do
  case (x, y) of
   (ValueUndefined _, ValueUndefined _) -> True
   (ValueNull _, ValueNull _) -> True
   (ValueNumber nx, ValueNumber ny) -> (nx == ny)
   (ValueString sx, ValueString sy) -> (sx == sy)
   (ValueBool bx, ValueBool by) -> (bx == by)
   (ValueObject ox, ValueObject oy) -> (ox == oy)
   _ -> False

compareLess :: Value -> Value -> Bool -> JavaScriptM (JSMaybe Bool)
compareLess x y leftFirst = do
  (px, py) <- if leftFirst
    then do
    px <- toPrimitive x (Just HintNumber)
    py <- toPrimitive y (Just HintNumber)
    return (px, py)
    else do
    py <- toPrimitive y (Just HintNumber)
    px <- toPrimitive x (Just HintNumber)
    return (px, py)
  case (px, py) of
   (PrimitiveString sx, PrimitiveString sy) -> do
     return $ JSJust (sx < sy)
   _ -> do
    nx <- toNumber px
    ny <- toNumber py
    if isNaN nx || isNaN ny
      then return JSNothing
      else return $ JSJust (nx < ny)

operatorPlus :: (SubType v1 CallValue, SubType v2 CallValue) =>
                v1 -> v2 -> JavaScriptM Value
operatorPlus lref rref = do
  lval <- getValue lref
  rval <- getValue rref
  lprim <- toPrimitive lval Nothing
  rprim <- toPrimitive rval Nothing
  if typeOf lprim == TypeString || typeOf rprim == TypeString
    then liftM2 (\l r -> inj $ l ++ r) (toString lprim) (toString rprim)
    else liftM2 (\l r -> inj $ l + r) (toNumber lprim) (toNumber rprim)

operatorMinus :: (SubType v1 CallValue, SubType v2 CallValue) =>
                 v1 -> v2 -> JavaScriptM Number
operatorMinus lref rref = do
  lval <- getValue lref
  rval <- getValue rref
  lnum <- toNumber lval
  rnum <- toNumber rval
  return $ lnum - rnum

operatorMult :: (SubType v1 CallValue, SubType v2 CallValue) =>
                v1 -> v2 -> JavaScriptM Number
operatorMult left right = do
  leftValue <- getValue left
  rightValue <- getValue right
  leftNum <- toNumber leftValue
  rightNum <- toNumber rightValue
  return $ leftNum * rightNum

operatorDiv :: (SubType v1 CallValue, SubType v2 CallValue) =>
               v1 -> v2 -> JavaScriptM Number
operatorDiv left right = do
  leftValue <- getValue left
  rightValue <- getValue right
  leftNum <- toNumber leftValue
  rightNum <- toNumber rightValue
  return $ leftNum / rightNum

operatorMod :: (SubType v1 CallValue, SubType v2 CallValue) =>
               v1 -> v2 -> JavaScriptM Number
operatorMod left right = do
  leftValue <- getValue left
  rightValue <- getValue right
  leftNum <- toNumber leftValue
  rightNum <- toNumber rightValue
  return $ leftNum `mod'` rightNum

operatorLeftShift :: (SubType v1 CallValue, SubType v2 CallValue) =>
                     v1 -> v2 -> JavaScriptM Number
operatorLeftShift left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toInt32 lval
  rnum <- toUint32 rval
  let shiftCount = fromInteger . Prelude.toInteger $ rnum .&. 0x1F
  return $ Number $ fromIntegral $ shiftL lnum shiftCount

operatorSignedRightShift :: (SubType v1 CallValue, SubType v2 CallValue) =>
                            v1 -> v2 -> JavaScriptM Number
operatorSignedRightShift left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toInt32 lval
  rnum <- toUint32 rval
  let shiftCount = fromInteger . Prelude.toInteger $ rnum .&. 0x1F
  return $ Number $ fromIntegral $ shiftR lnum shiftCount

operatorUnsignedRightShift :: (SubType v1 CallValue, SubType v2 CallValue) =>
                              v1 -> v2 -> JavaScriptM Number
operatorUnsignedRightShift left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toUint32 lval
  rnum <- toUint32 rval
  let shiftCount = fromInteger . Prelude.toInteger $ rnum .&. 0x1F
  return $ Number $ fromIntegral $ shiftR lnum shiftCount

operatorBitwiseAnd :: (SubType v1 CallValue, SubType v2 CallValue) =>
                      v1 -> v2 -> JavaScriptM Number
operatorBitwiseAnd left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toInt32 lval
  rnum <- toInt32 rval
  return $ Number $ fromIntegral $ lnum .&. rnum

operatorBitwiseXor :: (SubType v1 CallValue, SubType v2 CallValue) =>
                      v1 -> v2 -> JavaScriptM Number
operatorBitwiseXor left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toInt32 lval
  rnum <- toInt32 rval
  return $ Number $ fromIntegral $ lnum `xor` rnum

operatorBitwiseOr :: (SubType v1 CallValue, SubType v2 CallValue) =>
                     v1 -> v2 -> JavaScriptM Number
operatorBitwiseOr left right = do
  lval <- getValue left
  rval <- getValue right
  lnum <- toInt32 lval
  rnum <- toInt32 rval
  return $ Number $ fromIntegral $ lnum .|. rnum
