module Language.JavaScript.AST
       where

data IdentName =
  IdentName String
  deriving (Eq, Show)

data Ident =
  Ident IdentName
  deriving (Eq, Show)

data Literal
  = LiteralNull NullLit
  | LiteralBool BoolLit
  | LiteralNum NumLit
  | LiteralString StringLit
  | LiteralRegExp RegExpLit
  deriving (Eq, Show)

data NullLit
  = NullLit
  deriving (Eq, Show)

data BoolLit
  = BoolLit Bool
  deriving (Eq, Show)

data NumLit
  = NumLit Double
  deriving (Eq, Show)

data StringLit
  = StringLit String
  deriving (Eq, Show)

data RegExpLit
  = RegExpLit (String, String)
  deriving (Eq, Show)

data PrimExpr
  = PrimExprThis
  | PrimExprIdent Ident
  | PrimExprLiteral Literal
  | PrimExprArray ArrayLit
  | PrimExprObject ObjectLit
  | PrimExprParens Expr
  deriving (Eq, Show)

data ArrayLit
  = ArrayLitH (Maybe Elision)
  | ArrayLit ElementList
  | ArrayLitT ElementList (Maybe Elision)
  deriving (Eq, Show)

data ElementList
  = ElementList (Maybe Elision) AssignExpr
  | ElementListCons ElementList (Maybe Elision) AssignExpr
  deriving (Eq, Show)

data Elision
  = ElisionComma
  | ElisionCons Elision
  deriving (Eq, Show)

data ObjectLit
  = ObjectLitEmpty
  | ObjectLit PropList
  deriving (Eq, Show)

data PropList
  = PropListAssign PropAssign
  | PropListCons PropList PropAssign
  deriving (Eq, Show)

data PropAssign
  = PropAssignField PropName AssignExpr
  | PropAssignGet PropName FuncBody
  | PropAssignSet PropName PropSetParamList FuncBody
  deriving (Eq, Show)

data PropSetParamList
  = PropSetParamList Ident
  deriving (Eq, Show)

data PropName
  = PropNameId IdentName
  | PropNameStr StringLit
  | PropNameNum NumLit
  deriving (Eq, Show)

data MemberExpr
  = MemberExprPrim PrimExpr
  | MemberExprFunc FuncExpr
  | MemberExprArray MemberExpr Expr
  | MemberExprDot MemberExpr IdentName
  | MemberExprNew MemberExpr Arguments
  deriving (Eq, Show)

data NewExpr
  = NewExprMember MemberExpr
  | NewExprNew NewExpr
  deriving (Eq, Show)

data CallExpr
  = CallExprMember MemberExpr Arguments
  | CallExprCall CallExpr Arguments
  | CallExprArray CallExpr Expr
  | CallExprDot CallExpr IdentName
  deriving (Eq, Show)

data Arguments
  = ArgumentsEmpty
  | Arguments ArgumentList
  deriving (Eq, Show)

data ArgumentList
  = ArgumentList AssignExpr
  | ArgumentListCons ArgumentList AssignExpr
  deriving (Eq, Show)

data LeftExpr
  = LeftExprNewExpr NewExpr
  | LeftExprCallExpr CallExpr
  deriving (Eq, Show)

data PostFixExpr
  = PostFixExprLeftExpr LeftExpr
  | PostFixExprPostInc LeftExpr
  | PostFixExprPostDec LeftExpr
  deriving (Eq, Show)

data UExpr
  = UExprPostFix PostFixExpr
  | UExprDelete UExpr
  | UExprVoid UExpr
  | UExprTypeOf UExpr
  | UExprDoublePlus UExpr
  | UExprDoubleMinus UExpr
  | UExprUnaryPlus UExpr
  | UExprUnaryMinus UExpr
  | UExprBitNot UExpr
  | UExprNot UExpr
  deriving (Eq, Show)

data MultExpr
  = MultExpr UExpr
  | MultExprMult MultExpr UExpr
  | MultExprDiv MultExpr UExpr
  | MultExprMod MultExpr UExpr
  deriving (Eq, Show)

data AddExpr
  = AddExpr MultExpr
  | AddExprAdd AddExpr MultExpr
  | AddExprSub AddExpr MultExpr
  deriving (Eq, Show)

data ShiftExpr
  = ShiftExpr AddExpr
  | ShiftExprLeft ShiftExpr AddExpr
  | ShiftExprRight ShiftExpr AddExpr
  | ShiftExprRightZero ShiftExpr AddExpr
  deriving (Eq, Show)

data RelExpr
  = RelExpr ShiftExpr
  | RelExprLess RelExpr ShiftExpr
  | RelExprGreater RelExpr ShiftExpr
  | RelExprLessEq RelExpr ShiftExpr
  | RelExprGreaterEq RelExpr ShiftExpr
  | RelExprInstanceOf RelExpr ShiftExpr
  | RelExprIn RelExpr ShiftExpr
  deriving (Eq, Show)

data RelExprNoIn
  = RelExprNoIn ShiftExpr
  | RelExprNoInLess RelExprNoIn ShiftExpr
  | RelExprNoInGreater RelExprNoIn ShiftExpr
  | RelExprNoInLessEq RelExprNoIn ShiftExpr
  | RelExprNoInGreaterEq RelExprNoIn ShiftExpr
  | RelExprNoInInstanceOf RelExprNoIn ShiftExpr
  deriving (Eq, Show)

data EqExpr
  = EqExpr RelExpr
  | EqExprEq EqExpr RelExpr
  | EqExprNotEq EqExpr RelExpr
  | EqExprStrictEq EqExpr RelExpr
  | EqExprStrictNotEq EqExpr RelExpr
  deriving (Eq, Show)

data EqExprNoIn
  = EqExprNoIn RelExprNoIn
  | EqExprNoInEq EqExprNoIn RelExprNoIn
  | EqExprNoInNotEq EqExprNoIn RelExprNoIn
  | EqExprNoInStrictEq EqExprNoIn RelExprNoIn
  | EqExprNoInStrictNotEq EqExprNoIn RelExprNoIn
  deriving (Eq, Show)

data BitAndExpr
  = BitAndExpr EqExpr
  | BitAndExprAnd BitAndExpr EqExpr
  deriving (Eq, Show)

data BitAndExprNoIn
  = BitAndExprNoIn EqExprNoIn
  | BitAndExprNoInAnd BitAndExprNoIn EqExprNoIn
  deriving (Eq, Show)

data BitXorExpr
  = BitXorExpr BitAndExpr
  | BitXorExprXor BitXorExpr BitAndExpr
  deriving (Eq, Show)

data BitXorExprNoIn
  = BitXorExprNoIn BitAndExprNoIn
  | BitXorExprNoInXor BitXorExprNoIn BitAndExprNoIn
  deriving (Eq, Show)

data BitOrExpr
  = BitOrExpr BitXorExpr
  | BitOrExprOr BitOrExpr BitXorExpr
  deriving (Eq, Show)

data BitOrExprNoIn
  = BitOrExprNoIn BitXorExprNoIn
  | BitOrExprNoInOr BitOrExprNoIn BitXorExprNoIn
  deriving (Eq, Show)

data LogicalAndExpr
  = LogicalAndExpr BitOrExpr
  | LogicalAndExprAnd LogicalAndExpr BitOrExpr
  deriving (Eq, Show)

data LogicalAndExprNoIn
  = LogicalAndExprNoIn BitOrExprNoIn
  | LogicalAndExprNoInAnd LogicalAndExprNoIn BitOrExprNoIn
  deriving (Eq, Show)

data LogicalOrExpr
  = LogicalOrExpr LogicalAndExpr
  | LogicalOrExprOr LogicalOrExpr LogicalAndExpr
  deriving (Eq, Show)

data LogicalOrExprNoIn
  = LogicalOrExprNoIn LogicalAndExprNoIn
  | LogicalOrExprNoInOr LogicalOrExprNoIn LogicalAndExprNoIn
  deriving (Eq, Show)

data CondExpr
  = CondExpr LogicalOrExpr
  | CondExprIf LogicalOrExpr AssignExpr AssignExpr
  deriving (Eq, Show)

data CondExprNoIn
  = CondExprNoIn LogicalOrExprNoIn
  | CondExprNoInIf LogicalOrExprNoIn AssignExpr AssignExpr
  deriving (Eq, Show)

data AssignExpr
  = AssignExprCondExpr CondExpr
  | AssignExprAssign LeftExpr AssignOp AssignExpr
  deriving (Eq, Show)

data AssignExprNoIn
  = AssignExprNoInCondExpr CondExprNoIn
  | AssignExprNoInAssign LeftExpr AssignOp AssignExprNoIn
  deriving (Eq, Show)

data AssignOp
  = AssignOpNormal
  | AssignOpMult
  | AssignOpDiv
  | AssignOpMod
  | AssignOpPlus
  | AssignOpMinus
  | AssignOpShiftLeft
  | AssignOpShiftRight
  | AssignOpShiftRightZero
  | AssignOpBitAnd
  | AssignOpBitXor
  | AssignOpBitOr
  deriving (Eq, Show)

data Expr
  = Expr AssignExpr
  | ExprCons Expr AssignExpr
  deriving (Eq, Show)

data ExprNoIn
  = ExprNoIn AssignExprNoIn
  | ExprNoInCons ExprNoIn AssignExprNoIn
  deriving (Eq, Show)

data Stmt
  = StmtBlock Block
  | StmtVar VarStmt
  | StmtEmpty EmptyStmt
  | StmtExpr ExprStmt
  | StmtIf IfStmt
  | StmtIt ItStmt
  | StmtCont ContStmt
  | StmtBreak BreakStmt
  | StmtReturn ReturnStmt
  | StmtWith WithStmt
  | StmtLabelled LabelledStmt
  | StmtSwitch SwitchStmt
  | StmtThrow ThrowStmt
  | StmtTry TryStmt
  | StmtDbg DbgStmt
  deriving (Eq, Show)

data Block
  = Block (Maybe StmtList)
  deriving (Eq, Show)

data StmtList
  = StmtList Stmt
  | StmtListCons StmtList Stmt
  deriving (Eq, Show)

data VarStmt
  = VarStmt VarDeclList
  deriving (Eq, Show)

data VarDeclList
  = VarDeclList VarDecl
  | VarDeclListCons VarDeclList VarDecl
  deriving (Eq, Show)

data VarDeclListNoIn
  = VarDeclListNoIn VarDeclNoIn
  | VarDeclListNoInCons VarDeclListNoIn VarDeclNoIn
  deriving (Eq, Show)

data VarDecl
  = VarDecl Ident (Maybe Initialiser)
  deriving (Eq, Show)

data VarDeclNoIn
  = VarDeclNoIn Ident (Maybe InitialiserNoIn)
  deriving (Eq, Show)

data Initialiser
  = Initialiser AssignExpr
  deriving (Eq, Show)

data InitialiserNoIn
  = InitialiserNoIn AssignExprNoIn
  deriving (Eq, Show)

data EmptyStmt
  = EmptyStmt
  deriving (Eq, Show)

data ExprStmt
  = ExprStmt Expr
  deriving (Eq, Show)

data IfStmt
  = IfStmtIfElse Expr Stmt Stmt
  | IfStmtIf Expr Stmt
  deriving (Eq, Show)

data ItStmt
  = ItStmtDoWhile Stmt Expr
  | ItStmtWhile Expr Stmt
  | ItStmtFor (Maybe ExprNoIn) (Maybe Expr) (Maybe Expr) Stmt
  | ItStmtForVar VarDeclListNoIn (Maybe Expr) (Maybe Expr) Stmt
  | ItStmtForIn LeftExpr Expr Stmt
  | ItStmtForVarIn VarDeclNoIn Expr Stmt
  deriving (Eq, Show)

data ContStmt
  = ContStmt
  | ContStmtLabelled Ident
  deriving (Eq, Show)

data BreakStmt
  = BreakStmt
  | BreakStmtLabelled Ident
  deriving (Eq, Show)

data ReturnStmt
  = ReturnStmt
  | ReturnStmtExpr Expr
  deriving (Eq, Show)

data WithStmt
  = WithStmt Expr Stmt
  deriving (Eq, Show)

data SwitchStmt
  = SwitchStmt Expr CaseBlock
  deriving (Eq, Show)

data CaseBlock
  = CaseBlock (Maybe CaseClauses)
  | CaseBlockDefault (Maybe CaseClauses) DefaultClause (Maybe CaseClauses)
  deriving (Eq, Show)

data CaseClauses
  = CaseClauses CaseClause
  | CaseClausesCons CaseClauses CaseClause
  deriving (Eq, Show)

data CaseClause
  = CaseClause Expr (Maybe StmtList)
  deriving (Eq, Show)

data DefaultClause
  = DefaultClause (Maybe StmtList)
  deriving (Eq, Show)

data LabelledStmt
  = LabelledStmt Ident Stmt
  deriving (Eq, Show)

data ThrowStmt
  = ThrowStmt Expr
  deriving (Eq, Show)

data TryStmt
  = TryStmtBC Block Catch
  | TryStmtBF Block Finally
  | TryStmtBCF Block Catch Finally
  deriving (Eq, Show)

data Catch
  = Catch Ident Block
  deriving (Eq, Show)

data Finally
  = Finally Block
  deriving (Eq, Show)

data DbgStmt
  = DbgStmt
  deriving (Eq, Show)

data FuncDecl
  = FuncDecl Ident (Maybe FormalParamList) FuncBody
  deriving (Eq, Show)

data FuncExpr
  = FuncExpr (Maybe Ident) (Maybe FormalParamList) FuncBody
  deriving (Eq, Show)

data FormalParamList
  = FormalParamList Ident
  | FormalParamListCons FormalParamList Ident
  deriving (Eq, Show)

data FuncBody =
  FuncBody (Maybe SourceElements)
  deriving (Eq, Show)

data Program =
  Program (Maybe SourceElements)
  deriving (Eq, Show)

data SourceElements
  = SourceElements SourceElement
  | SourceElementsCons SourceElements SourceElement
  deriving (Eq, Show)

data SourceElement
  = SourceElementStmt Stmt
  | SourceElementFuncDecl FuncDecl
  deriving (Eq, Show)
