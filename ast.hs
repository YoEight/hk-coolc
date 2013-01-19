module AST where

data Program name = Program { programClasses :: [Class name] } deriving Show

data Class name = Class { className     :: String
                        , classParent   :: String
                        , classAttrs    :: [Attr name]
                        , classMethods  :: [Method name]} deriving Show

data Attr name = Attr { attrName    :: String 
                      , attrTyp     :: String
                      , attrPayload :: Maybe (Expr name)} deriving Show

data Method name = Method { methodName    :: String 
                          , methodType    :: String
                          , methodFormals :: [Formal]
                          , methodPayload :: Expr name } deriving Show

data Formal = Formal { formalName :: String
                     , formalType :: String} deriving Show

data Expr name = Assign name (Expr name)
               | Block [Expr name]
               | BoolConst Bool
               | Comp (Expr name)
               | Cond (Expr name) (Expr name) (Maybe (Expr name))
               | Dispatch String (Maybe String) (Expr name) [Expr name]
               | Divide (Expr name) (Expr name)
               | Eq (Expr name) (Expr name)
               | IntConst Int
               | Isvoid (Expr name)
               | Leq (Expr name) (Expr name)
               | Let [(String, String, Maybe (Expr name))] (Expr name) 
               | Loop (Expr name) (Expr name)
               | Lt (Expr name) (Expr name)
               | Gt (Expr name) (Expr name)
               | Geq (Expr name) (Expr name)
               | Mul (Expr name) (Expr name)
               | Neg (Expr name)
               | New String
               | NoExpr
               | Object name
               | Plus (Expr name) (Expr name)
               | StaticDispatch name [Expr name]
               | StringConst String
               | Sub (Expr name) (Expr name)
               | Tild (Expr name)
               | Not (Expr name)
               | Case (Expr name) [(String, String, (Expr name))] deriving Show
