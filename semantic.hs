module Semantic where

import Prelude hiding (foldr, foldl)

import Control.Monad.Trans.State

import Data.Maybe
import Data.Foldable
import Data.Traversable
import Parser
import qualified Data.IntMap as I

import Unique
import UniqueFM
import Control.Monad

type Type   = String
type Parent = String
type InheritanceGraph = I.IntMap Int

data Env a b c = Env { envClasses   :: UniqueFM a
                     , envFeatures  :: UniqueFM b
                     , envLocals    :: UniqueFM c } 

type ClassSet a   = UniqueFM (Class a)
type FeatureSet a = UniqueFM (Feature a)
type LocalSet a   = UniqueFM (a, a, Maybe (Expr a))

type StateTEnvName m a = StateT(Env (Class Name) (Feature Name) (Name, Name, Maybe (Expr Name))) m a
type StateEnvName a = State (Env (Class Name) (Feature Name) (Name, Name, (Maybe (Expr Name)))) a

failure :: String -> StateTEnvName (Either String) a
failure msg = StateT $ \_ -> Left msg

object_name = mkSimpleName "Object"
io_name = mkSimpleName "IO"
string_name = mkSimpleName "String"
int_name = mkSimpleName "Int"
bool_name = mkSimpleName "Bool"

emptyEnv :: Env a b c
emptyEnv = Env emptyUFM emptyUFM emptyUFM

checkInheritanceGraph :: Class Name -> State (UniqueFM (), ClassSet Name) (Maybe String)
checkInheritanceGraph (Class _ parent _)
  | isSystemClass parent = return Nothing
  | otherwise = do
    (passed_map, class_env) <- get
    case memberUFM_u (nameUnique parent) passed_map  of
      True  -> return $ Just $ "Cyclic class dependency on " ++ (nameLabel parent)
      False -> case lookupUFM_u (nameUnique parent) class_env of
        Nothing           -> return $ Just $ "Unknown class " ++ (nameLabel parent)
        Just parent_class -> do
          put (insertUFM_u (nameUnique parent) () passed_map, class_env)
          checkInheritanceGraph parent_class
          
--namer :: StateEnvName (Program Name)
--namer = error "todo"

validateProgram :: Program Name -> StateTEnvName (Either String) ()
validateProgram = traverse_ validateClass . programClasses

validateClass :: Class Name -> StateTEnvName (Either String) ()
validateClass named_class = do
  class_env <- getClassSet
  case evalState (checkInheritanceGraph named_class) (emptyUFM, class_env) of
    Just msg -> failure msg
    Nothing  -> return ()

registerProgram :: Program Name -> StateTEnvName (Either String) ()
registerProgram = traverse_ registerClass . programClasses

registerClass :: Class Name -> StateTEnvName (Either String) ()
registerClass r@(Class name _ features) = do
  exist <- memberOfClasses name
  case exist of
    True  -> failure $ "Class " ++ (nameLabel name) ++ " is already defined"
    False -> do
      insertIntoClasses r
      traverse_ registerFeature features

registerFeature :: Feature Name -> StateTEnvName (Either String) ()
registerFeature r@(Attr name typ expr) = do
  exist <- memberOfFeatures name
  case exist of
    True  -> failure $ "Attribute " ++ (nameLabel name) ++ " is already defined"
    False -> do
      insertIntoFeatures r
      traverse_ registerLocal expr
registerFeature r@(Method name typ formals payload) = do
  exist <- memberOfFeatures name
  case exist of
    True  -> failure $ "Method " ++ (nameLabel name) ++ " is already defined"
    False -> do
      insertIntoFeatures r
      traverse_ registerFormal formals
      registerLocal payload

registerFormal :: Formal Name -> StateTEnvName (Either String) ()
registerFormal (Formal name typ) = do
  exist <- memberOfLocales name
  case exist of
    True  -> failure $ "Local variable " ++ (nameLabel name) ++ " is already defined"
    False -> insertIntoLocals name typ Nothing

registerLocal :: Expr Name -> StateTEnvName (Either String) ()
registerLocal (Assign _ expr) = registerLocal expr
registerLocal (StaticDispatch _ params) = traverse_ registerLocal params
registerLocal (Block els) = traverse_ registerLocal els
registerLocal (Cond predicate then_body else_body) = do
  registerLocal predicate
  registerLocal then_body
  traverse_ registerLocal else_body
registerLocal (Dispatch _ _ expr params) = do
  registerLocal expr
  traverse_ registerLocal params
registerLocal (Let vars body) = do
  traverse_ registerLetVar vars
  registerLocal body
    where
      registerLetVar (name, typ, expr) = do
        exist <- memberOfLocales name
        case exist of
          True  -> failure $ (nameLabel name) ++ " has been already defined in let expression"
          False -> insertIntoLocals name typ expr
registerLocal (Case scrutinee decls) = do
  registerLocal scrutinee
  traverse_ registerCaseVar decls
    where
      registerCaseVar (name, typ, expr) = insertIntoLocals name typ (Just expr)
registerLocal (Loop left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Divide left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Eq left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Leq left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Lt left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Gt left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Geq left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Mul left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Plus left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Sub left right) = (registerLocal left) >> (registerLocal right)
registerLocal (Comp expr) = registerLocal expr
registerLocal (Isvoid expr) = registerLocal expr
registerLocal (Neg expr) = registerLocal expr
registerLocal (Tild expr) = registerLocal expr
registerLocal (Not expr) = registerLocal expr
registerLocal _ = return ()
  
getClassSet :: Monad m => StateTEnvName m (ClassSet Name)
getClassSet = do
  (Env classes _ _) <- get
  return classes

getFeatureSet :: Monad m => StateTEnvName m (FeatureSet Name)
getFeatureSet = do
  (Env _ features _) <- get
  return features

getLocalSet :: Monad m => StateTEnvName m (LocalSet Name)
getLocalSet = do
  (Env _ _ locals) <- get
  return locals

modFeatureSet :: Monad m => (FeatureSet Name -> FeatureSet Name) -> StateTEnvName m ()
modFeatureSet f = do
  r@(Env _ features _) <- get
  put r{envFeatures = f features}

modClassSet :: Monad m => (ClassSet Name -> ClassSet Name) -> StateTEnvName m ()
modClassSet f = do
  r@(Env classes _ _) <- get
  put r{envClasses = f classes}

modLocalSet :: Monad m => (LocalSet Name -> LocalSet Name) -> StateTEnvName m ()
modLocalSet f = do
  r@(Env _ _ locals) <- get
  put r{envLocals = f locals}

lookupClass :: Monad m => Name -> StateTEnvName m (Maybe (Class Name))
lookupClass Name{nameUnique=unique} = do
  classes <- getClassSet
  return $ lookupUFM_u unique classes

lookupFeature :: Monad m => Name -> StateTEnvName m (Maybe (Feature Name))
lookupFeature Name{nameUnique=unique} = do
  features <- getFeatureSet
  return $ lookupUFM_u unique features

lookupLocal :: Monad m => Name -> StateTEnvName m (Maybe (Name, Name, Maybe (Expr Name)))
lookupLocal Name{nameUnique=unique} = do
  locals <- getLocalSet
  return $ lookupUFM_u unique locals

insertIntoClasses :: Monad m => Class Name -> StateTEnvName m ()
insertIntoClasses r@Class{className=name} = modClassSet (insertUFM_u (nameUnique name) r)

insertIntoFeatures :: Monad m => Feature Name -> StateTEnvName m ()
insertIntoFeatures feature = modFeatureSet (insertUFM_u (nameUnique $ featureName feature) feature)

insertIntoLocals :: Monad m => Name -> Name -> Maybe (Expr Name) -> StateTEnvName m ()
insertIntoLocals name typ expr = modLocalSet (insertUFM_u (nameUnique name) (name, typ, expr))

memberOfClasses :: Monad m => Name -> StateTEnvName m Bool
memberOfClasses  = liftM isJust . lookupClass

isSystemClass :: Name -> Bool
isSystemClass name =
  name == object_name || name == io_name || name == string_name || name == int_name || name == bool_name

memberOfFeatures :: Monad m => Name -> StateTEnvName m Bool
memberOfFeatures = liftM isJust . lookupFeature

memberOfLocales :: Monad m => Name -> StateTEnvName m Bool
memberOfLocales = liftM isJust . lookupLocal

append_d :: String -> String -> String
append_d prefix name = prefix ++ "$$" ++ name

mkClassUnique :: Uniquable k => Class k -> Unique
mkClassUnique Class{className=name} = getUnique name

mkSimpleName :: String -> Name
mkSimpleName name = Name name name (getUnique name) 

mkName :: String -> String -> Name
mkName label uid = Name label uid (getUnique uid)

nameProgram :: Program String -> Program Name
nameProgram = Program . fmap nameClass . programClasses

nameClass :: Class String -> Class Name
nameClass (Class name parent features) =
  let nameName     = mkSimpleName name
      parentName   = mkSimpleName parent
      featuresName = fmap (nameFeature name) features
  in Class nameName parentName featuresName

nameFeature :: String -> Feature String -> Feature Name
nameFeature prefix (Attr name typ expr) =
  let prefix'  = append_d prefix name
      nameName = mkName name prefix'
      typName  = mkSimpleName typ
      exprName = fmap (nameExpr prefix') expr
  in Attr nameName typName exprName
nameFeature prefix (Method name typ formals payload) =
  let prefix'     = append_d prefix name 
      nameName    = mkName name prefix'
      typName     = mkSimpleName typ
      formalsName = fmap (nameFormal prefix') formals
      payloadName = (nameExpr prefix') payload
  in Method nameName typName formalsName payloadName

nameFormal :: String -> Formal String -> Formal Name
nameFormal prefix (Formal name typ) =
  let nameName = mkName name (append_d prefix name)
      typName  = mkSimpleName typ
  in Formal nameName typName 

nameExpr :: String -> Expr String -> Expr Name
nameExpr prefix expr =
  case expr of
    Assign name body -> Assign (mkName name $ append_d prefix name) (nameExpr prefix body)
    Block exprs -> Block (fmap (nameExpr prefix) exprs)
    Cond pred then_expr else_expr -> Cond (nameExpr prefix pred) (nameExpr prefix then_expr) (fmap (nameExpr prefix) else_expr)
    Dispatch name cast on params -> Dispatch name (fmap mkSimpleName cast) (nameExpr prefix on) (fmap (nameExpr prefix) params)
    Let vars body ->
      let prefix' = append_d prefix "let"
      in Let (fmap (nameLetVar prefix') vars) (nameExpr prefix' body)
    Case scrutinee decls ->
      let prefix' = append_d prefix "case"
      in Case (nameExpr prefix scrutinee) (evalState (traverse (nameCaseVar_st prefix) decls) 1)
    Divide left right -> Divide (nameExpr prefix left) (nameExpr prefix right)
    Eq left right -> Eq (nameExpr prefix left) (nameExpr prefix right)
    Leq left right -> Leq (nameExpr prefix left) (nameExpr prefix right)
    Lt left right -> Lt (nameExpr prefix left) (nameExpr prefix right)
    Gt left right -> Gt (nameExpr prefix left) (nameExpr prefix right)
    Geq left right -> Geq (nameExpr prefix left) (nameExpr prefix right)
    Mul left right -> Mul (nameExpr prefix left) (nameExpr prefix right)
    Plus left right -> Plus (nameExpr prefix left) (nameExpr prefix right)
    Sub left right -> Sub (nameExpr prefix left) (nameExpr prefix right)
    Loop left right -> Loop (nameExpr prefix left) (nameExpr prefix right)
    Comp body -> Comp $ nameExpr prefix body
    Isvoid body -> Isvoid (nameExpr prefix body)
    Tild body -> Tild (nameExpr prefix body)
    Not body -> Not (nameExpr prefix body)
    Neg body -> Neg (nameExpr prefix body)
    New name -> New $ mkSimpleName name
    Object name -> Object $ mkName name (append_d prefix name)
    StaticDispatch name params -> StaticDispatch (mkSimpleName name) (fmap (nameExpr prefix) params)
    BoolConst bool -> BoolConst bool
    StringConst string -> StringConst string
    IntConst int -> IntConst int

nameLetVar :: String -> (String, String, Maybe (Expr String)) -> (Name, Name, Maybe (Expr Name))
nameLetVar prefix (name, typ, expr) =
  let prefix' = append_d prefix name
  in (mkName name prefix', mkSimpleName typ, fmap (nameExpr prefix') expr)

nameCaseVar_st :: String -> (String, String, Expr String) -> State Int (Name, Name, Expr Name)
nameCaseVar_st prefix (name, typ, expr) = do
  i <- get
  let prefix' = (append_d prefix . append_d (show i)) name
  put (succ i)
  return (mkName name prefix', mkSimpleName typ, nameExpr prefix' expr)

data Name = Name { nameLabel  :: String
                 , nameHash   :: String  
                 , nameUnique :: Unique } deriving Show

instance Eq Name where
 Name _ _ l == Name _ _ r = l == r

{-
objectClassSym =
  let abort_meth    = ("abort", MethodSym "abord" "Object" [])
      typename_meth = ("type_name", MethodSym "type_name" "String" [])
      copy_meth     = ("copy", MethodSym "copy" "SELF_TYPE" [])
  in ("Object", ClassSym "Object" Nothing [] [abort_meth, typename_meth, copy_meth]) 

ioClassSym =
  let out_string_meth = ("out_string", MethodSym "out_string" "SELF_TYPE" [("x", "String")])
      out_int_meth    = ("out_int", MethodSym "out_int"  "SELF_TYPE" [("x", "Int")])
      in_string_meth  = ("in_string", MethodSym "in_string" "String" [])
      in_int_meth     = ("in_int", MethodSym "in_int" "Int" [])
  in ("IO", ClassSym "IO" (Just "Object") [] [out_string_meth, out_string_meth, in_string_meth, in_int_meth])

intClassSym = ("Int", ClassSym "Int" (Just "Object") [] [])

stringClassSym =
  let length_meth = ("length", MethodSym "length" "Int" [])
      concat_meth = ("concat", MethodSym "concat" "String" [])
      substr_meth = ("substr", MethodSym "substr" "String" [("i", "Int"), ("l", "Int")])
  in ("String", ClassSym "String" (Just "Object") [] [length_meth, concat_meth, substr_meth])

boolClassSym = ("Bool", ClassSym "Bool" (Just "Object") [] [])

initClassSyms = [objectClassSym
                ,ioClassSym
                ,intClassSym
                ,stringClassSym
                ,boolClassSym]
-}

--semantic :: Alex (InheritanceGraph, ClassDecls)
--semantic :: Alex [(String, ClassSym)]

namer :: Alex (Either String ())
namer = liftM go parser
  where
    go program = let named_program = nameProgram program
                     procedure     = registerProgram named_program >> validateProgram named_program
                 in evalStateT procedure emptyEnv
