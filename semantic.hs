{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Semantic where

import Prelude hiding (foldr, foldl)

import Control.Monad.Trans.State hiding (put, get, modify)
import Control.Monad.Trans.Reader hiding (ask, asks, local)

import Data.Either
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Parser

import Unique
import UniqueFM
import Control.Applicative
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.RWS

type Type   = String
type Parent = String

type ClassMap a = UniqueFM (Class a)
type MethodMap a = UniqueFM (Method a)
type AttrMap a = UniqueFM (Attr a)
type ObjectMap a = UniqueFM (Object a)

data Name = Name { nameLabel  :: String
                 , nameHash   :: String  
                 , nameUnique :: Unique } deriving Show

data Object a = Obj { objectValue :: a
                    , objectExpr  :: Maybe (Expr a)} deriving Show

data Scoped a = Scoped { scopedValue   :: a
                       , scopedClasses :: UniqueFM (Class a)
                       , scopedAttrs   :: UniqueFM (Attr a)
                       , scopedMethods :: UniqueFM (Method a)
                       , scopedObjects :: UniqueFM (Object a) } deriving Show

data CompilerError = Runtime
                   | ClassDuplicate String
                   | UnknownClass String
                   | IllegalInheritance String
                   | InvalidFeatureType String String String
                   | DuplicateFormalDeclaration String
                   | DuplicateVarDeclaration String
                   | DuplicateAttrDeclaration String
                   | DuplicateMethodDeclaration String
                   | UnknownVariable String
                   | UnknownMethod String String
                   | InvalidIdDeclaration
                   | CyclicInheritanceGraph String deriving Eq

data ScopedEnv = SPEnv { spCurrentClass :: Class String
                       , spClassMap     :: ClassMap String
                       , spMethodMap    :: MethodMap String
                       , spAttrMap      :: AttrMap String
                       , spObjMap       :: ObjectMap String}

instance Show CompilerError where
  show (ClassDuplicate name) = "Class " ++ name ++ " already exists"
  show (UnknownClass name) = "Class " ++ name ++ " is undeclared"
  show (IllegalInheritance name) = "Illegal inheritance on class " ++ name
  show (InvalidFeatureType name cType eType) = "Invalid attribute/method type definition named " ++ name ++ ": " ++ cType ++ " should be " ++ eType
  show (DuplicateFormalDeclaration name) = "Formal parameter " ++ name ++ " is already declared"
  show (DuplicateVarDeclaration name) = "Variable " ++ name ++ " is already declared"
  show (DuplicateAttrDeclaration name) = "Attribute " ++ name ++ " is already declared"
  show (DuplicateMethodDeclaration name) = "Method " ++ name ++ "is already declared"
  show (UnknownVariable name) = "Variable " ++ name ++ " is unknown"
  show (UnknownMethod name cName) = "Method " ++ name ++ " is unknown on class " ++ cName
  show InvalidIdDeclaration = "You can't declare a variable/attribute/method \"self\""
  show (CyclicInheritanceGraph name) = "Cyclic inheritance on class " ++ name

instance Error CompilerError where
  strMsg _ = Runtime 

objectUnique = getUnique "Object"
ioUnique = getUnique "IO"
stringUnique = getUnique "String"
intUnique = getUnique "Int"
boolUnique = getUnique "Bool"

objectClass =
  let meths = [ Method "abort" "Object" [] NoExpr
              , Method "type_name" "String" [] NoExpr
              , Method "copy" "SELF_TYPE" [] NoExpr]
  in Class "Object" "Object" [] meths

ioClass =
  let meths = [ Method "out_string" "SELF_TYPE" [Formal "x" "String"] NoExpr
              , Method "out_int" "SELF_TYPE" [Formal "x" "Int"] NoExpr
              , Method "in_string" "String" [] NoExpr
              , Method "in_int" "Int" [] NoExpr]
  in Class "IO" "Object" [] meths

intClass = Class "Int" "Object" [] []

stringClass =
  let meths = [ Method "length" "Int" [] NoExpr
              , Method "concat" "String" [Formal "s" "String"] NoExpr
              , Method "substr" "String" [Formal "i" "Int", Formal "l" "Int"] NoExpr]
  in Class "String" "Object" [] meths

boolClass = Class "Bool" "Object" [] []

sysClassMap = listToUFM [("Object", objectClass)
                        ,("IO", ioClass)
                        ,("Int", intClass)
                        ,("String", stringClass)
                        ,("Bool", boolClass)]

collectProgramObjects :: (MonadError CompilerError m, Applicative m)
                         => Program String
                         -> m (Program (Scoped String))
collectProgramObjects program = do
  class_map <- collectClasses program
  let class_map' = unionUFM_u sysClassMap class_map
  classes   <- runReaderT (traverse collectClassObjects (programClasses program)) class_map'
  return (Program classes)
  
collectClasses :: (MonadError CompilerError m, Functor m)
                  => Program String
                  -> m (ClassMap String)
collectClasses = flip execStateT emptyUFM . traverse_ go . programClasses
  where
    go c@(Class name _ _ _) = do
      class_map <- get
      case memberUFM name class_map of
        True  -> throwError (ClassDuplicate name)
        False -> put (insertUFM name c class_map)

illegalInheritance :: String -> Bool
illegalInheritance "String" = True
illegalInheritance "Int"    = True
illegalInheritance "Bool"   = True
illegalInheritance _        = False

checkTypeDecl :: (MonadError CompilerError m, MonadReader ScopedEnv m)
                 => String
                 -> m ()
checkTypeDecl "SELF_TYPE" = return ()
checkTypeDecl typ = do
  class_map <- asks spClassMap
  when (not (memberUFM typ class_map)) (throwError $ UnknownClass typ)

checkIdDecl :: MonadError CompilerError m
               => String
               -> m ()
checkIdDecl "self" = throwError InvalidIdDeclaration
checkIdDecl _ = return () 

validateClassGraph :: (MonadError CompilerError m, MonadReader (ClassMap String) m)
                      => Class String
                      -> m [Unique]
validateClassGraph = go emptyUFM
  where go passed_map (Class _ parent _ _)
          | memberUFM parent passed_map = throwError (CyclicInheritanceGraph parent)
          | parent == "Object"          = return [objectUnique]
          | parent == "IO"              = return [ioUnique, objectUnique]
          | illegalInheritance parent   = throwError (IllegalInheritance parent)
          | otherwise                   = do
            parent_class <- asks (lookupUFM parent)
            case parent_class of
              Nothing    -> throwError (UnknownClass parent)
              Just clazz -> do
                let passed_map' = insertUFM parent () passed_map
                liftM ((getUnique parent):) (go passed_map' clazz)
    
populateFeatureTable :: (MonadReader (ClassMap String) m, MonadError CompilerError m)
                        => AttrMap String
                        -> MethodMap String
                        -> Unique
                        -> m (AttrMap String, MethodMap String)
populateFeatureTable attrMap methMap unique = do
  clazz    <- asks (unsafeLookup_u unique)
  attrMap' <- foldrM (populateOverloadedFeature onAttr) attrMap (classAttrs clazz)
  methMap' <- foldrM (populateOverloadedFeature onMethod) methMap (classMethods clazz)
  return (attrMap', methMap')
    where
      onAttr (Attr name typ _)       = (name, typ)
      onMethod (Method name typ _ _) = (name, typ)

populateOverloadedFeature :: MonadError CompilerError m
                             => (f String -> (String, String))
                             -> f String
                             -> UniqueFM (f String)
                             -> m (UniqueFM (f String))
populateOverloadedFeature f feature m = do
  let (name, typ) = f feature
  case lookupUFM name m of
    Nothing    -> return $ insertUFM name feature m
    Just elder -> do
      let (_, elder_typ) = f elder
      if typ == elder_typ
        then return $ updateUFM (const $ Just feature) name  m
        else throwError (InvalidFeatureType name typ elder_typ)

collectClassObjects :: (MonadReader (ClassMap String) m, MonadError CompilerError m, Applicative m)
                       => Class String
                       -> m (Class (Scoped String))
collectClassObjects c@(Class n p cAttrs cMeths) = do
  validateClassFeatures c
  let init_state = (emptyUFM, emptyUFM)
      operation unique (attrs, meths) = populateFeatureTable attrs meths unique
  elders               <- validateClassGraph c
  (attr_map, meth_map) <- foldrM operation init_state ((getUnique n):elders)
  class_map            <- ask
  let init_sp_env = SPEnv c class_map meth_map attr_map emptyUFM
  cAttrs'              <- runReaderT (traverse collectAttrObjects cAttrs) init_sp_env
  cMeths'              <- runReaderT (traverse collectMethodObjects cMeths) init_sp_env
  return (Class n p cAttrs' cMeths')

validateClassFeatures :: MonadError CompilerError m
                         => Class String
                         -> m ()
validateClassFeatures (Class _ _ attrs meths) = do
  foldrM onAttr emptyUFM attrs
  foldrM onMeth emptyUFM meths
  return ()
    where
      onAttr (Attr name _ _) env = do
        checkIdDecl name
        when (memberUFM name env) (throwError $ DuplicateAttrDeclaration name)
        return (insertUFM name () env)
      onMeth (Method name _ _ _) env = do
        checkIdDecl name
        when (memberUFM name env) (throwError $ DuplicateMethodDeclaration name)
        return (insertUFM name () env)

collectAttrObjects :: (MonadError CompilerError m, MonadReader ScopedEnv m, Applicative m)
                      => Attr String
                      -> m (Attr (Scoped String))
collectAttrObjects (Attr n t payload) = do
  checkTypeDecl t
  payload' <- traverse collectExprObjects payload
  return (Attr n t payload')

collectMethodObjects :: (MonadError CompilerError m, MonadReader ScopedEnv m, Applicative m)
                        => Method String
                        -> m (Method (Scoped String))
collectMethodObjects (Method name typ formals body) = do
  checkTypeDecl typ
  object_map  <- asks spObjMap
  object_map' <- foldrM collectFormalObjects object_map formals
  body'       <- local (\e -> e{spObjMap=object_map'}) (collectExprObjects body)
  return (Method name typ formals body')
    where
      collectFormalObjects (Formal name typ) object_map = do
        checkIdDecl name
        class_map <- asks spClassMap
        let existInClassEnv = memberUFM typ class_map
        when (not existInClassEnv) (throwError $ UnknownClass typ)
        case memberUFM name object_map of
          True  -> throwError (DuplicateAttrDeclaration name)
          False -> return (insertUFM name (Obj name Nothing) object_map)

collectExprObjects :: (MonadError CompilerError m, MonadReader ScopedEnv m, Applicative m)
                      => Expr String
                      -> m (Expr (Scoped String))
collectExprObjects expr =
  case expr of
    Assign name expr -> do
      object_map <- asks spObjMap
      attr_map   <- asks spAttrMap
      let inObjMap  = memberUFM name object_map
          inAttrMap = memberUFM name attr_map
      if inObjMap || inAttrMap
        then fmap (Assign name) (collectExprObjects expr)
        else throwError (UnknownVariable name)
    Block exprs -> fmap Block (traverse collectExprObjects exprs)
    BoolConst b -> return (BoolConst b)
    Comp expr   -> fmap Comp (collectExprObjects expr)
    Cond p t e  -> do
      p' <- collectExprObjects p
      t' <- collectExprObjects t
      e' <- traverse collectExprObjects e
      return (Cond p' t' e')
    Dispatch name cast target params -> do
      traverse_ validCast cast
      target' <- collectExprObjects target
      params' <- traverse collectExprObjects params
      return (Dispatch name cast target' params')
        where
          validCast name = do
            class_map <- asks spClassMap
            case memberUFM name class_map of
              True  -> return ()
              False -> throwError (UnknownClass name)  
    Divide l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Divide l' r')
    Eq l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Eq l' r')
    IntConst i -> return $ IntConst i
    Isvoid expr -> fmap Isvoid (collectExprObjects expr)
    Leq l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Leq l' r')
    Let vars body -> do
      env                     <- ask
      (vars', object_map', (_ :: ())) <- runRWST (traverse go vars) env emptyUFM 
      body'                   <- local (\e -> e{spObjMap=object_map'}) (collectExprObjects body)
      return (Let vars' body')
        where
          go (name, typ, payload) = do
            checkIdDecl name
            checkTypeDecl typ
            object_map <- asks spObjMap
            let_vars   <- get
            case memberUFM name let_vars of
              True  -> throwError (DuplicateVarDeclaration name)
              False -> do
                let let_vars' = insertUFM name (Obj name payload) let_vars
                payload' <- traverse (local (\e -> e{spObjMap=(unionUFM_u let_vars' object_map)}) . collectExprObjects) payload
                put let_vars'
                return (name, typ, payload')
    Loop l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Loop l' r')
    Lt l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Lt l' r')
    Gt l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Gt l' r')
    Geq l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Geq l' r')
    Mul l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Mul l' r')
    Neg expr -> fmap Neg (collectExprObjects expr)
    New name -> do
      class_map <- asks spClassMap
      if memberUFM name class_map
        then return (New name)
        else throwError (UnknownClass name)
    NoExpr -> return NoExpr
    Object name -> do
      attr_map   <- asks spAttrMap
      object_map <- asks spObjMap
      meth_map   <- asks spMethodMap
      class_map  <- asks spClassMap
      let inAttrMap = memberUFM name attr_map
          inObjMap  = memberUFM name object_map
          isSelf    = "self" == name
      if inObjMap || inAttrMap || isSelf
        then return (Object (Scoped name class_map attr_map meth_map object_map))
        else throwError (UnknownVariable name)
    Plus l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Plus l' r')
    StaticDispatch name params -> do
      current_class <- asks spCurrentClass
      meth_map      <- asks spMethodMap
      case memberUFM name meth_map of
        False -> throwError (UnknownMethod name (className current_class))
        True  -> fmap (StaticDispatch name) (traverse collectExprObjects params)
    StringConst s -> return $ StringConst s
    Sub l r -> do
      l' <- collectExprObjects l
      r' <- collectExprObjects r
      return (Sub l' r')
    Tild expr -> fmap Tild (collectExprObjects expr)
    Not expr -> fmap Not (collectExprObjects expr)
    Case scrutinee decls -> do
      object_map <- asks spObjMap
      scrutinee' <- collectExprObjects scrutinee
      fmap (Case scrutinee') (traverse go decls)
        where
          go (name, typ, expr) = do
            checkIdDecl name
            checkTypeDecl typ
            object_map <- asks spObjMap
            expr'      <- local (\e -> e{spObjMap = insertUFM name (Obj name (Just expr)) object_map}) (collectExprObjects expr)
            return (name, typ, expr')

namer :: Alex (Program (Scoped String))
namer = go =<< parser
  where
    go program = case collectProgramObjects program of
      Left e  -> alexError (show e)
      Right a -> return a