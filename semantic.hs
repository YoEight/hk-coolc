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

data Object a = Obj { objectName  :: String
                    , objectTyp   :: String 
                    , objectExpr  :: Maybe (Expr a)} deriving Show

data Scoped a = Scoped { scopedValue     :: a
                       , scopedObjects   :: UniqueFM (Object String) } deriving Show

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
                   | TypeError String
                   | CyclicInheritanceGraph String deriving Eq

data ScopedEnv = SPEnv { spCurrentClass :: Class String
                       , spClassMap     :: ClassMap String
                       , spMethodMap    :: MethodMap String
                       , spObjMap       :: ObjectMap String}

data TypecheckEnv = TCEnv { tcCurrentClass :: Class (Scoped String)
                          , tcClassMap :: ClassMap (Scoped String) }

instance Show CompilerError where
  show (ClassDuplicate name) = "Class " ++ name ++ " already exists"
  show (UnknownClass name) = "Class " ++ name ++ " is undeclared"
  show (IllegalInheritance name) = "Illegal inheritance on class " ++ name
  show (InvalidFeatureType name cType eType) = "Invalid attribute/method type definition named " ++ name ++ ": " ++ cType ++ " should be " ++ eType
  show (DuplicateFormalDeclaration name) = "Formal parameter " ++ name ++ " is already declared"
  show (DuplicateVarDeclaration name) = "Variable " ++ name ++ " is already declared"
  show (DuplicateAttrDeclaration name) = "Attribute " ++ name ++ " is already declared"
  show (DuplicateMethodDeclaration name) = "Method " ++ name ++ " is already declared"
  show (UnknownVariable name) = "Variable " ++ name ++ " is unknown"
  show (UnknownMethod name cName) = "Method " ++ name ++ " is unknown on class " ++ cName
  show InvalidIdDeclaration = "You can't declare a variable/attribute/method \"self\""
  show (CyclicInheritanceGraph name) = "Cyclic inheritance on class " ++ name
  show (TypeError msg) = "Type error: " ++ msg

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

systemClass "Object" = True
systemClass "IO"     = True
systemClass "Int"    = True
systemClass "String" = True
systemClass "Bool"   = True
systemClass _        = False

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
--  let enrich_class_map = listToUFM $ fmap (\c -> (className c, c)) classes
  return (Program classes)
  
collectClasses :: (MonadError CompilerError m, Functor m)
                  => Program String
                  -> m (ClassMap String)
collectClasses = flip execStateT emptyUFM . traverse_ go . programClasses
  where
    go c@(Class name _ _ _) = do
      class_map <- get
      when (memberUFM name class_map) (throwError $ ClassDuplicate name)
      put (insertUFM name c class_map)

enrichClass :: (MonadError CompilerError m, MonadReader (ClassMap String) m)
               => Class String
               -> m (Class String, AttrMap String, MethodMap String)
enrichClass clazz = do
  let init_state = (emptyUFM, emptyUFM)
      operation unique (attrs, meths) = populateFeatureTable attrs meths unique
      (Class name parent attrs meths) = clazz
  graph                <- validateClassGraph clazz
  (attr_map, meth_map) <- foldrM operation init_state ((getUnique name):graph)
  return (Class name parent (elemsUFM attr_map) (elemsUFM meth_map), attr_map, meth_map)
  
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
collectClassObjects clazz = do
  validateClassFeatures clazz
  (enrich_class, attr_map, meth_map) <- enrichClass clazz
  class_map <- ask
  let toObj (Attr name typ p) = Obj name typ p
      (Class name parent attrs meths) = enrich_class
      init_sp_env = SPEnv enrich_class class_map meth_map (fmap toObj attr_map)
  attrs'    <- runReaderT (traverse collectAttrObjects attrs) init_sp_env
  meths'    <- runReaderT (traverse collectMethodObjects meths) init_sp_env
  return (Class name parent attrs' meths')

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
  object_map   <- asks spObjMap
  formal_decls <- foldrM collectFormalObjects emptyUFM formals
  body'        <- local (\e -> e{spObjMap=unionUFM_u formal_decls object_map}) (collectExprObjects body)
  return (Method name typ formals body')
    where
      collectFormalObjects (Formal name typ) object_map = do
        checkIdDecl name
        class_map <- asks spClassMap
        let existInClassEnv = memberUFM typ class_map
        when (not existInClassEnv) (throwError $ UnknownClass typ)
        when (memberUFM name object_map) (throwError $ DuplicateVarDeclaration name)
        return (insertUFM name (Obj name typ Nothing) object_map)

collectExprObjects :: (MonadError CompilerError m, MonadReader ScopedEnv m, Applicative m)
                      => Expr String
                      -> m (Expr (Scoped String))
collectExprObjects expr =
  case expr of
    Assign name expr -> do
      object_map <- asks spObjMap
      let inObjMap  = memberUFM name object_map
      when (not inObjMap) (throwError $ UnknownVariable name)
      fmap (Assign (Scoped name object_map)) (collectExprObjects expr)
    Block exprs -> fmap Block (traverse collectExprObjects exprs)
    BoolConst b -> return (BoolConst b)
    Comp expr   -> fmap Comp (collectExprObjects expr)
    Cond p t e  -> Cond <$> collectExprObjects p <*> collectExprObjects t <*> (traverse collectExprObjects e)
    Dispatch name cast target params -> do
      traverse_ validCast cast
      target' <- collectExprObjects target
      params' <- traverse collectExprObjects params
      return (Dispatch name cast target' params')
        where
          validCast name = do
            class_map <- asks spClassMap
            when (not (memberUFM name class_map)) (throwError $ UnknownClass name)
    IntConst i -> return $ IntConst i
    Isvoid expr -> fmap Isvoid (collectExprObjects expr)
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
            when (memberUFM name let_vars) (throwError $ DuplicateVarDeclaration name)
            let let_vars' = insertUFM name (Obj name typ payload) let_vars
            payload' <- traverse (local (\e -> e{spObjMap=(unionUFM_u let_vars' object_map)}) . collectExprObjects) payload
            put let_vars'
            return (name, typ, payload')
    Divide l r -> Divide <$> collectExprObjects l <*> collectExprObjects r
    Eq l r -> Eq <$> collectExprObjects l <*> collectExprObjects r
    Leq l r -> Leq <$> collectExprObjects l <*> collectExprObjects r
    Loop l r -> Loop <$> collectExprObjects l <*> collectExprObjects r
    Lt l r -> Lt <$> collectExprObjects l <*> collectExprObjects r
    Gt l r -> Gt <$> collectExprObjects l <*> collectExprObjects r
    Geq l r -> Geq <$> collectExprObjects l <*> collectExprObjects r
    Mul l r -> Mul <$> collectExprObjects l <*> collectExprObjects r
    Plus l r -> Plus <$> collectExprObjects l <*> collectExprObjects r
    Sub l r -> Sub <$> collectExprObjects l <*> collectExprObjects r
    Neg expr -> fmap Neg (collectExprObjects expr)
    New name -> do
      class_map <- asks spClassMap
      when (not (memberUFM name class_map)) (throwError $ UnknownClass name)
      return (New name)
    NoExpr -> return NoExpr
    Object name -> do
      object_map <- asks spObjMap
      let inObjMap  = memberUFM name object_map
          isSelf    = "self" == name
      when (not inObjMap && not isSelf) (throwError $ UnknownVariable name)
      return (Object (Scoped name object_map))
    StaticDispatch name params -> do
      current_class <- asks spCurrentClass
      meth_map      <- asks spMethodMap
      object_map    <- asks spObjMap
      when (not (memberUFM name meth_map)) (throwError (UnknownMethod name (className current_class)))
      fmap (StaticDispatch (Scoped name object_map)) (traverse collectExprObjects params)
    StringConst s -> return $ StringConst s
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
            expr'      <- local (\e -> e{spObjMap = insertUFM name (Obj name typ (Just expr)) object_map}) (collectExprObjects expr)
            return (name, typ, expr')

ancestorOf :: MonadReader TypecheckEnv m
            => Type
            -> Type
            -> m Bool
ancestorOf typ cand 
    | typ == cand = return True
    | otherwise = go typ cand
    where 
      go typ cand = do
        class_map <- asks tcClassMap
        let (Just parent) = fmap classParent (lookupUFM cand class_map)
        case typ == parent of
          False -> if parent == "Object"
                   then return False
                   else ancestorOf typ parent
          True  -> return True

objectEnv :: MonadReader TypecheckEnv m
             => String 
             -> ObjectMap String 
             -> m Type
objectEnv name scope = do
  (Class name _ _ _) <- asks tcCurrentClass
  let (Obj _ typ _) = unsafeLookup_u (getUnique name) scope
  case typ of
    "SELF_TYPE" -> return name
    _           -> return typ

methodEnv :: MonadReader TypecheckEnv m
             => String
             -> m (Type, [Type])
methodEnv name = do
  (Class cls _ _ meths) <- asks tcCurrentClass
  let (Method _ typ formals _) = lookupMethod name meths
      typ'                     = if typ == "SELF_TYPE" then cls else typ 
      lookupMethod name (m:ms)
          | name == methodName m = m
          | otherwise            = lookupMethod name ms
  return (typ', fmap formalType formals)

lesserUpperBound :: MonadReader TypecheckEnv m
                    => Type
                    -> Type
                    -> m Type
lesserUpperBound a b
    | a == b = return a
    | otherwise = do
  relatedToA <- a `ancestorOf` b
  relatedToB <- b `ancestorOf` a
  case (relatedToA, relatedToB) of
    (True, _) -> return a
    (_, True) -> return b
    _         -> do
      class_map <- asks tcClassMap
      let (Class _ a_parent _ _) = unsafeLookup_u (getUnique a) class_map
          (Class _ b_parent _ _) = unsafeLookup_u (getUnique b) class_map
      lesserUpperBound a_parent b_parent

typecheckClass :: (MonadError CompilerError m, MonadReader (ClassMap (Scoped String)) m, Applicative m)
                  => Class (Scoped String)
                  -> m (Class (Scoped (String, Type)))
typecheckClass c@(Class name parent attrs meths) = do
  class_map <- ask
  attrs'    <- runReaderT (traverse typecheckAttr attrs) (TCEnv c class_map)
  meths'    <- runReaderT (traverse typecheckMethod meths) (TCEnv c class_map)
  return (Class name parent attrs' meths')

typecheckAttr :: (MonadError CompilerError m, MonadReader TypecheckEnv m, Applicative m)
                 => Attr (Scoped String)
                 -> m (Attr (Scoped (String, Type)))
typecheckAttr (Attr name typ e) =
    case e of
      Nothing   -> return (Attr name typ Nothing)
      Just expr -> do
             (expr', e_typ) <- typecheckExpr expr
             when (typ /= e_typ) (throwError $ TypeError $ name ++ " attribute type is different from its init expression: " ++ e_typ)
             return (Attr name typ (Just expr'))

typecheckMethod :: (MonadError CompilerError m, MonadReader TypecheckEnv m, Applicative m)
                   => Method (Scoped String)
                   -> m (Method (Scoped (String, Type)))
typecheckMethod (Method name typ formals payload) = do
  (payload', p_typ) <- typecheckExpr payload
  when (typ /= p_typ) (throwError $ TypeError $ name ++ " method type is different from its body expression: " ++ p_typ)
  return (Method name typ formals payload')

typecheckExpr :: (MonadError CompilerError m, MonadReader TypecheckEnv m, Applicative m)
                 => Expr (Scoped String)
                 -> m (Expr (Scoped (String, Type)), Type)
typecheckExpr (Assign (Scoped name scope) expr) = do
  typ <- objectEnv name scope
  (expr', e_typ) <- typecheckExpr expr
  related        <- typ `ancestorOf` e_typ
  when (not related) (throwError $ TypeError $ name ++ ":" ++ typ ++ " can't be assigned to an expression of type " ++ e_typ)
  return (Assign (Scoped (name, typ) scope) expr', typ)
typecheckExpr (Block exprs) = error "todo"   --fmap Block (traverse typecheckExpr exprs)
typecheckExpr (BoolConst b) = return (BoolConst b, "Bool")
typecheckExpr (Comp expr) = fmap (\(expr', typ) -> (Comp expr', typ)) (typecheckExpr expr)
typecheckExpr (Cond pred the els) = do
  (pred', p_typ) <- typecheckExpr pred
  when (p_typ /= "Bool") (throwError $ TypeError $ "Condition predicate type must be Bool not " ++ p_typ)
  (the', t_typ)  <- typecheckExpr the
  els'           <- traverse typecheckExpr els
  cond_type      <- condType t_typ els'
  return (Cond pred' the' (fmap fst els'), t_typ)
    where
      condType t_typ Nothing           = return t_typ
      condType t_typ (Just (_, e_typ)) = lesserUpperBound t_typ e_typ
typecheckExpr (Dispatch meth cast target params) = error "todo"
typecheckExpr (Divide l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot divide " ++ l_typ ++ " by " ++ r_typ)
  return (Divide l' r', "Int")
typecheckExpr (Eq l r) = do  
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do equal operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Eq l' r', "Bool")
typecheckExpr (IntConst i) = return (IntConst i, "Int")
typecheckExpr (Isvoid expr) = do
  (expr', _) <- typecheckExpr expr
  return (Isvoid expr', "Bool")
typecheckExpr (Leq l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do comparaison operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Leq l' r', "Bool")
typecheckExpr (Let decls expr) = do
  decls'       <- traverse typecheckLetDecls decls
  (expr', typ) <- typecheckExpr expr
  return (Let decls' expr', typ)
      where
        typecheckLetDecls (name, typ, mexpr) = do
            mexpr' <- traverse typecheckExpr mexpr
            case mexpr' of
              Nothing            -> return (name, typ, Nothing)
              Just (expr, e_typ) -> do
                related <- typ `ancestorOf` e_typ
                when (not related) (throwError $ TypeError $ "Let variable " ++ name ++ " must be of type " ++ typ ++ " not " ++ e_typ)
                return (name, typ, Just expr)
typecheckExpr (Loop pred expr) = do
  (pred', p_typ) <- typecheckExpr pred
  when (p_typ /= "Bool") (throwError $ TypeError $ "Predicate expression must be of type Bool not " ++ p_typ)
  (expr', e_typ) <- typecheckExpr expr
  return (Loop pred' expr', e_typ)
typecheckExpr (Lt l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do comparaison operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Lt l' r', "Bool")
typecheckExpr (Gt l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do comparaison operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Gt l' r', "Bool")
typecheckExpr (Geq l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do comparaison operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Geq l' r', "Bool")
typecheckExpr (Mul l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do algebraic operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Mul l' r', "Int")
typecheckExpr (Neg expr) = do
  (expr', typ) <- typecheckExpr expr
  when (typ /= "Int") (throwError $ TypeError $ "Cannot do negation operation on type " ++ typ)
  return (Neg expr', typ)
typecheckExpr (New s) = do
  (Class name _ _ _) <- asks tcCurrentClass
  case s == "SELF_TYPE" of
    True  -> return (New name, name)
    False -> return (New s, s)
typecheckExpr NoExpr = return (NoExpr, "Void")
typecheckExpr (Object (Scoped name scope)) = do
  typ <- objectEnv name scope
  return (Object (Scoped (name, typ) scope), typ)
typecheckExpr (Plus l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do algebraic operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Plus l' r', "Int")
typecheckExpr (StaticDispatch (Scoped name scope) params) = do
  (ret_typ, par_typs) <- methodEnv name
  params'             <- traverse (typecheckParams name) (zip3 params par_typs [1..])
  return (StaticDispatch (Scoped (name, ret_typ) scope) params', ret_typ)
      where
        typecheckParams name (expr, typ, pos) = do
          (expr', e_typ) <- typecheckExpr expr
          related        <- typ `ancestorOf` e_typ
          when (not related) (throwError $ TypeError $ "Invalid type for paramenter " ++ (show pos) ++ " of " ++ name ++ " method , should be " ++ typ ++ " instead of " ++ e_typ)
          return expr'
typecheckExpr (StringConst s) = return (StringConst s, "String")
typecheckExpr (Sub l r) = do
  (l', l_typ) <- typecheckExpr l
  (r', r_typ) <- typecheckExpr r
  when (l_typ /= "Int" || r_typ /= "Int") (throwError $ TypeError $ "Cannot do algebraic operation on " ++ l_typ ++ " and " ++ r_typ)
  return (Sub l' r', "Int")
typecheckExpr (Tild expr) = throwError $ TypeError "Not implemented typechecking on (~) operator"
typecheckExpr (Not expr) = do
  (expr', typ) <- typecheckExpr expr
  when (typ /= "Bool") (throwError $ TypeError $ "Cannot use boolean opeation on type " ++ typ)
  return (Not expr', "Bool")
typecheckExpr (Case scrutinee decls) = do
  (scrutinee', s_typ) <- typecheckExpr scrutinee
  error "todo"
--  decls'              <- traverse typecheckDecls decls

namer :: Alex (Program (Scoped String))
namer = go =<< parser
  where
    go program = case collectProgramObjects program of
      Left e  -> alexError (show e)
      Right a -> return a
