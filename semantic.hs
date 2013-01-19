{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Semantic where

import Semantic.Model

import Prelude hiding (foldr, foldl, (.), id)

import Control.Category
import Control.Arrow
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

objectUnique = getUnique "Object"
ioUnique = getUnique "IO"
stringUnique = getUnique "String"
intUnique = getUnique "Int"
boolUnique = getUnique "Bool"

objectClass =
  let meths = [ Method "abort" "Object" [] (IntConst 1)
              , Method "type_name" "String" [] (StringConst "")
              , Method "copy" "SELF_TYPE" [] (Object "self")]
  in Class "Object" "Object" [] meths

ioClass =
  let meths = [ Method "out_string" "SELF_TYPE" [Formal "x" "String"] (Object "self")
              , Method "out_int" "SELF_TYPE" [Formal "x" "Int"] (Object "self")
              , Method "in_string" "String" [] (StringConst "")
              , Method "in_int" "Int" [] (IntConst 1)]
  in Class "IO" "Object" [] meths

intClass = Class "Int" "Object" [] []

stringClass =
  let meths = [ Method "length" "Int" [] (IntConst 1)
              , Method "concat" "String" [Formal "s" "String"] (StringConst "")
              , Method "substr" "String" [Formal "i" "Int", Formal "l" "Int"] (StringConst "")]
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

typecheckProgram :: (MonadError CompilerError m, Applicative m)
                    => Program String
                    -> m (Program (Scoped (String, Type)))
typecheckProgram program = do
  class_map <- collectClasses program
  let class_map' = unionUFM_u sysClassMap class_map
  classes   <- runReaderT (traverse collectClassObjects (programClasses program ++ elemsUFM sysClassMap)) class_map'
  let enrich_class_map = listToUFM $ fmap (\c -> (className c, c)) classes
  typecheck_classes <- runReaderT (traverse typecheckClass classes) enrich_class_map
  return (Program typecheck_classes)
  
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
        let parent = maybe "Object" id (fmap classParent (lookupUFM cand class_map))
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
  class_name <- asks (className . tcCurrentClass)
  case name of
    "self" -> return class_name
    _      -> do
      let (Obj _ typ _) = unsafeLookup_u (getUnique name) scope
      case typ of
        "SELF_TYPE" -> return class_name
        _           -> return typ

methodEnv :: (MonadReader TypecheckEnv m, MonadError CompilerError m)
             => String
             -> m (Type, [Type])
methodEnv name = do
  (cls, meths) <- asks ((className &&& classMethods) . tcCurrentClass)
  (Method _ typ formals _) <- lookupMethod cls name meths
  let typ' = if typ == "SELF_TYPE" then cls else typ 
  return (typ', fmap formalType formals)
    where
      lookupMethod cls name [] = throwError $ UnknownMethod name cls
      lookupMethod cls name (m:ms)
          | name == methodName m = return m
          | otherwise            = lookupMethod cls name ms

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
      let a_parent = maybe "Object" classParent (lookupUFM a class_map)
          b_parent = maybe "Object" classParent (lookupUFM b class_map)
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
  class_name <- asks (className . tcCurrentClass)
  (payload', p_typ) <- typecheckExpr payload
  let typ' = if "SELF_TYPE" == typ then class_name else typ
  related <- typ' `ancestorOf` p_typ
  when (not related) (throwError $ TypeError $ name ++ " method type (" ++ typ'  ++ ") is different from its body expression: " ++ p_typ)
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
typecheckExpr (Block (e:exprs)) = do
  (e', e_typ) <- typecheckExpr e
  (exprs', r_typ) <- runStateT (traverse typecheckBlock exprs) e_typ
  return (Block (e':exprs'), r_typ)
    where
      typecheckBlock expr = do
        (expr', e_typ) <- typecheckExpr expr
        put e_typ
        return expr'
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
typecheckExpr (Dispatch meth cast target params) = do
  (target', t_typ) <- typecheckExpr target
  traverse (validCast t_typ) cast
  class_map <- asks tcClassMap
  let clazz = unsafeLookup_u (getUnique (maybe t_typ id cast)) class_map
  (r_typ, p_typs) <- local (\e -> e{tcCurrentClass=clazz}) (methodEnv meth)
  params' <- traverse (typecheckParam meth) (zip3 params p_typs [1..])
  return (Dispatch meth cast target' params', r_typ)
    where
      validCast t_typ cast = do
        parent  <- t_typ `ancestorOf` cast
        child   <- cast  `ancestorOf` t_typ
        let related = parent || child
        when (not related) (throwError $ TypeError $ "Cannot cast " ++ t_typ ++ " to " ++ cast)
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
  (expr', _) <- typecheckExpr expr
  return (Loop pred' expr', "Object")
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
  params'             <- traverse (typecheckParam name) (zip3 params par_typs [1..])
  return (StaticDispatch (Scoped (name, ret_typ) scope) params', ret_typ)
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
typecheckExpr (Case scrutinee (x:decls)) = do
  (scrutinee', s_typ) <- typecheckExpr scrutinee
  (x', x_typ)         <- typecheckDecl s_typ x
  (decls', r_typ)     <- runStateT (traverse (typecheckDecl' s_typ) decls) x_typ
  return (Case scrutinee' (x':decls'), r_typ)
    where
      typecheckDecl s_typ (name, typ, expr) = do
         parent <- s_typ `ancestorOf` typ
         child  <- typ `ancestorOf` s_typ
         let related = parent || child
         when (not related) (throwError $ TypeError $ "You can't declare a case branch of type" ++ typ ++ "which isn't related to scrutinee type (" ++ s_typ ++ ")")
         (expr', e_typ) <- typecheckExpr expr
         return ((name, typ, expr'), e_typ)
      typecheckDecl' s_typ triple = do
        (triple', t_typ) <- typecheckDecl s_typ triple 
        lub <- get
        r_type <- lesserUpperBound lub t_typ
        put r_type
        return triple'

typecheckParam :: (MonadError CompilerError m, MonadReader TypecheckEnv m, Applicative m)
                  => String
                  -> (Expr (Scoped String), Type, Int)
                  -> m (Expr (Scoped (String, Type)))
typecheckParam name (expr, typ, pos) = do
  (expr', e_typ) <- typecheckExpr expr
  related        <- typ `ancestorOf` e_typ
  when (not related) (throwError $ TypeError $ "Invalid type for paramenter " ++ (show pos) ++ " of " ++ name ++ " method , should be " ++ typ ++ " instead of " ++ e_typ)
  return expr'
          
typecheck :: Alex (Program (Scoped (String, Type)))
typecheck = go =<< parser
  where
    go program = case typecheckProgram program of
      Left e  -> alexError (show e)
      Right a -> return a
