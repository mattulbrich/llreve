{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module AST where

import           Bound
import           Control.Monad
import           Data.List
import           Data.String
import qualified Data.Text as T
import           Prelude.Extras
import           Text.PrettyPrint.HughesPJClass

data SortedVar =
  SortedVar Symbol
            Sort
  deriving (Show,Eq)

instance Pretty SortedVar where
  pPrint (SortedVar sym sor) = parens (pPrint sym <+> pPrint sor)

data Symbol =
  Symbol T.Text
  deriving (Show,Eq)

instance IsString Symbol where
  fromString = Symbol . T.pack

instance Pretty Symbol where
  pPrint (Symbol t) = text . T.unpack $ t

data FunDef a =
  FunDef Symbol
         [SortedVar]
         Sort
         (Term a)
  deriving (Show,Eq)

instance Pretty (FunDef Symbol) where
  pPrint (FunDef n vars out t) =
    parens $
    hang (text "define-fun") 2 $ pPrint n $$
    (parens $ vcat $ map pPrint vars) $$ pPrint out $$ pPrint t

data Sort =
  Sort T.Text
  deriving (Show,Eq,Ord)

instance Pretty Sort where
  pPrint (Sort t) = text . T.unpack $ t

data VarBinding a =
  VarBinding Symbol
             (Term a)
  deriving (Show,Eq,Functor,Foldable,Traversable)

instance Pretty (Term a) => Pretty (VarBinding a) where
  pPrint (VarBinding s t) = parens (pPrint s <+> pPrint t)

instance Applicative Term where
  pure = QualIdentifier
  (<*>) = ap

instance Monad Term where
  QualIdentifier a >>= f = f a
  SpecConstant s >>= _ = SpecConstant s
  QualIdentifierT i terms >>= f = (f i) >>= \i' -> QualIdentifierT i' (map (>>= f) terms)
  Let binds scope >>= f = Let (map mapBind binds) (scope >>>= f)
    where mapBind (VarBinding s t)  = VarBinding s (t >>= f)
  Forall vars term >>= f = Forall vars (term >>>= f)
  Exists vars term >>= f = Exists vars (term >>>= f)


data SpecConstant = SpecConst T.Text deriving (Show,Eq)

instance Pretty SpecConstant where
  pPrint (SpecConst s) = text . T.unpack $ s

data Term a
  = SpecConstant SpecConstant
  | QualIdentifier a
  | QualIdentifierT a
                    [Term a]
  | Let [VarBinding a]
        (Scope Int Term a)
  | Forall [SortedVar]
           (Scope Int Term a)
  | Exists [SortedVar]
           (Scope Int Term a)
  deriving (Functor,Eq,Foldable,Traversable,Show)

instantiateBindings :: [VarBinding a] -> Int -> Term Symbol
instantiateBindings binds i =
  let VarBinding n _ = binds !! i
  in QualIdentifier n

abstractBindings :: [VarBinding Symbol] -> Symbol -> Maybe Int
abstractBindings binds i = i `elemIndex` map sym binds
  where sym (VarBinding s _) = s

instantiateVars :: [SortedVar] -> Int -> Term Symbol
instantiateVars vars i = let SortedVar n _ = vars !! i
                         in QualIdentifier n

abstractVars :: [SortedVar] -> Symbol -> Maybe Int
abstractVars vars i = i `elemIndex` map sym vars
  where sym (SortedVar s _) = s

instance Pretty (Term Symbol) where
  pPrint (SpecConstant s) = pPrint s
  pPrint (QualIdentifier a) = pPrint a
  pPrint (QualIdentifierT a terms)
    | noLineBreak a = parens $ (pPrint $ a) <+> (hsep $ map pPrint terms)
    | otherwise = parens $ (pPrint $ a) $$ nest 2 (vcat $ map pPrint terms)
  pPrint (Let assgns t)
    | null assgns =
      pPrint (instantiate (instantiateBindings assgns)
                          t)
    | otherwise =
      parens $
      hang (text "let") 2 $
      (parens (vcat $ map pPrint assgns) $+$
       pPrint (instantiate (instantiateBindings assgns)
                           t))
  pPrint (Forall vars t)
    | null vars =
      pPrint (instantiate (instantiateVars vars)
                          t)
    | otherwise =
      parens $
      hang (text "forall") 2 $
      (parens (vcat $ map pPrint vars) $+$
       pPrint (instantiate (instantiateVars vars)
                           t))
  pPrint (Exists vars t)
    | null vars =
      pPrint (instantiate (instantiateVars vars)
                          t)
    | otherwise =
      parens $
      hang (text "exists") 2 $
      (parens (vcat $ map pPrint vars)) $+$
      pPrint (instantiate (instantiateVars vars)
                          t)

instance Eq1 Term
instance Show1 Term

data Attribute = KeyVal T.Text T.Text deriving (Eq,Show)

instance Pretty Attribute where
  pPrint (KeyVal key t) = colon <> (text $ T.unpack key) <+> doubleQuotes (text $ T.unpack t)

data Command a
  = Assert (Term a)
  | CheckSat
  | Exit
  | GetModel
  | DefineFun (FunDef a)
  | DeclareFun Symbol
               [Sort]
               Sort
  | SetLogic T.Text
  | SetInfo Attribute
  | Comment T.Text
  deriving (Show,Eq)

instance Pretty (Command Symbol) where
  pPrint (Assert t) = parens $ hang (text "assert") 2 $ pPrint t
  pPrint CheckSat = parens $ text "check-sat"
  pPrint Exit = parens $ text "exit"
  pPrint GetModel = parens $ text "get-model"
  pPrint (DefineFun f) = pPrint f
  pPrint (DeclareFun n args out) =
    parens $
    hang (text "declare-fun") 2 $
    pPrint n $$ (parens $ vcat $ map pPrint args) $$ pPrint out
  pPrint (SetLogic t) = parens $ text "set-logic" <+> (text $ T.unpack t)
  pPrint (Comment t) = text ";" <+> (text $ T.unpack t)
  pPrint (SetInfo a) = parens $ text "set-info" <+> pPrint a

data SMT a = SMT [Command a] deriving (Show,Eq)

instance Pretty (SMT Symbol) where
  pPrint (SMT cmds) = vcat $ map pPrint cmds

noLineBreak :: Symbol -> Bool
noLineBreak (Symbol s) = s `elem` specialOps || "INV_" `T.isPrefixOf` s

specialOps :: [T.Text]
specialOps = ["+","-","<=","<",">",">=","not","=","*"]
