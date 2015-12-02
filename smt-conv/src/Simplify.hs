{-# LANGUAGE OverloadedStrings #-}
module Simplify where

import           AST
import           Bound
import           Control.Monad.Gen
import           Data.Bifunctor
import           Data.Either
import           Data.Monoid
import qualified Data.Text as T

simplify :: SMT Symbol -> SMT Symbol
simplify (SMT []) = SMT [GetModel]
simplify (SMT cmds) = SMT cmds'
  where cmds' = map simplifyCommand cmds

simplifyCommand :: Command Symbol -> Command Symbol
simplifyCommand (Assert t) = Assert $ simplifyTerm t
simplifyCommand c = c

simplifyTerm :: Term Symbol -> Term Symbol
simplifyTerm (QualIdentifierT "and" ts) =
  let ts' = map simplifyTerm ts
      liftAnd (QualIdentifierT "and" ts'') rest = ts'' ++ rest
      liftAnd t rest = t : rest
  in QualIdentifierT "and" $ foldr liftAnd [] ts'
simplifyTerm (QualIdentifierT "*" (QualIdentifierT "-" [SpecConstant (SpecConst "1")]:t)) =
  QualIdentifierT "-" t
simplifyTerm (Let binds t) =
  Let binds .
  abstract (abstractBindings binds) .
  simplifyTerm . instantiate (instantiateBindings binds) $
  t
simplifyTerm (Forall vars t) =
  Forall vars .
  abstract (abstractVars vars) .
  simplifyTerm . instantiate (instantiateVars vars) $
  t
simplifyTerm (Exists vars t) =
  Exists vars .
  abstract (abstractVars vars) .
  simplifyTerm . instantiate (instantiateVars vars) $
  t
simplifyTerm (QualIdentifierT op ts) = QualIdentifierT op $ map simplifyTerm ts
simplifyTerm t = t

notExists :: Command Symbol -> Gen Int (Either (Command Symbol) ([SortedVar],Term Symbol))
notExists (Assert (QualIdentifierT "not" [Exists vars t])) =
  do unique <- show <$> gen
     let renamedVars = map (renameVar unique) vars
     pure $
       Right (renamedVars
             ,instantiate (instantiateVars renamedVars)
                          t)
  where renameVar
          :: String -> SortedVar -> SortedVar
        renameVar s (SortedVar (Symbol sym) sort) =
          SortedVar (Symbol (sym <> "___" <> T.pack s)) sort
notExists c = pure $ Left c

mergeNotExists :: SMT Symbol -> SMT Symbol
mergeNotExists (SMT cmds) =
  let (rest,(vars,terms)) =
        second unzip . partitionEithers . runGen . mapM notExists $ cmds
      merged =
        QualIdentifierT "not" $
        pure $
        Exists (concat vars) . abstract (abstractVars (concat vars)) $
        QualIdentifierT "or" terms
  in SMT $ (filter (not . instrCmd) rest) ++ [Assert merged,CheckSat,GetModel]
  where instrCmd :: Command Symbol -> Bool
        instrCmd CheckSat = True
        instrCmd GetModel = True
        instrCmd _ = False
