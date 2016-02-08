{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists #-}
module Parser where

import           AST
import           Bound
import           Control.Applicative
import           Control.Monad
import qualified Data.Text as T
import           Text.Parser.LookAhead
import qualified Text.Parser.Token.Highlight as HI
import qualified Text.Trifecta as Tri
import           Text.Trifecta hiding (Parser,symbol)
import           Text.Trifecta.Delta

newtype Parser a =
  Parser {runParser :: Tri.Parser a}
  deriving (Alternative,Applicative,CharParsing,DeltaParsing,Functor
           ,LookAheadParsing,MarkParsing Delta,Monad,MonadPlus
           ,Parsing,TokenParsing)

symbolId :: IdentifierStyle Parser
symbolId =
  IdentifierStyle {_styleName = "sort identifier"
                  ,_styleStart = letter <|> oneOf special
                  ,_styleLetter = alphaNum <|> oneOf special
                  ,_styleReserved =
                     ["set-logic"
                     ,"get-model"
                     ,"forall"
                     ,"let"
                     ,"assert"
                     ,";"
                     ,"set-info"]
                  ,_styleHighlight = HI.Identifier
                  ,_styleReservedHighlight = HI.ReservedIdentifier}
  where special = "~!@$%^&*_-+=<>.?/"

specConstId :: IdentifierStyle Parser
specConstId = IdentifierStyle {_styleName = "spec constant identifier"
                                  ,_styleStart = digit
                                  ,_styleLetter = digit
                                  ,_styleReserved = ["true","false"]
                                  ,_styleHighlight = HI.Identifier
                                  ,_styleReservedHighlight = HI.ReservedIdentifier}

reserved :: String -> Parser ()
reserved = reserve symbolId

identifier :: Parser T.Text
identifier = ident symbolId

setLogic :: Parser (Command a)
setLogic = parens $ do
  reserved "set-logic"
  SetLogic <$> identifier

getModel :: Parser (Command a)
getModel = parens $ reserved "get-model" *> pure GetModel

checkSat :: Parser (Command a)
checkSat = parens $ reserved "check-sat" *> pure CheckSat

funDef :: Parser (Command Symbol)
funDef = parens $ do
  reserved "define-fun"
  name <- symbol
  vars <- parens $ many sortedVar
  sort' <- sort
  term' <- term
  return $ DefineFun $ FunDef name vars sort' term'

funDecl :: Parser (Command a)
funDecl = parens $ do
  reserved "declare-fun"
  name <- symbol
  vars <- parens $ many sort
  sort' <- sort
  return $ DeclareFun name vars sort'

symbol :: Parser Symbol
symbol = Symbol <$> ident symbolId

sortedVar :: Parser (SortedVar)
sortedVar = parens $ do
  name <- symbol
  sort' <- sort
  return $ SortedVar name sort'

sort :: Parser Sort
sort = Sort <$> identifier

term :: Parser (Term Symbol)
term =
  try specConstant <|> try (QualIdentifier <$> symbol) <|> try qualIdentifierT <|>
  try forall <|>
  try let' <|>
  try exists

forall :: Parser (Term Symbol)
forall = parens $ do
  reserved "forall"
  vars <- parens $ many sortedVar
  term' <- term
  return $ Forall vars (abstract (abstractVars vars) term')

exists :: Parser (Term Symbol)
exists = parens $ do
  reserved "exists"
  vars <- parens $ many sortedVar
  term' <- term
  return $ Exists vars (abstract (abstractVars vars) term')

let' :: Parser (Term Symbol)
let' = parens $ do
  reserved "let"
  vars <- parens $ some varBinding
  term' <- term
  return $ Let vars (abstract (abstractBindings vars) term')

varBinding :: Parser (VarBinding Symbol)
varBinding = parens $ VarBinding <$> symbol <*> term

command :: Parser (Command Symbol)
command =
  try setLogic <|> try funDef <|> try funDecl <|> try assert <|> try getModel <|>
  try checkSat <|>
  try comment <|>
  try setInfo

smt :: Parser (SMT Symbol)
smt = SMT <$> many (token command)

test :: Parser a -> String -> Result a
test p s = parseString (runParser p) mempty s

specConstant :: Parser (Term a)
specConstant = SpecConstant . SpecConst <$> ident specConstId

qualIdentifierT :: Parser (Term Symbol)
qualIdentifierT = parens $ do
  name <- symbol
  terms <- some term
  return $ QualIdentifierT name terms

assert :: Parser (Command Symbol)
assert = parens $ do
  reserved "assert"
  Assert <$> term

comment :: Parser (Command a)
comment = do
  _ <- reserved ";"
  Comment . T.pack <$> manyTill anyChar newline

setInfo :: Parser (Command a)
setInfo = parens $ do reserved "set-info"
                      SetInfo <$> token attribute

attribute :: Parser Attribute
attribute = do k <- token keyword
               x <- stringLiteral
               pure $ KeyVal k x

keyword :: Parser T.Text
keyword = char ':' *> (T.pack <$> some (letter <|> digit))

testString :: String
testString =
  "(set-info :origin \"NTS benchmark converted to SMT-LIB2 using Eldarica (http://lara.epfl.ch/w/eldarica)\")"
