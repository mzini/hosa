{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import System.Console.CmdArgs
import Data.Typeable (Typeable)
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Applicative.Problem as P
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Data.Rewriting.Applicative.Term as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Except
import System.Exit

import HoSA.Utils
import qualified HoSA.CallSite as C
import qualified HoSA.Infer as I
import qualified HoSA.Index as Ix
import qualified HoSA.Solve as S
import qualified HoSA.SizeType as SzT

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: S.Solver
                 , mainIs :: Maybe [String]
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "width, i.e. number of extra variables, of size-types"
       , input = def &= typFile &= argPos 0
       , solver = S.MiniSmt &= help "SMT solver (minismt, z3)"
       , mainIs = Nothing &= help "Main function to analyse"
       , clength = 1 &= help "length of call-site contexts" }
  &= help "Infer size-types for given ATRS"


abstraction :: HoSA -> C.CSAbstract String
abstraction cfg = C.kca (clength cfg)

data Error = ParseError P.ProblemParseError
           | SimpleTypeError String
           | SizeTypeError (I.TypingError String String)
           | ConstraintUnsolvable
           | NonSimpleApplicative (String,Int)

instance PP.Pretty Error where
  pretty (ParseError e) =
    PP.text "Error parsing ATRS, reason was:"
    PP.</> PP.indent 2 (ppErr e)
    where
      ppErr (P.SomeParseError pe) = PP.text (show pe)
      ppErr _ = PP.empty
  pretty (SimpleTypeError e) =
    PP.text "Error inferring simple types, reason was:"
    PP.</> PP.indent 2 (PP.text e)
  pretty (SizeTypeError e) =
    PP.text "Error inferring size types, reason was:"
    PP.</> PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = 
    PP.text "Constraints cannot be solved"
  pretty (NonSimpleApplicative (f,i)) =
    PP.text "ATRS contains non-constant symbol"
    PP.<+> PP.squotes (PP.text f) PP.<+> PP.text "of arity" PP.<+> PP.int i
    

type RunM = ExceptT Error IO

getConfig :: RunM HoSA
getConfig = lift (cmdArgs defaultConfig)

-- curryAtrs :: [R.ARule String String] -> [R.ARule String String]
-- curryAtrs = map (R.mapSides curryTerm) where
--   curryTerm = undefined

fromFile :: HoSA -> RunM [R.ARule String String]
fromFile cfg = do
  p <- lift (P.fromFile (input cfg) (`elem` ["app","@","."]))
  rs <- assertRight ParseError (P.allRules <$> P.rules <$> p)
  let ts = T.withArity `map` (RS.lhss rs ++ RS.rhss rs)
  case listToMaybe [ p | p <- foldr T.funsDL [] ts , snd p > 0 ] of
    Nothing -> return rs
    Just p -> throwError (NonSimpleApplicative p)

inferSimpleTypes :: [R.ARule String String] -> RunM (ST.STAtrs String String)
inferSimpleTypes = assertRight SimpleTypeError . ST.fromATRS

generateConstraints :: HoSA -> ST.STAtrs String String -> RunM (SzT.Signature String Ix.Term, [C.AnnotatedRule String String], [Ix.Constraint])
generateConstraints cfg ars = 
  lift (I.generateConstraints (abstraction cfg) (width cfg) (mainIs cfg) ars)
  >>= assertRight SizeTypeError
  
solveConstraints :: HoSA -> SzT.Signature String Ix.Term -> [Ix.Constraint] -> RunM (SzT.Signature String (S.Polynomial Integer))
solveConstraints cfg asig cs =
  S.solveConstraints (solver cfg) asig cs
  >>= assertJust ConstraintUnsolvable

-- instance PP.Pretty String where pretty = PP.text

status :: PP.Pretty e => String -> e -> RunM ()
status n e = lift (putDocLn (PP.text n PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

run :: IO (Either Error ())
run = runExceptT $ do
  cfg <- getConfig 
  atrs <- fromFile cfg >>= inferSimpleTypes
  (asig,ars,cs) <- generateConstraints cfg atrs
  status "Considered ATRS" (PP.pretty ars
                            PP.<$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty (ST.signature atrs)))
  status "Abstract Signature" asig
  status "Generated Constraints" cs
  sig <- solveConstraints cfg asig cs
  status "Signature" sig
  return ()

main :: IO ()
main = run >>= exit where
  exit (Left e@SizeTypeError{}) = putDocLn e >> exitWith ExitSuccess
  exit (Left e) = putDocLn e >> exitWith (ExitFailure (-1))
  exit _ = exitWith ExitSuccess
  

