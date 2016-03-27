module HoSA.CallSite where

import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import           Data.Rewriting.Applicative.Term
import HoSA.Utils
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Text.PrettyPrint.ANSI.Leijen as PP


data CallSite f = CallSite f Int deriving (Eq, Ord)

data AnnotatedRule f v = AR { lhs :: ATerm f v
                            , rhs :: ATerm f v
                            , arhs :: ATerm (CallSite f) v
                            , ruleEnv :: ST.Env v
                            , ruleType :: ST.Type}

calls :: AnnotatedRule f v -> [CallSite f]
calls = funs . arhs

withCallSites :: ST.STAtrs f v -> [AnnotatedRule f v]
withCallSites satrs = runUnique (annotateRule `mapM` ST.rules satrs) where
  annotateRule strl = do
    let rl = ST.untypedRule strl
    r <- annotate (R.rhs rl)
    return AR { lhs = R.lhs rl
              , rhs = R.rhs rl
              , arhs = r
              , ruleEnv = ST.ruleEnv strl
              , ruleType = ST.ruleType strl}
  annotate (aterm -> TVar v) = return (var v)
  annotate (aterm -> t1 :@ t2) = app <$> annotate t1 <*> annotate t2
  annotate (aterm -> TFun f ts) = 
    fun <$> (CallSite f <$> uniqueToInt <$> unique) <*> mapM annotate ts


data CallCtx f = CallCtx f Int [CallSite f] deriving (Eq, Ord)

initialCC :: f -> CallCtx f
initialCC f = CallCtx f 0 []

-- pushCS :: CSAbstract f -> CallSite f -> CallCtx f -> CallCtx f
-- pushCS abstr (CallSite f i) (CallCtx g j css) = abstr (CallCtx f i (CallSite g j : css))
  
type CSAbstract f = CallSite f -> CallCtx f -> CallCtx f

kca :: Eq f => Int -> CSAbstract f
kca n (CallSite f i) (CallCtx g j css)
  | n <= 0 = CallCtx f 0 []
  | otherwise = CallCtx f i (take (n - 1) css)


callContexts :: Eq f => CSAbstract f -> [AnnotatedRule f v] -> [CallCtx f] -> [CallCtx f]
callContexts abstr ars = walk [] where
  walk seen [] = seen
  walk seen (cc : ccs)
    | cc `elem` seen = walk seen ccs
    | otherwise = walk (cc : seen) (succs cc ++ ccs)

  succs cc@(CallCtx f _ _) =
    [ abstr c cc | arl <- ars, headSymbol (lhs arl) == Just f, c <- calls arl]    

-- pretty printing

instance PP.Pretty f => PP.Pretty (CallSite f) where
  pretty (CallSite f i) = PP.pretty f PP.<> PP.text "@" PP.<> PP.int i
  
instance PP.Pretty f => PP.Pretty (CallCtx f) where
  pretty (CallCtx f i cs) = PP.pretty f PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") [PP.int j | j <- i : [k | CallSite _ k <- cs]]

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedRule f v) where
  pretty rl = PP.pretty (ruleEnv rl)
    PP.<+> PP.text "⊢"
    PP.</> PP.hang 2 (rule PP.<+> PP.text ":" PP.<+> PP.pretty (ruleType rl))
    where
      rule = prettyATerm (lhs rl) PP.<+> PP.text "->" PP.</> prettyATerm (arhs rl)
