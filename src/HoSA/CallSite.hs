module HoSA.CallSite where
       
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import Data.Rewriting.Applicative.SimpleTypes ((:::)(..))
import           Data.Rewriting.Applicative.Term
import HoSA.Utils
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Text.PrettyPrint.ANSI.Leijen as PP


data CallSite f = CallSite (f ::: ST.Type) Int

instance Eq f => Eq (CallSite f) where
    CallSite (f ::: _) i == CallSite (g ::: _) j = f == g && i == j

data AnnotatedRule f v = AR { lhs :: ATerm f v
                            , rhs :: ATerm f v
                            , arhs :: ATerm (CallSite f) v
                            , ruleEnv :: ST.Env v
                            , ruleType :: ST.Type }

calls :: AnnotatedRule f v -> [CallSite f]
calls = funs . arhs

withCallSites :: ST.STAtrs f v -> [AnnotatedRule f v]
withCallSites satrs = runUnique (annotateRule `mapM` ST.rules satrs) where
  annotateRule strl = do
    let rl = ST.untypedRule strl
        trl = ST.typedRule strl
    r <- annotate (R.rhs trl)
    return AR { lhs = R.lhs rl
              , rhs = R.rhs rl
              , arhs = r
              , ruleEnv = ST.ruleEnv strl
              , ruleType = ST.ruleType strl}
  annotate (aterm -> TVar (v ::: _)) = return (var v)
  annotate (aterm -> t1 :@ t2) = app <$> annotate t1 <*> annotate t2
  annotate (aterm -> TFun (f ::: td) ts) = 
    fun <$> (CallSite (f ::: tp) <$> uniqueToInt <$> unique) <*> mapM annotate ts where
      tp = foldr (ST.:~>) (ST.outputType td) (ST.inputTypes td)


data CallCtx f = CallCtx (CallSite f) [CallSite f] deriving (Eq)

initialCC :: f -> ST.Type -> CallCtx f
initialCC f tp = CallCtx (CallSite (f ::: tp) 0) []

type CSAbstract f = CallSite f -> CallCtx f -> CallCtx f

kca :: Eq f => Int -> CSAbstract f
kca n cs@(CallSite (f ::: tp) _) (CallCtx cs' css')
  | n <= 0 || firstOrder tp = CallCtx (CallSite (f ::: tp) 0) []
  | n == 1 = CallCtx cs []
  | otherwise = CallCtx cs (take (n - 1) (cs' : css'))
 where 
   firstOrder ST.BT {} = True
   firstOrder (ST.BT{} ST.:~> tp') = firstOrder tp'
   firstOrder _ = False

ctxSym :: CallCtx f -> f
ctxSym (CallCtx (CallSite (f ST.::: _) _) _) = f

callContexts :: Eq f => CSAbstract f -> [AnnotatedRule f v] -> [CallCtx f] -> [CallCtx f]
callContexts abstr ars = walk [] where
  walk seen [] = seen
  walk seen (cc : ccs)
    | cc `elem` seen = walk seen ccs
    | otherwise = walk (cc : seen) (succs cc ++ ccs)

  succs cc@(CallCtx (CallSite (f ::: _) _) _) =
    [ abstr c cc | arl <- ars, headSymbol (lhs arl) == Just f, c <- calls arl]    

-- pretty printing

instance PP.Pretty f => PP.Pretty (CallSite f) where
  pretty (CallSite (f ::: _) i) = PP.pretty f PP.<> PP.text "@" PP.<> PP.int i

instance PP.Pretty f => PP.Pretty (CallCtx f) where
  pretty (CallCtx cs@(CallSite (f ::: _) _) css) = PP.pretty f PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") [PP.int j | j <- [k | CallSite _ k <- cs : css]]

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedRule f v) where
  pretty rl = PP.pretty (ruleEnv rl)
    PP.<+> PP.text "⊢"
    PP.</> PP.hang 2 (rule PP.<+> PP.text ":" PP.<+> PP.pretty (ruleType rl))
    where
      rule = prettyATerm (lhs rl) PP.<+> PP.text "->" PP.</> prettyATerm (arhs rl)
