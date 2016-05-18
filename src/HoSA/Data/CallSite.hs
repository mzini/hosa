module HoSA.Data.CallSite where

import           Data.Maybe (catMaybes)
import           Data.Map (Map)
import           HoSA.Utils
import           HoSA.Data.SimpleType
import qualified HoSA.Data.Rewriting as R
import qualified Data.Rewriting.Applicative.Term as T
import           HoSA.Data.Rewriting ((:::)(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP


data CallSite = CallSite (R.FunId ::: SimpleType) Int

instance Eq CallSite where
    CallSite (f ::: _) i == CallSite (g ::: _) j = f == g && i == j

type AnnotatedTerm = R.ATerm (Maybe CallSite) R.Variable

data AnnotatedRule = AR { lhs :: R.Term
                        , rhs :: R.Term
                        , arhs :: AnnotatedTerm
                        , ruleEnv :: Map R.Variable SimpleType
                        , ruleType :: SimpleType }

calls :: AnnotatedRule -> [CallSite]
calls = catMaybes . R.funs . arhs

withCallSites :: STAtrs -> [AnnotatedRule]
withCallSites satrs = runUnique (annotateRule `mapM` rules satrs) where
  annotateRule strl = do
    let rl = strRule strl
        trl = strTypedRule strl
    r <- annotate (R.rhs trl)
    return AR { lhs = R.lhs rl
              , rhs = R.rhs rl
              , arhs = r
              , ruleEnv = strEnv strl
              , ruleType = strType strl}
  annotate (R.tview -> R.TVar (v ::: _)) = return (T.var v)
  annotate (R.tview -> R.TAppl t1 t2) = T.app <$> annotate t1 <*> annotate t2
  annotate (R.tview -> R.TPair t1 t2) = tup <$> annotate t1 <*> annotate t2 where
    tup a b = T.fun Nothing [a,b]
  annotate (R.tview -> R.TConst (f ::: tp)) = 
    T.fun <$> (Just <$> CallSite (f ::: tp) <$> uniqueToInt <$> unique) <*> return []


data CallCtx = CallCtx CallSite [CallSite] deriving (Eq)

initialCC :: R.FunId -> SimpleType -> CallCtx
initialCC f tp = CallCtx (CallSite (f ::: tp) 0) []

type CSAbstract = CallSite -> CallCtx -> CallCtx

kca :: Int -> CSAbstract
kca n cs@(CallSite (f ::: tp) _) (CallCtx cs' css')
  | n <= 0 || firstOrder tp = CallCtx (CallSite (f ::: tp) 0) []
  | n == 1 = CallCtx cs []
  | otherwise = CallCtx cs (take (n - 1) (cs' : css'))
 where
   dataType TyBase{} = True
   dataType (TyPair a b) = dataType a && dataType b
   dataType _ = False
   firstOrder (tp1 :-> tp2) = dataType tp1 && firstOrder tp2
   firstOrder tp = dataType tp

ctxSym :: CallCtx -> R.FunId
ctxSym (CallCtx (CallSite (f ::: _) _) _) = f

callContexts :: CSAbstract -> [AnnotatedRule] -> [CallCtx] -> [CallCtx]
callContexts abstr ars = walk [] where
  walk seen [] = seen
  walk seen (cc : ccs)
    | cc `elem` seen = walk seen ccs
    | otherwise = walk (cc : seen) (succs cc ++ ccs)

  succs cc@(CallCtx (CallSite (f ::: _) _) _) =
    [ abstr c cc | arl <- ars, R.headSymbol (lhs arl) == Just (R.Symbol f), c <- calls arl]    

-- pretty printing

instance PP.Pretty CallSite where
  pretty (CallSite (f ::: _) i) = PP.pretty f PP.<> PP.text "@" PP.<> PP.int i

instance PP.Pretty CallCtx where
  pretty (CallCtx cs@(CallSite (f ::: _) _) css) = PP.pretty f PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") [PP.int j | j <- [k | CallSite _ k <- cs : css]]

instance {-# OVERLAPPING  #-} PP.Pretty AnnotatedTerm where
  pretty = PP.pretty . T.amap toSym id where
    toSym Nothing = R.Tuple
    toSym (Just (CallSite (R.FunId f ::: _) i)) = R.Symbol (R.FunId (f ++ "@" ++ show i))
    -- pp _ (T.aterm -> T.TVar v) = PP.pretty v
    -- pp _ (T.aterm -> T.TConst f) = PP.pretty f
    -- pp _ (T.aterm -> T.TFun Nothing [t1,t2]) = 
    --   PP.parens (ppSeq (PP.text ", ") [ pp id t1, pp id t2])
    -- pp par (T.aterm -> t1 T.:@ t2) =
    --   par (pp id t1 PP.</> pp PP.parens t2)

  
instance PP.Pretty AnnotatedRule where
  pretty rl = PP.group (PP.pretty (ruleEnv rl))
    PP.<+> PP.text "⊢"
    PP.</> PP.hang 2 (prettyRl (lhs rl) (arhs rl) PP.<+> PP.text ":" PP.<+> PP.pretty (ruleType rl))
    where prettyRl l r = PP.pretty l PP.<+> PP.text "=" PP.</> PP.pretty r
