module HoSA.Data.CallSite where

import           Data.Map (Map)
import           HoSA.Utils
import           HoSA.Data.SimpleType
import           HoSA.Data.Rewriting
import           HoSA.Data.Rewriting ((:::)(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP


data CallSite f = CallSite (f ::: SimpleType) Int

data CallCtx f = CallCtx (CallSite f) [CallSite f] deriving (Eq)

instance Eq f => Eq (CallSite f) where
    CallSite (f ::: _) i == CallSite (g ::: _) j = f == g && i == j

type AnnotatedTerm f v = Term (CallSite f) v

data AnnotatedRule f v = AR { arlRule :: STRule f v
                            , arlAnnotatedRhs :: AnnotatedTerm f v }

arlEnv :: AnnotatedRule f v -> Map v SimpleType
arlEnv = strlEnv . arlRule

arlUntypedRule :: AnnotatedRule f v -> Rule f v
arlUntypedRule = strlUntypedRule . arlRule

arlType :: AnnotatedRule f v -> SimpleType
arlType = strlType . arlRule

calls :: Eq v => AnnotatedRule f v -> [CallSite f]
calls = funs . arlAnnotatedRhs

withCallSites :: STAtrs f v -> [AnnotatedRule f v]
withCallSites satrs = runUnique (annotateRule `mapM` statrsRules satrs) where
  annotateRule strl = AR strl <$> annotate (rhs (strlTypedRule strl))
  annotate (Var (v ::: _)) = return (Var v)
  annotate (Fun (f ::: tp)) = Fun <$> (CallSite (f ::: tp) <$> uniqueToInt <$> unique)
  annotate (Apply t1 t2) = Apply <$> annotate t1 <*> annotate t2
  annotate (Pair t1 t2) = Pair <$> annotate t1 <*> annotate t2
  annotate (Let t1 (x ::: _, y ::: _) t2) = Let <$> annotate t1 <*> return (x,y) <*> annotate t2  

initialCC :: f -> SimpleType -> CallCtx f
initialCC f tp = CallCtx (CallSite (f ::: tp) 0) []

type CSAbstract f = CallSite f -> CallCtx f -> CallCtx f

kca :: Int -> CSAbstract f
kca n cs@(CallSite (f ::: tp) _) (CallCtx cs' css')
  | n <= 0 || firstOrder tp = CallCtx (CallSite (f ::: tp) 0) []
  | n == 1 = CallCtx cs []
  | otherwise = CallCtx cs (take (n - 1) (cs' : css'))
 where
   dataType TyBase{} = True
   dataType (a :*: b) = dataType a && dataType b
   dataType _ = False
   firstOrder (tp1 :-> tp2) = dataType tp1 && firstOrder tp2
   firstOrder tp = dataType tp

ctxSym :: CallCtx f -> f
ctxSym (CallCtx (CallSite (f ::: _) _) _) = f

callContexts :: (Eq v, Eq f) => CSAbstract f -> [AnnotatedRule f v] -> [CallCtx f] -> [CallCtx f]
callContexts abstr ars = walk [] where
  walk seen [] = seen
  walk seen (cc : ccs)
    | cc `elem` seen = walk seen ccs
    | otherwise = walk (cc : seen) (succs cc ++ ccs)

  succs cc@(CallCtx (CallSite (f ::: _) _) _) =
    [ abstr c cc | arl <- ars, headSymbol (lhs (strlUntypedRule (arlRule arl))) == Just f, c <- calls arl]    

-- pretty printing

instance PP.Pretty f => PP.Pretty (CallSite f) where
  pretty (CallSite (f ::: _) i) = PP.pretty f PP.<> PP.text "@" PP.<> PP.int i

instance PP.Pretty f => PP.Pretty (CallCtx f) where
  pretty (CallCtx cs@(CallSite (f ::: _) _) css) = PP.pretty f PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") [PP.int j | j <- [k | CallSite _ k <- cs : css]]

-- instance {-# OVERLAPPING  #-} (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedTerm f v) where
--   pretty = PP.pretty . tmap toSym id where
--     toSym (CallSite (Symbol f ::: _) i) = Symbol (f ++ "@" ++ show i)
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedRule f v) where
  pretty rl = PP.group (PP.pretty (arlEnv rl))
    PP.<+> PP.text "⊢"
    PP.</> PP.hang 2 (prettyRl (lhs (arlUntypedRule rl)) (arlAnnotatedRhs rl) PP.<+> PP.text ":" PP.<+> PP.pretty (arlType rl))
    where
      prettyRl l r = PP.pretty l PP.<+> PP.text "=" PP.</> PP.pretty r
