{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, MultiParamTypeClasses, TypeFamilies  #-}

module Main where

import Language.KURE
import Language.KURE.Boilerplate
import Data.Monoid
import Data.List
import Debug.Trace

import Exp
import Id

-- data MyGeneric = ExpG Exp
type MyGeneric = Exp

$(kureYourBoilerplate ''MyGeneric ''Id ''())

instance Term Exp where
  type Generic Exp = MyGeneric  -- MyGeneric is its own Generic root.
  inject    = id
  select e  = return e

{-
instance Term Exp where
  type Generic Exp = MyGeneric
  inject           = ExpG
  select (ExpG e)  = return e

instance Term MyGeneric where
  type Generic MyGeneric = MyGeneric  -- MyGeneric is its own Generic root.
  inject    = id
  select e  = return e
-}
type R e = Rewrite Id () e
type T e1 e2 = Translate Id () e1 e2

main = do
	let es1 = [e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11]
	sequence_ [ print e | e <- es1]

	let frees :: Exp -> Id [Name]
	    frees exp = do Right (fs,b) <- runTranslate freeExpT () exp
			   return $ nub fs
	let e_frees = map (runId . frees) es1
	sequence_ [ print e | e <- e_frees]
        
        sequence [ print (e,function (substExp v ed) e)  | v <- ["x","y","z"], ed <- es1, e <- es1 ]

        sequence  [ print (runId $ runTranslate betaRedR () e) | e <- es1 ]
        let fn = extractR (topdownR (repeatR betaRedR))
        sequence  [ print (runId $ runTranslate fn () e) | e <- es1 ]


------------------------------------------------------------------------

function :: Translate Id () a b -> a -> b
function f a = runId $ do 
        Right (b,_) <- runTranslate f () a
	return $ b

------------------------------------------------------------------------

freeExpT :: T Exp [Name]
freeExpT = lambda <+ var <+ crushU freeExpT
  where
          var    = varG >-> translate (\ (Var v) -> return [v])
          lambda = lamG >-> translate (\ (Lam n e) -> do
                frees <- apply freeExpT e
                return (nub frees \\ [n]))
                
freeExp :: Exp -> [Name]
freeExp = function freeExpT

newName :: Name -> [Name] -> Name
newName suggest frees = 
        head [ nm | nm <- suggest : suggests
             , nm `notElem` frees
             ]
   where suggests = [ suggest ++ "_" ++ show n | n <- [1..]]

-- Only works for lambdas, fails for all others
shallowAlpha :: [Name] -> R Exp
shallowAlpha frees' = lamG >-> 
                        rewrite (\ (Lam n e) -> do
                frees <- apply freeExpT e
                let n' = newName n (frees ++ frees')
                e' <- apply (substExp n (Var n')) e
                return $ Lam n' e') 

substExp :: Name -> Exp -> R Exp
substExp v s = rule1 <+ rule2 <+ rule3 <+ rule4 <+ rule5 <+ rule6
 where
        -- From Lambda Calc Textbook, the 6 rules.
        rule1 = rewrite $ withVar $ \ n -> n == v ? return s
        rule2 = varP $ \ n -> n /= v ? idR
        rule3 = lamP $ \ n e -> n == v ? idR
        rule4 = lamP $ \ n e -> (n `notElem` freeExp s || v `notElem` freeExp e) 
                                ? allR (substExp v s)
        rule5 = lamP $ \ n e -> (n `elem` freeExp s && v `elem` freeExp e)
                                ? (shallowAlpha (freeExp s) >-> substExp v s)
        rule6 = appG >-> allR (substExp v s)

              
-------------

betaRedR :: R Exp
betaRedR = rewrite $ \ e ->
   case e of
     (App (Lam v e1) e2) -> apply (substExp v e2) e1
     _ -> fail "betaRed"

debugR :: (Show e) => String -> R e      
debugR msg = translate $ \ e -> transparently $ trace (msg ++ " : " ++ show e) (return e)




