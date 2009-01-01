{-# LANGUAGE TemplateHaskell #-}
-- |
-- Module: Language.KURE.Boilerplate 
-- Copyright: (c) 2009 Andy Gill
-- License: BSD3
--
-- Maintainer: Andy Gill <andygill@ku.edu>
-- Stability: unstable
-- Portability: ghc
--
-- This module contains a Template Haskell based generator for the many data-type specific
-- functions that KURE want users to write. Kure Your Boilerplate (KYB) attempts to make
-- writing these function easy. Eventually, there will be a small DSL for effects inside the 
-- generated functions.
--
-- Unfortunately, you still need to write the 'Term' instance by hand, because of the use of
-- type families, a feature that post-dates Template Haskell. You also need to write
-- the single MyGeneric datatype.
--
--  'kureYourBoilerplate' generates a Walker instance for every data-type mentioned in your Generic,
-- and the following for every constructor in every data-structure that is mentioned in Generic, if the constructor
-- is called 'Foo', and have type @Foo :: A -> B -> C@.
--
--  * @fooR :: (...) => R A -> R B -> R C --@ congruence over @Foo@.
--
--  * @fooU :: (...,Monoid m) => T A r -> T B r -> T C r --@ unify the interesting arguments of a @Foo@
--
--  * @fooG :: (...) => R C --@ guard for the constructor @Foo@.
--
--  * @fooP :: (...) => (A -> B -> T C a) -> T C a --@ pattern matching on @Foo@.
--
--  * @withFoo :: (...,Failable) => (A -> B -> f a) -> C -> f a --@ application and pattern matching on @Foo@.
-- 
-- Here, R is short for a 'Rewrite m dec', and 'T is short for 'Translate m dec'.
--
-- An example of use is
--
-- > $(kureYourBoilerplate ''MyGeneric ''Id ''())
--
-- Which means @MyGeneric@ is my universal type, @Id@ is my monad, and @()@ is my monoid.

module Language.KURE.Boilerplate 
	( kureYourBoilerplate
	)

 where
        
import Language.KURE

import Language.Haskell.TH

import Data.Char
import Data.Monoid
import Control.Monad
import System.Environment

-- | 'kureYourBoilerplate' generates a number of functions for each data-type mentioned in
-- our given Generic data-type, which we need to provide for KURE, as well as the
-- Walker instance.
--
-- The first argument is the name of the Generic data-structure, which you need to write by hand.
-- If you provide the name of a type synonym as the first argument, then KYB assumes that you are acting
-- over a single data-type, i.e. you generic is your AST type.
-- If you provide the name of a data-type  (the typical use-case), then this function generates
-- code for every conceptual sub-type of the provided data-type.

-- The second argument is the monad over which you will be parameterizing your rewrite rules,
-- and the third argument is the monoid over which you will be parameterizing.
--
kureYourBoilerplate :: Name -> Name -> Name -> Q [Dec]
kureYourBoilerplate gname m dec = do
  debug <- runIO $ (do _k_debug <- getEnv "KURE_DEBUG"
		       return $ True) `catch` (\ _ -> return False)
  info <- reify gname
  tys <- case info of
            TyConI (DataD _ _ _ cons _) -> do
                -- we look at *types* so that we can support more in the future.
                let tys = [ argTy | (NormalC _ [(_,argTy)]) <- cons ]
                when (length tys /= length cons) $ do
                        fail $ "Strange type inside Generic datatype: " ++ show gname
                return tys
            TyConI (TySynD _ [] singleTy) -> 
                return [singleTy]
            _ -> fail $ "problem with generic type name " ++ show gname
  let tyNames = map pprint tys
  decs <- sequence [ kureType debug (ConT m,ConT dec) tyNames ty | ty <- tys ]
  when debug $ runIO $ do putStrLn $ pprint (concat decs)
  return $ concat decs

kureType :: Bool -> (Type,Type) -> [String] -> Type -> Q [Dec]
kureType debug (m,dec) tyNames ty@(ConT nm) = do
  info <- reify nm
  cons <- case info of
            TyConI (DataD _ _ _ cons _) -> return cons
            _ -> fail $ "strange info on name " ++ show nm
  (decs,consNames,argCounts) <- liftM unzip3 $ sequence [ kureCons debug tyNames con | con <- cons ]
  rr <- newName "rr"
  let buildFn name suffix extract = FunD (mkName $ name)
             [ Clause [VarP rr] (NormalB $ foldl1 choice alts) []]
          where
             choice e1 e2 = InfixE (Just e1) (VarE '(<+)) (Just e2)
             alts = [ foldl AppE (VarE (mkName $ consName ++ suffix))
                                 [ AppE (VarE extract) (VarE rr)
                                 | _ <- take argCount [(0::Int)..]
                                 ]
                    | (consName,argCount) <- zip consNames argCounts
                    ]
  let theInstance = InstanceD []
                              (foldl AppT (ConT ''Walker) [m,dec,ty]) 
                              [ buildFn "allR"   "R" 'extractR
                              , buildFn "crushU" "U" 'extractU
                              ]
                        

  return $ concat decs ++ [theInstance] 
kureType _debug _ _tyNames ty = fail $ "kureType: unsupported type :: " ++ show ty        

kureCons :: Bool -> [String] -> Con -> Q ([Dec],String,Int)
kureCons _debug tyNames (NormalC consName args)  = do 

        let guardName = mkName (combName consName ++ "G")
        v <- newName "v"
        let guardExpr = AppE (VarE 'acceptR)  (LamE [VarP v] 
              (CaseE (VarE v) 
                [ Match (RecP consName []) 
                        (NormalB (ConE 'True)) []
                , Match WildP (NormalB (ConE 'False)) []
                ]))
        let guardDef = ValD (VarP guardName) (NormalB guardExpr) []

        let withName = mkName ("with" ++ nameBase consName)
        (f:vs) <- mapM newName ("f": ["v" | _ <- args])
        let withDef = FunD withName 
               [ Clause [VarP f,ConP consName (map VarP vs)] (NormalB (foldl AppE (VarE f) (map VarE vs))) []
               , Clause [WildP,WildP] (NormalB (AppE (VarE 'failure) (LitE (StringL (show withName ++ " failed"))))) []
               ]

        let nameR = mkName (combName consName ++ "R")
        let interestingConsArgs = 
                [ case ty of
                    VarT {} -> error $ "found " ++ show ty ++ " as argument to " ++ show consName
                    ConT nm -> pprint nm `elem` tyNames
                    _ -> error $ "unsupported type " ++ show ty ++ " as argument to " ++ show consName                       
                | ty <- argsTypes
                ]

        rrs <- mapM newName [ "rr" | True <- interestingConsArgs ]
        es  <- mapM newName ["e"  | _ <- args ]
        es' <- sequence [ if interesting 
                          then liftM Just $ newName "e'" 
                          else return $ Nothing
                        | interesting <- interestingConsArgs ]

        let es'' = [ case opt_e' of
                       Just e' -> e'
                       _ -> e
                   | (e,opt_e') <- zip es es' 
                   ]

        let es'_rrs_es = [ (e',rr,e)
                         | (rr,(e,e')) <- zip rrs
                                [  (e,e') | (e,Just e') <- zip es es' ]
                         ]
                                      
        let nameRExpr = AppE (VarE 'rewrite) 
                             (AppE (VarE withName)
                                   (LamE (map VarP es) 
                                   (AppE (VarE 'transparently)
                                   (DoE (  [ BindS (VarP e')
                                                   (foldl AppE (VarE 'apply) (map VarE [rr,e]))
                                           | (e',rr,e) <- es'_rrs_es
                                           ]
                                       ++ [ NoBindS $ 
                                            AppE (VarE 'return) 
                                               $ foldl AppE (ConE consName) (map VarE es'')
                                          ])))))

        let nameRDef = FunD nameR [ Clause (map VarP rrs) (NormalB nameRExpr) []]

        let nameU = mkName (combName consName ++ "U")

        let nameUExpr = AppE (VarE 'translate) 
                             (AppE (VarE withName)
                                   (LamE (map VarP es) 
                                   (DoE (  [ BindS (VarP e')
                                                   (foldl AppE (VarE 'apply) (map VarE [rr,e]))
                                           | (e',rr,e) <- es'_rrs_es
                                           ]
                                       ++ [ NoBindS $ 
                                            AppE (VarE 'return) 
                                               $ AppE (VarE 'mconcat) (ListE (map VarE [ e' | Just e' <- es']))
                                          ]))))
        
--        let nameRDef = ValD (VarP nameR) (NormalB nameRExpr) []

        let nameUDef = FunD nameU [ Clause (map VarP rrs) (NormalB nameUExpr) []]

        let nameP = mkName (combName consName ++ "P")
        the_e <- newName "the_e"
        let namePExpr = AppE (VarE 'translate)
                             (LamE [VarP the_e]
                               (AppE (AppE (VarE withName)
                                     (LamE (map VarP es) 
                                       (AppE (VarE 'transparently)
                                           (AppE (AppE (VarE 'apply)
                                                       (foldl AppE (VarE f) (map VarE es))
                                                  )
                                                  (VarE the_e)
                                           )
                                       )
                                    )
                                ) (VarE the_e)
                           ))

        let namePDef = FunD nameP [ Clause [VarP f] (NormalB namePExpr) []]

        return ([guardDef,withDef,nameRDef,nameUDef,namePDef],combName consName,length rrs)
   where
        argsTypes = map snd args
kureCons _ _tyNames other  = error $ "Unsupported constructor : " ++ show other

combName :: Name -> String
combName nm = case nameBase nm of
                (t:ts) -> toLower t : ts
                [] -> ""