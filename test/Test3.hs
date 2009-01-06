{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, MultiParamTypeClasses, TypeFamilies, FlexibleInstances  #-}

module Main where

import Language.KURE
import Language.KURE.Boilerplate
import Data.Monoid
import Data.List
import Debug.Trace

import Id

import Language.KURE.Boilerplate

{-
type Name = String	-- lower case
type Lit  = String	-- upper case or numerals

data Exp = Var Name
         | Lit Lit
         | App Exp Exp
         | APP Exp Type
         | Lam Name Type Exp
         | LAM Name Exp
         | Let Binding Exp
         | LET Name Type Exp
         | Case Exp [(Pat,Exp)] (Maybe Exp)
           deriving Show

data Binding = NonRecBinding Bind
             | RecBindings [Bind]	-- (v1,..,vn) = fix (\ (v1,..,vn) -> ...)
           deriving Show

type Bind = (Name,(Type,Exp))

data Type = TyCon Lit [Type]
          | TyVar Name
          | TyForAll Name Type
           deriving Show

type TypeEnv = [(Name,Type)]

data Pat = Pat Lit [(Name,Type)]
           deriving Show

data Program = Program TypeEnv [Binding]        -- The list of bindings are 
           deriving Show

data SystemFGeneric 
        = ExpG          Exp
        | BindingG      Binding
        | BindG         Bind
        | TypeG         Type
        | TypeEnvG      TypeEnv
        | PatG          Pat
        | ProgramG      Program

instance Term SystemFGeneric where {}
instance Term Program where {}
instance Term Pat where {}
instance Term [(String, Type)] where {}
instance Term Type where {}
instance Term (String,(Type,Exp)) where {}
instance Term Binding where {}
instance Term Exp where {}
-}

data SystemFGeneric 
        = ExpG          Exp
--        | ExpG2         (Exp,Int)
--  	| ExpG3		[Exp]
--	| ExpG4		[Int]
--	| ExpG5		[(Exp,Int)]

data Exp = Exp Int
	 | Exp2 [Int] (Exp,Exp) [Exp] (Maybe Exp)
 

instance Term SystemFGeneric where
	type Generic SystemFGeneric = SystemFGeneric
	select = Just
	inject = id
	
instance Term Exp where 
	type Generic Exp = SystemFGeneric
	select (ExpG e) = Just e
	select _        = Nothing
	inject          = ExpG
	
{-
instance Term (Exp,Int) where 
	type Generic (Exp,Int) = SystemFGeneric
instance Term [Exp] where 
	type Generic [Exp] = SystemFGeneric
instance Term [Int] where 
	type Generic [Int] = SystemFGeneric
instance Term [(Exp,Int)] where 
	type Generic [(Exp,Int)] = SystemFGeneric
-}

$(kureYourBoilerplate ''SystemFGeneric ''Id ''())

main = print "Hello"


