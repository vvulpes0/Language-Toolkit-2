> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.JoinVariety
> Copyright : (c) 2025 Dakotah Lambert
> License   : MIT

> This module provides a mechanism for deciding membership
> in conjunctive varieties.  It extends the systems defined by
> LTK.Decide.Variety, but the more complex structure used
> incurs a performance cost.
>
> @since 1.3
> -}

> module LTK.Decide.JoinVariety ( isJoinVariety
>                               , isMJoinVariety
>                               , isJoinVarietyJS
>                               ) where

> import Data.Char (isLetter, isSpace)
> import qualified Data.Map as Map
> import qualified Data.Set as Set

> import LTK.FSA ( FSA
>                , JSemigroup
>                , neutralize
>                , renameSymbolsByMonotonic
>                , syntacticJSemigroup
>                )

> -- |Determine if the syntactic join-monoid of the given language
> -- is a member of the variety given by equations and inequalities.
> -- The precondition, that the automaton be normalized, is not checked.
> isMJoinVariety :: (Ord n, Ord e) => String -> FSA n e -> Maybe Bool
> isMJoinVariety s = isJoinVariety s
>                    . neutralize (Set.singleton Nothing)
>                    . renameSymbolsByMonotonic Just

> -- |Determine if the syntactic join-semigroup of the given language
> -- is a member of the variety given by equations and inequalities.
> -- The precondition, that the automaton be normalized, is not checked.
> isJoinVariety :: (Ord n, Ord e) => String -> FSA n e -> Maybe Bool
> isJoinVariety s = isJoinVarietyJS s . syntacticJSemigroup

> -- |Determine if the given join-semigroup is a member of the variety
> -- given by equations and inequalities.
> isJoinVarietyJS :: Ord e => String -> JSemigroup e -> Maybe Bool
> isJoinVarietyJS s j
>     | take 1 s' /= "[" = Nothing
>     | take 1 (reverse s') /= "]" = Nothing
>     | otherwise = and <$> (mapM (universallySatisfies j) =<< progs)
>     where s' = expand s
>           s'' = reverse . drop 1 . reverse $ drop 1 s'
>           progs = sequenceA . map (flip shunt []) $ splitOn ';' s''

> jsappend :: [Int] -> [Int] -> [Int]
> jsappend x y = map (y!!) x

> jsomega :: [Int] -> [Int]
> jsomega x = head' . snd . break idem $ iterate (jsappend x) x
>     where head' y = case y of
>                       (yy:_) -> yy
>                       _ -> error "unbounded omega search"
>           idem y = jsappend y y == y

> jsjoin :: JSemigroup e -> [Int] -> [Int] -> [Int]
> jsjoin ((q2qs,qs2q),_) = zipWith g
>     where g x y = qs2q Map.! ((q2qs Map.! x) `Set.union` (q2qs Map.! y))

> universallySatisfies :: Ord e => JSemigroup e -> [Token] -> Maybe Bool
> universallySatisfies j@(_,(_,a2s)) ts
>     = case filter isVar ts of
>         (x:_) -> fmap and . sequenceA
>                  . map (universallySatisfies j . bind x)
>                  $ Map.keys a2s
>         _ -> satisfies j ts' []
>     where bind x a = map (\t -> if t == x then TAction a else t) ts
>           ts' = let unit = case Map.keys a2s of
>                              (m:_) -> zipWith const [0..] m
>                              _ -> []
>                 in map (\t -> if t == TUnit
>                               then (if unit `Map.member` a2s
>                                     then TAction unit
>                                     else TUnit)
>                               else t) ts
>           isVar (TVariable _) = True
>           isVar _ = False

> satisfies :: JSemigroup e -> [Token] -> [Token] -> Maybe Bool
> satisfies _ [] _ = Just True
> satisfies j (t@(TAction _):ts) stack = satisfies j ts (t:stack)
> satisfies j (TConcat : ts) (TAction y : TAction x : stack)
>     = satisfies j ts (TAction (jsappend x y) : stack)
> satisfies j (TJoin : ts) (TAction y : TAction x : stack)
>     = satisfies j ts (TAction (jsjoin j x y) : stack)
> satisfies j (TOmega : ts) (TAction x : stack)
>     = satisfies j ts (TAction (jsomega x) : stack)
> satisfies j (TLEQ : ts) (TAction y : TAction x : stack)
>     | jsjoin j x y == y = satisfies j ts (TAction x : stack)
>     | otherwise = Just False
> satisfies j (TEQ : ts) (TAction y : TAction x : stack)
>     | x == y = satisfies j ts (TAction x : stack)
>     | otherwise = Just False
> satisfies j (TGEQ : ts) (TAction y : TAction x : stack)
>     | jsjoin j x y == x = satisfies j ts (TAction x : stack)
>     | otherwise = Just False
> satisfies _ _ _ = Nothing

> data Token = TVariable Char
>            | TAction [Int]
>            | TUnit
>            | TConcat
>            | TJoin
>            | TOmega
>            | TLEQ
>            | TEQ
>            | TGEQ
>              deriving (Eq, Ord, Read, Show)

> prec :: Char -> Int
> prec '*' = 10
> prec '.' = 8
> prec '+' = 5
> prec  _  = 0

> -- |Make explicit any implicit concatenation.
> expand :: String -> String
> expand (x:y:s)
>     | shouldDot = x : '.' : expand (y:s)
>     | isSpace x = expand (y:s)
>     | otherwise = x : expand (y:s)
>     where shouldDot = (isLetter x || x == '*' || x == ')')
>                       && (isLetter y || y == '(')
> expand s = filter (not . isSpace) s

> shunt :: String -> [Char] -> Maybe [Token]
> shunt "" [] = Just []
> shunt "" (s:ss) = (:) <$> tokenify s <*> shunt "" ss
> shunt (x:xs) stack
>     | isLetter x = (TVariable x :) <$> shunt xs stack
>     | x == '1' = (TUnit :) <$> shunt xs stack
>     | x == '(' = shunt xs ('(':stack)
>     | x == ')' = let (ops,s) = break (== '(') stack
>                  in case s of
>                       ('(':ss) -> (++) <$> flush ops <*> shunt xs ss
>                       _ -> Nothing
>     | prec x == 0 = if '(' `elem` stack then Nothing else go
>     | otherwise = go
>     where flush = sequenceA . map tokenify
>           go = let (tighter,s) = span (\p -> prec p > prec x) stack
>                in (++) <$> flush tighter <*> shunt xs (x:s)

> tokenify :: Char -> Maybe Token
> tokenify '*' = Just TOmega
> tokenify '+' = Just TJoin
> tokenify '<' = Just TLEQ
> tokenify '≤' = Just TLEQ
> tokenify '=' = Just TEQ
> tokenify '≥' = Just TGEQ
> tokenify '>' = Just TGEQ
> tokenify '.' = Just TConcat
> tokenify  _  = Nothing


Helpers
=======

> splitOn :: Eq a => a -> [a] -> [[a]]
> splitOn x xs = let (a,b) = break (== x) xs
>                in if null b then [a] else a : splitOn x (drop 1 b)
