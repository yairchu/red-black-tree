{-# OPTIONS -Wall #-}
{-# LANGUAGE EmptyDataDecls, FlexibleInstances, GADTs #-}

module AvlTree
    ( Tree
    , empty, insert
    , fromList, toList
    ) where

import Data.List (foldl')

data Zero
data Succ n

data Tree a where
    Tree :: Node n a -> Tree a
data Node n a where
    Nil :: Node Zero a
    Node :: HeightRule n l r -> Node l a -> a -> Node r a -> Node (Succ n) a
data HeightRule n l r where
    SameHeight :: HeightRule n n n
    LeftHigher :: HeightRule (Succ n) (Succ n) n
    RightHigher :: HeightRule (Succ n) n (Succ n)

instance Show a => Show (Tree a) where
    show (Tree tree) = show tree
instance Show a => Show (Node n a) where
    show Nil = ""
    show (Node _ left mid right) =
        indentSide (' ', '|') (show left) ++
        show mid ++ "\n" ++
        indentSide ('|', ' ') (show right)
        where
            indentSide _ "" = ""
            indentSide (leftIndent, rightIndent) side =
                unlines $ map (leftIndent:) l ++ ['+':m] ++ map (rightIndent:) r
                where
                    (l, m:r) = break ((`notElem` " |+") . head) $ lines side

toList :: Tree a -> [a]
toList (Tree node) =
    nodeToList node
    where
        nodeToList :: Node n a -> [a]
        nodeToList (Node _ left mid right) = nodeToList left ++ [mid] ++ nodeToList right
        nodeToList _ = []

empty :: Tree a
empty = Tree Nil

fromList :: Ord a => [a] -> Tree a
fromList = foldl' (flip insert) empty

insert :: Ord a => a -> Tree a -> Tree a
insert x (Tree node) =
    case nodeInsert x node of
    InsertResult _ result -> Tree result

data InsertResult n a where
    InsertResult :: InsertResultRule new old -> Node new a -> InsertResult old a
data InsertResultRule new old where
    InsertSame :: InsertResultRule n n
    InsertHigher :: InsertResultRule (Succ n) n

nodeInsert :: Ord a => a -> Node n a -> InsertResult n a
nodeInsert x Nil = InsertResult auto (Node SameHeight Nil x Nil)
nodeInsert x node@(Node _ _ mid _) = nodeInsertH (x >= mid) x node

class Auto a where
    auto :: a
instance Auto (InsertResultRule n n) where
    auto = InsertSame
instance Auto (InsertResultRule (Succ n) n) where
    auto = InsertHigher
instance Auto (HeightRule (Succ n) (Succ n) n) where
    auto = LeftHigher
instance Auto (HeightRule n n n) where
    auto = SameHeight
instance Auto (HeightRule (Succ n) n (Succ n)) where
    auto = RightHigher

nodeInsertH :: Ord a => Bool -> a -> Node (Succ n) a -> InsertResult (Succ n) a
nodeInsertH isRev x node =
    case revNode isRev node of
    Node rule left mid right ->
        case nodeInsert x left of
        InsertResult InsertSame newLeft -> InsertResult auto . revNode isRev $ Node rule newLeft mid right
        InsertResult InsertHigher newLeft -> nodeBalanceH isRev rule newLeft mid right

revNode :: Bool -> Node n a -> Node n a
revNode False x = x
revNode _ Nil = Nil
revNode True (Node rule left mid right) =
    case rule of
    LeftHigher -> go auto
    SameHeight -> go auto
    RightHigher -> go auto
    where
        go newRule = Node newRule right mid left

nodeBalanceH :: Bool -> HeightRule n l r -> Node (Succ l) a -> a -> Node r a -> InsertResult (Succ n) a
nodeBalanceH isRev rule left mid right =
    case rule of
    RightHigher -> go SameHeight
    SameHeight -> go LeftHigher
    LeftHigher -> rotate isRev left mid right
    where
        go newRule = InsertResult auto . revNode isRev $ Node newRule left mid right

rotate :: Bool -> Node (Succ (Succ n)) a -> a -> Node n a -> InsertResult (Succ (Succ n)) a
rotate isRev l m r =
    case revNode isRev l of
    Node lRule ll lm lr ->
        let
            go0 r1 = InsertResult auto . revNode isRev . Node r1 ll lm . revNode isRev $ Node auto lr m r
        in
        case lRule of
        LeftHigher -> go0 SameHeight
        SameHeight -> go0 RightHigher
        RightHigher ->
            case revNode isRev lr of
            Nil -> undefined -- should never happen
            Node lrRule lrl lrm lrr ->
                let
                    go1 leftRule =
                        InsertResult auto . revNode isRev $ Node SameHeight
                            (revNode isRev $ Node leftRule ll lm lrl)
                            lrm
                            (revNode isRev $ Node auto lrr m r)
                in
                case lrRule of
                LeftHigher -> go1 SameHeight
                SameHeight -> go1 SameHeight
                RightHigher -> go1 LeftHigher
