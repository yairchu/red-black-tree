{-# OPTIONS -Wall #-}
{-# LANGUAGE EmptyDataDecls, FlexibleInstances, GADTs #-}

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
nodeInsert x Nil = InsertResult InsertHigher (Node SameHeight Nil x Nil)
nodeInsert x node@(Node _ _ mid _) = nodeInsertH (x >= mid) x node

nodeInsertH :: Ord a => Bool -> a -> Node (Succ n) a -> InsertResult (Succ n) a
nodeInsertH isRev x node =
    case revNode isRev node of
    Node rule left mid right ->
        case nodeInsert x left of
        InsertResult InsertSame newLeft -> InsertResult InsertSame . revNode isRev $ Node rule newLeft mid right
        InsertResult InsertHigher newLeft -> nodeBalanceH isRev rule newLeft mid right

revNode :: Bool -> Node n a -> Node n a
revNode False x = x
revNode _ Nil = Nil
revNode True (Node rule left mid right) =
    case rule of
    LeftHigher -> go RightHigher
    SameHeight -> go SameHeight
    RightHigher -> go LeftHigher
    where
        go newRule = Node newRule right mid left

nodeBalanceH :: Bool -> HeightRule n l r -> Node (Succ l) a -> a -> Node r a -> InsertResult (Succ n) a
nodeBalanceH isRev rule left mid right =
    case rule of
    RightHigher -> go InsertSame SameHeight
    SameHeight -> go InsertHigher LeftHigher
    LeftHigher -> rotate isRev left mid right
    where
        go insRule newRule = InsertResult insRule . revNode isRev $ Node newRule left mid right

rotate :: Bool -> Node (Succ (Succ n)) a -> a -> Node n a -> InsertResult (Succ (Succ n)) a
rotate isRev l m r =
    case revNode isRev l of
    Node lRule ll lm lr ->
        let
            go0 r0 r1 r2 = InsertResult r0 . revNode isRev . Node r1 ll lm . revNode isRev $ Node r2 lr m r
        in
        case lRule of
        LeftHigher -> go0 InsertSame SameHeight SameHeight
        SameHeight -> go0 InsertHigher RightHigher LeftHigher
        RightHigher ->
            case revNode isRev lr of
            Nil -> undefined -- should never happen
            Node lrRule lrl lrm lrr ->
                let
                    go1 leftRule rightRule =
                        InsertResult InsertSame . revNode isRev $ Node SameHeight
                            (revNode isRev $ Node leftRule ll lm lrl)
                            lrm
                            (revNode isRev $ Node rightRule lrr m r)
                in
                case lrRule of
                LeftHigher -> go1 SameHeight RightHigher
                SameHeight -> go1 SameHeight SameHeight
                RightHigher -> go1 LeftHigher SameHeight
