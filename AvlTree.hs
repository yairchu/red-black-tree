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
nodeInsert x (Node rule left mid right)
    | x < mid =
        case nodeInsert x left of
        InsertResult InsertSame newLeft -> InsertResult InsertSame (Node rule newLeft mid right)
        InsertResult InsertHigher newLeft -> nodeInsertL rule newLeft mid right
    | otherwise =
        case nodeInsert x right of
        InsertResult InsertSame newRight -> InsertResult InsertSame (Node rule left mid newRight)
        InsertResult InsertHigher newRight -> nodeInsertR rule left mid newRight

nodeInsertL :: HeightRule n l r -> Node (Succ l) a -> a -> Node r a -> InsertResult (Succ n) a
nodeInsertL RightHigher left mid right = InsertResult InsertSame (Node SameHeight left mid right)
nodeInsertL SameHeight left mid right = InsertResult InsertHigher (Node LeftHigher left mid right)
nodeInsertL LeftHigher left mid right = rotateR left mid right

nodeInsertR :: HeightRule n l r -> Node l a -> a -> Node (Succ r) a -> InsertResult (Succ n) a
nodeInsertR LeftHigher left mid right = InsertResult InsertSame (Node SameHeight left mid right)
nodeInsertR SameHeight left mid right = InsertResult InsertHigher (Node RightHigher left mid right)
nodeInsertR RightHigher left mid right = rotateL left mid right

rotateR :: Node (Succ (Succ n)) a -> a -> Node n a -> InsertResult (Succ (Succ n)) a
rotateR (Node LeftHigher ll lm lr) m r = InsertResult InsertSame (Node SameHeight ll lm (Node SameHeight lr m r))
rotateR (Node SameHeight ll lm lr) m r = InsertResult InsertHigher (Node RightHigher ll lm (Node LeftHigher lr m r))
rotateR (Node RightHigher _ _ Nil) _ _ = undefined  -- cant be!
rotateR (Node RightHigher ll lm (Node RightHigher lrl lrm lrr)) m r =
    InsertResult InsertSame (Node SameHeight (Node LeftHigher ll lm lrl) lrm (Node SameHeight lrr m r))
rotateR (Node RightHigher ll lm (Node SameHeight lrl lrm lrr)) m r =
    InsertResult InsertSame (Node SameHeight (Node SameHeight ll lm lrl) lrm (Node SameHeight lrr m r))
rotateR (Node RightHigher ll lm (Node LeftHigher lrl lrm lrr)) m r =
    InsertResult InsertSame (Node SameHeight (Node SameHeight ll lm lrl) lrm (Node RightHigher lrr m r))

rotateL :: Node n a -> a -> Node (Succ (Succ n)) a -> InsertResult (Succ (Succ n)) a
rotateL l m (Node RightHigher rl rm rr) = InsertResult InsertSame (Node SameHeight (Node SameHeight l m rl) rm rr)
rotateL l m (Node SameHeight rl rm rr) = InsertResult InsertHigher (Node LeftHigher (Node RightHigher l m rl) rm rr)
rotateL _ _ (Node LeftHigher Nil _ _) = undefined  -- cant be!
rotateL l m (Node LeftHigher (Node LeftHigher rll rlm rlr) rm rr) =
    InsertResult InsertSame (Node SameHeight (Node SameHeight l m rll) rlm (Node RightHigher rlr rm rr))
rotateL l m (Node LeftHigher (Node SameHeight rll rlm rlr) rm rr) =
    InsertResult InsertSame (Node SameHeight (Node SameHeight l m rll) rlm (Node SameHeight rlr rm rr))
rotateL l m (Node LeftHigher (Node RightHigher rll rlm rlr) rm rr) =
    InsertResult InsertSame (Node SameHeight (Node LeftHigher l m rll) rlm (Node SameHeight rlr rm rr))
