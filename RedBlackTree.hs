{-# OPTIONS -Wall #-}
{-# LANGUAGE EmptyDataDecls, ExistentialQuantification, GADTs #-}

module RedBlackTree
    ( RedBlackTree
    , redBlackEmpty, redBlackInsert
    , redBlackFromList, redBlackToList
    ) where

data Zero
data Succ n

data RedBlackTree a = forall n. RBTree (BlackNode n a)
data BlackNode n a where
    RBNil :: BlackNode Zero a
    BlackNode :: RBNode n a -> a -> RBNode n a -> BlackNode (Succ n) a
data RedNode n a = RedNode (BlackNode n a) a (BlackNode n a)
data RBNode n a
    = ItsRed (RedNode n a)
    | ItsBlack (BlackNode n a)

instance Show a => Show (RedBlackTree a) where
    show (RBTree tree) = show tree

instance Show a => Show (RBNode n a) where
    show (ItsRed tree) = show tree
    show (ItsBlack tree) = show tree

indentSide :: (Char, Char) -> String -> String
indentSide _ "" = ""
indentSide (leftIndent, rightIndent) side =
    unlines $ map (leftIndent:) left ++ ['+':mid] ++ map (rightIndent:) right
    where
        (left, mid:right) = break ((`notElem` " |+") . head) $ lines side

instance Show a => Show (RedNode n a) where
    show (RedNode left mid right) =
        indentSide (' ', '|') (show left) ++
        "R:" ++ show mid ++ "\n" ++
        indentSide ('|', ' ') (show right)

instance Show a => Show (BlackNode n a) where
    show RBNil = ""
    show (BlackNode left mid right) =
        indentSide (' ', '|') (show left) ++
        "B:" ++ show mid ++ "\n" ++
        indentSide ('|', ' ') (show right)

redBlackEmpty :: RedBlackTree a
redBlackEmpty = RBTree RBNil

redBlackFromList :: Ord a => [a] -> RedBlackTree a
redBlackFromList = foldr redBlackInsert redBlackEmpty

redBlackToList :: RedBlackTree a -> [a]
redBlackToList (RBTree node) = bNodeToList node

bNodeToList :: BlackNode n a -> [a]
bNodeToList RBNil = []
bNodeToList (BlackNode left x right) = rbNodeToList left ++ [x] ++ rbNodeToList right

rbNodeToList :: RBNode n a -> [a]
rbNodeToList (ItsRed (RedNode left x right)) = bNodeToList left ++ [x] ++ bNodeToList right
rbNodeToList (ItsBlack node) = bNodeToList node

redBlackInsert :: Ord a => a -> RedBlackTree a -> RedBlackTree a
redBlackInsert x (RBTree tree) =
    case bInsert x tree of
        ItsBlack newTree -> RBTree newTree
        ItsRed (RedNode left mid right) -> RBTree $ BlackNode (ItsBlack left) mid (ItsBlack right)

data InsertResult n a where
    ValidTree :: RBNode n a -> InsertResult n a
    RRB :: RedNode n a -> a -> BlackNode n a -> InsertResult n a
    BRR :: BlackNode n a -> a -> RedNode n a -> InsertResult n a

rbInsert :: Ord a => a -> RBNode n a -> InsertResult n a
rbInsert x (ItsBlack node) = ValidTree $ bInsert x node
rbInsert x (ItsRed (RedNode left mid right))
    | x < mid =
        case bInsert x left of
            ItsBlack newLeft -> ValidTree . ItsRed $ RedNode newLeft mid right
            ItsRed newLeft -> RRB newLeft mid right
    | otherwise =
        case bInsert x right of
            ItsBlack newRight -> ValidTree . ItsRed $ RedNode left mid newRight
            ItsRed newRight -> BRR left mid newRight

bInsert :: Ord a => a -> BlackNode n a -> RBNode n a
bInsert x RBNil = ItsRed $ RedNode RBNil x RBNil
bInsert x (BlackNode left mid right)
    | x < mid =
        case rbInsert x left of
            ValidTree newLeft -> ItsBlack $ BlackNode newLeft mid right
            RRB ll lm lr -> leftRrb ll lm lr
            BRR ll lm (RedNode lrl lrm lrr) -> leftRrb (RedNode ll lm lrl) lrm lrr
    | otherwise =
        case rbInsert x right of
            ValidTree newRight -> ItsBlack $ BlackNode left mid newRight
            BRR rl rm rr -> rightBrr rl rm rr
            RRB (RedNode rll rlm rlr) rm rr -> rightBrr rll rlm (RedNode rlr rm rr)
    where
        leftRrb ll lm lr =
            case right of
                ItsRed (RedNode rl rm rr) ->
                    ItsRed $ RedNode
                        (BlackNode (ItsRed ll) lm (ItsBlack lr))
                        mid
                        (BlackNode (ItsBlack rl) rm (ItsBlack rr))
                ItsBlack r ->
                    ItsBlack $ BlackNode
                        (ItsRed ll)
                        lm
                        (ItsRed (RedNode lr mid r))
        rightBrr rl rm rr =
            case left of
                ItsRed (RedNode ll lm lr) ->
                    ItsRed $ RedNode
                        (BlackNode (ItsBlack ll) lm (ItsBlack lr))
                        mid
                        (BlackNode (ItsBlack rl) rm (ItsRed rr))
                ItsBlack l ->
                    ItsBlack $ BlackNode
                        (ItsRed (RedNode l mid rl))
                        rm
                        (ItsRed rr)
