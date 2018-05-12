\begin{code}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, AllowAmbiguousTypes #-}

module RhoCalcHW(
  Nominal
  ,Name
  ,Behavioral
  ,Process
  ,RhoProcess
--  ,procToIntegerList
--  ,integerListToProc
  ,discriminator
  ,popen
  ,pclose
  ,nopen
  ,nclose
  ,kApply
  ,toNumber
  ,toBits
  ,procToIntegerList
  ,integerListToProc
  -- ,unquote
  -- ,getNextEntity
  -- ,getLastEntity
  -- ,getSubject
  -- ,getObject
  -- ,getParLeft
  -- ,getParRight
  -- ,getContinuation
  -- ,getTransmission
  -- ,getNameCenter
  )
  where
-- import Debug.Trace
-- tracey :: Show a => [Char] -> a -> a
-- tracey name x = trace (name ++ ": " ++ show x) x

import CLaSH.Sized.Unsigned (Unsigned)
import CLaSH.Sized.Vector (Vec((:>), Nil), 
        (!!), replace, repeat, (++), zip)
import CLaSH.Class.Resize (zeroExtend)
import CLaSH.Sized.BitVector (BitVector, (++#), Bit)
import CLaSH.Class.BitPack (pack, unpack)
import CLaSH.Prelude (slice, mealy, moore, bundle, unbundle)
import CLaSH.Promoted.Nat.Literals as Nat
import CLaSH.Signal (Signal, register, sample, sampleN, signal, mux)
import CLaSH.Sized.Index (Index)
    
import Prelude (Show, Eq, print, (+), (-), (*), (==), (/=),(^),
    ($), (.), filter, take, fmap, mapM_, length, Functor,
    Bool(True,False), not, Maybe(Just,Nothing), (<$>), (<*>), undefined)
import qualified Prelude as Plude (zip,unzip,repeat,floor,logBase,fromIntegral,realToFrac,(++),(>))
import qualified Data.List as DL (sortBy)
import qualified Data.Ord as DO ( Ordering(..) )

class Nominal n where
  code :: p -> n p

data Name p = Address (Unsigned 64) | Code p deriving (Eq,Show)

instance Nominal Name where
  code = Code

class (Nominal n) => Behavioral n p | n -> p where
  zero :: p
  input :: (Nominal n, Eq (n p)) => (n p) -> (n p) -> p -> p
  output :: (Nominal n, Eq (n p)) => (n p) -> p -> p
  par :: p -> p -> p
  eval :: (Nominal n, Eq (n p)) => (n p) -> p

data Process x = Stop 
  | Input x x (Process x)
  | Output x (Process x) 
  | Par (Process x) (Process x)
  | Eval x deriving (Eq,Show)

data RhoProcess = Reflect (Process (Name RhoProcess)) deriving (Eq,Show)

instance Behavioral Name RhoProcess where
  zero = Reflect Stop
  input x y (Reflect p) = Reflect (Input x y p)
  output x (Reflect q) = Reflect (Output x q)
  par (Reflect p) (Reflect q) = Reflect  (Par p q)
  eval x = Reflect (Eval x)

procToIntegerList :: RhoProcess -> [(Unsigned 64)]
nameToIntegerList :: (Name RhoProcess) -> [(Unsigned 64)]
discriminator :: RhoProcess -> [(Unsigned 64)]
popen :: [(Unsigned 64)]
pclose :: [(Unsigned 64)]
nopen :: [(Unsigned 64)]
nclose :: [(Unsigned 64)]

discriminator (Reflect Stop)          = [0,0,0,0]
discriminator (Reflect (Input _ _ _)) = [0,0,0,1]
discriminator (Reflect (Output _ _))  = [0,0,1,0]
discriminator (Reflect (Par _ _))     = [0,0,1,1]
discriminator (Reflect (Eval _))      = [0,1,0,0]

popen                                 = [0,1,0,1]
pclose                                = [0,1,1,0]
nopen                                 = [0,1,1,1]
nclose                                = [1,0,0,0]


-- Known issues: in order to provide name equality as bit compare we ...
-- must produce bit vectors for addresses
-- must provide a canonical order for pars
-- must use DeBruijn indices for bound variables
--   [| for( y <- x )P |](l,w,h) = let z = [| (l,w,h) |] in for( z <- x )([| P |](l+1,w,h){z/y})
--   [| for( y1 <- x1 )P1 | ... | for( yN <- xN )PN |](l,w,h) 
--   = let z1 = [| (l,w,h) |] in ... let zN = [| w + N-1 |] in
--     for( z1 <- x )([| P |](l+1,w,h){z1/y}) | ... | for( z <- x )([| P |](l+1,w + N-1,h){zN/y})
-- h is used for descent into names

substitute :: RhoProcess -> Name RhoProcess -> Name RhoProcess -> RhoProcess
substitute (Reflect Stop) y x = (Reflect Stop)
substitute (Reflect (Input a b q)) y x = (Reflect (Input a' b' q'))
  where a' = (if (a == x) then y else a)
        b' = (if (b == x) then (Code (Reflect (Par (Eval b) q))) else b)
        (Reflect q') = (substitute q'' y x)
        q'' = (if (b == x) then (substitute (Reflect q) b' b) else (Reflect q))
substitute (Reflect (Output a q)) y x = (Reflect (Output a' q'))
  where a' = (if (a == x) then y else a)
        (Reflect q') = (substitute (Reflect q) y x)
substitute (Reflect (Par p q)) y x = (Reflect (Par p' q'))
  where (Reflect p') = (substitute (Reflect p) y x)
        (Reflect q') = (substitute (Reflect q) y x)
substitute (Reflect (Eval a)) y x = (Reflect (Eval a'))
  where a' = (if (a == x) then y else a)

kApply :: RhoProcess -> RhoProcess -> RhoProcess
kApply p@(Reflect (Input x y p')) q = (substitute p (Code q) y)
kApply p _ = p -- should throw and error instead

toNumber :: [(Unsigned 64)] -> (Unsigned 64)
toNumber [] = 0
toNumber l@(x:xs) = 2^((length l) - 1) * x + (toNumber xs)

--x - ((logBase 2 x)  | listlength = ((logBase 2 x) + 1) --subtract 1 from this every recursion
--this is your first value in the list
toBits :: (Unsigned 64) -> [(Unsigned 64)]
toBits 0 = []
toBits x = [1] Plude.++ l
  where l = (take (m - n) (Plude.repeat 0)) Plude.++ (if ((Plude.fromIntegral m) == d) then [] else r)
        m = (Plude.floor (Plude.realToFrac d))
        d = (Plude.logBase (Plude.fromIntegral 2) (Plude.fromIntegral x))
        n = (if ((Plude.fromIntegral m) == d) then 0 else (length r))
        r = (toBits (x - m))  

deBruijnify :: RhoProcess -> (Unsigned 64) -> (Unsigned 64) -> (Unsigned 64) -> RhoProcess
deBruijnify (Reflect Stop) l w h = (Reflect Stop)
deBruijnify (Reflect (Input (Code px) y q)) l w h = (Reflect (Input x dbny q''))
  where (Reflect q'')    = (substitute q' dbny y)
        q'     = (deBruijnify (Reflect q) (l+1) w h)
        x      = (Code (deBruijnify px l w (h+1)))
        dbny   = (Address dbnidx)
        dbnidx = (toNumber ((toBits l) Plude.++ (toBits w) Plude.++ (toBits h)))
deBruijnify (Reflect (Output (Code px) q)) l w h = (Reflect (Output x q'))
  where x               = (Code (deBruijnify px l w (h+1)))
        (Reflect q')    = (deBruijnify (Reflect q) l w h)
deBruijnify (Reflect (Par p q)) l w h = (Reflect (Par p' q'))
  where (Reflect p')    = (deBruijnify (Reflect p) l w h)
        (Reflect q')    = (deBruijnify (Reflect q) l (w+1) h)
deBruijnify (Reflect (Eval (Code px))) l w h = (Reflect (Eval x))
  where x     = (Code (deBruijnify px l w (h+1)))
deBruijnify (Reflect (Eval (Address addr))) l w h = (Reflect (Eval (Address addr)))

flatten :: RhoProcess -> [RhoProcess]
flatten (Reflect Stop) = [(Reflect Stop)]
flatten (Reflect (Input (Code px) y q)) = [(Reflect (Input (Code px) y q))]
flatten (Reflect (Output (Code px) q)) = [(Reflect (Output (Code px) q))]
flatten (Reflect (Par p q)) = (flatten (Reflect p)) Plude.++ (flatten (Reflect q))
flatten (Reflect (Eval (Code px))) = [(Reflect (Eval (Code px)))]
flatten (Reflect (Eval (Address addr))) = [(Reflect (Eval (Address addr)))]

enPar :: [RhoProcess] -> RhoProcess
enPar [] = (Reflect Stop)
enPar ((Reflect p):ps) = (Reflect (Par p q))
 where (Reflect q) = (enPar ps)

order :: [RhoProcess] -> [RhoProcess]
order ps = DL.sortBy (sortGT) ps
  where sortGT (Reflect Stop) (Reflect Stop) = DO.EQ
        sortGT (Reflect Stop) _ = DO.LT
        sortGT _ (Reflect Stop) = DO.GT
        sortGT (Reflect (Eval (Code px))) (Reflect (Eval (Code qx))) = sortGT px qx
        sortGT (Reflect (Eval (Code px))) _ = DO.LT
        sortGT _ (Reflect (Eval (Code px))) = DO.GT
        sortGT (Reflect (Output (Code p1x) q1)) (Reflect (Output (Code p2x) q2)) =
          case ((sortGT p1x p2x),(sortGT (Reflect q1) (Reflect q2))) of
            (DO.LT,DO.LT) -> DO.LT
            (DO.LT,DO.GT) -> DO.GT
            (DO.GT,DO.LT) -> DO.LT
            (DO.GT,DO.GT) -> DO.GT
        sortGT (Reflect (Output (Code p1x) q1)) _ = DO.LT
        sortGT _ (Reflect (Output (Code p1x) q1)) = DO.GT
        sortGT (Reflect (Input (Code p1x) y1 q1)) (Reflect (Input (Code p2x) y2 q2)) =
          case ((sortGT p1x p2x),(sortGT (Reflect q1) (Reflect q2))) of
            (DO.LT,DO.LT) -> DO.LT
            (DO.LT,DO.GT) -> DO.GT
            (DO.GT,DO.LT) -> DO.LT
            (DO.GT,DO.GT) -> DO.GT
        sortGT (Reflect (Input (Code p1x) y1 q1)) _ = DO.LT
        sortGT _ (Reflect (Input (Code p1x) y1 q1)) = DO.GT
          

normalizeP :: RhoProcess -> RhoProcess
normalizeP (Reflect Stop) = (Reflect Stop)
normalizeP (Reflect (Input (Code px) y q)) = (Reflect (Input x y q'))
  where (Reflect q')    = (normalizeP (Reflect q))
        x               = (Code (normalizeP px))
normalizeP (Reflect (Output (Code px) q)) = (Reflect (Output x q'))
  where x               = (Code (normalizeP px))
        (Reflect q')    = (normalizeP (Reflect q))
normalizeP ppq@(Reflect (Par p q)) = (enPar (order (flatten ppq)))
  where (Reflect p')    = (normalizeP (Reflect p))
        (Reflect q')    = (normalizeP (Reflect q))
normalizeP (Reflect (Eval (Code px))) = (Reflect (Eval x))
  where x     = (Code (normalizeP px))
normalizeP (Reflect (Eval (Address addr))) = (Reflect (Eval (Address addr)))

normalize :: RhoProcess -> RhoProcess
normalize p = (normalizeP (deBruijnify p 0 0 0))  

nameToIntegerList (Code px) = (procToIntegerList px)

procToIntegerList (Reflect Stop) = tag 
  where tag = (discriminator (Reflect Stop))
procToIntegerList (Reflect (Input (Code px) (Code py) q)) = tag Plude.++ nx Plude.++ ny Plude.++ qx 
  where tag = (discriminator (Reflect (Input (Code px) (Code py) q)))
        nx  = nopen Plude.++ (procToIntegerList px) Plude.++ nclose
        ny  = nopen Plude.++ (procToIntegerList py) Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose 
procToIntegerList (Reflect (Input (Address a) (Code py) q)) = tag Plude.++ nx Plude.++ ny Plude.++ qx
  where tag = (discriminator (Reflect (Input (Address a) (Code py) q)))
        nx  = nopen Plude.++ [a] Plude.++ nclose
        ny  = nopen Plude.++ (procToIntegerList py) Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Input (Code px) (Address a) q)) = tag Plude.++ nx Plude.++ ny Plude.++ qx
  where tag = (discriminator (Reflect (Input (Code px) (Address a) q)))
        nx  = nopen Plude.++ (procToIntegerList px) Plude.++ nclose
        ny  = nopen Plude.++ [a] Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Input (Address ax) (Address ay) q)) = tag Plude.++ nx Plude.++ ny Plude.++ qx
  where tag = (discriminator (Reflect (Input (Address ax) (Address ay) q)))
        nx  = nopen Plude.++ [ax] Plude.++ nclose
        ny  = nopen Plude.++ [ay] Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Output (Code px) q)) = tag Plude.++ nx Plude.++ qx
  where tag = (discriminator (Reflect (Output (Code px) q)))
        nx  = nopen Plude.++ (procToIntegerList px) Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Output (Address a) q)) = tag Plude.++ nx Plude.++ qx
  where tag = (discriminator (Reflect (Output (Address a) q)))
        nx  = nopen Plude.++ [a] Plude.++ nclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Par p q)) = tag Plude.++ px Plude.++ qx
  where tag = (discriminator (Reflect (Par p q)))
        px  = popen Plude.++ (procToIntegerList (Reflect p)) Plude.++ pclose
        qx  = popen Plude.++ (procToIntegerList (Reflect q)) Plude.++ pclose
procToIntegerList (Reflect (Eval (Code px))) = tag Plude.++ nx
  where tag = (discriminator (Reflect (Eval (Code px))))
        nx  = nopen Plude.++ (procToIntegerList px) Plude.++ nclose

--       bit string   open paren   close paren   contents & remainder of the string
unquote :: [(Unsigned 64)] -> [(Unsigned 64)] -> [(Unsigned 64)] -> Maybe ([(Unsigned 64)], [(Unsigned 64)])
unquote (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) =
  if ([a,b,c,d] == [oa,ob,oc,od])
  then
    (h l [oa,ob,oc,od] [ca,cb,cc,cd] 1 [])
  else Nothing
  where h [] _ _ n acc                                        =
          (if (n Plude.> 0) then Nothing else Just (acc,[]))
        h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) 0 acc = Just (acc,(a:b:c:d:l))
        h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) n acc =
          (if ([a,b,c,d] == [oa,ob,oc,od])
            then
              (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n + 1) (acc Plude.++ [a,b,c,d]))
            else if ([a,b,c,d] == [ca,cb,cc,cd])
                 then (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n - 1) (if (n == 1) then acc else (acc Plude.++ [a,b,c,d])))
                 else (h l [oa,ob,oc,od] [ca,cb,cc,cd] n (acc Plude.++ [a,b,c,d])))

integerListToProc :: [(Unsigned 64)] -> Maybe RhoProcess
integerListToName :: [(Unsigned 64)] -> Maybe (Name RhoProcess)
getSubject :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
getObject :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
getContinuation :: [(Unsigned 64)] -> Maybe RhoProcess
getTransmission :: [(Unsigned 64)] -> Maybe RhoProcess
getParLeft :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
getParRight :: [(Unsigned 64)] -> Maybe RhoProcess
getNameCenter :: [(Unsigned 64)] -> Maybe RhoProcess

-- todo: replace with do-blocks

getNextEntity l open close =
  case (unquote l open close) of
   Just (contents, remainder) -> (case (integerListToProc contents) of
     Just p -> Just (p, remainder)
     Nothing -> Nothing)
   Nothing -> Nothing

getLastEntity l open close =
  case (unquote l open close) of
   Just (contents, []) -> (integerListToProc contents)
   _ -> Nothing

getNextName l = getNextEntity l nopen nclose

getSubject l = getNextName l  
   
getObject l = getNextName l

getParLeft l = getNextEntity l popen pclose

getContinuation l = getLastEntity l popen pclose

getTransmission l = getLastEntity l popen pclose

getParRight l = getLastEntity l popen pclose

getNameCenter l = getLastEntity l nopen nclose

integerListToProc [] = Just (Reflect Stop)
integerListToProc (0:0:0:0:[]) = Just (Reflect Stop)
integerListToProc (0:0:0:1:l) = 
  case (getSubject l) of
    Just (px,l') -> (case (getObject l') of
      Just (py,l'') -> (case (getContinuation l'') of        
        Just (Reflect q) -> Just (Reflect (Input (Code px) (Code py) q))
        Nothing -> Nothing)
      Nothing -> Nothing)
    Nothing -> Nothing      
integerListToProc (0:0:1:0:l) =
  case (getSubject l) of 
    Just (px,l') -> (case (getTransmission l') of
      Just (Reflect q) -> Just (Reflect (Output (Code px) q))
      Nothing -> Nothing)
    Nothing -> Nothing
integerListToProc (0:0:1:1:l) =
  case (getParLeft l) of 
    Just (pl,l') -> (case (getParRight l') of 
      Just pr -> (case (pl,pr) of
        ((Reflect ql),(Reflect qr)) -> Just (Reflect (Par ql qr)))
      Nothing -> Nothing)
    Nothing -> Nothing
integerListToProc (0:1:0:0:l) = 
  case (getNameCenter l) of
    Just q -> Just (Reflect (Eval (Code q)))
    Nothing -> Nothing

integerListToName l@(0:1:1:1:rl) =
  case (getNameCenter l) of
    Just q -> (Code q)
    Nothing -> Nothing

roundtrip :: RhoProcess -> Bool
roundtrip p = case (integerListToProc (procToIntegerList p)) of
  Just q -> p == q
  Nothing -> False
\end{code}
