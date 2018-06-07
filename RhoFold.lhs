\begin{code}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, AllowAmbiguousTypes #-}

module RhoFold(
  Nominal
  ,Name(..)
  ,Behavioral
  ,Process(..)
  ,RhoProcess
  ,procToIntegerList
  ,integerListToProc
  ,discriminator
  ,popen
  ,pclose
  ,nopen
  ,nclose
  ,unquote
  ,getNextEntity
  ,getLastEntity
  ,getSubject
  ,getObject
  ,getParLeft
  ,getParRight
  ,getContinuation
  ,getTransmission
  ,getNameCenter
  )
  where
import CLaSH.Sized.Unsigned (Unsigned)
import CLaSH.Sized.Vector (Vec((:>), Nil), 
        (!!), replace, repeat, (++), zip, take, drop, findIndex, mapAccumL)
import CLaSH.Class.Resize (zeroExtend)
import CLaSH.Sized.BitVector (BitVector, (++#), Bit)
import CLaSH.Class.BitPack (BitSize, pack, unpack)
import CLaSH.Prelude (slice, mealy, moore, bundle, unbundle, SNat)
import CLaSH.Promoted.Nat.Literals as Nat
import CLaSH.Promoted.Nat (SNat(..), addSNat, snatToNum, snatToInteger)
import CLaSH.Promoted.Nat.Unsafe
import CLaSH.Signal (Signal, register, sample, sampleN, signal, mux)
import CLaSH.Sized.Index (Index)

import Prelude (Show(..), Eq, print, (+), (-), (*), (==), (/=),(^),
    ($), (.), filter, fmap, mapM_, length, Functor,
    Bool(True,False), not, Maybe(Just,Nothing), (<$>), (<*>), undefined)

import qualified Prelude as H (zip,unzip,repeat,fromIntegral,floor,logBase,realToFrac,(++),(>),(<))
       
       
import Data.Ord
import qualified Data.List as DL

-- import Debug.Trace
-- tracey :: Show a => [Char] -> a -> a
-- tracey name x = trace ("\n" ++ name ++ ": " ++ show x) x

\end{code}

== The core data types

\begin{code}
class Signifier x where
  sign :: x -> (Unsigned 64)

class Nominal n where
  code :: (Signifier p) => p -> n p

data Name p = Address (Unsigned 64) | Code p deriving (Eq)

-- data Sign p = Sign { mark :: (Unsigned 64), name :: (Name p) } deriving (Eq,Show)

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

-- data RhoSignalProcess = Mirror (Process (Sign RhoSignalProcess)) deriving (Eq,Show)  

-- instance Behavioral Sign RhoSignalProcess where
--   zero = Mirror Stop
--   input x y (Mirror p) = Mirror (Input x y p)
--   output x (Mirror q) = Mirror (Output x q)
--   par (Mirror p) (Mirror q) = Mirror  (Par p q)
--   eval x = Mirror (Eval x)

exampleProc1 :: (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> (Name RhoProcess) -> RhoProcess
exampleProc1 w x1 y1 y2 y3 z1 u5 out = (Reflect p)
  where p  = (Par i1 p1)
        i1 = (Input x1 y1 p2)
        p1 = (Par o1 i2)
        p2 = (Par o2 i3)
        o1 = (Output x1 (Eval w))
        i2 = (Input y3 w o3)
        o2 = (Output y1 (Eval z1))
        o3 = (Output y3 (Eval u5))
        i3 = (Input z1 y2 o4)
        o4 = (Output out (Eval y2))

rpz   :: RhoProcess
rpz   = Reflect Stop
rpzn  :: Name RhoProcess
rpzn  = Code rpz
rpi1  :: RhoProcess      
rpi1  = Reflect (Input rpzn rpzn Stop)
rpi1n :: Name RhoProcess 
rpi1n = Code rpi1
rpo1  :: RhoProcess      
rpo1  = Reflect (Output rpzn Stop)
rpo1n :: Name RhoProcess 
rpo1n = Code rpo1
rpp1  :: RhoProcess      
rpp1  = Reflect (Par (let (Reflect p) = rpi1 in p) (let (Reflect p) = rpi1 in p))
rpp1n :: Name RhoProcess 
rpp1n = Code rpp1
rpp2  :: RhoProcess      
rpp2  = Reflect (Par (let (Reflect p) = rpi1 in p) (Par (let (Reflect p) = rpi1 in p) (let (Reflect p) = rpi1 in p)))
rpp2n :: Name RhoProcess
rpp2n = Code rpp2
rpp3  :: RhoProcess     
rpp3  = Reflect (Par (let (Reflect p) = rpo1 in p) (let (Reflect p) = rpo1 in p))
rpp3n :: Name RhoProcess 
rpp3n = Code rpp3
rpp4  :: RhoProcess
rpp4  = Reflect (Par (let (Reflect p) = rpo1 in p) (Par (let (Reflect p) = rpo1 in p) (let (Reflect p) = rpo1 in p)))
rpp4n :: Name RhoProcess
rpp4n = Code rpp4
rpp5  :: RhoProcess
rpp5  = Reflect (Par (let (Reflect p) = rpi1 in p) (let (Reflect p) = rpo1 in p))
rpp5n = Code rpp5

tp1   :: RhoProcess
tp1   = exampleProc1 rpzn rpi1n rpo1n rpp1n rpp2n rpp3n rpp4n rpp5n

\end{code}

== Arithmetic encodings

\begin{code}
procToIntegerList :: RhoProcess -> [(Unsigned 64)]
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

deBruijnify :: RhoProcess -> (Unsigned 64) -> (Unsigned 64) -> (Unsigned 64) -> RhoProcess
deBruijnify (Reflect Stop) l w h = (Reflect Stop)
deBruijnify (Reflect (Input (Code px) y q)) l w h = (Reflect (Input x dbny q''))
  where (Reflect q'')    = (substitute q' dbny y)
        q'     = (deBruijnify (Reflect q) (l+1) w h)
        x      = (Code (deBruijnify px l w (h+1)))
        dbny   = (Address dbnidx)
        dbnidx = (toNumber ((toBits l) H.++ (toBits w) H.++ (toBits h)))
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
flatten (Reflect (Par p q)) = (flatten (Reflect p)) H.++ (flatten (Reflect q))
flatten (Reflect (Eval (Code px))) = [(Reflect (Eval (Code px)))]
flatten (Reflect (Eval (Address addr))) = [(Reflect (Eval (Address addr)))]

enPar :: [RhoProcess] -> RhoProcess
enPar [] = (Reflect Stop)
enPar ((Reflect p):ps) = (Reflect (Par p q))
 where (Reflect q) = (enPar ps)

order :: [RhoProcess] -> [RhoProcess]
order ps = DL.sortBy (sortGT) ps
  where sortGT (Reflect Stop) (Reflect Stop) = EQ
        sortGT (Reflect Stop) _ = LT
        sortGT _ (Reflect Stop) = GT
        sortGT (Reflect (Eval (Code px))) (Reflect (Eval (Code qx))) = sortGT px qx
        sortGT (Reflect (Eval (Code px))) _ = LT
        sortGT _ (Reflect (Eval (Code px))) = GT
        sortGT (Reflect (Output (Code p1x) q1)) (Reflect (Output (Code p2x) q2)) =
          case ((sortGT p1x p2x),(sortGT (Reflect q1) (Reflect q2))) of
            (LT,LT) -> LT
            (LT,GT) -> GT
            (GT,LT) -> LT
            (GT,GT) -> GT
        sortGT (Reflect (Output (Code p1x) q1)) _ = LT
        sortGT _ (Reflect (Output (Code p1x) q1)) = GT
        sortGT (Reflect (Input (Code p1x) y1 q1)) (Reflect (Input (Code p2x) y2 q2)) =
          case ((sortGT p1x p2x),(sortGT (Reflect q1) (Reflect q2))) of
            (LT,LT) -> LT
            (LT,GT) -> GT
            (GT,LT) -> LT
            (GT,GT) -> GT
        sortGT (Reflect (Input (Code p1x) y1 q1)) _ = LT
        sortGT _ (Reflect (Input (Code p1x) y1 q1)) = GT
          

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

procToIntegerList (Reflect Stop) = tag
  where tag = (discriminator (Reflect Stop))
procToIntegerList (Reflect (Input (Code px) (Code py) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Code px) (Code py) q)))
        nx  = nopen H.++ (procToIntegerList px) H.++ nclose
        ny  = nopen H.++ (procToIntegerList py) H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Input (Address a) (Code py) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Address a) (Code py) q)))
        nx  = nopen H.++ [a] H.++ nclose
        ny  = nopen H.++ (procToIntegerList py) H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Input (Code px) (Address a) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Code px) (Address a) q)))
        nx  = nopen H.++ (procToIntegerList px) H.++ nclose
        ny  = nopen H.++ [a] H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Input (Address ax) (Address ay) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Address ax) (Address ay) q)))
        nx  = nopen H.++ [ax] H.++ nclose
        ny  = nopen H.++ [ay] H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Output (Code px) q)) = tag H.++ nx H.++ qx
  where tag = (discriminator (Reflect (Output (Code px) q)))
        nx  = nopen H.++ (procToIntegerList px) H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Output (Address a) q)) = tag H.++ nx H.++ qx
  where tag = (discriminator (Reflect (Output (Address a) q)))
        nx  = nopen H.++ [a] H.++ nclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Par p q)) = tag H.++ px H.++ qx
  where tag = (discriminator (Reflect (Par p q)))
        px  = popen H.++ (procToIntegerList (Reflect p)) H.++ pclose
        qx  = popen H.++ (procToIntegerList (Reflect q)) H.++ pclose
procToIntegerList (Reflect (Eval (Code px))) = tag H.++ nx
  where tag = (discriminator (Reflect (Eval (Code px))))
        nx  = nopen H.++ (procToIntegerList px) H.++ nclose

nameToIntegerVec (Code px) = (procToIntegerVec px)

procToIntegerVec (Reflect Stop) = tag 
  where tag = (discriminator (Reflect Stop))
procToIntegerVec (Reflect (Input (Code px) (Code py) q)) = tag H.++ nx H.++ ny H.++ qx 
  where tag = (discriminator (Reflect (Input (Code px) (Code py) q)))
        nx  = nopen H.++ (procToIntegerVec px) H.++ nclose
        ny  = nopen H.++ (procToIntegerVec py) H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose 
procToIntegerVec (Reflect (Input (Address a) (Code py) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Address a) (Code py) q)))
        nx  = nopen H.++ [a] H.++ nclose
        ny  = nopen H.++ (procToIntegerVec py) H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Input (Code px) (Address a) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Code px) (Address a) q)))
        nx  = nopen H.++ (procToIntegerVec px) H.++ nclose
        ny  = nopen H.++ [a] H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Input (Address ax) (Address ay) q)) = tag H.++ nx H.++ ny H.++ qx
  where tag = (discriminator (Reflect (Input (Address ax) (Address ay) q)))
        nx  = nopen H.++ [ax] H.++ nclose
        ny  = nopen H.++ [ay] H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Output (Code px) q)) = tag H.++ nx H.++ qx
  where tag = (discriminator (Reflect (Output (Code px) q)))
        nx  = nopen H.++ (procToIntegerVec px) H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Output (Address a) q)) = tag H.++ nx H.++ qx
  where tag = (discriminator (Reflect (Output (Address a) q)))
        nx  = nopen H.++ [a] H.++ nclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Par p q)) = tag H.++ px H.++ qx
  where tag = (discriminator (Reflect (Par p q)))
        px  = popen H.++ (procToIntegerVec (Reflect p)) H.++ pclose
        qx  = popen H.++ (procToIntegerVec (Reflect q)) H.++ pclose
procToIntegerVec (Reflect (Eval (Code px))) = tag H.++ nx
  where tag = (discriminator (Reflect (Eval (Code px))))
        nx  = nopen H.++ (procToIntegerVec px) H.++ nclose                

--        bit string   open paren   close paren   contents & remainder of the string
unquote :: [(Unsigned 64)] -> [(Unsigned 64)] -> [(Unsigned 64)] -> Maybe ([(Unsigned 64)], [(Unsigned 64)])
unquote (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) =
  if ([a,b,c,d] == [oa,ob,oc,od])
  then
    (h l [oa,ob,oc,od] [ca,cb,cc,cd] 1 [])
  else Nothing
  where h [] _ _ n acc                                        =
          (if (n > 0) then Nothing else Just (acc,[]))
        h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) 0 acc = Just (acc,(a:b:c:d:l))
        h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) n acc =
          (if ([a,b,c,d] == [oa,ob,oc,od])
            then
              (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n + 1) (acc H.++ [a,b,c,d]))
            else if ([a,b,c,d] == [ca,cb,cc,cd])
                 then (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n - 1) (if (n == 1) then acc else (acc H.++ [a,b,c,d])))
                 else (h l [oa,ob,oc,od] [ca,cb,cc,cd] n (acc H.++ [a,b,c,d])))

integerListToProc :: [(Unsigned 64)] -> Maybe RhoProcess
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

roundtrip :: RhoProcess -> Bool
roundtrip p = case (integerListToProc (procToIntegerList p)) of
  Just q -> p == q
  Nothing -> False

toNumber :: [(Unsigned 64)] -> (Unsigned 64)
toNumber [] = 0
toNumber l@(x:xs) = 2^((length l) - 1) * x + (toNumber xs)

--x - ((logBase 2 x)  | listlength = ((logBase 2 x) + 1) --subtract 1 from this every recursion
--this is your first value in the list
toBits :: (Unsigned 64) -> [(Unsigned 64)]
toBits 0 = []
toBits x = [1] H.++ l
  where l = (DL.take (m - n) (DL.repeat 0)) H.++ (if ((H.fromIntegral m) == d) then [] else r)
        m = (H.floor (H.realToFrac d))
        d = (H.logBase (H.fromIntegral 2) (H.fromIntegral x))
        n = (if ((H.fromIntegral m) == d) then 0 else (length r))
        r = (toBits (x - m))

-- instance Signifier RhoProcess where
--   sign = show . toNumber . procToIntegerList

-- instance Nominal Sign where
--   code p = Sign { mark = (sign p), name = Code p }

procToNumber :: RhoProcess -> (Unsigned 64)
procToNumber p = (toNumber (procToIntegerList p))

instance Show (Name RhoProcess) where
  show (Code p) = "@" H.++ (show (procToNumber p))

\end{code}

== New execution model

This procedure works
[| for( y1 <- x1 ){ y1!( *z1 ) | for( y2 <- z1 ){ output! y2 } } | x1!( *w ) | for( y3 <- w ){ y3!( 5 ) } |]
=
[( x1, [( y1, [y1, z1])], [*w] ), 
 ( w, [(y3, [y3])], [] ), 
 ( y1, [], [*z1] ),
 ( z1, [( y2, [output])], [] )
 ( output, [], [y2] )
 ( y3 [], [5])]
-> // merge ( w, [(y3, [y3])], [] ) and ( y1, [], [*z1] ), with w replacing y1
[( w, [(y3, [y3])], [*z1] ), 
 ( z1, [( y2, [output])], [] )
 ( output, [], [y2] )
 ( y3 [], [5])]
-> // merge ( z1, [( y2, [output])], [] ) and ( y3 [], [5])
[( z1, [( y2, [output,y3])], [5] )
 ( output, [], [y2] )]
-> // substitute y -> 5 into ( output, [], [y2] )
[( output, [], [5] )]

However, if we flip the record of the dependents to have children
point to their parents -- which we calculate at compilation, not in
the hardware -- then we have a much easier time determining which
are entries are redex sites. The function shred does this.

The function shred should be convertible into a fold, which makes
it potentially synthesizable. However, this is a compilation phase
computation and so doesn't have to be realized in hardware.

\begin{code}
surface :: RhoProcess -> [(Name RhoProcess)]
surface (Reflect Stop) = []
surface (Reflect (Input (Code px) y q)) = [(Code px)]
surface (Reflect (Output (Code px) q)) = [(Code px)]
surface (Reflect (Par p q)) = (surface (Reflect p)) H.++ (surface (Reflect q))
surface (Reflect (Eval n)) = [n]

expose :: (Name RhoProcess) -> [((Name RhoProcess), [((Name RhoProcess),[(Name RhoProcess)])],[RhoProcess])] -> ((Maybe ((Name RhoProcess), [((Name RhoProcess),[(Name RhoProcess)])],[RhoProcess])),[((Name RhoProcess), [((Name RhoProcess),[(Name RhoProcess)])],[RhoProcess])])
expose x [] = (Nothing,[])
expose x ((u,dpnds,prods):rs) =
  if (x == u)
  then ((Just (u,dpnds,prods)),rs)
  else let (trpl,rs') = (expose x rs) in
         (trpl, [(u,dpnds,prods)] H.++ rs')

reveal :: (Name RhoProcess) -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> ((Maybe ((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])),[((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])])
reveal x [] = (Nothing,[])
reveal x ((u,dpnds,prods):rs) =
  if (x == u)
  then ((Just (u,dpnds,prods)),rs)
  else let (trpl,rs') = (reveal x rs) in
         (trpl, [(u,dpnds,prods)] H.++ rs')

inform :: (Name RhoProcess) -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> ([((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])],[((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])])
inform x _ [] = ([],[])
inform x@(Code px) acc ((u,dpnds,prods):rs) =
  if (DL.elem px prods)
  then let (acc',rs') = (inform x acc rs) in (([(u,dpnds,prods)] H.++ acc'), rs')
  else let (acc',rs') = (inform x acc rs) in (acc', [(u,dpnds,prods)] H.++ rs')                  

-- to do: products should have parents too!
shred :: RhoProcess -> [(Name RhoProcess)] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])]

shred (Reflect Stop) parents rspace = rspace
shred (Reflect (Input x y q)) parents rspace = (shred (Reflect q) qprnts prspace)
  where prspace                         = [(x, xprnts, products)] H.++ rspace'
        qprnts                          = DL.foldl (H.++) [] (DL.map (\e -> let (mv,ps) = e in ps) xprnts)
        xprnts                          = [((Just y), parents H.++ [x])] H.++ xrprnts
        xrprnts                         = (DL.map (\pair -> let (mv,ps) = pair in (mv,(parents H.++ [x] H.++ ps))) rprnts) 
        (rprnts, products, rspace')     = case (reveal x rspace) of
                                            ((Just (_, rprnts, products)), rspace') ->
                                              (rprnts, products, rspace')
                                            (Nothing,rspace') -> ([],[],rspace')
shred (Reflect (Output x q)) parents rspace = (shred (Reflect q) qprnts prspace)
  where prspace                       = [(x, rprnts, products H.++ [(Reflect q)])] H.++ rspace'
        qprnts                        = DL.foldl (H.++) [] (DL.map (\e -> let (mv,ps) = e in ps) xprnts)
        xprnts                        = [(Nothing, [x] H.++ parents)] H.++ xrprnts
        xrprnts                       = (DL.map (\pair -> let (mv,ps) = pair in (mv,(parents H.++ [x] H.++ ps))) rprnts)
        (rprnts, products, rspace')   = case (reveal x rspace) of
                                          ((Just (_, rprnts, products)), rspace') ->
                                            (rprnts, products, rspace')
                                          (Nothing,rspace') -> ([],[],rspace')
shred (Reflect (Par p q)) parents rspace = (shred (Reflect q) parents (shred (Reflect p) parents rspace))
shred (Reflect (Eval (Code px))) parents rspace = (shred px parents rspace)

swap :: (Name RhoProcess) -> (Name RhoProcess) -> [RhoProcess] -> [RhoProcess]
swap (Code q) (Code p) [] = []
swap y@(Code q) x@(Code p) (r:rs) = [r'] H.++ (swap y x rs)
  where r' = (if (p == r) then q else r)

greet :: ((Maybe (Name RhoProcess)),[(Name RhoProcess)]) -> RhoProcess -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])]
greet ((Just y),[]) p rspace = 
  case (reveal y rspace) of
    ((Just (y,dpnds,prods)),rs) ->
      let (trps,rs') = (inform y [] rs) in
        rs' H.++ (DL.map (\trpl -> let (z,dpnds,prods) = trpl in (z,dpnds,(swap (Code p) y prods))) trps)      
    (Nothing,rs) -> rs H.++ [((Code p),[],[])]
greet _ _ rspace = rspace

meet :: ((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess]) -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])]

meet (x,(ylocs@((Just y),[]):[]),(prdct:[])) rspace = (greet ylocs prdct rspace)
meet t@(x,((my,(d:ds)):[]),(prdct:[])) rspace = [t]
meet (x,(ylocs@((Just y),[]):dpnds),(prdct:[])) rspace = (greet ylocs prdct rspace) H.++ [(x,dpnds,[])]
meet t@(x,(ylocs@(my,(d:ds)):dpnds),(prdct:[])) rspace = [t]
meet (x,(ylocs@((Just y),[]):[]),(prdct:prdcts)) rspace = (greet ylocs prdct rspace) H.++ [(x,[],prdcts)]
meet t@(x,(ylocs@(my,(d:ds)):[]),(prdct:prdcts)) rspace = [t]
meet (x,(ylocs@((Just y),[]):dpnds),(prdct:prdcts)) rspace =
  (meet (x,(ylocs:dpnds),(prdct:prdcts)) ((greet ylocs prdct rspace) H.++ rspace))
meet t@(x,(ylocs@(my,(d:ds)):dpnds),(prdct:prdcts)) rspace = [t]

reduce :: [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])]

reduce [] = []
reduce (t@(x,[],_) : rspace) = [t] H.++ (reduce rspace)
reduce (t@(x,_,[]) : rspace) = [t] H.++ (reduce rspace)
reduce (t@(x,dpnds,prdcts) : rspace) = rspace' H.++ (reduce rspace)
  where rspace' = (meet t rspace)
\end{code}

\begin{code}
newtype Word = Word (Unsigned 64) deriving Show

-- To do: this is still only an approximation as we need to put in a *pointer* rather than procToNumber
loadDpnd :: [Word] -> ((Maybe (Name RhoProcess)), [(Name RhoProcess)]) -> [Word]
loadDpnd acc (mx,parents) = acc DL.++ [(Word (prntlSz + 1))] DL.++ [(Word vn)] DL.++ prnts
  where prntlSz = (H.fromIntegral (length parents))
        prnts   = (DL.map (\(Code p) -> (Word (procToNumber p))) parents)        
        vn      = (case mx of (Just (Code x)) -> ((procToNumber x) + 1); Nothing -> 0)

loadDpnds :: [((Maybe (Name RhoProcess)), [(Name RhoProcess)])] -> [Word]
loadDpnds dpnds = (DL.foldl loadDpnd [] dpnds)         

loadPrdcts :: [RhoProcess] -> [Word]
loadPrdcts ps = (DL.map (\p -> (Word (procToNumber p))) ps)

rcrdToRAM :: ([((Name RhoProcess),(Unsigned 64))],[Word]) -> ((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess]) -> ([((Name RhoProcess),(Unsigned 64))],[Word])
rcrdToRAM  (nameAddrMap, ram) (x,dpnds,prdcts) = (nameAddrMap', ram')
  where dpndLn       = H.fromIntegral (length dpnds)
        prdctsLn     = H.fromIntegral (length prdcts)
        nIdx         = H.fromIntegral ((length ram) + 1)
        nameAddrMap' = (nameAddrMap DL.++ [(x,nIdx)])
        ram' = ram DL.++ [(Word dpndLn),(Word prdctsLn)] DL.++ (loadDpnds dpnds) DL.++ (loadPrdcts prdcts)

tblToRAM :: [((Name RhoProcess), [((Maybe (Name RhoProcess)),[(Name RhoProcess)])],[RhoProcess])] -> ([((Name RhoProcess),(Unsigned 64))],[Word])

tblToRAM rspace = (DL.foldl rcrdToRAM ([],[]) rspace)

    
\end{code}
