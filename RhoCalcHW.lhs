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
    
import Prelude (Show, Eq, print, (+), (-), (*), (==), (/=),
    ($), (.), filter, take, fmap, mapM_, Functor,
    Bool(True,False), not, Maybe(Just,Nothing), (<$>), (<*>), undefined)
import qualified Prelude as Plude (zip,unzip)    

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

--procToIntegerList :: RhoProcess -> [(Unsigned 64)]
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
-- must use DeBruijn indices for bound variables
-- must provide a canonical order for pars
procToIntegerList (Reflect Stop) = tag 
  where tag = (discriminator (Reflect Stop))
procToIntegerList _ = [1,1,1,1]  
-- procToIntegerList (Reflect (Input (Code px) (Code py) q)) = tag ++ nx ++ ny ++ qx
--   where tag = (discriminator (Reflect (Input (Code px) (Code py) q)))
--         nx  = nopen ++ (procToIntegerList px) ++ nclose
--         ny  = nopen ++ (procToIntegerList py) ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Input (Address a) (Code py) q)) = tag ++ nx ++ ny ++ qx
--   where tag = (discriminator (Reflect (Input (Address a) (Code py) q)))
--         nx  = nopen ++ [a] ++ nclose
--         ny  = nopen ++ (procToIntegerList py) ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Input (Code px) (Address a) q)) = tag ++ nx ++ ny ++ qx
--   where tag = (discriminator (Reflect (Input (Code px) (Address a) q)))
--         nx  = nopen ++ (procToIntegerList px) ++ nclose
--         ny  = nopen ++ [a] ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Input (Address ax) (Address ay) q)) = tag ++ nx ++ ny ++ qx
--   where tag = (discriminator (Reflect (Input (Address ax) (Address ay) q)))
--         nx  = nopen ++ [ax] ++ nclose
--         ny  = nopen ++ [ay] ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Output (Code px) q)) = tag ++ nx ++ qx
--   where tag = (discriminator (Reflect (Output (Code px) q)))
--         nx  = nopen ++ (procToIntegerList px) ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Output (Address a) q)) = tag ++ nx ++ qx
--   where tag = (discriminator (Reflect (Output (Address a) q)))
--         nx  = nopen ++ [a] ++ nclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Par p q)) = tag ++ px ++ qx
--   where tag = (discriminator (Reflect (Par p q)))
--         px  = popen ++ (procToIntegerList (Reflect p)) ++ pclose
--         qx  = popen ++ (procToIntegerList (Reflect q)) ++ pclose
-- procToIntegerList (Reflect (Eval (Code px))) = tag ++ nx
--   where tag = (discriminator (Reflect (Eval (Code px))))
--         nx  = nopen ++ (procToIntegerList px) ++ nclose

--        bit string   open paren   close paren   contents & remainder of the string
-- unquote :: [(Unsigned 64)] -> [(Unsigned 64)] -> [(Unsigned 64)] -> Maybe ([(Unsigned 64)], [(Unsigned 64)])
-- unquote (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) =
--   if ([a,b,c,d] == [oa,ob,oc,od])
--   then
--     (h l [oa,ob,oc,od] [ca,cb,cc,cd] 1 [])
--   else Nothing
--   where h [] _ _ n acc                                        =
--           (if (n > 0) then Nothing else Just (acc,[]))
--         h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) 0 acc = Just (acc,(a:b:c:d:l))
--         h (a:b:c:d:l) (oa:ob:oc:od:[]) (ca:cb:cc:cd:[]) n acc =
--           (if ([a,b,c,d] == [oa,ob,oc,od])
--             then
--               (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n + 1) (acc ++ [a,b,c,d]))
--             else if ([a,b,c,d] == [ca,cb,cc,cd])
--                  then (h l [oa,ob,oc,od] [ca,cb,cc,cd] (n - 1) (if (n == 1) then acc else (acc ++ [a,b,c,d])))
--                  else (h l [oa,ob,oc,od] [ca,cb,cc,cd] n (acc ++ [a,b,c,d])))

-- integerListToProc :: [(Unsigned 64)] -> Maybe RhoProcess
-- getSubject :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
-- getObject :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
-- getContinuation :: [(Unsigned 64)] -> Maybe RhoProcess
-- getTransmission :: [(Unsigned 64)] -> Maybe RhoProcess
-- getParLeft :: [(Unsigned 64)] -> Maybe (RhoProcess,[(Unsigned 64)])
-- getParRight :: [(Unsigned 64)] -> Maybe RhoProcess
-- getNameCenter :: [(Unsigned 64)] -> Maybe RhoProcess

-- todo: replace with do-blocks

-- getNextEntity l open close =
--   case (unquote l open close) of
--    Just (contents, remainder) -> (case (integerListToProc contents) of
--      Just p -> Just (p, remainder)
--      Nothing -> Nothing)
--    Nothing -> Nothing

-- getLastEntity l open close =
--   case (unquote l open close) of
--    Just (contents, []) -> (integerListToProc contents)
--    _ -> Nothing

-- getNextName l = getNextEntity l nopen nclose

-- getSubject l = getNextName l  
   
-- getObject l = getNextName l

-- getParLeft l = getNextEntity l popen pclose

-- getContinuation l = getLastEntity l popen pclose

-- getTransmission l = getLastEntity l popen pclose

-- getParRight l = getLastEntity l popen pclose

-- getNameCenter l = getLastEntity l nopen nclose

-- integerListToProc [] = Just (Reflect Stop)
-- integerListToProc (0:0:0:0:[]) = Just (Reflect Stop)
-- integerListToProc (0:0:0:1:l) = 
--   case (getSubject l) of
--     Just (px,l') -> (case (getObject l') of
--       Just (py,l'') -> (case (getContinuation l'') of        
--         Just (Reflect q) -> Just (Reflect (Input (Code px) (Code py) q))
--         Nothing -> Nothing)
--       Nothing -> Nothing)
--     Nothing -> Nothing      
-- integerListToProc (0:0:1:0:l) =
--   case (getSubject l) of 
--     Just (px,l') -> (case (getTransmission l') of
--       Just (Reflect q) -> Just (Reflect (Output (Code px) q))
--       Nothing -> Nothing)
--     Nothing -> Nothing
-- integerListToProc (0:0:1:1:l) =
--   case (getParLeft l) of 
--     Just (pl,l') -> (case (getParRight l') of 
--       Just pr -> (case (pl,pr) of
--         ((Reflect ql),(Reflect qr)) -> Just (Reflect (Par ql qr)))
--       Nothing -> Nothing)
--     Nothing -> Nothing
-- integerListToProc (0:1:0:0:l) = 
--   case (getNameCenter l) of
--     Just q -> Just (Reflect (Eval (Code q)))
--     Nothing -> Nothing

-- roundtrip :: RhoProcess -> Bool
-- roundtrip p = case (integerListToProc (procToIntegerList p)) of
--   Just q -> p == q
--   Nothing -> False
\end{code}
