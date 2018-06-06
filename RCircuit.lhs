\begin{code}
-- Allows GHC to automatically write code for mapping over register values,
-- and to automatically write code to fully evaluate writer state outputs.
{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module RCircuit where

-- CLaSH-provided hardware stuff
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
import CLaSH.Prelude.BlockRam (blockRam)

-- Plain old Haskell stuff
import Prelude (Show, Eq, print, (+), (-), (*), (==), (/=),(^),
    ($), (.), filter, take, fmap, mapM_, length, Functor,
    Bool(True,False), not, Maybe(Just,Nothing), (<$>), (<*>), undefined)
import qualified Prelude as Plude (zip,unzip,repeat,floor,(++))

import qualified RhoFold as RF (Nominal, Name(..), Behavioral, Process(..), RhoProcess)

-- Used to make sure that something is fully evaluated.
-- Good for making sure that our circuit 
-- doesn't have any undefined behavior.
import Control.DeepSeq (NFData, rnf)

import qualified Test.QuickCheck as QC

import GHC.Generics (Generic)

\end{code}
