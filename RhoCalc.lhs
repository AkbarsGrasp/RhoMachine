data Process x = Stop | Input x x (Process x) | Output x (Process x) | Par (Process x) (Process x) | Eval x deriving Show

data Name p = Address (Unsigned 64) | Code p deriving Show

data RhoProcess = Process (Name RhoProcess) deriving Show

-- toBinaryArray :: RhoProcess -> Array Integer


