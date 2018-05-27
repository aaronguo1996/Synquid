import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Cont
import Control.Monad.List

takeWhileM :: (Monad m) => (a -> Bool) -> [m a] -> m [a]
takeWhileM _ [] = return []
takeWhileM p (a:as) =
   do v <- a
      if p v
         then do vs <- takeWhileM p as
                 return (v:vs)
         else return []

myTest :: Int -> ListT IO (Int, Int)
myTest n = do
  let squares = takeWhileM (<=n) $ map (^(2::Int)) [0..]
  x <- squares
  y <- squares
  lift $ print (x,y)
  guard $ x + y == n
  lift $ putStrLn "Sum of squares."
  return (x,y)
 
runMyTest :: Int -> (Int, Int)  
runMyTest = fmap (fst . fromJust) . runListT . myTest
