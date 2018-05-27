import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Cont
import Control.Monad.List

myTest :: Int -> ListT IO (Int, Int)
myTest n = do
  let squares = liftList . takeWhile (<=n) $ map (^(2::Int)) [0..]
  x <- squares
  y <- squares
  lift $ print (x,y)
  guard $ x + y == n
  lift $ putStrLn "Sum of squares."
  return (x,y)
 
runMyTest :: Int -> IO (Int, Int)  
runMyTest = fmap (fst . fromJust) . runListT . myTest