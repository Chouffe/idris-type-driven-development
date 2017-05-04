module State

import Control.Monad.State

increase : Nat -> State Nat ()
increase k = do
  current <- get
  put (current + k)


-- get : MonadState stateType m => m stateType
-- put : MonadState stateType m => stateType -> m ()
