module Fuel

public export
data Fuel = Dry | More Fuel

export
partial
forever : Fuel
forever = More forever
