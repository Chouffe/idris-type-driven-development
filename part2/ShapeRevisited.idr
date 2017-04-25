module ShapeRevisited

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

export
data ShapeView : Shape -> Type where
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle radius)

total
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle

total
area : Shape -> Double
area x with (shapeView x)
  area (triangle base height) | STriangle = base * height / 2
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius
