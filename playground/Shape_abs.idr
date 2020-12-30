-- Type-Driven Development - section 10.3

module Shape_abs

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

public export
data ShapeView : Shape -> Type where
  STriangle : {base, height : _} -> ShapeView (triangle base height)
  SRectabgle : {width, height : _ } -> ShapeView (rectangle width height)
  SCirce : {radius : _} -> ShapeView (circle radius)

export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectabgle
shapeView (Circle x) = SCirce


