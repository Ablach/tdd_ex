module ch10Shapes

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
  Tri : ShapeView (triangle b h)
  Rec : ShapeView (rectangle w h)
  Cir : ShapeView (circle r)
  
export  
shapeView : (shape : Shape) -> ShapeView shape  
shapeView (Triangle x y) = Tri
shapeView (Rectangle x y) = Rec
shapeView (Circle x) = Cir

