import ch10DataStore
import ch10Shapes

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974)
                       (addToStore ("Venus", "Venera", 1961)
                       (addToStore ("Uranus", "Voyager 2", 1986)
                       (addToStore ("Pluto", "New Horizons", 2015)
                       empty ))) 
                       
listItems : DataStore schema -> List (SchemaType schema)                       
listItems x with (storeView x)
  listItems x | SNil = []
  listItems (addToStore value store) | (SAdd rec) = value :: listItems store | rec
  
getValues : DataStore (SString .+. val_schema)
            -> List (SchemaType val_schema)
getValues x with (storeView x)
  getValues x | SNil = []
  getValues (addToStore (k, v) store) | (SAdd rec) = v :: getValues store | rec

testStore' : DataStore (SString .+. SInt)
testStore' = addToStore ("First", 1) $
             addToStore ("Second", 2) $
             empty

area : Shape -> Double
area x with (shapeView x)
  area (triangle b h) | Tri = b * h / 2
  area (rectangle w h) | Rec = w * h
  area (circle r) | Cir = pi * r * r


