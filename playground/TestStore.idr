-- Type-Driven Development - section 10.3

module TestStore

import DataStore
import Shape_abs

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974)
            (addToStore ("Venus", "Venera", 1961)
            (addToStore ("Uranus", "Voyager 2", 1986)
            (addToStore ("Pluto", "New Horizon", 2015)
            empty)))

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
  listItems empty | SNil = []
  listItems (addToStore entry store) | (SAdd entry store rec) = entry :: listItems store | rec

filterKeys : (test : SchemaType val_schema -> Bool) -> DataStore (SString .+. val_schema) -> List String
filterKeys test input with (storeView input)
  filterKeys test empty | SNil = []
  filterKeys test (addToStore (key, value) store) | (SAdd (key, value) store rec)
    = if test value then key :: filterKeys test store | rec
                    else filterKeys test store | rec

-- Exercise 1

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues input with (storeView input)
  getValues empty | SNil = []
  getValues (addToStore (key, value) store) | (SAdd (key, value) store rec)
    = value :: getValues store | rec

-- Exercise 2

area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = (base * height) / 2
  area (rectangle width height) | SRectabgle = width * height
  area (circle radius) | SCirce = 2 * 3.14 * radius

