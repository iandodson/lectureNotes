// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a

  Deduce (
    1 ( max == a ) by Premise,
    2 ( a > b ) by Premise,
    3 ( max >= a ) by Algebra*(1),
    4 ( max >= b ) by Algebra*(1, 2),

    //could use OrI1 to claim max == a | max == b
  )
  //show some claim
  //show claim A
} else {
  max = b

  Deduce (
    1 ( max == b ) by Premise,
    2 ( !(a > b) ) by Premise,
    3 ( a <= b ) by Algebra*(2),
    4 ( max >= b ) by Algebra*(1),
    5 ( max >= a ) by Algebra*(1, 3)

    //could use OrI2 to claim max == a | max == b
  )
  //show same claim
  //show claim B
}

//afterwards, I can put "claim" as a premise
//afterwards, I can put "A | B" as a premise
Deduce (
  1 ( max >= a ) by Premise,
  2 ( max >= b ) by Premise,
  3 ( max == a | max == b ) by Premise
  //need max >= a
  //need max >= b
  //need max == a | max == b
)

//how can we assert that we've found the max?
assert(max >= a)
assert(max >= b)
assert(max == a | max == b)