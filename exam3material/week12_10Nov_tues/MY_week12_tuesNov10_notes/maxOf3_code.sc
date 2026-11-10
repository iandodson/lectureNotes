// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//just the code for finding the biggest of 3 numbers

val a: Z = Z.read()    //suppose a is 3
val b: Z = Z.read()    //suppose b is 5
val c: Z = Z.read()    //suppose c is 10
var max: Z = 0

/*
    mark where logic blocks would go
    finish the verification in the next file
*/

if (a >= b) {
  if (a >= c) {
    max = a

    Deduce (
      1 ( max == a ) by Premise,
      2 ( a >= b ) by Premise,
      3 ( a >= c ) by Premise,

      4 ( max >= a ) by Algebra*(1),
      5 ( max >= b ) by Algebra*(2, 1),
      6 ( max >= c ) by Algebra*(3, 1),
      7 ( max == a | max == b ) by OrI1(1)
    )

    //what do we need to show here?
  } else {
    max = c

    Deduce (
      1 ( max == c ) by Premise,
      2 ( a >= b ) by Premise,
      3 ( !(a >= c) ) by Premise,

      4 ( c >= a ) by Algebra*(3),
      5 ( c >= b ) by Algebra*(2, 4),

      6 ( max >= a ) by Algebra*(4, 1),
      7 ( max >= b ) by Algebra*(5, 1),
      8 ( max >= c ) by Algebra*(1),
    )

    //what do we need to show here?
  }
  //what do we put here?
} else {
  if (b >= c) {
    max = b

    //what do we need to show here?
  } else {
    max = c

    //what do we need to show here?
  }

  //what goes here?
}

//what goes here?
Deduce (

)

println("Max between ", a, ", ", b, " and ", c, " is ", max)

//How do we know we have the max?
//what assert(s) do we want?
assert(max >= a)
assert(max >= b)
assert(max >= c)
assert(max == a | max == b | max == c)
//where do we need to prove the asserts?