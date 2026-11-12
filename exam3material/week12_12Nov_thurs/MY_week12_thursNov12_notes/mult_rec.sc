// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?
  Contract(
    Requires( y >= 0 ),
    Ensures( Res[Z] == x*y )
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    //what do we need to do here?
    Deduce (
      1 ( y == 0 ) by Premise,
      2 ( answer == 0 ) by Premise,
      // 3 ( y >= 0 ) by Premise,
      3 ( answer == x*y ) by Algebra*(1, 2)
    )

  } else {
    //need to prove precondtion (requires) before recursive call
    Deduce (
      1 ( !(y == 0) ) by Premise,
      2 ( y >= 0 ) by Premise,

      3 ( y-1 >= 0 ) by Algebra*(1, 2)
    )

    //will tell me x*(y-1)
    //will be x + x + ... + x (a total of y-1 times)
    var temp: Z = mult(x, y-1)
    answer = x + temp

    //what do we need to show here?
    Deduce(
      1 ( temp == x*(y-1) ) by Premise,
      2 ( answer == x + temp ) by Premise,
      // 3 ( !(y == 0) ) by Premise,


      3 ( temp == x*y - x ) by Algebra*(1),
      4 ( answer == x + x*y - x ) by Algebra*(2, 3),
      5 ( answer == x*y ) by Algebra*(4)
    )
  }

  //what do we need to do here?
  //need to prove the postcondition
  //need: answer == x*y
  Deduce(
    1 ( answer == x* y ) by Premise
  )

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

Deduce (
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1)
)

var ans: Z = mult(a, b)

Deduce (
  1 (ans == a*b) by Premise,
  2 ( a == 5 ) by Premise,
  3 ( b == 4 ) by Premise,

  4 ( ans == 20 ) by Algebra*(1, 2, 3)
)

//what do we want to assert that ans is?
assert(ans == 20)